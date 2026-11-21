# Nodes and composing contracts

The examples on this page run in order (`python/tests/test_readme.py`), from this setup:

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
from sverify.io import DeltaSink, DeltaSource
```

## Composing contracts

When one contracted transformation's result feeds another, the downstream
precondition is proved from the upstream contract without checking the
data:

```python
@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
              ensures=[_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull(), sv.unique("id")])
def paid(orders):
    return orders.filter(orders.amount.notnull())

@sv.transform(requires={"t": [_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull()]},
              ensures=[_.doubled >= 0, _.doubled.notnull()])
def doubled_paid(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)

expr = doubled_paid(paid(orders))
print(doubled_paid.report)
# proved
# The output guarantees:
#   doubled ≥ 0
#   doubled is never NULL
# Each run checks on the data:
#   t: amount ≥ 0          ← what `paid` guarantees, named by `t`, the parameter
#   t: amount is never NULL
#   t: no two rows share id
```

If the upstream contract doesn't imply the downstream precondition, the call
fails at once with a `CompositionError` (in `sverify.errors`) that names the
broken link.

## Nodes: composing, storing, refreshing

A source or a node pipes into a transform to build a new node, so a
job reads in the order its data flows: `orders.pipe(paid).pipe(doubled_paid)`
is one plan, the same as the call form `doubled_paid(paid(orders))`. The
chained node fills the transform's first table parameter, and its other
inputs come by keyword. `refresh()` brings a node up to date from the
changes to its sources, with the delta plans Lean derives, and the results
come out through `to_arrow()`, `to_polars()`, `to_pandas()` and `.table`, an
Ibis table to query further. An update is a delete plus an insert:

```python
customers = StaticSource(pa.table({"name": ["ada"], "city": ["Paris"]}), name="customers")

@sv.transform()
def cities(orders, customers):
    return orders.join(customers, orders.customer == customers.name).select(
        orders.id, customers.city)

c = orders.pipe(cities, customers=customers)   # fan-in: the other inputs by keyword
c.refresh()
customers.apply(Changes(inserts=[("cy", "Rome")]))
print(c.refresh())
# cities:
#   customers@v0→v1: 1 insert(s), 0 delete(s); Δ as applied to customers v0→v1
# ...
assert c.to_arrow().to_pylist() == [{"id": 3, "city": "Rome"}]
assert c.table.filter(_.city == "Rome").count().to_pyarrow().as_py() == 1
```

A step can also be SQL or a plain function. `sv.sql(query)` is a step whose
inputs are the tables the query reads: the keyword inputs bind their own
names, and the chained node binds to the one table left over (`name="orders"`
names it, and is checked). A plain function from Ibis tables to an Ibis
table is a transform with no contract:

```python
c2 = orders.pipe(
    sv.sql("SELECT o.id, c.city FROM customers c JOIN orders o ON o.customer = c.name"),
    customers=customers,
)                                                    # the chained node is `orders`
large = orders.pipe(lambda t: t.filter(_.amount > 20))
```

SQL is DuckDB's dialect. Sverify reads it with its own lift (SQLGlot)
and writes every choice DuckDB's SQL leaves implicit into the plan: `/` divides
as doubles, NULLs sort last, an integer literal has the narrowest type that
holds it.

Every check uses sverify's reference semantics unless you opt into DuckDB's.
`semantics="reference"`, the default, means what sverify's reference
computes, so a double divided by zero raises; `semantics="duckdb"` means what
DuckDB computes, which gives `inf`, and models NaN and ±inf as DuckDB has
them. `sv.sql(query, semantics=...)` attaches the choice to the query.
`sv.verify(..., semantics=...)` and `@sv.transform(..., semantics=...)` make
it for the SQL they lift themselves: a SQL transformation and SQL conditions.
An `sv.sql` expression inside an Ibis transformation keeps its own. The report
says which semantics it used (`Report.semantics`, a `semantics:` line).
`semantics="polars"` is pending like Spark's: Polars floors integer `//` and
`%`, so `-7 % 2` is `1` there, and until the checker reports under Polars's own
profile
the report is the reference's, with the stated `FLOOR` read by the core, and a
`ProfilePendingWarning` says so ([engine-profiles.md](engine-profiles.md#polars-as-a-profile)).
`semantics="spark"` reads an Ibis transformation as Spark 4.3.0 computes it
under ANSI mode, and doubles that overflow are ±inf with no precondition.
Until the checker reports under Spark's own profile,
the report is the reference's, `report.semantics` says `"reference"`, a
`ProfilePendingWarning` says so, and the plan reaches Spark through its
translation ([engine-profiles.md](engine-profiles.md#spark-as-a-profile)).
The lift reads a subset (SELECT, WHERE,
joins of every kind, subqueries and CTEs, GROUP BY with grouping sets,
windows, set operations, ORDER BY, LIMIT, CASE, CAST, and the numeric,
string, date and list functions of
[the coverage targets](coverage-targets.md)) and
refuses the rest, saying what.

A node that ends in `COUNT` and integer `SUM` per group, or in `DISTINCT`,
over an input with delta rules, is maintained from a count and a sum per
group, which each batch's change adds to
(`LinearAgg.aggregate_maintained` in
[`analysis/Sverify/Analysis/IncrementalAgg.lean`](../analysis/Sverify/Analysis/IncrementalAgg.lean),
[section 6 of the optimizations note](optimizations.md#6-incremental-maintenance)).
`DECIMAL` `SUM` and `AVG` keep the same state, `SUM`, `AVG`, `VAR`,
`STDDEV`, `COVAR` and `CORR` of doubles an exact one, rounded once, with no
drift
(`LinearAgg.fsum_no_drift` in
[`analysis/Sverify/Analysis/IncrementalFloat.lean`](../analysis/Sverify/Analysis/IncrementalFloat.lean)), and `MIN` and `MAX` keep each
group's extreme: a batch that only inserts into a group merges, and the
groups it deletes from are recomputed from the new input
(`ExtremeAgg.extreme_maintained` in
[`analysis/Sverify/Analysis/IncrementalMinMax.lean`](../analysis/Sverify/Analysis/IncrementalMinMax.lean)).
A node that ends in a semi or anti join on equal keys keeps a count of
matches per key and reads the left input only for the keys whose count
leaves or returns to 0 (`SemiDelta.semi_maintained` in
[`analysis/Sverify/Analysis/IncrementalSemi.lean`](../analysis/Sverify/Analysis/IncrementalSemi.lean)).
A node without delta rules (left join, other aggregates, window, `LIMIT`) is
recomputed and diffed instead, and `status()` says so. An
aggregate whose input has delta rules recomputes only the groups a batch
touches: Sverify takes the group keys of the input rows the batch inserts or
deletes, recomputes those groups from the new input (a semi-join on the
keys), and replaces their rows. This holds for every measure, because an
aggregate's groups are independent (see [proved-theorems.md](proved-theorems.md)).
A projection whose window functions share one `PARTITION BY`, with the
partition keys among its columns, recomputes the partitions a batch touches
the same way, for inputs without ties on the partition and sort columns. With a time bucket among the keys, the
recompute reads only the range the touched buckets cover.

Window aggregates over bounded RANGE frames of one time column, such as the
sum over the last five minutes per host, recompute only the rows near the
change: for a batch whose rows span `[t0, t1]`, the output rows from
`t0 - end` to `t1 - start` of the touched partitions (or of the whole
table, without `PARTITION BY`), from the input rows in that span
widened by the frame. Lean proves that a window value depends only on the
rows in its frame, so this equals a full recompute for inputs without ties
on the partition and time columns (`TouchedFrames.framed_batch` in
[`analysis/Sverify/Analysis/TouchedFrames.lean`](../analysis/Sverify/Analysis/TouchedFrames.lean)),
and `status()` says "touched frames recomputed". The tests
([`test_touched_frames.py`](../python/tests/test_touched_frames.py)) compare
every refresh with a full recompute on random streams with late rows, rows
on the frame edges, and duplicate and NULL times.
`status()` says "touched groups recomputed", and the refresh summary gives
how many groups each batch touched ("12 touched group(s) recomputed") or
"recomputed and diffed". Filters and projections over the aggregate that
keep the group keys keep this strategy; SQL steps and aggregates over
another aggregate or a window are recomputed and diffed. Contracted
nodes keep their guarantees in every state: their preconditions on the
sources are checked in full once, then only on each batch.

A node whose transform has `on_unproved="check"` checks the postconditions
Lean could not prove on its output at every refresh: on the full result the
first time, then on the rows each batch inserts, before its sink commits. A
violation raises `PostconditionError`, and the refresh writes nothing. The
report marks those postconditions as checked on data, and transforms
downstream may assume only the proved ones, so such a node is stored with
`.write` before another transform reads it:

```python
@sv.transform(ensures=[_.amount < 1_000], on_unproved="check")
def capped(orders):
    return orders.select(orders.id, orders.amount)

n = orders.pipe(capped)    # no VerificationError: checked at refresh
print(capped.report)
# Each run checks on the data:
#   output: amount < 1000
# ...
print(n.refresh())
# capped:
#   computed
#   ensures capped: (_.amount < 1000) (checked on data)
```

`.write(sink)` stores a node, as a cache in the middle of a job or as its
output, and returns the stored node, which transforms downstream read as a
versioned source. Without a `.write` in between, transforms fuse into one
plan and the intermediate rows are never stored:

```python
paid_orders = orders.pipe(paid).write(DeltaSink("lake/paid"))         # stored: a source
report = paid_orders.pipe(doubled_paid).write(DeltaSink("lake/report"))
print(report.refresh(engine="polars"))  # paid first, then report; each written once
# paid:
#   computed
# ...
```

`refresh()` on any node brings its whole lineage up to date, upstream first,
writing every stored node exactly once per state. To fan out, assign the
shared node to a variable and pipe it into each branch;
`sv.group(a, b).refresh()` refreshes several nodes against the same source
versions, and a stored node they share is refreshed and written once:

```python
totals = paid_orders.pipe(lambda t: t.group_by("customer").aggregate(n=t.count()))
print(sv.group(report, totals).refresh())  # paid is refreshed and written once
# paid:
# ...
```

The engine is chosen at refresh time: `"duckdb"` (the default, in memory),
`"polars"`, `"spark"` or a Spark session. The nodes keep their
state while the process runs; a stored node's table is its durable state.

A job that refreshes every minute logs `summary()`, one line per node, and
`str()` keeps the full report. A node's entry is in full when its refresh did
something notable: its first refresh, a source recomputed for want of a change
feed, a schema change, or a sink overwriting its table. A failed check raises,
and its message says which rows failed what:

```python
customers.apply(Changes(inserts=[("dan", "Oslo")]))
print(c.refresh().summary())
# cities: changes from orders v1, customers v1→v2 (change feed)
```
