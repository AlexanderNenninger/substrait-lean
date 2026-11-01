# substrait-lean

**Prove a data pipeline's contracts before it runs, get the same result on
DuckDB, Polars, DataFusion and Spark, and keep it up to date from Delta Lake
and Iceberg change feeds.**

You write a transformation in [Ibis](https://ibis-project.org) or SQL, as
usual, and say what it assumes about its inputs (`requires`) and what it
guarantees about its output (`ensures`). The Python package `sverify` hands
the query plan to a checker written in [Lean](https://lean-lang.org), a
proof assistant, which proves the guarantees for every possible input or
says why it can't. The checked plan then runs on the engine you choose.

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import StaticSource

orders = StaticSource(  # in memory; Delta and Iceberg tables work the same way
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)

@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

big = orders.pipe(big_orders)  # proved here, before any data runs
big.refresh()             # computed, on DuckDB by default
orders.apply(sv.Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))
big.refresh()             # updated from the changes alone
assert big.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
```

The three postconditions were proved before anything ran, and the result
was updated from the changes alone, by a plan proved to give the same result
as a full recompute.

## Where it stands

sverify is a young, independent project, and for now it is purely
observational. It tells you what it can and can't prove about your
transformations, and it describes how each engine behaves as we observed it:
at pinned versions, through their documentation, their own test suites and
our differential tests. Those findings describe engines; they don't certify
or rank them, and sverify isn't affiliated with any engine's project or
vendor. Use it as a careful second pair of eyes on your pipelines rather
than a gate production depends on, and expect the API to keep changing
between minor releases.

What it's for is making data engineering more joyful: fewer 3 a.m. pages
over a NULL nobody expected, fewer afternoons spent finding out why two
engines disagree, and more trust in the tables you hand to the next team.

### Engine tiers

Not every engine is held to the same standard yet ([#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211)):

| Tier | Engines | What it means today |
|---|---|---|
| **1** | DuckDB | Characterized as a diff against the reference model ([`characterization/duckdb/`](characterization/duckdb/FACTS.md)): every reference behaviour is native, shimmed or refused, and the shims are proved. In progress ([#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185)). |
| **2** | Polars, Spark, DataFusion | Run checked plans and are differentially tested against `Rel.eval` in CI, with known deviations documented. Not yet characterized or proved; Polars and Spark aim for Tier 1. |
| **3** | Snowflake | Aspirational: sverify writes Snowflake SQL and checks it on an emulator, [fakesnow](https://github.com/tekumara/fakesnow), but not yet on a real account ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)). |

SQL strings are compiled to Substrait by DataFusion today. That is planned to
change: SQL will need [Isthmus](https://github.com/substrait-io/substrait-java/releases),
and DataFusion will be an execution backend only ([#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211)).

## What it does for you

In order of what it is worth in day-to-day data engineering:

1. **Contracts proved before the pipeline runs.** The checks you would
   write as dbt tests or data expectations (`not_null`, `unique`, accepted
   ranges, relations between columns) hold on every input that meets the
   preconditions, not just on the data you tested with. A test finds a
   NULL city after a left join when one shows up in production; the checker
   refuses `not_null(city)` when you write the model. **Runtime errors**
   (division by zero, integer overflow, bad casts, regular expressions that
   don't compile) are ruled out the same way, or reported before the job
   can fail at 3 am. Preconditions are checked on the data, or proved from
   Delta and Iceberg metadata (schemas, CHECK constraints, file statistics).
2. **One plan, the same answer on every engine.** Develop on DuckDB or
   Polars, run on Spark (and, one day, on Snowflake). The same SQL text doesn't mean the
   same thing on each (`/` on integers truncates in DataFusion and
   PostgreSQL and gives a double in DuckDB and Spark; DataFusion wraps on
   overflow where DuckDB raises; NULLs sort first or last depending on the
   engine). sverify translates the checked plan for each engine with every
   such choice spelled out, or refuses the plan where an engine can't
   match, as for windows over a Snowflake table with ties.
3. **Results kept up to date from the changes, provably.** Instead of a
   watermark job ("process the rows newer than…"), which misses deletes,
   late rows and new join matches, sverify updates a result from the
   inserts and deletes alone, with a delta plan proved equal to a full
   recompute. It reads Delta's Change Data Feed and Iceberg's appends
   (skipping the Delta files a proof shows a filter can't match),
   writes each state to a Delta or Iceberg sink exactly once, and the sink
   carries the proved contract to the next job, which builds on it instead
   of re-checking the data.
4. **Proved optimizations.** A plan can be split across shards (Delta or
   Iceberg partitions, files) and the results combined, with a proof that
   the result is the same; per-row overflow checks can be dropped where a
   contract proves them unnecessary; and a plan can be rewritten with what
   its contract establishes (a `DISTINCT` over a key or an implied filter
   goes, a left join on a NOT NULL foreign key becomes an inner join). See
   [docs/optimizations.md](docs/optimizations.md).

**What it doesn't do (yet).** DECIMAL columns are refused (keep money as
integer cents); framed window aggregates (running totals, moving averages),
`RANK` and `NTILE` are not in the model; and incremental maintenance covers
filters, projections, inner and cross joins and `UNION ALL`. Other views (left
joins, aggregates, windows, `DISTINCT`) are recomputed and diffed inside a
are recomputed and diffed instead, and `node.status()` says so. [What is supported](#what-is-supported) has
the full table.

## Workflows

Three complete jobs, condensed from the [query catalogue](catalogue/INDEX.md)
of 139 real analytical queries, are the first chapters of the
[tour](#the-tour). Each starts from source tables, states and proves a
contract, runs on every engine, keeps up with new data, writes a sink, and
shows what goes wrong without the checker. They run headless in CI, so they
stay correct.

| Workflow | Sources and sinks | What the checker catches |
|---|---|---|
| [Duplicate card payments](notebooks/01_duplicate_payments.py) | Delta table with Change Data Feed → Delta sink → a downstream job | a self-join matching each payment with itself; a watermark job that misses a late duplicate and keeps a reversed one |
| [Sensor alerts](notebooks/02_sensor_alerts.py) | Iceberg table → Iceberg sink | an alert over `LAG` that depends on how ties break; a NaN reading raising a false alert (`NaN > 30` is TRUE in SQL); a sensor sending twice |
| [An orders mart](notebooks/03_orders_mart.py) | Delta orders and a type-2 customer dimension → Delta sink | dbt's `not_null(city)` failing after a point-in-time left join; `/` meaning three things on three engines |

The first, in outline:

```python
import datetime as dt
from pathlib import Path
from tempfile import mkdtemp

import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from sverify.engines import ENGINES
from sverify.io import DeltaSink, DeltaSource

lake = Path(mkdtemp())
TXN = pa.schema([
    pa.field("txn_id", pa.int64(), nullable=False),
    pa.field("card_id", pa.int64(), nullable=False),
    pa.field("merchant", pa.string()),
    pa.field("amount_cents", pa.int64(), nullable=False),
    pa.field("ts", pa.timestamp("us"), nullable=False),
])

def txns(*rows):
    return pa.Table.from_pylist([dict(zip(TXN.names, r)) for r in rows], schema=TXN)

def at(minute):
    return dt.datetime(2026, 3, 2, 9, minute)

write_deltalake(lake / "transactions",
                txns((1, 10, "coffee", 450, at(0)), (2, 10, "coffee", 450, at(2)),
                     (3, 11, "books", 2599, at(10))),
                configuration={"delta.enableChangeDataFeed": "true"})
DeltaTable(lake / "transactions").alter.add_constraint({"non_negative": "amount_cents >= 0"})

@sv.transform(
    requires={"transactions": [sv.unique("txn_id"), _.amount_cents >= 0,
                               _.ts < dt.datetime(2100, 1, 1)]},
    ensures=[sv.unique("first_txn", "duplicate_txn"), _.first_txn < _.duplicate_txn,
             _.merchant.notnull(), _.amount_cents >= 0],
)
def duplicate_payments(transactions):
    a, b = transactions, transactions.view()
    return a.join(
        b,
        (a.card_id == b.card_id) & (a.merchant == b.merchant)
        & (a.amount_cents == b.amount_cents) & (a.txn_id < b.txn_id)
        & (b.ts >= a.ts) & (b.ts <= a.ts + ibis.interval(minutes=5)),
    ).select(first_txn=a.txn_id, duplicate_txn=b.txn_id, merchant=a.merchant,
             amount_cents=a.amount_cents)

transactions = DeltaSource(str(lake / "transactions"))
dups = transactions.pipe(duplicate_payments)  # proves the contract
sink = DeltaSink(str(lake / "duplicate_payments"))
stored = dups.write(sink)  # NOT NULL and CHECK constraints from `ensures`, the contract in the commit
first = stored.refresh()   # checks the preconditions, computes, writes
for p in first["duplicate_payments"].preconditions:
    print(p)
# transactions: unique(txn_id) (checked on data)
# transactions: (_.amount_cents >= 0) (Delta constraint)
# transactions: (_.ts < datetime.datetime(2100, 1, 1, 0, 0)) (file stats @v1)

# A late duplicate of transaction 3 arrives, and transaction 2 is reversed.
t = DeltaTable(lake / "transactions")
write_deltalake(t, txns((4, 11, "books", 2599, at(13))), mode="append")
t.delete("txn_id = 2")
print(stored.refresh())  # the Change Data Feed v1→v3, the proved delta plans, one MERGE commit
# duplicate_payments:
#   transactions@v1→v3: 1 insert(s), 1 delete(s); Δ trusted as coming from Delta CDF v1→v3
# ...
#   wrote duplicate_payments from transactions@v3: merge v3, 1 row(s) written, 1 deleted
assert stored.to_arrow().to_pylist() == [
    {"first_txn": 3, "duplicate_txn": 4, "merchant": "books", "amount_cents": 2599}]

for engine in ENGINES:  # the same rows on DuckDB, Polars and DataFusion
    again = duplicate_payments(transactions)
    again.refresh(engine=engine)
    assert again.to_arrow().to_pylist() == stored.to_arrow().to_pylist()
```

## What goes wrong without it

The catalogue probed its 139 queries on DataFusion, DuckDB, Polars and
Snowflake SQL and recorded each query's cross-engine pitfalls
([`pitfalls.toml`](catalogue/pitfalls.toml), [FINDINGS](catalogue/FINDINGS.md)).
The most common, and what sverify does about each:

| Pitfall | What the engines do | sverify |
|---|---|---|
| **Ties** in `ROW_NUMBER`, `LAG`, `LIMIT`, top-N, dedup (44 of the 139 queries) | no engine promises an order among ties; Snowflake and Spark tables have no row order at all | without a key that rules ties out, nothing is proved (`deterministic=False`); Snowflake and Spark SQL is only written with a proved `tie_free=True` |
| **NULL join keys** | SQL engines never match them; pandas `merge` does, Polars with `nulls_equal=True` | the model's semantics, on every engine; proofs use it (`merchant` is never NULL after `a.merchant = b.merchant`) |
| **Integer division** | DataFusion and PostgreSQL truncate; DuckDB and Spark give a double; Snowflake a NUMBER with extra scale | truncates on every engine |
| **Division by zero** (14 queries) | DataFusion, Snowflake and PostgreSQL raise; DuckDB returns NULL; Polars null or inf | proved impossible, or reported as `may fail` before the job runs |
| **Integer overflow** | DataFusion wraps silently; DuckDB raises; Snowflake's NUMBER(38) doesn't overflow | reported as a warning; the engines raise instead of wrapping |
| **NaN** | in SQL engines NaN equals itself and is above every number (`NaN > 30` is TRUE); in Python and pandas it compares False | one NaN, as SQL engines have it, on every engine; contracts see it (`~_.v.isnan()` is refused unless proved) |
| **`NOT IN` with a NULL** | standard SQL returns no rows; DataFusion gets it wrong | refused; write an anti join |
| **Guards that don't guard** | DataFusion evaluates both branches of some `CASE`s and merges filters, so `WHERE n <> 0 AND x / n > 1` can still fail | the runtime-error analysis only counts guards that hold: a `CASE` branch, `NULLIF`, a filter below a projection |
| **NULL ordering** | DataFusion, PostgreSQL and Snowflake put NULLs last ascending and first descending, DuckDB last both ways, Spark first ascending, a Polars sort first | every `ORDER BY` says where NULLs go |

Front ends change meaning too: the catalogue found Ibis rewriting TPC-H Q11's
threshold (a total over all parts) into each part's own sum, so the query
compared each part with itself, and nothing failed. Chapters
[16](notebooks/16_datafusion_semantics.py) and
[17](notebooks/17_backend_semantics.py) of the tour check every such quirk
against the model.

## Using sverify

```bash
pip install sverify                 # or: uv add sverify
pip install 'sverify[delta,iceberg,polars,datafusion,spark]'   # or 'sverify[all]'
```

The core runs on DuckDB: contracts, incremental maintenance, and the
SQL for DuckDB, Snowflake and Spark. The extras add `datafusion` (an engine,
and the default compiler for SQL strings), `polars`, `spark` (runs plans on
a Spark session; needs Java 17 or 21), `delta` and `iceberg`. Wheels bundle
the Lean checker as a small native binary, so you need no Lean toolchain;
they exist for Linux (x86_64, aarch64) and macOS (arm64, x86_64), Python
3.12 and later.

The [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents every public function and class, for the released version (built
from `python/great-docs.yml` with `uv run poe docs`), and so do
[agent skills](https://alexandernenninger.github.io/substrait-lean/skills.html)
for coding agents that write sverify code (`npx skills add
https://alexandernenninger.github.io/substrait-lean/`, or `sverify/skills/` in
the wheel). The [tour](#the-tour)
explains each feature in a chapter of its own
(chapters 4 to 12).

### Contracts

`@sv.transform` decorates a function from Ibis tables to an Ibis table.
Called on a source or another node, it builds a node (and on Ibis tables, an
Ibis expression). Each call proves the postconditions before it returns:

```python
@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)
print(doubled.last_report)
# requires orders: (_.amount >= 0)
# requires orders: _.id.notnull()
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer ≥ 22
```

Lean worked out that `doubled` is at least 22: the filter keeps only
`amount > 10`, and doubling preserves that. A postcondition that doesn't
follow is refused, with what *is* known:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

from sverify.errors import CompositionError, NotIncremental, VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# could not prove: (_.total > 5) (it is TRUE or FALSE)
# ...
#   total: an integer ≥ 1
```

* **Conditions** are Ibis expressions (`_.amount >= 0`) or SQL snippets
  (`"amount >= 0"`). SQL transformations are checked with
  `sv.verify(sql, tables=..., requires=..., ensures=...)`, which returns the
  report.
* **Preconditions** describe data that comes from outside. On a source, they
  are checked on the data when the node is first refreshed and then on each
  batch (`PreconditionError`), or proved from the table's metadata; on Ibis
  tables bound to data (`sv.connect()`), at call time.
* **Unproved postconditions** raise `VerificationError`. With
  `on_unproved="runtime"` they are checked on the output data instead
  (`PostconditionError`); with `on_unproved="warn"` you get a warning.
* **What Lean tracks** per column: whether it can be NULL, integer, double
  and timestamp ranges, which booleans it can be, and whether it can be a
  string. Filters (`amount > 10`, `x IN (1, 2, 3)`, `x IS NOT NULL`) refine
  those facts; arithmetic, `CASE`, `COALESCE`, joins and `UNION ALL` carry
  them through. Schemas count: a non-nullable column is never NULL.
* **Relations between columns:** join and filter conditions such as
  `w1.ts = w0.ts + 60`, `a.ts = b.ts`, `t0 < t1` or `value != -9999` become
  facts about each row, so postconditions like `t1 - t0 == 60` or
  `first_txn < duplicate_txn` follow.
* **Keys:** `sv.unique("user_id", "ts")` says there is at most one row per
  key. In `requires` it is checked on the data; in `ensures` it is proved
  (keys survive filters, projections, aggregates and joins whose condition
  pins down the other side's key).
* **Foreign keys:** `sv.references("cust", "customers", "id")` in `requires`
  says every non-NULL `cust` occurs in `customers.id` (checked on the data,
  like `unique`). It is only an assumption: nothing proves it in `ensures`.
* **Windows:** `LAG`, `LEAD` and `ROW_NUMBER` over `PARTITION BY … ORDER BY`.
  If rows can tie in the order, the engine decides which comes first, so
  every postcondition is `undetermined` and `report.deterministic` is
  `False`; a key on the partition and order columns fixes that.
* **ASOF joins:** `sv.asof_join(left, right, on="ts", by="device",
  tolerance=...)` matches each row with the latest earlier row of the other
  table, built from a range join and `ROW_NUMBER` that Lean checks like any
  plan.
* **Doubles and time:** comparisons with constants are exact, including
  sentinels like `-9999.0`, `isnan()` and intervals; doubles compare as SQL
  engines compare them, with one zero and one NaN above every number.
* **Not tracked yet:** string contents, DECIMAL columns, relations beyond
  "column plus constant" (`a < 2 * b`), and counts across rows (so
  `COUNT(*) >= 1` in a group is not known).

### Runtime errors

The report lists every runtime error that may happen on some input that
meets the preconditions, and `@sv.transform` refuses the transformation
while there is one:

```python
@sv.transform(requires={"orders": [_.amount >= 0]})
def share(orders):
    return orders.select(orders.id, per_unit=orders.amount // (orders.amount - 30))

try:
    share(orders)
except VerificationError as e:
    print(str(e).splitlines()[0])
# could not prove: no runtime error (division by zero: ($2 % ($2 - 30))), ...
```

Errors are what an engine fails on: integer division or remainder by zero,
`MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions that may
not compile. Warnings are what an engine gets silently wrong: `+`, `-`, `*`
and `SUM` leaving 64 bits, where DataFusion wraps around. Guards are
understood where the engine respects them: in a `CASE` branch or
`NULLIF(n, 0)`, and in a filter below a projection, but not in the same
`AND`.

### Composing contracts

When one contracted transformation's result feeds another, the downstream
precondition is **proved** from the upstream contract, not checked on the
data:

```python
@sv.transform(requires={"orders": [_.amount >= 0, sv.unique("id")]},
              ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")])
def paid(orders):
    return orders.filter(orders.amount.notnull())

@sv.transform(requires={"t": [_.amount >= 0, _.amount.notnull()]},
              ensures=[_.doubled >= 0, _.doubled.notnull()])
def doubled_paid(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)

expr = doubled_paid(paid(orders))
print(doubled_paid.last_report)
# requires paid: (_.amount >= 0)          ← what `paid` guarantees, not `orders`
# requires paid: _.amount.notnull()
# requires paid: unique(id)
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
```

If the upstream contract doesn't imply the downstream precondition, the call
fails at once with a `CompositionError` (in `sverify.errors`) that names the
broken link.

### Nodes: composing, storing, refreshing

A source or a node **pipes** into a transform to build a new **node**, so a
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
customers.apply(sv.Changes(inserts=[("cy", "Rome")]))
print(c.refresh())
# cities:
#   customers@v0→v1: 1 insert(s), 0 delete(s); Δ as applied to customers v0→v1
# ...
assert c.to_arrow().to_pylist() == [{"id": 3, "city": "Rome"}]
assert c.table.filter(_.city == "Rome").count().to_pyarrow().as_py() == 1
```

A step can also be SQL or a plain function. `sv.sql(query)` is a step whose
inputs are the tables the query reads: the keyword inputs bind their own
names, and the chained node binds to the one table left over (`as_="orders"`
names it, and is checked). A plain function from Ibis tables to an Ibis
table is a transform with no contract:

```python
c2 = orders.pipe(
    sv.sql("SELECT o.id, c.city FROM customers c JOIN orders o ON o.customer = c.name"),
    customers=customers,
)                                                    # the chained node is `orders`
large = orders.pipe(lambda t: t.filter(_.amount > 20))
```

A node without delta rules (left join, aggregate, window, `DISTINCT`,
`LIMIT`) is recomputed and diffed instead, and `status()` says so. Contracted
nodes keep their guarantees in every state: their preconditions on the
sources are checked in full once, then only on each batch.

**`.write(sink)` stores a node**, as a cache in the middle of a job or as its
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
`"polars"`, `"datafusion"`, `"spark"` or a Spark session. The nodes keep their state while the process
runs; a stored node's table is its durable state.

### Delta Lake and Iceberg

`sverify.io` reads and writes Delta Lake (delta-rs) and Iceberg (pyiceberg)
tables. A table format plays three roles:

* **A change source.** A transform reads `DeltaSource(uri)` or
  `IcebergSource(catalog, identifier)` directly. The first `refresh()` loads
  a snapshot and records its version; each later one reads the Change Data
  Feed (or, for Iceberg, the files that appends added) from that version to
  the latest, applies it, and records the new version. A failed refresh
  changes nothing, so a retry never applies a batch twice. Where the history
  is gone (CDF off, files vacuumed, row-level deletes in Iceberg), the data
  files that changed are diffed, and the report says so.
  `refresh(audit=True)` also compares the batch with the new snapshot and
  every node with a recompute, before committing anything (`AuditError`).
* **A source of preconditions.** `requires` conditions are proved from
  schema nullability, Delta CHECK constraints and per-file statistics:
  min/max of integers, doubles (only where the files count no NaN), dates
  and timestamps, and NULL counts, so a nullable column still proves
  `amount >= 0 OR amount IS NULL`. A batch only uses the statistics of the
  files it added. Strings, decimals and zoned timestamps get no bounds, and
  keys are always checked on the data, since neither format enforces them.
* **Proved file pruning (Delta).** `DeltaSource(uri, where="amount * 2 > 100")`
  reads only the rows on which the condition is TRUE, and skips a file only
  if Lean proves from its statistics that the condition is TRUE on none of
  its rows. That covers conditions the readers' own statistics pushdown
  doesn't, such as arithmetic on a column. Changes are filtered the same
  way, and the condition becomes a fact about every row for the contracts.
* **A sink that carries the contract.** `node.write(DeltaSink(uri))` and
  `node.write(IcebergSink(catalog, identifier))` store a node in one commit
  per state, exactly once (keyed by the source versions).
  The proved guarantees become NOT NULL columns and CHECK constraints (Delta)
  or table properties (Iceberg), and the commit records the plan hash, the
  source versions and the contract. A job that reads the table gets its
  preconditions from them. After the first write, `DeltaSink` MERGEs each
  change in one commit, and `IcebergSink` writes it as one snapshot of
  position delete files and a data file of the new rows.

**Schema changes.** A batch whose data fits the old schema (added columns,
widened types whose values still fit) is read in it, and the report names
the change. Otherwise the nodes reading the source are planned again and
recomputed, except a node with a contract, whose proof was for the old
schema: `refresh` then raises `SchemaError` and changes nothing.

**Tables outside a table format**, such as a small lookup table, are
`StaticSource(table, version=1, name="regions")`, so that sinks still have a
version for every input; `regions.apply(sv.Changes(...))` changes some rows,
and `regions.replace(new_table, version=2)` swaps the table, which recomputes
the nodes that read it.

**Your own sources and sinks** take one method each. A `sverify.io.Source`
implements `read(since)`, which returns the new rows and a cursor;
`from_query(fn, cursor_on="ts")`, `from_frame(fn)` and `from_files(path)`
build one from a function or a directory. sverify numbers the reads as
versions, works out the change, and says in the report what the reads
assume ("rows only arrive with a greater ts"), which `refresh(audit=True)`
checks. A `sverify.io.Sink` implements `write(change)` and optionally
`committed()`, and sverify writes each state once, with its contract;
`sink_from(fn)` hands the whole table to a function. `Storage` holds object
store credentials, or a function that renews them, for every table that
needs them. [Chapter 10](notebooks/10_pipelines.py) of the tour walks
through both.

**A restarted job resumes from its sink** instead of recomputing: build the
same nodes again and refresh. A stored node takes the stored rows only if
its plan and source versions match what the sink recorded; otherwise it is
computed, and the report says why:

```python
restarted = DeltaSource(str(lake / "transactions")).pipe(duplicate_payments).write(
    DeltaSink(str(lake / "duplicate_payments")))
print(restarted.refresh())
# duplicate_payments:
#   resumed from .../duplicate_payments@v3
# ...
#   wrote duplicate_payments from transactions@v3: already committed (v3)
```

Each refresh report names what it trusted: that the change feed turns the
old snapshot into the new one, and that writers and file statistics are
correct (Delta's millisecond timestamp maxima are widened by 999 µs; with
deletion vectors the statistics cover deleted rows too, which still bounds
the live ones). Iceberg tables with equality deletes can't be read. What is
proved is listed under [Table formats](#table-formats).

### Engines and SQL

```python
import json

from sverify.engines import SNOWFLAKE, create_table, run, to_sql  # also DUCKDB, SPARK

plan = c.plan                                  # the plan Lean checked
c.refresh(engine="polars")                     # or "duckdb" (the default), "datafusion", "spark"
con = sv.connect()                             # or run a plan on tables of your own
create_table(con, "orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
             [(2, "bob", 5), (3, "cy", 50)])
create_table(con, "customers", ibis.schema({"name": "string", "city": "string"}),
             [("ada", "Paris"), ("cy", "Rome")])
run(con, plan, "polars")
snowflake_sql = to_sql(json.loads(plan), SNOWFLAKE)  # or sverify.engines.Unsupported, saying why
```

`refresh(engine=...)` picks where a node's plans run; `sv.connect(engine=...)`
and `engine=` on a transform pick where checks on data run.
`sverify.engines.run_spark(plan, tables)` runs the Spark SQL on a local
session or one you pass (the `spark` extra). The generated SQL makes some
assumptions about the warehouse:

* **Snowflake:** time columns are `TIMESTAMP_NTZ`, strings have no
  collation, and tables and columns have quoted lower-case names.
* **Spark and Databricks:** the session uses the settings of
  `sverify.engines.SPARK_CONF` (ANSI mode, a pinned time zone, NTZ
  timestamps, case-sensitive names), and strings use the default
  `UTF8_BINARY` collation.
* Both have no row order, so sorts, `LIMIT` and windows are refused unless
  you pass `tie_free=True` (justified by a report's `deterministic`), and
  so is a `SUM` or `AVG` of doubles, whose rounding depends on the order of
  the additions. Snowflake has no interval type, so interval-valued
  expressions are refused there.

How the engine translations relate to the reference semantics, and where
that is going, is in [docs/engine-profiles.md](docs/engine-profiles.md).

### Sharding and other optimizations

`sverify.engines.run_sharded(plan, shards, sharded=[...], broadcast=...)`
runs a plan on each shard of its data and combines the results, with a Lean
proof that this equals the result on all the data. Filters, projections and
joins with a broadcast table are concatenated; `COUNT`, integer `SUM`, `MIN`
and `MAX` combine in two phases; with split keys (`keys={"orders":
["region"]}`, as a partition column guarantees), aggregates grouped by the
key, co-partitioned joins and tie-free windows run per shard. Anything else
raises `NotShardable` with the reason. When a report says `guard_free`,
`to_sql(..., guards=False)` leaves out the per-row overflow checks. And
`sv.verify(...).optimized` is the transformation rewritten with what the
preconditions establish, with `rewrites` naming the changes (a `DISTINCT`
over a key goes, a filter the preconditions imply goes, a left join on a NOT
NULL foreign key becomes an inner join, an unread join to a dimension goes);
run it instead of the original on data that meets the preconditions
([Contracts](#contracts-1) under How it works lists them).
[docs/optimizations.md](docs/optimizations.md) compares these with what the
engines already do.

### Testing with pytest

Installing sverify registers a pytest plugin, so your suite can test its
transforms without a conftest. `sverify.testing.assert_contract(node)`
asserts that a node's contract is proved; with `data=` and `expected=` it
also runs the node on those rows, checks the preconditions and
postconditions on them, and diffs the output against the expected rows.
`assert_engines_agree(node, data)` runs it on every installed engine and
diffs their results. `cases(node)` is a Hypothesis strategy of inputs that
meet the preconditions (`pip install 'sverify[testing]'`). The fixtures are
`sv_source(rows, schema, name=...)`, an in-memory source, and `sv_engine`,
which runs a test once per installed engine (`--sv-engines=duckdb,polars`
picks them). [`python/tests/test_plugin_example.py`](python/tests/test_plugin_example.py)
is an example test file, and [`python/tests/test_tour.py`](python/tests/test_tour.py)
tests the tour's transforms the same way.

### What is supported

How much of the Ibis API gets through, from
[`sverify/coverage.py`](python/src/sverify/coverage.py) and its cases in
[`sverify/coverage_cases/`](python/src/sverify/coverage_cases) (regenerated on
`main` after every merge by `uv run python -m sverify.coverage --write-readme`):

<!-- coverage:start -->
146 of 170 probed Ibis operations reach the checker (✓ verified, ✗ rejected by the checker, – fails in Ibis or DataFusion; *inc.* marks incremental maintenance).

| Area | Operations |
|---|---|
| rows | ✓ filter, select *inc.* · ✓ mutate *inc.* · ✓ drop, rename *inc.* · ✓ drop_null *inc.* · ✓ isnull *inc.* · ✓ between *inc.* · ✓ isin *inc.* · ✓ notin *inc.* · ✓ ifelse *inc.* · ✓ cases *inc.* · ✓ order_by *inc.* · ✓ limit · ✓ limit with offset · ✓ order_by + limit · ✗ sample · ✓ order_by expression *inc.* · ✗ limit expression · ✗ limit count() · ✓ fill_null table *inc.* · ✓ fill_null all *inc.* · ✓ memtable *inc.* · ✓ constant table *inc.* · ✓ alias *inc.* · ✓ sql view *inc.* · ✓ sql query *inc.* |
| joins | ✓ inner join *inc.* · ✓ non-equi join *inc.* · ✓ cross join *inc.* · ✓ left join · ✓ right join · ✓ outer join · ✓ semi join · ✓ anti join · ✓ isin subquery · ✓ isin subquery in select · ✓ notin subquery · ✓ scalar subquery in select · ✓ scalar subquery, one row · ✗ scalar subquery, many rows · ✓ exists · ✓ not exists · ✓ exists, uncorrelated · ✗ correlated scalar subquery · ✓ union all *inc.* · ✓ union distinct · ✓ intersect · ✓ difference · ✓ intersect all · ✓ difference all |
| aggregation | ✓ count() · ✓ group_by sum · ✓ count, max, mean · ✓ nunique · ✓ sum(where=) · ✓ having · ✓ value_counts · ✓ distinct · ✗ distinct(on=) · ✗ std · ✓ collect · ✓ collect ordered · ✗ collect include_null · ✓ scalar subquery · ✓ unnest |
| lists | ✓ unnest column · ✗ unnest keep_empty · ✓ list literal *inc.* · ✓ list column *inc.* |
| windows | ✓ row_number · ✓ lag · ✓ rank · ✓ dense_rank · ✓ cumsum · ✓ sum over group · ✗ rolling mean (rows) · ✗ rolling mean (interval) · ✓ ntile · ✓ first · ✓ percent_rank, cume_dist · ✓ running mean · ✓ rolling sum (interval) · ✓ rolling sum (range) · ✓ last, nth · ✓ max, count over frame · ✗ min over a sliding frame · ✗ window sum of an expression |
| numbers | ✓ +, -, * *inc.* · ✓ float division *inc.* · ✓ integer division *inc.* · ✓ mod *inc.* · ✓ abs *inc.* · ✓ round *inc.* · ✓ ceil, floor *inc.* · ✓ power *inc.* · ✓ greatest *inc.* · ✓ least *inc.* · ✓ clip *inc.* · ✓ cast int → double *inc.* · ✓ cast int → string *inc.* · ✓ cast double → int *inc.* |
| nulls | ✓ fill_null *inc.* · ✓ coalesce *inc.* · ✓ nullif *inc.* |
| strings | ✓ upper *inc.* · ✓ length *inc.* · ✓ concat *inc.* · ✓ substr *inc.* · ✓ contains *inc.* · ✓ startswith *inc.* · ✓ like *inc.* · ✓ re_search *inc.* · ✓ strip *inc.* · ✓ lpad *inc.* · ✓ rpad *inc.* · ✓ repeat *inc.* · ✓ reverse *inc.* · ✓ right *inc.* · ✓ replace *inc.* · ✓ replace '' *inc.* · ✓ ilike *inc.* · ✓ find from *inc.* · ✓ ascii *inc.* · ✓ join *inc.* · ✓ levenshtein *inc.* · ✓ find_in_set *inc.* · ✓ capitalize *inc.* · ✓ slice *inc.* · ✗ translate |
| time | ✓ timestamp + interval *inc.* · ✓ compare with literal *inc.* · ✓ year *inc.* · ✓ date *inc.* · ✓ truncate *inc.* · ✓ date + days *inc.* · ✓ date - months *inc.* · ✓ date + years *inc.* · ✓ date - column days *inc.* · ✓ timestamp + months *inc.* · ✓ constant interval arithmetic *inc.* · ✓ date - date *inc.* · ✓ date delta *inc.* · ✓ date parts *inc.* · ✓ date truncate *inc.* · ✓ day_of_week *inc.* · ✓ day_of_week name *inc.* · ✓ iso_year *inc.* · ✓ epoch_seconds *inc.* · ✓ millisecond, microsecond *inc.* · ✗ timestamp + column interval · ✗ date + column months · ✗ timestamp delta · ✓ bucket *inc.* · ✓ group_by_dynamic (no overlap) · ✓ rolling sum by time · ✓ offset_by months and days *inc.* · ✓ month end *inc.* · ✗ group_by_dynamic (overlapping) · ✓ time of day *inc.* · ✓ time parts *inc.* · ✓ compare times *inc.* · ✓ strftime *inc.* · ✓ timestamp from unix *inc.* · ✓ date from constants *inc.* · ✓ timestamp from constants *inc.* · ✗ date from columns · ✗ string to timestamp · ✗ time + interval · ✗ time truncate · ✗ strftime other directives · – between_time |

Every engine runs the plans of the 146 verified operations, except:

| Engine | Runs | Refuses |
|---|---|---|
| Polars | 145 | non-equi join |
| DuckDB | 139 | non-equi join · collect · collect ordered · unnest · unnest column · list literal · replace '' |
| Snowflake | 116 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · order_by expression (with `tie_free=True` it runs) · non-equi join · scalar subquery, one row · count, max, mean · collect · collect ordered · scalar subquery · unnest · unnest column · list literal · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) · rank (with `tie_free=True` it runs) · dense_rank (with `tie_free=True` it runs) · cumsum (with `tie_free=True` it runs) · sum over group · ntile (with `tie_free=True` it runs) · first (with `tie_free=True` it runs) · percent_rank, cume_dist (with `tie_free=True` it runs) · running mean · rolling sum (interval) (with `tie_free=True` it runs) · rolling sum (range) (with `tie_free=True` it runs) · last, nth (with `tie_free=True` it runs) · max, count over frame (with `tie_free=True` it runs) · replace '' · rolling sum by time (with `tie_free=True` it runs) |
| Spark | 113 | order_by (with `tie_free=True` it runs) · limit · limit with offset · order_by + limit · order_by expression (with `tie_free=True` it runs) · non-equi join · scalar subquery, one row · count, max, mean · collect · collect ordered · scalar subquery · unnest · unnest column · list literal · row_number (with `tie_free=True` it runs) · lag (with `tie_free=True` it runs) · rank (with `tie_free=True` it runs) · dense_rank (with `tie_free=True` it runs) · cumsum (with `tie_free=True` it runs) · sum over group · ntile (with `tie_free=True` it runs) · first (with `tie_free=True` it runs) · percent_rank, cume_dist (with `tie_free=True` it runs) · running mean · rolling sum (interval) (with `tie_free=True` it runs) · rolling sum (range) (with `tie_free=True` it runs) · last, nth (with `tie_free=True` it runs) · max, count over frame (with `tie_free=True` it runs) · replace '' · rolling sum by time (with `tie_free=True` it runs) · time of day · time parts · compare times |
<!-- coverage:end -->

The engines refuse what they cannot do as Lean does: `<` on strings is
undefined in the model (it is NULL there, while SQL compares), and Snowflake
and Spark tables have no row order for FETCH, or for the ties of a sort or a window, to
follow, nor for the order a `SUM` or `AVG` of doubles adds in. See
[Engines and SQL](#engines-and-sql).

## Development

To work on the library itself, or to run the tour from a clone, you need [uv](https://docs.astral.sh/uv/) for Python,
[elan](https://github.com/leanprover/elan) for Lean (elan is to Lean what
rustup is to Rust, or uv to Python), and Java 17 or 21 for the Spark tests:

```bash
brew install uv          # or: curl -LsSf https://astral.sh/uv/install.sh | sh
```
```bash
brew install openjdk@21  # or: sudo apt install openjdk-21-jre-headless
```

Homebrew's JDK is not on the `PATH`; point `JAVA_HOME` at it (in `~/.zshrc`):

```bash
export JAVA_HOME=/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home
```

Without a JVM the Spark tests are skipped and everything else runs.
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Open a new terminal so `lake` (Lean's build tool) is on your PATH. Then, from
the project root:

```bash
lake build                       # checks every proof and builds the substrait-check CLI
```
```bash
cd python && uv sync             # sverify with every extra, and the dev tools (pytest, hypothesis, …)
```
```bash
uv run pytest                    # all pass; the Spark tests skip without a JVM
```

`uv sync` installs `sverify` in editable mode, with every extra (below). Its build hook runs
`lake build substrait-check` and links `sverify/_bin/substrait-check` to the
result, so later `lake build`s take effect without reinstalling. To use a
different binary, set `SVERIFY_CHECK` to its path.

### Development tasks

Tasks are defined with [poe](https://poethepoet.natn.io) in `python/pyproject.toml`:

```bash
cd python && uv run poe qa       # everything below, in order; stops at the first failure
```

| Task | What it does |
|---|---|
| `poe prove` | Checks every Lean proof. Any warning fails, including a `sorry` (an unfinished proof). |
| `poe build` | Builds the `substrait-check` CLI that `sverify` calls |
| `poe lint` | `ruff check` and `ruff format --check`, on `python/` and `notebooks/` |
| `poe fmt` | Fixes lint issues and formats the Python code |
| `poe typecheck` | Type-checks the Python code with pyrefly |
| `poe golden` | Golden tests: CLI output on every plan in `tests/fixtures` |
| `poe test` | Python tests, including the randomized engine tests, on every core |
| `poe test-core`, `test-datafusion`, `test-duckdb`, `test-polars`, `test-snowflake`, `test-spark` | The Python tests of one backend (`pytest -m <backend>`; see `python/tests/conftest.py`). CI runs one job per backend. |
| `poe notebooks` | Checks the tour notebooks and runs each one headless |
| `poe docs`, `poe docs_preview` | Builds the API reference site into `python/great-docs/_site` (or serves it locally). Needs [Quarto](https://quarto.org) and `uv sync --group docs`; not part of `qa` |

From the project root, use `uv run --project python poe -C python qa`. The Lean
tasks need `lake` on your PATH.

### The tour

The notebooks in [`notebooks/`](notebooks) form a guided tour, starting at
[`00_start_here.py`](notebooks/00_start_here.py). Open the whole folder, so the
links between chapters work:

```bash
uvx marimo edit --sandbox notebooks              # from the project root
```
```bash
uvx marimo run --sandbox --include-code notebooks   # read-only apps
```

`--sandbox` runs each notebook in its own environment, with `sverify` installed
from `python/` as declared in the notebook's header; the first start takes a
minute. Build the checker first (`lake build`). To use the project's own
environment instead: `uv run --project python marimo edit notebooks`.

| | Chapter | What it covers |
|---:|:---|:---|
| 0 | [Start here](notebooks/00_start_here.py) | what the library does for you, and how to use the tour |
| 1 | [Duplicate card payments](notebooks/01_duplicate_payments.py) | workflow: Delta source and sink, a self-join's contract, refresh from the Change Data Feed |
| 2 | [Sensor alerts](notebooks/02_sensor_alerts.py) | workflow: Iceberg source and sink, `LAG` and ties, NaN, Snowflake and Spark |
| 3 | [An orders mart](notebooks/03_orders_mart.py) | workflow: a point-in-time join to a type-2 dimension, dbt tests as a contract, SQL |
| 4 | [Contracts](notebooks/04_contracts.py) | `requires`/`ensures`, what Lean tracks, `on_unproved` |
| 5 | [Keys and relations](notebooks/05_keys_and_relations.py) | `sv.unique`, facts between columns, joins |
| 6 | [Runtime errors](notebooks/06_runtime_errors.py) | division by zero, overflow, casts; proving they can't happen |
| 7 | [Windows and ASOF joins](notebooks/07_windows_and_asof.py) | LAG, LEAD, ROW_NUMBER, ties; aligning two sensors |
| 8 | [Composing contracts](notebooks/08_composition.py) | proving one step's preconditions from the previous step |
| 9 | [Incremental views](notebooks/09_incremental_views.py) | nodes kept up to date from changes, what is recomputed, Z-sets and delta rules |
| 10 | [Pipelines](notebooks/10_pipelines.py) | composing nodes, `.write`, `sv.group`, contracts that hold in every state, your own source and sink |
| 11 | [Engines and SQL](notebooks/11_engines.py) | DuckDB, Polars, DataFusion; SQL for DuckDB, Snowflake and Spark |
| 12 | [Doubles, time and text](notebooks/12_values.py) | NaN and −0.0, timestamps and intervals, calendar functions, strings |
| 13 | [Plans, meaning and proofs](notebooks/13_plans_and_proofs.py) | under the hood: Substrait plans, Lean's interpreter, theorems, NULL |
| 14 | [The checker](notebooks/14_the_checker.py) | under the hood: `substrait-check`, Lean as a reference engine, Ibis coverage |
| 15 | [What is proved, what is trusted](notebooks/15_trust.py) | under the hood: the trusted boundary, a glossary and a map of the code |
| 16 | [DataFusion's surprising semantics](notebooks/16_datafusion_semantics.py) | appendix: every DataFusion quirk, checked against the Lean model |
| 17 | [One expression, many engines](notebooks/17_backend_semantics.py) | appendix: DataFusion, DuckDB, Polars, Snowflake and Ibis, question by question |

`poe notebooks` (part of `poe qa`) checks every chapter with `marimo check` and
runs it headless. The chapters' tables come from `sverify.display`, which needs
marimo.

### Wheels

`uv build python --wheel` builds a wheel for the current platform. It bundles a
stripped `substrait-check`, so installing it needs neither Lean nor elan. The
[Wheels workflow](.github/workflows/wheels.yml) builds and tests wheels for Linux
(x86_64, aarch64) and macOS (arm64, x86_64). A `v*` tag that matches the
version in `python/pyproject.toml` also publishes them to PyPI.

`uv build python` also builds the sdist. It carries the Lean project under
`lean/`, and `uv build` makes the wheel from it, so the sdist is checked on
every build. Installing from the sdist (on a platform without a wheel) needs
elan; the build hook runs `lake build` there.

To run your own scripts with the package available, from the project root:

```bash
uv run --project python python my_pipeline.py
```

### Configuration

* `SVERIFY_CHECK`: path to a `substrait-check` binary to use instead of the
  bundled one, for example your own `lake build`.
* `SVERIFY_ISTHMUS`: path to an [Isthmus](https://github.com/substrait-io/substrait-java/releases)
  binary (otherwise `isthmus` on `PATH`), for compiling SQL strings without
  DataFusion: `sv.connect(sql_producer="isthmus")`, the default when
  DataFusion is not installed. sverify doesn't ship it (~120 MB);
  `python/scripts/fetch_isthmus.sh <dir>` downloads the pinned release.
* DataFusion is pinned to 51, because Ibis 12's DataFusion backend fails to
  connect with 52 and later.

### Troubleshooting

* **`lake: command not found`**: open a new terminal, or call `~/.elan/bin/lake`.
* **`no configuration file …lakefile`**: run `lake` from the project root, where `lakefile.toml` is.
* **`… does not exist`** for a notebook or `--project` path: those paths are relative to the
  project root, not to `python/`.
* **Why DataFusion 51?** Ibis 12's DataFusion backend fails to connect with
  DataFusion 52 and later (a changed user-defined-function API).

## How it works

The rest of this README is for people who want to look under the hood: how plans are
checked, how the engines are made to agree, and exactly what is proved.

```bash
lake build                                                  # proofs + CLI
tests/run.sh                                                # golden tests for the CLI
```

There are no dependencies beyond Lean core (no Mathlib yet), so the build takes seconds.

### Checking real plans

`substrait-check` reads any Substrait JSON plan, shows it in readable form,
and reports what was verified about it:

```python
from sverify.engines import substrait_json

plan = substrait_json(con, "select id, amount * 2 as doubled from orders where amount > 10")
open("plan.json", "w").write(plan)
```
```text
$ .lake/build/bin/substrait-check plan.json
Emit [1, 2]                    ← output columns: id, doubled
  Project +[($0 * 2)]          ← append amount * 2
    Filter (10 < $0)           ← amount > 10
      Emit [2, 0]              ← read only (amount, id)
        Read orders
tables: orders(3)
arity: 2
well-formed: yes               ← every column reference exists (a check proven correct)
incremental: yes               ← a proven update plan exists
roundtrip: ok                  ← writing the plan back out reproduces it
rows (0):                      ← named tables carry no data here, only their schema
```

Columns are referred to by position (`$0` is the first column), which is how
Substrait works.

`substrait-check plan.json` reads a Substrait plan in protobuf-JSON form, as
produced by `sverify`'s Ibis producer or DataFusion's Substrait producer
(Substrait 0.77). It then:

1. translates it into the formal `Rel` model, or rejects anything outside the fragment (exit 1);
2. decides `Rel.WF` with `checkWF`, which is proven equivalent (`checkWF_iff`), and
   checks that `RelRoot.names` match the output arity (exit 2 if ill-formed);
3. evaluates the plan. Named tables are schema-only (arity from `baseSchema`, no rows),
   so only `VirtualTable` data produces output rows.

```text
$ substrait-check tests/fixtures/virtual_left_join.json
Emit [0, 4]
  Project +[IF IS_NULL($3) THEN "unknown" ELSE $3]
    LeftJoin ($1 = $3)
      Values[3] 3 row(s)
      Values[1] 2 row(s)
arity: 2
well-formed: yes
rows (3):
  (1, "ada")
  (2, "unknown")
  (3, "ada")
```

What it accepts is the model's fragment (`SubstraitLean/Rel.lean` lists the
operators): the coverage table under [What is supported](#what-is-supported)
probes it from the Ibis side, and the catalogue's
[`features.toml`](catalogue/features.toml) records it per feature. Function
calls are matched by name in `extensions`, and anything else is rejected.

The CLI also reports whether the plan is in the incremental fragment
(`isIncremental`, proven equivalent to `Rel.Incremental`) and whether writing
it back out as JSON and re-parsing gives the same `Rel` (`roundtrip: ok`).

The parser ([Parse.lean](SubstraitLean/Parse.lean)) and writer
([Write.lean](SubstraitLean/Write.lean)) are **trusted, unverified code**. The
proofs are about `Rel`, so a parser bug would make the CLI check the wrong plan.
The golden tests in `tests/fixtures` are the guard against that. The
`df_*.json` fixtures are real plans: the Ibis pipelines in
`sverify/examples.py`, compiled by Ibis and DataFusion
(`python/scripts/capture_fixtures.py`). The others are hand-written.

### How incremental views work

`python/` holds `sverify`, which maintains query results incrementally on
DuckDB (by default), Polars or DataFusion, using delta plans from Lean. Under
a node's `refresh` is an incremental view (`sverify.incremental`, internal):

```python
import sverify as sv
from sverify.examples import PIPELINES, create_tables
from sverify.incremental import IncrementalView

con = sv.connect()          # Arrow tables; plans run on DuckDB
create_tables(con, orders_rows=[(1, "ada", 30)], customers_rows=[("ada", "Paris")])
view = IncrementalView(con, PIPELINES["inner_join"], "v")
view.apply({"orders": sv.Changes(inserts=[(3, "bob", 7)], deletes=[(1, "ada", 30)]),
            "customers": sv.Changes(inserts=[("bob", "Rome")])})
assert view.rows() == view.recompute()
```

The query can be an Ibis expression or a SQL string. A node's view reads its
sources, or the stored nodes it reads, as the view's base tables.

How it works:

1. The query becomes a Substrait plan: an Ibis expression through the vendored
   Ibis producer (below), a SQL string through the connection's SQL producer
   (DataFusion's, or Isthmus: see "SQL producers" below).
2. `substrait-check --delta` compiles the plan with `Rel.delta`, splits it into
   union-free terms (`Rel.terms`) and applies the weight-column encoding
   (`Rel.weighted`). It prints one Substrait plan per term, after checking each
   one is incremental and well-formed. The plans are union-free because
   DataFusion's Substrait consumer loses table qualifiers at a `UNION ALL`,
   and the duplicate column names then break a later join.
3. For each change batch, `sverify` registers the change tables `t$delta` (rows
   plus `__weight` = ±1), runs every term on the connection's engine (DuckDB by
   default; on DataFusion with its Substrait consumer), sums the weights per
   row, and merges the result into the view.

`python/tests/test_incremental.py` is a differential test (with `hypothesis`):
after random insert/delete batches, the maintained view must equal the query
recomputed from scratch. It runs every pipeline in `sverify/examples.py`:
filters and projections, inner joins, self-joins, `UNION ALL`, cross products,
and a filter-join-compute chain. It also runs one plain-SQL query, so the SQL
entry point stays covered.

**Connections.** `sv.connect(engine=...)` gives a `Connection`: the Arrow
tables (`sverify.engines.create_table`, `con.arrow`), the engine plans run on, and Ibis
tables bound to them (`con.table(name)`, through an in-memory Ibis DuckDB
backend that views the Arrow tables, so Ibis's own `.to_pyarrow()` works and
contracts find a table's data). `con.datafusion` is a DataFusion session with
the same tables, created on first use. Tables are stored with their doubles as
the model has them (below).

**DataFusion is optional** (`pip install 'sverify[datafusion]'`): it runs plans
with `engine="datafusion"` and compiles SQL strings unless Isthmus does, and
nothing else needs it
(`python/tests/test_without_datafusion.py` blocks its import). It is pinned to
51: Ibis 12's DataFusion backend can't connect to 52 and later. Tables are
registered there as record batches, not datasets: DataFusion pushes filters
into datasets, where PyArrow compares doubles by IEEE rules, which would make
filters and projections disagree on NaN.

##### Doubles: one zero and one NaN

The model has the doubles users expect from SQL (PostgreSQL, DuckDB, Spark,
Snowflake): −0.0 is 0.0, and every NaN is one NaN, equal to itself and above
`inf`. `-1 * 0.0` is `0.0`, `-0.0 >= 0` is TRUE, and `GROUP BY`, `DISTINCT`,
joins, partitions and sorts put the two zeros (and all NaNs) together. Each
engine is made to agree:

* DuckDB, Polars, Snowflake and Spark already compare this way. Their SQL (or
  Polars expressions) makes a table's −0.0 zero on read, and adds `0.0` after
  every operation that IEEE lets produce −0.0 (negation, `*`, `/`, `POWER`,
  rounding, `AVG`): `-0.0 + 0.0` is `0.0`, and other values stay. Ibis
  queries on a connection run on DuckDB, so they agree too.
* DataFusion orders doubles by `f64::total_cmp` (−0.0 < 0.0, a negative NaN
  first), so connections store canonical tables (`sverify.engine.canonical`),
  its results are canonicalized, and the plans Lean writes wrap every double
  operation in `nanvl(x + 0.0, 'NaN')`, which DataFusion evaluates and every
  parser reads back as `x`. This also gives every NaN the same payload, which
  `total_cmp` would tell apart. Two gaps remain: a `SUM` or `AVG` of doubles
  inside a plan on DataFusion is not wrapped, so a sum that is NaN (as
  `inf + -inf`, negative on x86) or underflows to −0.0, and is then compared
  in the same plan, follows DataFusion's order; and so does SQL run on
  DataFusion directly (`run_sql`, a query on `con.datafusion`).

#### The Ibis producer

Ibis expressions become Substrait directly, without SQL:
`sverify/ibis_substrait` is [ibis-substrait](https://github.com/ibis-project/ibis-substrait)
(Apache 2.0, last released for Ibis 9), vendored and ported to Ibis 12. It
writes the functions and encodings the Lean parser reads, and each operation
means what Ibis's own DataFusion SQL compiler makes of it, with Ibis's type
promotions written as explicit casts. That makes plans typed: `qty > amount`
compares as doubles, where DataFusion's producer (from its unanalysed plan)
left an integer next to a double's code (#16). Upstream's mistakes are fixed
(integer `/` divided integers, `where=` filters were dropped, sorts were always
`NULLS FIRST`, promotions could cast a double down to an integer, timestamp
literals were read in local time), and anything outside the model raises
`Unsupported`. `python/tests/test_ibis_substrait.py` checks every verified
coverage case against DataFusion running Ibis's SQL on random tables.

A few operations have no node of their own. Memtables and `ibis.literal(…).as_table()`
become virtual tables, table-level `fill_null` a `COALESCE` per column (as Ibis
rewrites it), and a sort by an expression projects the key, sorts and drops it.
SQL strings (`t.alias("v").sql(…)`) are compiled by DataFusion's Substrait
producer and spliced in, with reads of the alias replaced by its plan.
`INTERSECT ALL` and `EXCEPT ALL` number the copies of each row
(`ROW_NUMBER() OVER (PARTITION BY` every column`)`) and semi- or anti-join on the
rows and their numbers, which keeps min(m, n) or max(m − n, 0) copies: SQL's
meaning, as DuckDB computes it. DataFusion 51 plans them as a plain semi and
anti join, keeping or dropping every copy (`test_datafusion_quirks.py`), so
those two cases are compared with DuckDB running Ibis's SQL instead
(`coverage.DATAFUSION_SQL`). Ibis writes a `LIMIT` that is not an integer as a
subquery over the table, which DataFusion cannot run, so it is refused.

Subqueries: a correlated `[NOT] EXISTS` in a filter becomes a semi (anti) join
on the subquery's condition, as DataFusion decorrelates it; other correlated
subqueries are refused. Uncorrelated ones go into the plan as Substrait
subquery expressions, which the checker lifts into joins (`liftSubquery` in
`SubstraitLean/Parse.lean`): a scalar subquery is a left join on `TRUE`, and
because DataFusion fails when one returns several rows, the checker accepts it
only where `Rel.keys` proves at most one row (an aggregate without groups,
`LIMIT 1`); `x IN (subquery)` outside a filter's conjuncts is a left join with
the subquery's distinct values plus a count of its `NULL`s, which gives SQL's
three-valued answer; `EXISTS` compares a `COUNT(*)` with 0. DataFusion 51
cannot run `IN` or `EXISTS` subqueries in a projection, and its
`NOT IN (subquery)` ignores the subquery's `NULL`s, so those cases are
compared with DuckDB running Ibis's SQL (`coverage.DATAFUSION_SQL`).

#### SQL producers

SQL strings go through DataFusion's Substrait producer, or through
[Isthmus](https://github.com/substrait-io/substrait-java) (substrait-java's
Calcite-based compiler) as its native release binary, with no JVM:
`sv.connect(sql_producer="isthmus")`, and the default when DataFusion is not
installed. sverify finds the binary through `$SVERIFY_ISTHMUS` or `isthmus` on
`PATH` and doesn't ship it (~120 MB; `python/scripts/fetch_isthmus.sh`
downloads the pinned release). It writes a `CREATE TABLE` per connection table
from its Arrow schema, with quoted identifiers, and keeps unquoted identifiers'
case (`--unquotedcasing=UNCHANGED`). Isthmus reads standard SQL in Calcite's
default conformance, not DataFusion's or Postgres's dialect: `FLOOR(ts TO DAY)`
rather than `DATE_TRUNC`, no `GROUP BY` ordinals, `POSITION(a IN b)`.

Isthmus writes typed function names (`add:date_iday`), CHAR and VARCHAR
literals, window functions inside expressions (`ROW_NUMBER() OVER (…) - 1`),
`is_true` and timestamps at precision 0; the parser reads these (hoisting the
windows into `Rel.window`) and checks the argument kinds a signature names.
`poe compare-sql` compiles every SQL string the tests compile with DataFusion
with Isthmus too, and fails if both plans verify but give different rows;
`python/scripts/isthmus_catalogue.py` does the same for the query catalogue.

#### Engines

Plans come from the Ibis producer or DataFusion's Substrait producer, and they can run on
DuckDB (the default, below), [Polars](https://pola.rs) or DataFusion. Pass
`engine="polars"` to `node.refresh`, `sv.connect` or
`sverify.engines.run(con, plan, "polars")`. The tables stay in `con` and are handed to
the engine as Arrow. The point is differential testing,
with the Lean semantics as the spec.

Polars runs Lean's own serialisation of the checked plan: the plan as
`substrait-check --write` writes it back out from the parsed `Rel`
(`sverify.engines.written_plan`), and the delta plans of `--delta`, which use the same
writer. `sverify/polars_engine.py` translates only that small, canonical form
to a `LazyFrame` and raises `Unsupported` on anything else. It does not go
through Ibis's Polars backend, which would compile a different plan. The
translator pins the semantics instead of taking Polars defaults:

* Filters and join conditions keep a row only when it is TRUE. `and`/`or` are
  written out as Kleene `and3`/`or3`. Equi-join keys never match on NULL.
  Semi and anti joins keep the left rows with (without) a TRUE match, so an
  anti join keeps a row whose key is NULL. Lean writes an outer join as a
  left join plus the unmatched right rows (an anti join), padded with NULLs.
* Rows come out in `Rel.eval`'s order. Joins are left-major, with a left
  join's padded row in its place, and windows emit their sorted order. Sorts
  are stable, so ties keep their input order, and `DISTINCT` keeps the first
  of each set of equal rows in place. So `FetchRel` takes the same rows as
  Lean, and the tests compare Polars with Lean row for row.
* Doubles compare, join, partition and sort with one zero and one NaN
  (`-inf < … < 0.0 < … < inf < NaN`), like the float codes. Sorts place NULLs
  as each key says. `DISTINCT` compares rows as `Value`s: NULLs are equal,
  and so are -0.0 and 0.0, and all NaNs.
* Aggregates (`aggregateEval`): one row per group, in order of first
  occurrence (or exactly one without `GROUP BY`), grouping as `DISTINCT`
  compares. Each measure skips NULLs and the rows its `FILTER` drops;
  `DISTINCT` measures keep the first of equal values. Integer `SUM` is exact
  and raises `IntegerOverflow` outside 64 bits, where DataFusion wraps. `SUM`
  and `AVG` of doubles add one by one in Lean's list order.
* Strings are sequences of Unicode scalar values: `character_length`,
  `strpos` and `substring` count characters, not bytes, and `substring` with
  a start below 1 keeps only the positions that exist. `LIKE` escapes with a
  backslash, and a trailing one stands for itself. `UPPER`, `LOWER` and
  regular expressions are black boxes in Lean; Polars computes them with the
  Rust code DataFusion uses.
* `date_part` and `date_trunc` follow `SubstraitLean/Time.lean`: parts
  within a day are integer arithmetic on the microseconds, the calendar comes
  from chrono (as in DataFusion), and `date_part` is NULL outside the years
  chrono represents.
* Integers are unbounded in Lean. Polars computes on 128 bits, and a result
  outside 64 bits raises `IntegerOverflow`, where DataFusion wraps silently
  (`2^62 + 2^62` gives `-2^63`). Integer division and remainder truncate
  toward zero, as `Int.tdiv` and `Int.tmod` do (Polars' own operators floor).
* Runtime errors are the `Issue`s of `SubstraitLean/Safety.lean`: division by
  zero, `MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions
  that do not compile and `date_trunc` to a week or longer outside ±2⁶³ ns. Each expression
  carries a per-row flag for each one, masked by `CASE` as `Expr.issues`
  masks it. The operator raises the matching error if a flag is set on a row
  it evaluates. Polars runs filters where the plan puts them, so a filter
  guards the projections above it. DataFusion merges filters, which is what
  `Rel.loose` models.
* Doubles divide in numpy: Polars divides a column by a constant by
  multiplying with its reciprocal, which rounds differently.

`python/tests/test_polars.py` runs every golden fixture (among them sorts,
`DISTINCT`, semi, anti and outer joins, and the string and time functions),
the window and rewrite queries of the other suites, and every delta plan of
the example pipelines on both engines. It checks Polars against DataFusion as bags and
against Lean's `Rel.eval` in order. It also has targeted tests for NULL join
keys, three-valued filters, NULL and NaN order in windows, overflow, and each runtime error and its guards. The
incremental-view tests run on both engines.

`python/tests/test_backends.py` runs every Ibis operation the coverage
harness verifies on random tables, on DataFusion, Polars and DuckDB, and
generates its Snowflake SQL and runs its Spark SQL on a local Spark session; `test_text.py` and `test_time.py` run their edge
cases on all three engines.

Known gaps: the writer gives virtual tables placeholder `i64` column types and
writes `FetchRel`'s deprecated `offset`/`count`. DataFusion rejects both, so
written plans with string `VALUES` or a fetch run only on Polars. Doubles in a
virtual table come out as their integer codes. `lt` on strings or booleans is
undefined in the model (unlike in SQL), so the translator refuses it.

#### DuckDB, through generated SQL

`engine="duckdb"` runs plans on [DuckDB](https://duckdb.org) as SQL that
`sverify.sql.to_sql(plan, DUCKDB)` generates from them. DuckDB's Substrait
extension is not used. Like Polars, DuckDB runs Lean's written plans over the
tables of `con`, which are copied into a fresh in-process database for each
run. Contracts take `engine=` for their runtime checks on data too:

```python
view = IncrementalView(con, PIPELINES["inner_join"], "v", engine="duckdb")

@sv.transform(ensures=[_.amount < 100], on_unproved="runtime", engine="duckdb")
def passthrough(orders): ...
```

The SQL generator (`python/src/sverify/sql/`) reads Substrait JSON as
`Parse.lean` does. It accepts exactly the plans `substrait-check` accepts and
raises `Unsupported` on everything else. It then writes SQL whose result is
`Rel.eval`. The query spells out every semantic choice instead of leaving it to
the engine:

* subqueries name their columns `c0, c1, …`;
* integers are `BIGINT`, and overflow raises (DataFusion wraps around);
* division and remainder truncate; where DataFusion fails at run time
  (division by zero, `MIN / -1`, bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and the SQL raises;
* doubles have one zero and one NaN (`-inf < … < 0.0 < … < inf < NaN`) in
  comparisons, joins, partitions and sorts, and −0.0 is made 0.0 wherever it
  could arise;
* every `ORDER BY` key says `NULLS FIRST`/`LAST`;
* filters keep only TRUE rows; semi and anti joins are `[NOT] EXISTS` over
  the rows where the condition is TRUE;
* `DISTINCT` groups by the same keys as a window partition, so equal means
  equal as `Value`s;
* aggregates group by the same keys as `DISTINCT`; a `DISTINCT` measure
  counts the first row of each value, integer `SUM` raises outside 64 bits,
  and doubles are added in Lean's order (`list_reduce` over a list ordered
  by the ordinal), so the result has Lean's bits, not DataFusion's;
* strings: lengths and positions count characters, a `substring` start below
  1 is handled before it reaches the engine (which would count it from the
  end), and `LIKE` names its escape character;
* `date_part` and `date_trunc` use the engine's calendar functions where they
  agree with `SubstraitLean/Time.lean` (ISO weeks, `dow` from Sunday,
  milliseconds within the minute), and the SQL raises where DataFusion's
  calendar truncation fails;
* below a `FETCH`, a window or a sort, an ordinal column carries Lean's list
  order, so `LIMIT` and ties in sorts and windows pick Lean's rows, and a
  sorted result comes out in Lean's order.

Engine differences go through the hooks of a `Dialect`
(`sverify/sql/core.py`). DuckDB's is `sverify/sql/duckdb.py`.

`python/tests/test_sql.py` checks the generator. Every golden fixture and every
delta plan of the incremental fixtures and example pipelines runs on DataFusion
and on DuckDB with random tables. The results must agree with each other and
with Lean's `Rel.eval` (row for row, in Lean's order, when `FETCH` or a window
makes order matter). The file also has targeted tests for engine traps: NULL
join keys, three-valued logic, NULL ordering in windows, refused integer
division, overflow, and NaN and signed zeros. It keeps snapshots of the
generated SQL in `python/tests/sql_snapshots/`. The incremental, window,
rewrite and ASOF differential tests run on DuckDB too.

##### Snowflake

Snowflake support is mostly aspirational for now: everything below has been
checked on an emulator, not on a real account ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)).

`to_sql(plan, SNOWFLAKE)` (from `sverify.sql.snowflake`) writes checked plans
and Lean delta plans as Snowflake SQL. The SQL is written to match Lean where
Snowflake's documented behaviour differs:

* integers are `NUMBER(38,0)` and are checked against the 64-bit range;
  division and remainder truncate (through `MOD`, as `/` rounds to six
  decimals), and `CAST(double AS BIGINT)` truncates and raises out of range;
* timestamps are `TIMESTAMP_NTZ(6)`; weeks, days of the week and truncation
  to a week use the ISO functions, not the session's `WEEK_START`;
* backslashes and control characters in strings are escaped;
* every identifier is quoted, so create tables and columns with quoted
  lower-case names.

Where Snowflake can't match, the plan is refused (`Unsupported`) or the query
raises instead of answering differently:

* FETCH over a named table is refused: Snowflake tables have no row order.
  So is a `SUM` or `AVG` of doubles, whose rounding depends on the order of
  the additions.
  Windows and sorts are refused too, unless you pass `tie_free=True` to
  promise there are no ties on their keys (a contract report's
  `deterministic` says so for windows).
* Interval-valued expressions (`ts1 - ts0`) are refused: Snowflake has no
  interval type.

Time columns must be `TIMESTAMP_NTZ`, and string columns must have no
collation. `python/tests/test_sql_snowflake.py` snapshots the SQL for every
fixture and delta plan, parses it with sqlglot's Snowflake parser, and runs it
on [fakesnow](https://github.com/tekumara/fakesnow) against Lean's `Rel.eval`,
along with sorts, `DISTINCT`, aggregates, semi, anti and outer joins and
string functions.
fakesnow emulates Snowflake on DuckDB, so this checks the SQL, not Snowflake's
behaviour. To run the same checks on a real account, set `SNOWFLAKE_ACCOUNT`,
`SNOWFLAKE_USER`, a credential (`SNOWFLAKE_PASSWORD`,
`SNOWFLAKE_AUTHENTICATOR` or `SNOWFLAKE_PRIVATE_KEY_FILE`) and
`SNOWFLAKE_WAREHOUSE`/`DATABASE`/`SCHEMA`.

##### Spark

`to_sql(plan, SPARK)` (from `sverify.sql.spark`) writes checked plans and
Lean delta plans as Spark SQL, for Spark 4 and Databricks SQL. With the
`spark` extra, `sverify.spark_engine.run(plan, tables)` runs a plan over Arrow
tables on a local session (or on the session you pass). Run it in a
session with the settings of `SPARK_CONF`: ANSI mode
(`spark.sql.ansi.enabled`), without which an overflow wraps around and a bad
cast gives NULL, plus a pinned time zone, NTZ timestamps, case-sensitive
names and backslash escapes in string literals. The SQL matches Lean where
Spark differs:

* integers are `BIGINT`; division is `div` (`/` gives a double) and
  remainder `%`, both truncating; a `SUM` adds `DECIMAL(38,0)` values, since
  Spark raises when a partial sum overflows even if the total fits;
* doubles divided by zero give ±inf or NaN (ANSI mode raises);
  `CAST(double AS BIGINT)` is range-checked first (Spark saturates at 2⁶³);
  `FLOOR` and `CEIL` (which return `BIGINT`) keep NaN, ±inf and large values;
* timestamps are `TIMESTAMP_NTZ` and intervals `INTERVAL DAY TO SECOND`;
  `date_trunc` returns a time-zone timestamp, so truncation is computed on
  `TIMESTAMP_NTZ` and `DATE` values;
* backslashes and control characters in strings are escaped, and every
  identifier is quoted with backticks.

Spark refuses, as Snowflake does, FETCH and sorts or windows over a named
table without `tie_free=True` (tables have no row order), and so `SUM` or
`AVG` of doubles over one. It also refuses `POWER` of doubles, which is Java's
`Math.pow` (within 1 ulp of C's).

String columns must use the default `UTF8_BINARY` collation (code point
order). `python/tests/test_sql_spark.py` snapshots the SQL, parses it with
sqlglot's Spark parser, and runs the Snowflake suite's queries, the hooks
and `date_part`/`date_trunc` at the calendar's edges on a local Spark session
against `Rel.eval`; `test_backends.py` runs every coverage case there. The
session needs a JVM (Java 17 or 21: `JAVA_HOME` or `java` on `PATH`), or the
Spark tests are skipped (`poe test-spark` runs them).

**Trusted components** (not covered by the proofs): the JSON parser and
writer, the `sverify` glue (change tables, consolidation, merge), the Polars
translator, the SQL generator, and each engine's execution (DataFusion's
Substrait consumer, Polars, DuckDB's and Spark's SQL). These are covered by golden tests,
round trips and the differential tests instead.

### How do I know it's right?

* **Proofs**: `lake build` re-checks every theorem. The main ones say that the
  update plan computes exactly the change to the result, and that running it on
  DataFusion with the weight-column encoding gives that result. See
  [Proven theorems](#proven-theorems).
* **Randomized testing**: `uv run pytest` generates random tables and random batches of
  inserts and deletes, including NULLs and duplicates. After every batch it
  checks that the maintained result equals a full recompute. This covers the parts
  the proofs don't: the JSON translation, the Python glue and the engine itself.

### What's here

| File | Contents |
|---|---|
| `SubstraitLean/Value.lean` | Nullable values, rows, bag-semantics relations |
| `SubstraitLean/Float.lean` | Doubles as exact integer codes (multiples of 2⁻¹⁰⁷⁴), NaN and −0.0 |
| `SubstraitLean/Rounding.lean` | Exact `FLOOR`/`CEIL`/`ROUND` and casts to `BIGINT` on double codes; monotonicity |
| `SubstraitLean/Text.lean` | String functions, `LIKE`; black-box `UPPER`/`LOWER`/regexes; patterns that certainly compile |
| `SubstraitLean/Time.lean` | Exact `date_part` and `date_trunc` on the proleptic Gregorian calendar; monotonicity |
| `SubstraitLean/Expr.lean` | `Literal`, `FieldReference`, scalar functions, `IfThen`, Kleene 3-valued logic |
| `SubstraitLean/Window.lean` | Sort orders, `ROW_NUMBER`/`LAG`/`LEAD` semantics over partitions |
| `SubstraitLean/Aggregate.lean` | `GROUP BY` with `COUNT`/`SUM`/`MIN`/`MAX`/`AVG` (`DISTINCT`, `FILTER`) semantics |
| `SubstraitLean/Rel.lean` | `Read`, `VirtualTable`, `Filter`, `Project`, `Emit`, `Cross`, `Join` (inner/left/semi/anti), `Sort`, `Aggregate`, `Fetch`, `UnionAll`, `Window`; arity, well-formedness, `eval`; **type soundness** |
| `SubstraitLean/Rewrites.lean` | Verified rewrites (below) |
| `SubstraitLean/Incremental.lean` | Z-set semantics, delta rules, delta plans (incremental view maintenance) |
| `SubstraitLean/Terms.lean` | Splitting a plan into union-free terms (for DataFusion's consumer) |
| `SubstraitLean/Weighted.lean` | Weight-column encoding for bag engines; `isIncremental` |
| `SubstraitLean/Write.lean` | `Rel` → Substrait JSON, delta plans for engines (trusted) |
| `SubstraitLean/Contracts.lean` | Verified abstract interpreter: NULLs, intervals, filter refinement; `contract_sound` |
| `SubstraitLean/Keys.lean` | Derived keys (`Rel.keys_sound`), window tie-breaking (`Rel.window_deterministic`) |
| `SubstraitLean/Completeness.lean` | The converse of contracts for the IoT example: no window is lost (`IoT.window_complete`) |
| `SubstraitLean/Compose.lean` | Composing contracts (Hoare triples), preconditions under updates, views over views (chain rule) |
| `SubstraitLean/TableFormat.lean` | Change feeds (`Rel.cdf_sound`, views only depend on weights) and file statistics (`stats_table`) |
| `SubstraitLean/Safety.lean` | Runtime errors and 64-bit wrap-around; `Rel.mayIssues_sound` |
| `SubstraitLean/Partition.lean` | Sharded evaluation of linear plans, two-phase `COUNT`/`SUM`/`MIN`/`MAX`; `Rel.shardSplit_sound` |
| `SubstraitLean/Semantic.lean` | Rewrites from contract facts and keys (`DISTINCT` on a key, …); `Rel.optimize_sound` |
| `SubstraitLean/Guards.lean` | Guard elimination: unchecked engine functions are exact where no issue happens; `Rel.guardFree_sound` |
| `SubstraitLean/ContractCheck.lean` | `--contract`: proving postconditions from preconditions and schemas |
| `SubstraitLean/ShardCheck.lean` | `--shard`: splitting a plan into per-shard and combining plans (trusted) |
| `SubstraitLean/Check.lean` | Executable `checkWF`, proven equivalent to `Rel.WF`; `Decidable` instance |
| `SubstraitLean/Parse.lean` | Substrait protobuf-JSON → `Rel` (trusted) |
| `SubstraitLean/Pretty.lean` | Plan / row rendering |
| `Main.lean` | `substrait-check` CLI (`--delta` for engine delta plans) |
| `python/` | `sverify`: contracts, incremental views, pipelines, Delta/Iceberg IO, sharding; the DuckDB, Polars, DataFusion and Spark runners and the Snowflake SQL; differential tests |
| `notebooks/` | The tour: three workflows, nine feature chapters, three on how it works and two appendices (marimo) |
| `tests/` | Golden tests of the CLI (`tests/run.sh`, plans in `tests/fixtures`) |
| `docs/optimizations.md` | Proved optimizations beyond incremental maintenance: what engines already do, what is proved, what is next |
| `catalogue/` | 139 real analytical queries (TPC-H, TPC-DS, SSB, ClickBench, JOB, H2O, practitioner, IoT and finance idioms), probed against the checker and the engines; [`FINDINGS.md`](catalogue/FINDINGS.md) |
| `SubstraitLean/Examples.lean` | Concrete plans checked with `#guard` at build time, plus `#print axioms` |

#### Proven theorems

* `Rel.eval_arity`: a well-formed plan on a well-formed catalog only produces
  rows of its declared arity.
* `filter_filter`: `Filter(Filter(r,p),q) = Filter(r, p AND q)`, which also holds under three-valued logic.
* `filter_true`, `fetch_zero_none`: identity eliminations.
* `filter_unionAll`: filter distributes over `UNION ALL`.
* `unionAll_comm`: `UNION ALL` commutes up to bag equivalence (`≈ᵣ`).
* `join_inner_eq_filter_cross`: an inner join is a filtered cross product.
* `filter_project_pushdown`: a filter that only reads input columns can be moved below a `ProjectRel`.
* `filter_cross_pushdown_left`: a filter that only reads left columns can be pushed into the left side of a `CrossRel`.
* `emit_project_identity`: emitting only the input columns of a `ProjectRel` removes the projection.
* `Rel.eval_sharded`, `twoPhase_correct`, `Rel.shardSplit_sound`: a plan linear in the sharded
  tables is the union of its results on the shards (with split keys, also aggregates grouped by
  the key, `DISTINCT` over it, co-partitioned joins and tie-free windows partitioned by it), and
  decomposable aggregates combine in two phases
  ([docs/optimizations.md](docs/optimizations.md)).
* `Rel.evalI_eq`, `Rel.guardFree_sound`: a plan whose only possible issues are integer `SUM`s
  runs correctly without per-row checks.

#### Contracts

[Contracts.lean](SubstraitLean/Contracts.lean) is an abstract interpreter
over `Rel`. Each column gets an `AVal`, a set of possible values: whether it can be NULL, an integer
interval, possible booleans, and whether it can be a string.

* `Expr.abs_sound`: abstract evaluation of expressions is sound, including SQL's
  three-valued `AND`/`OR`, NULL-propagating arithmetic and comparisons.
* `Expr.refine_sound`: a row that passes a filter satisfies what the condition
  says about its columns.
* `Expr.factsOf_sound`, `Rel.facts_sound`: relational facts (`x − y ∈ [lo, hi]`,
  `x ≠ k`) taken from filter and join conditions hold on every output row. They
  survive projections, emits, joins, NULL padding and unions.
* `Expr.absD_sound`: evaluating expressions with those facts (sharpening
  `x − y`, `x < y`, `x = y` and `x = k`) is sound. Each `CASE` branch is
  evaluated knowing whether its condition is TRUE: `Expr.cstr_sound` turns
  `IS NULL` and comparisons with constants into constraints on the tested
  expression (or its negation), and `Expr.refineNeg_sound` refines columns
  where a condition is not TRUE. This is how `clip`, `abs`, `greatest` and
  `least` get their bounds. `Expr.refine_sound` also covers `OR` and
  `IS NULL`, so a filter `x IN (1, 2, 3)` gives `x ∈ [1, 3]` and
  `x IS NULL OR x >= 0` gives "NULL or ≥ 0". `p OR q` is evaluated with `q`
  refined where `p` is not TRUE, also when `p` may be NULL (`orSplitNull`),
  which proves `x >= 0 OR x IS NULL` for a nullable `x`.
* `Rel.keys_sound` ([Keys.lean](SubstraitLean/Keys.lean)): derived keys hold. No two
  output rows agree on them.
* `Rel.optimize_sound` ([Semantic.lean](SubstraitLean/Semantic.lean)): the
  rewrites a contract's keys and facts allow keep a plan's rows, on data that
  meets the preconditions. A `DISTINCT` or measure-less `GROUP BY` over a key
  goes, and so does the `DISTINCT` of `COUNT(DISTINCT id)` with `id` a key.
  A filter the preconditions imply goes; one they rule out empties the plan.
  A left join on a NOT NULL foreign key (`sv.references`) becomes an inner
  join, and so does one under a filter that rejects its padded rows. A join
  whose condition hits a key of the right side goes when nothing reads the
  right side's columns (for an inner join, given a NOT NULL foreign key).
  A `GROUP BY` column that the other grouping columns determine (functional
  dependencies from keys and equalities, `Rel.fds_sound`) moves into a `MIN`.
  A `GROUP BY` of left columns over a join on a key of the right side is
  computed before the join (eager aggregation).
  `sv.verify(...).optimized` is the rewritten plan.
* Key rules for ASOF (all in `Rel.keys_sound`): `ROW_NUMBER()` with the partition
  columns is a key (`windowRows_rowNumber_key`); a column `$i + c` of a non-NULL
  integer column can stand in for it in a key; a filter `$i = k` drops `i` from
  keys; join keys drop right-key columns the condition ties to the left side
  (`a.device = b.device`), for inner and left joins.
* `window_tiebreak`, `Rel.window_deterministic` ([Keys.lean](SubstraitLean/Keys.lean)):
  when a window's partition and sort columns contain a key of its input, every
  arrangement of the input sorted by the window's keys gives the same rows as
  `Rel.eval`. So the proofs describe what DataFusion computes, however it breaks ties.
* `orderFact_sound`, `winFacts_sound`, `WinFn.abs_sound`: what is known about
  `LAG`/`LEAD`/`ROW_NUMBER` columns holds. Strict order uses an oracle saying
  which windows have a key (`WindowKeys`); `Rel.keyedWindows_sound` proves the
  one computed from `Rel.keys` right, which is what `contract_sound` asks for.
* `IoT.window_complete` ([Completeness.lean](SubstraitLean/Completeness.lean)): the
  converse of the contracts. If both sensors have valid readings at `t` and `t + 60`,
  the window at `t` is in the output, so no window is lost. It's built from one
  membership lemma per operator.

Doubles are modelled as exact integer codes (each double is a multiple of 2⁻¹⁰⁷⁴),
timestamps as microseconds; see [Float.lean](SubstraitLean/Float.lean). The conversions
between codes and native floats are trusted code.
* `Rel.aeval_sound`: every row a well-formed plan produces is described by `Rel.aeval`.
* `Rel.colExprs_eval`: a precondition plan (`orders.select(cond, ...)`) computes its
  conditions row by row, so "all its columns are TRUE" is the precondition.
* `contract_sound`: suppose every input row matches its schema and satisfies its
  preconditions. If every column of the postcondition plan is certainly TRUE,
  then every output row satisfies every postcondition.

Trusted: the schema description taken from `baseSchema` types and nullability, and
the JSON plumbing.

#### Composition

[Compose.lean](SubstraitLean/Compose.lean) builds on `contract_sound`,
`Rel.keys_sound` and `Rel.delta_correct`, with no induction over plans:

* `Triple.compose`: Hoare triples over queries compose, `{P} g {Q}` and
  `{Q} f {S}` give `{P} f ∘ g {S}`, where `f ∘ g` reads `g`'s output as one of
  its tables. `Triple.of_contract`, `Triple.of_keys` and `Triple.of_aeval` turn
  what the checker proves into triples; `Triple.compose_spec` is the rule as
  `sverify` applies it.
* `RowsSat.update`, `KeyOn.update`, `Spec.update`: a table's contract survives a
  batch if the inserted rows satisfy the row conditions and their keys clash
  with neither each other nor the kept rows. `Triple.maintained`: a contracted
  view's guarantees then hold in the new state.
* `Rel.chain_sound`: when a view reads another view's materialized result and
  gets that view's delta-plan output as its change table, its own delta plan is
  correct (DBSP's chain rule). `Rel.stack_sound` holds for any upstream change;
  `ZSet.diff_correct` shows a recomputed view's `new − old` is one.

#### Runtime errors

[Safety.lean](SubstraitLean/Safety.lean) proves that a transformation runs without
runtime errors, or reports what may go wrong. `sverify` reports these as
`may fail: …` (a `VerificationError` from `@sv.transform`) or, for wrapping,
`warning: …`.

* Errors, where DataFusion fails: integer division or remainder by zero, `MIN / -1`,
  integer `POWER` with a negative exponent or a result outside 64 bits,
  `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, a regular expression
  that may not compile, and `date_trunc` to a week, month, quarter or year outside
  ±2⁶³ nanoseconds (DataFusion panics or returns garbage there).
* Warnings: `+`, `-`, `*` and negation leaving 64 bits, an integer `SUM` (nothing
  bounds how many rows a group has), and `date_trunc` to a day or
  less below `-2⁶³` µs. DataFusion wraps around silently, so the result is not the
  mathematical one.
* `Rel.mayIssues_sound`: every issue that can happen on any input is reported. Guards
  are understood where DataFusion respects them: in a `CASE` branch (and so
  `NULLIF(b, 0)`), or in a filter below a *projection*. They are not respected in the
  same `AND`, nor in an earlier *filter*: DataFusion merges filters, so
  `t.filter(n != 0).filter(q % n > 1)` can fail.
* `FloatCode.floor_mono`, `round_mono`, `toInt?_mono`, `toInt?_of_range`
  ([Rounding.lean](SubstraitLean/Rounding.lean)): `FLOOR`, `CEIL`, `ROUND` and the cast
  to `BIGINT` are exact on double codes and monotone, so `amount ∈ [0, 100]` proves
  `amount.round()` is an integer in `[0, 100]`, and the cast safe.
* Abstract rules for truncating `/` and `%` (`divBound_sound`, `modBound_sound`) and
  for squares (`powAbs_sound`).
* `Time.monthIndex_spec`, `Time.trunc_mono`, `Time.year_mono`
  ([Time.lean](SubstraitLean/Time.lean)): every day lies in the month the calendar
  arithmetic computes, so years and truncations grow with the timestamp, and
  `ts ∈ [2024-01-01, 2025-01-01)` proves `ts.year() == 2024` and
  `ts.truncate("M") >= 2024-01-01`. The other parts have proved ranges (`day` in
  `[1, 31]`, …); `date_part` is `NULL` outside the years ±262142.

Trusted: *when* DataFusion evaluates an expression (`Rel.HasIssue`: `CASE` is lazy,
`AND`/`OR` are not, filter and join conditions may run before the filters below
them). `python/tests/test_numeric.py` runs DataFusion on random data and checks it
only fails where an error was reported. `BIGINT` and timestamp columns are taken to
hold 64-bit values (from the schema); arithmetic on 32-bit columns is checked
against 64-bit limits, so its overflow is not caught.

#### Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
It covers every operator except left, semi and anti joins, `DISTINCT`, aggregates,
fetch and windows (`Rel.Incremental`):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit, sort and union
  are linear (a sort only orders the bag), and cross and inner join use the bilinear rule
  `Δ(A×B) = ΔA×(B+ΔB) + A×ΔB`.
* `Rel.delta`: compiles a plan into a **delta plan**, an ordinary `Rel` that reads the
  old tables and the change tables (`δ t`, e.g. `orders$delta`).
  `Rel.delta_correct` proves it computes exactly `ΔQ`.
* `Rel.incremental_sound`: combines the two, so old result + delta-plan output =
  full recomputation.
* `Rel.zeval_lift`: with all weights 1, Z-set evaluation equals the bag
  semantics `Rel.eval`, so the two models agree.
* `Rel.zeval_terms`: a plan's result is the concatenation of its union-free
  terms' results (`Rel.terms`).
* `Rel.weighted_eval`: running the weight-column encoding (`Rel.weighted`) on an
  ordinary bag engine gives exactly the Z-set result, with each weight as a
  trailing column. Old tables get weight 1, and joins multiply weights.

Equivalence is `List.Perm`, which never cancels `+1` against `-1`. That makes it
stronger than Z-set equality, so the results also hold under consolidation.
`Examples.lean` runs a delete, an insert and an update through a filter/project
plan and an inner join where both sides change.

#### Table formats

[TableFormat.lean](SubstraitLean/TableFormat.lean) covers what `sverify.io`
takes from Delta Lake and Iceberg, with the format's part as explicit
hypotheses:

* `Rel.zeval_weight_congr`: on the incremental fragment, Z-set evaluation only
  depends on the tables' weights. A change feed deletes and re-inserts rows,
  so the old table plus the feed is not a permutation of the new table, only
  equal in weights.
* `Rel.cdf_sound`: if the feed turns each old snapshot into the new one up to
  weights (`ChangeFeed`, trusted) and is loaded as the change tables (`hδ` of
  `Rel.delta_correct`), the old view plus the delta plan's output has the
  weights of the view on the new snapshot. `ChangeFeed.of_diff`: the diff of
  two snapshots is such a feed, so the fallback needs no trust in the feed.
  `ChangeFeed.of_changed_files`: so is the diff of only the files that
  changed, if the unchanged files are the same rows in both snapshots.
* `stats_table`: with correct per-file statistics (`ColStats.Correct`,
  trusted), every row of the table lies in the join of the files' bounds;
  `stats_append`: the files an append added bound its rows; `stats_bounds`:
  that bound is the `IS NOT NULL AND c >= lo AND c <= hi` fact handed to the
  contract checker; `stats_fact`: with NULLs or a missing side it is
  `c IS NULL OR (…)`; `stats_all_null`: files that are all NULL give `c IS NULL`.
* `prune_sound`: filtering only the files that are not skipped gives the
  same rows as filtering the whole table, if no row of a skipped file makes
  the filter TRUE (which the checker proves from the file's statistics).

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Modelling choices

* **Positional schemas.** Substrait field references are ordinals, so a
  schema is just an arity. Types beyond "nullable value" are not tracked yet.
* **Project appends, Emit narrows.** This matches Substrait's `ProjectRel` +
  `RelCommon.emit`. Here `Emit` is its own node rather than a field on every rel.
* **Bags as lists.** `Rel.eval` returns a `List`, and plan equivalence is `List.Perm`.
  Several rewrites are stronger than that and hold as exact list equality.
* **Windows sort stably.** `Rel.eval` sorts a window's input with a stable merge
  sort, so ties keep input order. The checker only claims results for windows
  without ties (see `window_tiebreak`).
* **Fetch is order-dependent.** Without a `SortRel`, real engines may return any
  rows. The semantics fixes list order, so `fetch` theorems describe one valid behavior.
  `SortRel` is a stable sort here, while engines may order ties either way, so after
  `ORDER BY … LIMIT` the checker's claims hold for every row the engine could keep.
* **Semi joins and `DISTINCT` are their own operators.** `Rel.semi` keeps the left
  rows with some (or, for anti joins, no) matching right row; `Rel.distinct` keeps
  the first occurrence of every row (NULLs equal, doubles by their codes: one
  zero and one NaN). `DISTINCT` rows are a key (`Rel.keys`). DataFusion writes
  `DISTINCT` as an aggregate with one empty grouping, which its own consumer
  rejects; the parser reads it as "all columns".
* **Aggregates have one grouping set.** `Rel.aggregate` outputs one row per
  distinct grouping value (NULLs group together; doubles by their codes, so
  -0.0 and 0.0 are one group), or exactly one row without
  grouping expressions, even on an empty input. Measures skip NULLs; on no
  values `COUNT` is 0 and the rest are NULL. Integer `SUM` is exact (DataFusion
  wraps around, which is a warning), double `SUM`/`AVG` add with native floats
  (DataFusion promises no order; contracts only say "a double"), and `AVG` of
  integers is the `AVG` of their conversion to double. `MIN`/`MAX` of doubles
  are refused: DataFusion's grouped version turns a group of +∞ into the largest
  finite double and skips NaN next to other values. The grouping columns are a
  key of the result.
* **Ill-typed calls evaluate to `null`.** This keeps `eval` total. `Rel.WF` rules out
  out-of-range field references.
* **Some operations are rewrites in the parser.** `IN` lists become `OR`s of
  equalities; `COALESCE`, `NULLIF`, `GREATEST`, `LEAST` and `ABS` become
  conditionals; `RIGHT JOIN` becomes a `LEFT JOIN` with its sides swapped;
  `FULL OUTER JOIN` becomes the left join plus the anti join of the right side,
  padded with NULLs; `x IN (subquery)` in a filter becomes a semi join on `=`;
  `UNION` is `DISTINCT` of `UNION ALL`; `IS NOT DISTINCT FROM` becomes a
  conditional. The rewrites are trusted code, checked against DataFusion by
  `python/tests/test_rewrites.py` and `python/tests/test_relations.py`. (`ABS` of the smallest `BIGINT` fails in
  DataFusion; here it is reported as wrapping around.)
* **Integers are unbounded; overflow is an `Issue`.** `Rel.eval` computes exact
  integers, and [Safety.lean](SubstraitLean/Safety.lean) reports every operation that may
  leave 64 bits. Where DataFusion fails instead (division, `POWER`, casts), the
  value in the model is `NULL`.
* **Strings are Unicode scalar values.** `substring`, `strpos`, `LIKE`, `btrim`, `||`,
  `character_length`, `repeat`, `reverse`, `replace`, `ascii` and `levenshtein` are
  computed exactly, checked against DataFusion by `python/tests/test_text.py`; a
  `repeat` of more than 2³¹ - 1 bytes is an error, as in DataFusion. `UPPER`, `LOWER`,
  `ILIKE` and regular expressions are black boxes (`opaque`): no proof depends on what
  they compute, and Lean's evaluator handles only ASCII case and no regular
  expressions. `translate` is refused: DataFusion translates grapheme clusters. A pattern is an error unless
  `Text.simpleRegex` accepts it, a conservative subset of Rust's syntax that is
  tested to compile.
* **Timestamps are microseconds (UTC).** `date_part` and `date_trunc` are computed
  exactly, checked against DataFusion by `python/tests/test_time.py`, including at
  the ends of the ranges where DataFusion stops being exact. Dates (`DATE`) are not
  supported by them yet.
* **Integer `//` from Ibis is exact.** Ibis compiles it through doubles
  (`CAST(FLOOR(CAST(a AS DOUBLE) / b) AS BIGINT)`), which is wrong beyond 2⁵³;
  `sverify` compiles it to integer division instead.

### Prior work to build on

No existing formal semantics for Substrait came up in my search. The closest work formalizes SQL or relational algebra:

**Coq (most mature)**
* **SQLCert / SQL_Coq** (Benzaken, Contejean): a mechanized semantics for
  realistic SQL with nulls, aggregates and correlated subqueries, an extended bag
  algebra, and proofs of common optimizer rewrites.
  [HAL 01487062](https://hal.archives-ouvertes.fr/hal-01487062),
  [HAL 01955433](https://hal.archives-ouvertes.fr/hal-01955433)
* **HoTTSQL** (Chu, Weitz, Cheung, Suciu; PLDI 2017): denotes queries as
  K-relations using univalence. It proves many rewrite rules, and the Cosette prover grew out of it.
  [arXiv 1607.04822](https://arxiv.org/abs/1607.04822),
  [PLDI page](https://pldi17.sigplan.org/event/pldi-2017-papers-hottsql-proving-query-rewrites-with-univalent-sql-semantics)
* **A Formalization of SQL with Nulls** (Ricciotti, Cheney; JAR 2022): covers
  three-valued logic, set and bag operations, lateral joins and nested subqueries.
  [arXiv 2003.11331](https://arxiv.org/abs/2003.11331),
  [PMC9637088](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9637088/)
* **Q\*cert** (Auerbach et al., SIGMOD 2017): a verified query compiler
  built around the nested relational algebra (NRA<sup>e</sup>). It's the closest
  analogue to "verified IR for queries".

**Lean 4**
* **RelationalAlgebra** (Rickerd): relational algebra ≡ first-order logic, built on Mathlib.
  [Reservoir](https://reservoir.lean-lang.org/@Rickerd1234/RelationalAlgebra)
* **provenance** (Senellart): semantics for ProvSQL with semiring provenance,
  a natural route to K-relation semantics in Lean.
  [Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/provenance)
* Emergence AI's [Lean SQL equivalence write-up](https://www.emergence.ai/blog/formal-verification-of-sql-queries-in-lean-for-enhanced-accuracy)
  and the typed-queries chapter of
  [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/).

### Possible next steps

The open work is tracked on GitHub:

* [#29, the roadmap](https://github.com/AlexanderNenninger/substrait-lean/issues/29):
  closing the gaps between the model and the engines, engine profiles, and the
  optimizations of [docs/optimizations.md](docs/optimizations.md).
* [#60, Ibis API coverage](https://github.com/AlexanderNenninger/substrait-lean/issues/60):
  the operations the coverage table above marks ✗, ranked by how many queries
  of the [catalogue](catalogue/FINDINGS.md) they block.
* [#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85): proved
  error bounds, so that sharded `SUM` and `AVG` of doubles can be allowed.
* [#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63): testing
  the Snowflake SQL on a real account; today it only runs on an emulator.

Longer-term directions:

1. **Non-linear incremental operators.** Aggregates (SUM and COUNT per group
   are linear over Z-sets), `DISTINCT`, semi and left joins, windows.
2. **Completeness.** Contracts say what every output row satisfies; the
   converse ("no window is lost") is a Lean theorem per plan today
   (`IoT.window_complete`), not something the checker reports.
3. **Translation validation.** Given a plan and its optimized form, have Lean
   check that they are equivalent. A decision procedure for the conjunctive
   fragment would mirror Cosette and HoTTSQL.
4. **Real types.** A typing judgement over Substrait types (decimals, dates,
   nullability), with `eval` proven to respect it.
5. **Mathlib `Multiset` or K-relations.** Move bag equivalence to quotients, or
   generalize to semiring-annotated relations as HoTTSQL and provenance do.

## License

sverify is licensed under the [Mozilla Public License 2.0](LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](python/src/sverify/ibis_substrait/LICENSE).
