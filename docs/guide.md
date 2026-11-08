# Guide

What sverify does and how to use it, with examples that the test suite
runs. [python/README.md](../python/README.md) is the short version,
[examples.md](examples.md) shows each feature in a few lines, and how it
works inside is in [how-it-works.md](how-it-works.md).

## Install and a first contract

```bash
pip install sverify                 # or: uv add sverify
pip install 'sverify[delta,iceberg,polars,spark]'   # or 'sverify[all]'
```

The core runs on DuckDB: contracts, incremental maintenance, and SQL for
DuckDB, Snowflake and Spark. The extras add `datafusion`, `polars`, `spark`
(needs Java 17 or 21), `delta`, `iceberg`, `flight` (`FlightSource`) and
`testing` (Hypothesis strategies). Wheels bundle the Lean checker
as a small native binary, so you need no Lean toolchain; they exist for Linux
(x86_64, aarch64) and macOS (arm64), Python 3.12 and later.

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
```

A transform states what it assumes about its inputs (`requires`) and what
it promises about its output (`ensures`). Applying it to a source proves
the promise for every input that meets the assumptions, before any data
runs; `refresh` runs it, here on Polars by a route that says how the proof
carries over ([Routes](#routes-classes-and-profiles)):

```python
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 22, sv.unique("id")],
)
def first_contract(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


first = orders.pipe(first_contract)  # proved here
first.refresh(engine="polars", route="auto")
print(first.to_arrow().to_pylist())
# [{'id': 3, 'doubled': 100}]
```

## What it does for you

In order of day-to-day value:

1. Contracts proved before the pipeline runs. The checks you would
   write as dbt tests or data expectations (`not_null`, `unique`, accepted
   ranges, relations between columns) hold on every input that meets the
   preconditions, including data you never tested with. A test finds a
   NULL city after a left join when one shows up in production; the checker
   refuses `not_null(city)` when you write the model. Runtime errors
   (division by zero, integer overflow, bad casts, regular expressions that
   don't compile) are ruled out the same way, or reported before the job
   can fail at 3 am. Preconditions are checked on the data, or proved from
   Delta and Iceberg metadata (schemas, CHECK constraints, file statistics).
2. One plan, the same answer on every engine. You develop on DuckDB or
   Polars and run on Spark (one day, on Snowflake). The same SQL text doesn't
   mean the same thing on each (`/` on integers truncates in DataFusion and
   PostgreSQL and gives a double in DuckDB and Spark; DataFusion wraps on
   overflow where DuckDB raises; NULLs sort first or last depending on the
   engine). Sverify translates the checked plan for each engine with every
   such choice spelled out, or refuses the plan where an engine can't
   match, as for windows over a Snowflake table with ties. On DuckDB and
   Polars a route says how the proof carries over, and its class what you
   can rely on ([Routes](#routes-classes-and-profiles)).
3. Results kept up to date from the changes, provably. Instead of a
   watermark job ("process the rows newer than…"), which misses deletes,
   late rows and new join matches, sverify updates a result from the
   inserts and deletes alone, with a delta plan proved equal to a full
   recompute. It reads Delta's Change Data Feed and Iceberg's appends
   (skipping the Delta files a proof shows a filter can't match),
   writes each state to a Delta or Iceberg sink exactly once, and the sink
   carries the proved contract to the next job, which builds on it without
   re-checking the data.
4. Proved optimizations. A plan can be split across shards (Delta or
   Iceberg partitions, files) and the results combined, with a proof that
   the result is the same; per-row overflow checks can be dropped where a
   contract proves them unnecessary; and a plan can be rewritten with what
   its contract establishes (a `DISTINCT` over a key or an implied filter
   goes, a left join on a NOT NULL foreign key becomes an inner join). See
   [docs/optimizations.md](optimizations.md).

What it doesn't do (yet). Correlated scalar subqueries are not in the
model. An `ibis.param` is checked with its value bound,
`sv.verify(expr, params={threshold: 50})`, and the report and `report.run`
are about that value; an unbound parameter is refused, and so is one in a
transform or a node. Incremental maintenance covers filters,
projections, inner, cross, semi and anti joins, `UNION ALL`, `DISTINCT`, and
`COUNT`, exact `SUM` and `AVG`, `MIN` and `MAX` per group; another aggregate
recomputes only the groups a batch touches, and a window only the partitions
it touches. Other views (left joins) are recomputed and diffed instead, and
`node.status()` says so. [The Ibis coverage table](../README.md#ibis-coverage)
has the full list.

## Workflows

Three complete jobs, condensed from the [query catalogue](../catalogue/INDEX.md)
of 139 real analytical queries, are the first notebooks of the
[tour](../README.md#the-tour). Each starts from source tables, states and proves a
contract, runs on every engine, keeps up with new data, writes a sink, and
shows what goes wrong without the checker. `poe notebooks` runs them
headless in CI.

| Workflow | Sources and sinks | What the checker catches |
|---|---|---|
| [Duplicate card payments](../notebooks/01_duplicate_payments.py) | Delta table with Change Data Feed → Delta sink → a downstream job | a self-join matching each payment with itself; a watermark job that misses a late duplicate and keeps a reversed one |
| [Sensor alerts](../notebooks/02_sensor_alerts.py) | Iceberg table → Iceberg sink | an alert over `LAG` that depends on how ties break; a NaN reading raising a false alert (`NaN > 30` is TRUE in SQL); a sensor sending twice |
| [An orders mart](../notebooks/03_orders_mart.py) | Delta orders and a type-2 customer dimension → Delta sink | dbt's `not_null(city)` failing after a point-in-time left join; `/` meaning three things on three engines |

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
# transactions: (_.ts < datetime(2100, 1, 1)) (file stats @v1)

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

for engine in ENGINES:  # the same rows on DuckDB and Polars
    again = duplicate_payments(transactions)
    again.refresh(engine=engine)
    assert again.to_arrow().to_pylist() == stored.to_arrow().to_pylist()
```

## What goes wrong without it

The catalogue probed its 139 queries on DataFusion, DuckDB, Polars and
Snowflake SQL and recorded each query's cross-engine pitfalls
([`pitfalls.toml`](../catalogue/pitfalls.toml), [FINDINGS](../catalogue/FINDINGS.md)).
The most common, and what sverify does about each:

| Pitfall | What the engines do | sverify |
|---|---|---|
| Ties in `ROW_NUMBER`, `LAG`, `LIMIT`, top-N, dedup (44 of the 139 queries) | no engine promises an order among ties; Snowflake and Spark tables have no row order at all | without a key that rules ties out, nothing is proved (`deterministic=False`); Snowflake and Spark SQL is only written with a proved `deterministic=True` |
| NULL join keys | SQL engines never match them; pandas `merge` does, Polars with `nulls_equal=True` | the model's semantics, on every engine; proofs use it (`merchant` is never NULL after `a.merchant = b.merchant`) |
| Integer division | DataFusion and PostgreSQL truncate; DuckDB and Spark give a double; Snowflake a NUMBER with extra scale | truncates on every engine |
| Division by zero (14 queries) | DataFusion, Snowflake and PostgreSQL raise; DuckDB returns NULL; Polars null or inf | proved impossible, or reported as `may fail` before the job runs |
| Integer overflow | DataFusion wraps silently; DuckDB raises; Snowflake's NUMBER(38) doesn't overflow | an error at the declared width, reported as `may fail` unless a precondition rules it out; the engines raise there. A `SUM` that may overflow is assumed to fit (inferred) and checked on the data before the run |
| NaN | in SQL engines NaN equals itself and is above every number (`NaN > 30` is TRUE); in Python and pandas it compares False | one NaN, as SQL engines have it, on every engine; contracts see it (`~_.v.isnan()` is refused unless proved) |
| `NOT IN` with a NULL | standard SQL returns no rows; DataFusion gets it wrong | refused; write an anti join |
| Guards that don't guard | DuckDB and Polars evaluate both operands of `AND` and `OR`, and DataFusion merges filters, so `WHERE n <> 0 AND x / n > 1` can still fail; DuckDB evaluates a `CASE`'s constant conditions while it plans the query | the runtime-error analysis only counts guards that hold: a `CASE` branch, `NULLIF`, a filter below a projection ([Guards](#guards)); a constant that raises makes the whole plan raise |
| NULL ordering | DataFusion, PostgreSQL and Snowflake put NULLs last ascending and first descending, DuckDB last both ways, Spark first ascending, a Polars sort first | every `ORDER BY` says where NULLs go |

Front ends change meaning too: the catalogue found Ibis rewriting TPC-H Q11's
threshold (a total over all parts) into each part's own sum, so the query
compared each part with itself, and nothing failed. [backend_semantics.py](../catalogue/backend_semantics.py) checks every such quirk
against the model, and its section 8 checks DataFusion as a backend.

## Using sverify

[Install](#install-and-a-first-contract) covers the release; the nightly
builds of `main` and how to pin one are in
[python/README.md](../python/README.md).

The [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents every public function and class, for the released version (built
from `python/great-docs.yml` with `uv run poe docs`), and so do
[agent skills](https://alexandernenninger.github.io/substrait-lean/skills.html)
for coding agents that write sverify code (`npx skills add
https://alexandernenninger.github.io/substrait-lean/`, or `sverify/skills/` in
the wheel). The [tour](../README.md#the-tour)
covers each feature in notebooks 4 and 5.

### Contracts

`@sv.transform` decorates a function from Ibis tables to an Ibis table.
Called on a source or another node, it builds a node (and on Ibis tables, an
Ibis expression). Each call proves the postconditions before it returns:

```python
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)
print(doubled.report)
# requires orders: (_.amount >= 0)
# requires orders: (_.amount < 1000000000)
# requires orders: _.id.notnull()
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer in [22, 1999999998]
```

Lean worked out that `doubled` is at least 22: the filter keeps only
`amount > 10`, and doubling preserves that. The bound on `amount` keeps
`amount * 2` within 64 bits, and caps `doubled`; without a bound, the
report names the one the plan needs ([Inferred bounds](#inferred-bounds)). A
postcondition that doesn't follow is refused, with what *is* known:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

from sverify.errors import CompositionError, NotIncrementalError, VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# 1 of 1 postcondition not proved, 1 precondition needed (e.report has the details)
#   ...
#   not proved: (_.total > 5): it may be FALSE on some rows ...
#     would hold with `(_.amount >= 5)` in the requires of 'orders'
```

* Conditions are Ibis expressions (`_.amount >= 0`) or SQL snippets
  (`"amount >= 0"`), whichever language the transformation is in. SQL
  transformations are checked with
  `sv.verify(sql, tables=..., requires=..., ensures=...)`, which returns the
  report; an Ibis condition there reads the query's output, or in `requires`
  its input table ([#438](https://github.com/AlexanderNenninger/substrait-lean/issues/438)).
* `report.run(con)` runs the plan the report checked over the tables of an
  `sv.connect()` connection, on its engine or the one you name
  (`report.run(con, "polars")`). The result is the one the report is about,
  `params` and `semantics` included
  ([#461](https://github.com/AlexanderNenninger/substrait-lean/issues/461)).
  It first checks the report's preconditions on the tables, the inferred
  ones included, and refuses a batch that breaks one with a
  `PreconditionError` that names it, before anything runs
  ([#604](https://github.com/AlexanderNenninger/substrait-lean/issues/604)).
  `check_requires=False` skips the check for a caller that has made it
  already; the report's guarantee then holds only on data that meets them:

  ```python
  report = sv.verify(query, tables={"t": con.table("t")}, ensures=[sv.unique("host")])
  if report.proved:
      result = report.run(con)
  ```
* `requires` maps each input to its conditions. A transformation with one
  input also takes a plain list, `requires=[_.amount >= 0]`. A key that
  names no input raises a `ValueError` that lists the inputs (#408).
* Preconditions describe data that comes from outside. On a source, they
  are checked on the data when the node is first refreshed and then on each
  batch (`PreconditionError`), or proved from the table's metadata; on Ibis
  tables bound to data (`sv.connect()`), at call time. The error carries
  the table (`e.source`), the condition as stated or inferred
  (`e.condition`) and up to ten of the rows that break it, as an Arrow
  table (`e.rows`; None for `max_rows` and `rows_per`)
  ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)):

  ```python
  try:
      node.refresh()
  except PreconditionError as e:
      log.error("%s breaks %s", e.source, e.condition)
      quarantine.write(e.rows)
  ```
* Unproved postconditions raise `VerificationError`. With
  `on_unproved="check"` they are checked on the output data instead
  (`PostconditionError`): on bound tables at call time, on a node at every
  refresh (see [Nodes](#nodes-composing-storing-refreshing)). With
  `on_unproved="warn"` you get a warning.
* Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base (`ValueError`,
  `RuntimeError`); import the exceptions from `sverify.errors`
  ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
* What Lean tracks per column: whether it can be NULL, integer, double
  and timestamp ranges, which booleans it can be, and whether it can be a
  string. Filters (`amount > 10`, `x IN (1, 2, 3)`, `x IS NOT NULL`) refine
  those facts; arithmetic, `CASE`, `COALESCE`, joins and `UNION ALL` carry
  them through. Schemas count: a non-nullable column is never NULL.
  `x IN (0, 1)`, and `isin([0, 1])`, of integers that fill a range is
  read as `x BETWEEN 0 AND 1`, so a column known to lie in `[0, 1]` meets
  it ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
  `report.not_null` lists the output columns the checker shows are never NULL.
* Relations between columns: join and filter conditions such as
  `w1.ts = w0.ts + 60`, `a.ts = b.ts`, `t0 < t1` or `value != -9999` become
  facts about each row, so postconditions like `t1 - t0 == 60` or
  `first_txn < duplicate_txn` follow.
* Conditions kept whole (#597): each precondition and filter condition, of
  any shape, is also a fact about each row, as stated. A postcondition that
  restates one is proved where the plan keeps it: through projections that
  keep its columns (renamed or not), filters, sorts, limits, joins and
  `UNION ALL`s whose inputs all have it. The right side of a left join loses
  it, since its padded rows are NULL. Under a filter or in a `CASE` branch,
  a disjunct that cannot be TRUE drops out, and the rest narrows the columns:
  with `(_.a <= 0) | (_.b < 0)` in `requires`, `t.filter(_.a > 0)` gives
  `b <= -1`, and so does the branch `ifelse(_.a > 0, ..., ...)`. A NULL
  disjunct is not TRUE either, so the columns need not be NOT NULL.
  Implications written `ifelse(_.a > 0, _.b < 0, True)` work the same way.
  Comparisons between columns other than `x - y` against a constant,
  products and facts through aggregates are later steps of #597
  ([tests](../python/tests/test_relational_preconditions.py)).
* Keys: `sv.unique("user_id", "ts")` says there is at most one row per
  key. In `requires` it is checked on the data; in `ensures` it is proved
  (keys survive filters, projections, aggregates and joins whose condition
  pins down the other side's key). Every Arrow column is nullable, so
  `sv.unique("id")` leaves `id` able to be NULL. `sv.key("id")` is a
  primary key: `sv.unique("id")` and `'"id" IS NOT NULL'`, which the report
  lists in its place ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
* Foreign keys: `sv.references("cust", to=customers.id)` in `requires`
  says every non-NULL `cust` occurs in `customers.id` (checked on the data,
  like `unique`). `to` also takes a pair of names, `("customers", "id")`. Nothing proves it in `ensures`, so it stays an assumption.
* Windows: `LAG`, `LEAD` and `ROW_NUMBER` over `PARTITION BY … ORDER BY`.
  If rows can tie in the order, the engine decides which comes first:
  `verify` proves the postconditions that hold for every order of the ties,
  `report.deterministic` is `False`, `str(report)` names the window and
  `report.ties` the key that would close it ([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)).
  A key on the partition and order columns makes the order total, which
  facts such as `prev_ts < ts` and a rerun that must give the same rows
  need.
* ASOF joins: `sv.asof_join(left, right, on="ts", by="device",
  tolerance=...)` matches each row with the latest earlier row of the other
  table, built from a range join and `ROW_NUMBER` that Lean checks like any
  plan.
* Doubles and time: comparisons with constants are exact, including
  sentinels like `-9999.0`, `isnan()` and intervals; doubles compare as SQL
  engines compare them, with one zero and one NaN above every number.
* Sums and means of doubles round once (D25). Their signs are exact, a mean
  of values in `[0, 100]` is in `[0, 100]`, and with a row cap in
  `requires`, `sv.max_rows(10_000_000)` (checked on the data), a sum of
  values in `[0, 100]` is in `[0, 10⁹]` ([float bounds](float-bounds.md)).
  `sv.approx(_.total <= 1e9)` states a postcondition up to rounding; the
  report suggests it when an exact claim misses only by rounding.
* Strings: a column's strings while they are few (up to 64), from constants,
  `IN` lists, `=` and `<>` filters, `CASE`, `COALESCE` and `UNION ALL`. That
  proves dbt's `accepted_values` and keys over `UNION ALL` branches tagged by
  a constant
  ([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708),
  [#436](https://github.com/AlexanderNenninger/substrait-lean/issues/436)).
* Not tracked yet: what is inside a string (`LIKE`, lengths), relations beyond
  "column plus constant" (`a < 2 * b`), and counts across rows (so
  `COUNT(*) >= 1` in a group is not known).

### Runtime errors

The report lists every runtime error that may happen on some input that
meets the preconditions, and `@sv.transform` refuses the transformation
while there is one:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, on_inferred="off")
def share(orders):
    return orders.select(orders.id, per_unit=orders.amount // (orders.amount - 30))

try:
    share(orders)
except VerificationError as e:
    print(e)
# 1 possible runtime error (e.report has the details)
#   may fail: division by zero: amount // (amount - 30)
#     hint: state `(_.amount != 30)` in the requires of 'orders'
```

Without `on_inferred="off"`, the report names the precondition the plan needs,
`(_.amount != 30)`; declare it in `requires`, and `share` is proved
([Inferred bounds](#inferred-bounds)).

Errors are what an engine fails on: integer division or remainder by zero,
`MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions that may
not compile, and `+`, `-`, `*` leaving their declared width (DataFusion
wraps around there; the reference raises). An integer `SUM` leaving 64 bits,
or a decimal `SUM` leaving its precision ([#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316)),
is ruled out where the plan bounds a group's rows (a `VALUES` list, a `FETCH`
count, or a row cap `sv.max_rows(n)` on an input: [Row caps](#row-caps)) and
`requires` bounds the column. Elsewhere sverify assumes the sum fits, and
the job checks it at run time, on the data before the run
(`Report.assumed`; an error with `on_inferred="off"`). The same holds for an
operation on finite doubles that may overflow to `±∞`, which the reference
raises on ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)).

### Guards

Guards are understood where the engine respects them: in a `CASE` branch
or `NULLIF(n, 0)`, and in a filter below a projection. Filter first, then
compute, and the division is proved safe with no precondition:

```python
gcon = sv.connect()
gcon.put("lines", pa.table({"id": [1, 2, 3], "n": [4, 0, 2], "total": [100, 250, 30]}))
lines = gcon.table("lines")
kept = lines.filter(lines.n != 0)
per_line = sv.verify(kept.select(kept.id, per=kept.total // kept.n), requires={"lines": [_.total >= 0]})
print(per_line.run(gcon).to_pylist())
# [{'id': 1, 'per': 25}, {'id': 3, 'per': 15}]
```

A guard inside an `AND` or `OR` protects nothing, since DuckDB and Polars
evaluate both operands (D19 of [core-semantics.md](core-semantics.md)), and
neither does a guard in one column of a `SELECT` for a division in another.
The report then needs the precondition `n != 0`, and says where the error
sits:

```python
mixed = sv.verify(
    lines.select(lines.id, ok=(lines.n != 0) & (lines.total // lines.n > 1), per=lines.total // lines.n)
)
print(mixed)
# needs: (_.total >= -9 * 10**18) and (_.n != 0) on lines, inferred from `total // n` ...
# hint: `total // n` is inside an AND or OR you wrote (`&` or `|`), and DuckDB and Polars evaluate both operands ...
```

Declared in `requires`, `n != 0` is checked on each batch before the run,
and `run` refuses this batch, whose second row has `n = 0`, with a
`PreconditionError`. Guard the operation itself,
`ibis.cases((_.n != 0, _.total // _.n))`, and no precondition is needed.
A constant subexpression that raises, such as `1 // 0 = 1` in a later
`WHEN`, makes the whole plan raise on any data, since DuckDB evaluates it
while it plans the query
([#609](https://github.com/AlexanderNenninger/substrait-lean/issues/609)).

### Inferred bounds

An overflow at the declared width is an error (#202), so `amount * 2` on a
`BIGINT` needs a bound on `amount`. Sverify infers it (#244): for each `+`,
`-`, `*` by a constant, negation, `abs` and timestamp truncation that may
leave its range, it works out the range each input column must stay in. By
default the plan is not proved until you declare it, and the report says
where it came from and how to fix it
([D23](core-semantics.md#d23-inferred-preconditions-are-errors-by-default)):

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.twice >= 0])
def twice(orders):
    return orders.select(orders.id, twice=orders.amount * 2)

try:
    twice(orders)
except VerificationError as e:
    print(e)
# 1 precondition needed (e.report has the details)
#   needs: (_.amount < 2**62) on orders, inferred from `amount * 2` (overflow otherwise): declare it in requires ...
```

Declare `_.amount < 2**62`, or a tighter bound your data keeps, or filter
the rows out first. A tool that phrases the fix in its own terms (a dbt
test, an editor's quick fix) reads `Report.needs`: one `Needed` per
precondition, with its table, column, comparison, bound, SQL and the
runtime error it rules out. Each postcondition's
`CheckedCondition.reason` says the same of an unproved postcondition, as a
code (`"not_a_key"`, `"may_be_false"`, `"may_be_null"`, …).

`on_inferred` takes four values: `"error"` (the default) needs the bound in
`requires`, `"warn"` assumes it with an `InferredWarning`,
`"ignore"` assumes it without one, and `"off"` infers nothing:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.twice >= 0], on_inferred="ignore")
def twice_assumed(orders):
    return orders.select(orders.id, twice=orders.amount * 2)

twice_assumed(orders)
print(twice_assumed.report)
# requires orders: (_.amount >= 0)
# requires orders: (_.amount < 2**62) (inferred from amount * 2)
# ensures (_.twice >= 0): proved
# ...
```

An assumed bound is a precondition like the rest. It is checked on the
data at call time and on every refresh, or proved from Delta and Iceberg
file statistics, and refresh reports list it as
`orders: (_.amount < 2**62) (inferred, checked on data)`. Downstream nodes
build on it like on any other precondition of a source.

* The inference is untrusted: Lean proves the contract again with the
  inferred bounds added, so a wrong bound makes the proof fail
  ([SubstraitLean/Infer.lean](../SubstraitLean/Infer.lean)).
* Bounds are rounded inward to round numbers (`3 * 10**18`, `2**62`) and
  timestamps to whole years (`ts.truncate("M")` needs
  `_.ts >= datetime(1678, 1, 1)` and `_.ts < datetime(2262, 1, 1)`, the
  range of nanosecond timestamps).
* Other runtime errors get preconditions the same way:

  | Operation | Inferred precondition |
  |---|---|
  | `a // b`, `a % b` | `(_.b != 0)`, `(_.b != 1)` for `a % (b - 1)` |
  | `x.sqrt()`, `x ** 0.5` | `(_.x >= 0.0)` |
  | `x.ln()`, `x.log10()`, `x.log2()` | `(_.x > 0)` |
  | `x.asin()`, `x.acos()` | `(_.x >= -1.0)`, `(_.x <= 1.0)` |
  | `x.cast("int64")` of a double | `(_.x >= -2**63)`, `(_.x < 2**63)` |
  | `a.cast("int32")` | `(_.a >= -2**31)`, `(_.a < 2**31)` |
  | `ibis.literal("ab").repeat(n)` | `(_.n < 2**30)` |
  | `big * 2` of a `DECIMAL(38, 2)` | `(_.big >= -4 * 10**35)`, `(_.big < 5 * 10**35)` |
  | `d + ibis.interval(days=10)` | `(_.d >= date(1, 1, 1))`, `(_.d < date(9999, 1, 1))` |

  [test_infer_errors.py](../python/tests/test_infer_errors.py) has these
  cases.
* A product or sum of two unbounded columns has no single weakest bound,
  the value of an aggregate (`SUM`) or window function has none on a
  column, and a value from another contracted transformation is bounded by
  its `ensures`. For these the report's hint suggests a bound
  (`Issue.hint`), and sverify assumes none.
* `on_inferred="off"`, on `@sv.transform` and `sv.verify`, infers and
  assumes nothing: each overflow, a `SUM`'s included, fails the proof, and
  its hint names the bound to state.

For what it does not infer, the report's `hint:` lines name
the bound to add. An integer `SUM` gets the range Lean knows for the column it
adds up and the largest group whose sum then fits 64 bits, or a bound to add
when the column has none:

```python
samples = ibis.table({"host": "string", "ts": "timestamp", "cpu": "int64"}, name="samples")
per_minute = samples.group_by(["host", samples.ts.truncate("m").name("minute")]).aggregate(
    cpu=samples.cpu.sum()
)
print(sv.verify(per_minute))
# needs: (_.ts >= datetime(1, 1, 1)) on samples, inferred from `ts.truncate('minute')` ...
# ...
# hint: SUM of `cpu`: bound it in `requires` of samples, for example `_.cpu <= 1_000_000_000` and `_.cpu >= -1_000_000_000`; then a group's sum fits 64 bits for up to 9,223,372,036 rows...
```

### Row caps

`sv.max_rows(n)` in `requires` states that an input has at most `n` rows
(#219). Lean carries the caps through the plan
([Rows.lean](../SubstraitLean/Rows.lean)), and an integer `SUM` of values in
`[-m, m]` over at most `n` rows, with `n · m < 2⁶³`, is proved to fit, with
nothing to check on the data:

```python
per_host = samples.group_by("host").aggregate(cpu=samples.cpu.sum())
report = sv.verify(
    per_host, requires={"samples": [_.cpu >= 0, _.cpu <= 100, sv.max_rows(10**12)]}
)
print(report)
# requires samples: (_.cpu >= 0)
# requires samples: (_.cpu <= 100)
# requires samples: max_rows(1000000000000)
# semantics: reference
# known about the output:
#   rows: at most 1,000,000,000,000
# ...
```

* Filters, semi-joins and `DISTINCT` keep at most their input's rows,
  `LIMIT` at most its count, `UNION ALL` adds, and an aggregate without
  `GROUP BY` has one row. A join multiplies, or keeps the left side's rows
  when its condition matches a `unique` key of the right side
  (`Rel.capJoins_eval`).
* A cap is checked on the data at call time and on every batch of an
  incremental view, or proved from the record counts of the Delta or Iceberg
  files a source reads.
* In `ensures`, `sv.max_rows(n)` is proved from the inputs' caps.
  `Report.rows` is the cap on the output, under "known about the output".
* The SUM hint names the cap that proves a sum fits.
* A cap also bounds the magnitude of an integer or decimal `SUM`: at most
  `n` values in `[lo, hi]` add up to within `[min(0, n·lo), max(0, n·hi)]`,
  so arithmetic on the sum can be proved to fit
  ([#470](https://github.com/AlexanderNenninger/substrait-lean/issues/470)).

### Rows per key

`sv.rows_per("customer", at_most=n)` in `requires` states that at most
`n` rows of an input agree on the columns (#219). A cap on the whole table
bounds every group at once; this bounds each group alone, so a table may
grow without limit while each customer's rows stay few:

```python
sales = ibis.table({"customer": "string", "amount": "int64"}, name="sales")
per_customer = sales.group_by("customer").aggregate(total=sales.amount.sum())
report = sv.verify(
    per_customer,
    requires={"sales": [_.amount >= 0, _.amount <= 10**6, sv.rows_per("customer", at_most=10**12)]},
)
assert not report.assumed and not report.errors
# Each group's sum is at most 10¹² · 10⁶, which fits 64 bits.
```

* Filters, sorts, `LIMIT`, `DISTINCT`, semi-joins, projections and
  `UNION ALL` keep the bounds (`Rel.perKey_sound` in
  [Rows.lean](../SubstraitLean/Rows.lean)), and so does a join on a `unique`
  key of its right side. A `unique` key is a bound of 1.
* An aggregate grouping by all of a bound's columns has groups of at most
  that many rows (`Rel.groupRows_sound`), which bounds its integer and
  decimal `SUM`s.
* `Report.rows` is the bound on the result's rows.
* It is checked on the data at call time (a `GROUP BY` of the columns, with
  NULLs as one key), or proved from a row count of a Delta or Iceberg table
  of at most `n` rows. Incremental views refuse it until batches are checked
  against it.

### Suggested preconditions

An unproved postcondition that compares a value with a constant gets a
suggestion: the precondition on the inputs under which Lean proves it. It
is never assumed, since it changes what the transformation accepts:

```python
items = ibis.table({"id": "int64", "qty": "!int64"}, name="items")
report = sv.verify(
    items.select(items.id, doubled=items.qty * 2),
    requires={"items": [_.qty >= 0]},
    ensures=[_.doubled <= 100],
)
print(report)
# ...
# ensures (_.doubled <= 100): NOT proved: it may be FALSE on some rows
#   would hold with `(_.qty < 51)` in the requires of 'items'
# ...
```

Sverify proves each suggestion before showing it, by proving the
postcondition again with it added. `Report.suggestions` has them as
`Needed` records, per postcondition, for editors and language servers
([test_suggestions.py](../python/tests/test_suggestions.py)).

### Checking without running

A tool that reads a contract's proof, such as an editor, a CI step or dbt,
checks a transform on input schemas with `check`. It returns the report
without raising and reads no data, so `requires` is not checked on a bound
table:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.unit >= 0])
def unit_price(orders):
    return orders.select(orders.id, unit=orders.amount // orders.qty)


report = unit_price.check(orders={"id": "int64", "amount": "int64", "qty": "int64"})
print(report.proved, [n.label for n in report.needs])
# False ['(_.qty != 0)']
print(report.ensures[0].message)
# NOT proved: it may be FALSE or NULL on some rows
print(report.route("duckdb").cls)
# refused
```

The report's parts come as data and as the lines `str(report)` prints:

- `Report.inputs` and `Report.output` give the schemas of the input tables
  and of the result, the columns `requires` and `ensures` may name.
- `CheckedCondition.message`, `Issue.message`, `Issue.assumption` and
  `Report.notes` are the report's lines for each postcondition, possible
  runtime error, assumption and note.
- `Report.needs` gives the preconditions the proof needs, one `Needed` each:
  table, column, comparison, bound, SQL, the runtime error it rules out,
  the fixes in words (`text`) and the `condition` ready for `requires=`, in
  the transform's language: an Ibis deferred (`_.qty.isnull() | (_.qty != 0)`,
  NULL passing as the inferred bound lets it) or a SQL string
  ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
  `Issue.needs` holds the same records for one runtime error, which
  `Issue.hint` states in words.
- `Report.suggested_requires` is the whole `requires=` mapping: the stated
  preconditions and the inferred ones, ready to pass to `verify` again or
  to paste into the decorator.
- `Report.route(engine)` gives the route a run would take and the plan's
  class on the engine (exact, observed, shim or refused) without running
  it. After a run, `report.routes` records the route taken.
- `report.to_json()` writes the report as a versioned JSON document for CI
  jobs and tools: the verdict, each postcondition with its reason and
  counterexample, the issues, the needs, the facts and the routes, in the
  format of [`report.schema.json`](../python/src/sverify/schemas/report.schema.json).
  Postconditions, issues and assumptions are findings in the shape of a
  SARIF result, with a `ruleId`, a `level` and a `message`.
  `sv.Report.from_json(text)` reads it back into a `Report` with the same
  verdict ([#736](https://github.com/AlexanderNenninger/substrait-lean/issues/736),
  [stability](stability.md)).

The counterexample search tries 200 inputs per unproved postcondition. The
`SVERIFY_COUNTEREXAMPLES` environment variable sets that budget for
`sv.verify`, a transform's call and `check`; 0 skips the search, for a tool
that only needs the verdicts
([test_check_api.py](../python/tests/test_check_api.py)). It skips a
postcondition that only the order of ties leaves open: the checker proves
it where every window orders its rows totally, so its reason is `"ties"`
(`CheckedCondition.ties`), and a key that breaks the ties proves it
([test_checker_speed.py](../python/tests/test_checker_speed.py)).

Sverify keeps the checker's answers on disk, so the next `verify`, `check`
or `refresh` of an unchanged transform takes its proof from there, and an
edit proves again only the transforms whose plans, conditions or inputs
changed ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
An entry is keyed by what the checker reads (the plans, the conditions and
the profile), sverify's version and a hash of the checker binary, so a
change to any of them proves again
([test_proof_cache.py](../python/tests/test_proof_cache.py)). The cache is
in `SVERIFY_CACHE_DIR`, else `$XDG_CACHE_HOME/sverify`, else
`~/.cache/sverify`; processes share it, and `SVERIFY_CACHE=off` turns it
off. Within a Python process or a command, one checker process answers
every request. A request that a time budget or an interrupt stops ends that
process, and the next request starts another.

### The command line

The `sverify` command checks, fixes and runs a pipeline's file from a
shell, a CI job or an agent
([#744](https://github.com/AlexanderNenninger/substrait-lean/issues/744)):

```bash
sverify check pipelines/orders.py            # prove every transform and node in the file
sverify check pipelines/orders.py:paid       # one node or transform
sverify check pipelines/orders.py --full     # with each node's full report
sverify check pipelines/orders.py --diff     # the preconditions the proofs need, as a diff
sverify check pipelines/orders.py --fix      # write them into requires=, then check again
sverify refresh pipelines/orders.py:paid     # run a node and report what changed
sverify explain may_be_false                 # what a [code] of check's output means
```

`check` imports the file without running it. Every contracted transform
the file applies is proved, a node's on its sources' schemas, and a proof
that fails is reported where a call would raise, so one unproved node does
not hide the next. A `refresh()` in the file belongs under
`if __name__ == "__main__":`; while sverify checks the file, it raises. A
directory with a `dbt_project.yml` goes to `sverify-dbt check`.

The output starts with the contract in plain words, for a pull request's
comment or a phone's screen: what the output guarantees, what each refresh
checks on the data, and what is not proved, each finding with a code.

```text
Contract of pipelines/orders.py
  The output guarantees:
    paid (p): amount > 10; no two rows share id
  Each refresh checks on the data:
    paid (p): orders: amount ≥ 0; orders: amount < 1000; orders: no two rows share id
  Not proved:
    doubled (d): needs _.amount < 2**62 on orders (else overflow in amount * 2)  [needs]

paid (p): proved
doubled (d): NOT proved: 1 precondition needed
```

`sverify explain <code>` says what a code means and how to fix it, and
`check --full` adds each node's full report, so the default output stays
short in an agent's context. `check --diff` shows the preconditions the
proofs need (`Report.needs`) as a diff of the decorators' `requires=`, and
`check --fix` writes them and checks the file again.

`--format` (or `--output-format`) chooses the output:

- `text`, the default, as above;
- `json` (`--json` for short), one document for tools in the format of
  [`cli.schema.json`](../python/src/sverify/schemas/cli.schema.json): the
  exit code and its `status`, for each node its `status`, the plain words
  (`summary`) and its report as `Report.to_json()` writes it, and the
  `findings`, each with its code, level and line;
- for `check`, `github`: GitHub's workflow commands, which annotate the
  transform's line on a pull request in any repository and in the mobile
  app;
- `sarif`: a SARIF 2.1.0 log for code scanning
  (`github/codeql-action/upload-sarif`), one rule per code, with
  `explain`'s text
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).

The codes are snake case (`may_be_false`), as the report's `reason` and
issue `kind` write them; `explain` reads kebab case too. The exit codes are:

| Code | Meaning |
|------|---------|
| 0 | proved, or every postcondition it does not prove is checked on the data at each refresh; a refresh committed every row |
| 1 | not proved |
| 2 | usage error: a flag, a missing file, a node the file lacks |
| 3 | unsupported or refused: a construct outside sverify's model (`sverify.errors.UnsupportedError`), or no route takes a proved node to the engine |
| 4 | time or memory budget exceeded |
| 5 | a refresh committed with rows quarantined, or held a node |
| 6 | error: the file raised, I/O, a crash |

With 5, `refresh` prints `Refresh.alert()` after the summary, and its
JSON has `"outcome"` and `"alert"` ([bad rows](#bad-rows-quarantine-and-hold)).
`--examples` adds the rows that broke a condition to both, rows of your
data that otherwise stay out of CI artifacts and issues
([#887](https://github.com/AlexanderNenninger/substrait-lean/issues/887)).

`--timeout` (default 30 s, or `SVERIFY_TIMEOUT`; 0 turns it off) bounds
proof, planning and checking. A refresh moving data has no time limit:
`--memory-limit` (or `SVERIFY_MEMORY_LIMIT`, such as `2GB`) bounds it
instead, as DuckDB's `memory_limit`, past which DuckDB spills to a
temporary directory (`SVERIFY_TEMP_DIRECTORY`). Past either budget the
call stops with code 4 before any sink commits, and reports what was
proved before it ([test_cli.py](../python/tests/test_cli.py)).
`sverify.cli.discover(path)` does what `check` does from Python.

### Environment variables

Each variable sets what a flag or a keyword sets; a flag or a keyword
given wins over the variable, and the variable over the default.

| Variable | Flag | Python | Default | Sets |
|---|---|---|---|---|
| `SVERIFY_CHECKER` | | | the bundled checker | the path to a `substrait-check` binary, such as your own `lake build` |
| `SVERIFY_CHECKER_MEMORY_MB` | | | 4096 | the memory, in MB, one checker request may take before the checker is stopped and the request raises `CheckerMemoryError` (Linux and macOS); 0 turns the cap off |
| `SVERIFY_COUNTEREXAMPLES` | | `verify(counterexamples=)` | 200 | how many inputs are tried per unproved postcondition; 0 skips the search |
| `SVERIFY_TIMEOUT` | `--timeout` | | 30 | seconds for proof, planning and checking; 0 turns it off |
| `SVERIFY_MEMORY_LIMIT` | `--memory-limit` | | none | DuckDB's `memory_limit`, such as `2GB` |
| `SVERIFY_TEMP_DIRECTORY` | | | a directory under the system's temporary one | DuckDB's `temp_directory`, where it spills past the memory limit |
| `SVERIFY_CACHE` | | | on | `off`, `0`, `false` or `no` turns the proof cache off ([Checking without running](#checking-without-running)) |
| `SVERIFY_CACHE_DIR` | | | `$XDG_CACHE_HOME/sverify`, else `~/.cache/sverify` | where the proof cache lives |
| `SVERIFY_SECRETS` | | `Resolver.from_config(path)` | the nearest `pyproject.toml` | the TOML file whose `[tool.sverify.secrets]` table configures named secrets ([Credentials](#credentials)) |
| `SVERIFY_PREBUILT_CHECKER` | | | | for contributors: an editable install links this checker and skips `lake build` |

`SVERIFY_CHECK`, `SVERIFY_PREBUILT_CHECK` and `SVERIFY_SPILL_DIRECTORY`,
their names in 0.6, are read too, the first and last with a
`DeprecationWarning`.

### Composing contracts

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

SQL is DuckDB's dialect. Sverify reads it with its own lift (SQLGlot, #239)
and writes every choice DuckDB's SQL leaves implicit into the plan: `/` divides
as doubles, NULLs sort last, an integer literal has the narrowest type that
holds it.

Every check uses sverify's reference semantics unless you opt into DuckDB's
(#411). `semantics="reference"`, the default, means what sverify's reference
computes, so a double divided by zero raises; `semantics="duckdb"` means what
DuckDB computes, which gives `inf`, and models NaN and ±inf as DuckDB has
them. `sv.sql(query, semantics=...)` attaches the choice to the query.
`sv.verify(..., semantics=...)` and `@sv.transform(..., semantics=...)` make
it for the SQL they lift themselves: a SQL transformation and SQL conditions.
An `sv.sql` expression inside an Ibis transformation keeps its own. The report
says which semantics it used (`Report.semantics`, a `semantics:` line).
`semantics="polars"` reads an Ibis transformation as Polars computes it:
integer `//` and `%` floor, so `-7 % 2` is `1`, and the plan states
`division_type: FLOOR` on each, which Polars runs natively and the other
engines refuse; a zero divisor and integer overflow still raise, so `verify`
infers the same preconditions as under the reference
([engine-profiles.md](engine-profiles.md#polars-as-a-profile)).
`semantics="spark"` reads an Ibis transformation as Spark 4.3.0 computes it
under ANSI mode: the same values as the reference, and doubles that overflow
are ±inf with no precondition, so the plan runs on Spark natively
([engine-profiles.md](engine-profiles.md#spark-as-a-profile)). Until
#411 `sv.sql` defaulted to DuckDB's semantics. The lift reads a subset so far (SELECT, WHERE,
joins of every kind, subqueries and CTEs, GROUP BY with grouping sets,
windows, set operations, ORDER BY, LIMIT, CASE, CAST, and the numeric,
string, date and list functions of
[#240](https://github.com/AlexanderNenninger/substrait-lean/issues/240)) and
refuses the rest, saying what.

A node that ends in `COUNT` and integer `SUM` per group, or in `DISTINCT`,
over an input with delta rules, is maintained from a count and a sum per
group, which each batch's change adds to
(`LinearAgg.aggregate_maintained` in
[`SubstraitLean/IncrementalAgg.lean`](../SubstraitLean/IncrementalAgg.lean),
[section 6 of the optimizations note](optimizations.md#6-incremental-maintenance)).
`DECIMAL` `SUM` and `AVG` keep the same state, and `MIN` and `MAX` keep each
group's extreme: a batch that only inserts into a group merges, and the
groups it deletes from are recomputed from the new input
(`ExtremeAgg.extreme_maintained` in
[`SubstraitLean/IncrementalMinMax.lean`](../SubstraitLean/IncrementalMinMax.lean)).
A node that ends in a semi or anti join on equal keys keeps a count of
matches per key and reads the left input only for the keys whose count
leaves or returns to 0 (`SemiDelta.semi_maintained` in
[`SubstraitLean/IncrementalSemi.lean`](../SubstraitLean/IncrementalSemi.lean)).
A node without delta rules (left join, other aggregates, window, `LIMIT`) is
recomputed and diffed instead, and `status()` says so. An
aggregate whose input has delta rules recomputes only the groups a batch
touches: Sverify takes the group keys of the input rows the batch inserts or
deletes, recomputes those groups from the new input (a semi-join on the
keys), and replaces their rows. This holds for every measure, because an
aggregate's groups are independent (`TouchedGroups.touched_sound` in
[`SubstraitLean/TouchedGroups.lean`](../SubstraitLean/TouchedGroups.lean)).
A projection whose window functions share one `PARTITION BY`, with the
partition keys among its columns, recomputes the partitions a batch touches
the same way (`TouchedGroups.touched_window_sound`, for inputs without ties on
the partition and sort columns). With a time bucket among the keys, the
recompute reads only the range the touched buckets cover.

Window aggregates over bounded RANGE frames of one time column, such as the
sum over the last five minutes per host, recompute only the rows near the
change: for a batch whose rows span `[t0, t1]`, the output rows from
`t0 - end` to `t1 - start` of the touched partitions (or of the whole
table, without `PARTITION BY`), from the input rows in that span
widened by the frame. Lean proves that a window value depends only on the
rows in its frame, so this equals a full recompute for inputs without ties
on the partition and time columns (`TouchedFrames.framed_batch` in
[`SubstraitLean/TouchedFrames.lean`](../SubstraitLean/TouchedFrames.lean)),
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
# ensures (_.amount < 1000): NOT proved: it may be FALSE or NULL on some rows
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
`"polars"`, `"spark"`, a Spark session, or the optional `"datafusion"`. The nodes keep their
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

### Bad rows: quarantine and hold

A batch that breaks a precondition on a source raises `PreconditionError` by
default, and the refresh commits nothing. `on_violation` on the transform, or
on the source, chooses otherwise
([#184](https://github.com/AlexanderNenninger/substrait-lean/issues/184)):

- `"quarantine"` sets the rows that break a precondition aside, with the
  reason, and the node runs on the others.
- `"hold"` commits nothing for the batch and holds the node at its
  versions. The next refresh reads the batch again, so a fix upstream lets it
  through.
- `"error"` is the default.

The transform's setting holds over the source's. Where two transforms fused
into one node state the same condition, the stricter setting holds: error,
then hold, then quarantine.

```python
from deltalake import write_deltalake

write_deltalake(
    "lake/raw_orders",
    pa.table({"id": [1, 2, 3, 3], "customer": ["ada", "bob", "cy", "dee"], "amount": [30, -5, 7, 8]}),
)


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.amount >= 0, sv.unique("id")],
    on_violation="quarantine",
)
def clean(orders):
    return orders.select("id", "customer", "amount")


raw = DeltaSource("lake/raw_orders", name="orders")
node = raw.pipe(clean).write(DeltaSink("lake/clean"))
r = node.refresh()
print(r)
# clean:
#   computed
# ...
#   quarantine: orders: 3 row(s) quarantined (1 × (_.amount >= 0), 2 × unique(id)), 3 in quarantine at lake/clean_quarantine
# ...
r.outcome           # "quarantined"
node.quarantined()  # the rows set aside, with _conditions, _reason, _source_version
```

Which rows are set aside is a function of the source's rows alone, so a
refresh batch by batch and a recompute agree:

- A row on which a row condition is FALSE or NULL (ranges, NOT NULL, value
  sets, inferred bounds).
- Among the other rows, every row of a key that occurs more than once
  (`sv.unique`, `sv.key`): both copies of a repeated `id`, the one the node
  held before included. The rule needs no order between rows, so it gives the
  same answer under every profile ([D24](core-semantics.md)).
- `max_rows`, `arrives_within` and the other conditions on a table as a whole
  have no rule for which rows break them. A batch that breaks one holds the
  node, as `"hold"` does, and the report says why.

Every precondition holds on the rows kept: `Catalog.kept_sound` in
[`Quarantine.lean`](../SubstraitLean/Quarantine.lean) proves it for this rule,
so the node's contract (`contract_sound`, `Rel.keys_sound`) holds on what it
reads. The batch checks then run on the kept rows as on any batch, and a row
the rule let through by mistake would raise.
[`tests/test_quarantine.py`](../python/tests/test_quarantine.py) compares
every refresh of random batches with the rule.

A fix upstream releases rows. A delete or an update of a row set aside takes
it out of the quarantine, and the updated row is judged again. A key that is
on one row again lets that row through. The report counts what each refresh
set aside, released and saw deleted upstream.

A stored node writes the rows it sets aside to a table next to its sink: the
sink's URI, or Iceberg identifier, with `_quarantine` appended.
`.write(sink, quarantine=DeltaSink(...))` names another one, and
`quarantine=False` keeps the rows in memory. The table has one row per
distinct row set aside: the source, the row as JSON, its copies, the
conditions it breaks, the reason, the source version that set it aside, when,
and the node. Each write records the node's epoch and source versions, and
is written before the node's sink, so the table never lags the data it
explains. Its format is stable within 1.x ([stability](stability.md)).

`Refresh.outcome` is `"ok"`, `"quarantined"` (rows are set aside) or
`"held"` (a node skipped a batch), for a job's exit code. `Refresh.alert()`
gives a short Markdown text for whoever is on call: what broke, how many
rows, where they are, and what to do. `Refresh.to_json()`
gives the whole refresh as JSON
([`refresh.schema.json`](../python/src/sverify/schemas/refresh.schema.json)).
Both leave the rows themselves out, since they go to CI artifacts and
issues that more people read than read the data: `alert(rows=True)` shows
five as a table, `to_json(examples=True)` writes up to ten per source in
`examples`, and `PreconditionError.rows` and `QuarantineReport.examples`
hold them in the process
([#887](https://github.com/AlexanderNenninger/substrait-lean/issues/887)).

A change to the schema that a contract cannot follow raises `SchemaError`,
and its message names the column, the version and the contract:

```text
`orders.id` became nullable at v12, and the new rows have NULLs in it; `paid`
requires _.id.notnull(). Fix the upstream, or handle NULLs in `paid` (e.g.
`.fill_null(0)`) and relax `requires`.
```

### Delta Lake and Iceberg

`sverify.io` reads and writes Delta Lake (delta-rs) and Iceberg (pyiceberg)
tables. A table format plays four roles:

* A change source. A transform reads `DeltaSource(uri)` or
  `IcebergSource(catalog, identifier)` directly. The first `refresh()` loads
  a snapshot and records its version; each later one reads the Change Data
  Feed (or, for Iceberg, the files that appends added) from that version to
  the latest, applies it, and records the new version. A failed refresh
  changes nothing, so a retry never applies a batch twice. Where the history
  is gone (CDF off, files vacuumed, row-level deletes in Iceberg), the data
  files that changed are diffed, and the report says so.
  `refresh(audit=True)` also compares the batch with the new snapshot and
  every node with a recompute, before committing anything (`AuditError`).
  On DuckDB, a local table is never loaded into Python: the pipeline holds
  the Parquet files of its version, with the rows that deletion vectors or
  position delete files remove, and DuckDB reads them with `read_parquet`.
  Partitioned tables, Delta column mapping, renamed Iceberg columns,
  equality deletes, object stores and the other engines read through Arrow
  (#173).
* A source of preconditions. `requires` conditions are proved from
  schema nullability, Delta CHECK constraints and per-file statistics:
  min/max of integers, doubles (only where the files count no NaN), dates
  and timestamps, and NULL counts, so a nullable column still proves
  `amount >= 0 OR amount IS NULL`. A batch only uses the statistics of the
  files it added. Strings, decimals and zoned timestamps get no bounds, and
  keys are always checked on the data, since neither format enforces them.
* Proved file pruning (Delta). `DeltaSource(uri, where="amount * 2 > 100")`
  reads only the rows on which the condition is TRUE, and skips a file only
  if Lean proves from its statistics that the condition is TRUE on none of
  its rows. That covers conditions the readers' own statistics pushdown
  doesn't, such as arithmetic on a column. Changes are filtered the same
  way, and the condition becomes a fact about every row for the contracts.
* A sink that carries the contract. `node.write(DeltaSink(uri))` and
  `node.write(IcebergSink(catalog, identifier))` store a node in one commit
  per state, exactly once (keyed by the source versions). A Delta source
  dropped and created again at the same path has a new table id, which the
  contract records: its sinks are rewritten from the new table. When two
  processes refresh the same `DeltaSink`, the second to commit an epoch
  raises `ConcurrentWriteError` and writes nothing; its next refresh
  recovers.
  The proved guarantees become NOT NULL columns and CHECK constraints (Delta)
  or table properties (Iceberg). The NOT NULL columns are those `ensures`
  states (`_.id.notnull()`) and those the proved report shows are never NULL
  (`report.not_null`, [#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
  The commit records the plan hash, the
  source versions and the contract (`sverify.io.Contract`, under the key
  `sverify.contract`, in the format of
  [`sink-contract.schema.json`](../python/src/sverify/schemas/sink-contract.schema.json),
  which every 1.x release reads: [stability.md](stability.md#the-formats)).
  A job that reads the table gets its preconditions from them. After the first write, `DeltaSink` MERGEs each
  change in one commit, and `IcebergSink` writes it as one snapshot of
  position delete files and a data file of the new rows.
  `IcebergSink(catalog, identifier, location=..., partition_by=[("ts", "day")],
  properties={...})` creates its table at that location, partitioned and
  with those properties, which a catalog without a default location, such
  as Unity Catalog's, needs (#468).
  A streaming sink adds a snapshot and small files on every refresh.
  `DeltaSink(uri, compact_every=..., vacuum_retention=...)` and
  `IcebergSink(catalog, identifier, compact_every=..., snapshot_retention=...)`
  compact the table after every so many writes and then remove what older
  versions alone used; `maintain()` does it on demand (#465).

Schema changes. A batch whose data fits the old schema (added columns,
widened types whose values still fit) is read in it, and the report names
the change. Otherwise the nodes reading the source are planned again and
recomputed, except a node with a contract, whose proof was for the old
schema: `refresh` then raises `SchemaError` and changes nothing.

Tables outside a table format, such as a small lookup table, are
`StaticSource(table, version=1, name="regions")`, so that sinks still have a
version for every input; `regions.apply(Changes(...))` changes some rows,
and `regions.replace(new_table, version=2)` swaps the table, which recomputes
the nodes that read it.

Your own sources and sinks take one method each. A `sverify.io.Source`
implements `read(since)`, which returns the new rows and a cursor;
`from_query(fn, cursor_on="ts")`, `from_frame(fn)` and `from_files(path)`
build one from a function or a directory. Sverify numbers the reads as
versions, works out the change, and says in the report what the reads
assume ("rows only arrive with a greater ts"), which `refresh(audit=True)`
checks. A `sverify.io.Sink` implements `write(change)` and optionally
`contract()`, and sverify writes each state once, with its contract;
`sink_from(fn)` hands the whole table to a function. `Storage` holds object
store options and credentials by name for every table that needs them
([Credentials](#credentials)). [Notebook 5](../notebooks/05_pipelines_and_engines.py) of the tour walks
through both.

`sverify.io.flight.FlightSource(location, table)` reads a table of a
numbered batch log on an Arrow Flight server (`pip install
'sverify[flight]'`). The server numbers each batch it receives with
`do_put`, one counter across tables, and keeps them in order. `do_get` with
the ticket `{"table": t, "after": n}` streams the batches numbered above
`n`, each with `{"seq": s}` as app metadata, and names in the stream's schema
metadata the `floor`, the lowest number it still holds; an optional
`"until": m` stops at `m`. The source's cursor is `{"seq": n, "floor": f}`,
the number of the last batch read and the floor at that read. A refresh
appends the new batches, as they arrived and without a copy, and the batches
below the floor, which the server dropped past its retention, come back as
deletes, so the source holds the server's window of rows. A restarted job
resumes at the cursor its sink recorded, unless the server dropped batches
since; then it reads the whole log again. The report states what this assumes: the server numbers batches in
order of arrival, never changes one, and drops only whole batches below its
floor. `sverify.testing.FlightLog()` is a small in-memory server that keeps such a log
(`keep=` batches per table, or `drop(table, below=n)`), the one
[the tests](../python/tests/test_io_flight.py) run against. With `schema=`, a
`FlightSource` proves contracts without asking the server, and `secret=`
names a bearer token ([Credentials](#credentials)):

```python
import pyarrow.flight as fl
from sverify.io.flight import FlightSource
from sverify.testing import FlightLog

log = FlightLog(keep=10_000)  # on 127.0.0.1, at a free port
location = f"grpc://127.0.0.1:{log.port}"


def send(rows):
    batch = pa.table(rows)
    writer, _ = fl.connect(location).do_put(fl.FlightDescriptor.for_path("samples"), batch.schema)
    writer.write_table(batch)
    writer.close()


@sv.transform()
def busy(samples):
    return samples.filter(samples.cpu > 0.5)


send({"host": ["pi3"], "cpu": [0.75]})
node = busy(FlightSource(location, "samples"))
node.refresh()
send({"host": ["nas"], "cpu": [0.9]})
print(node.refresh())
# busy:
#   samples@v1→v2: 1 insert(s), 0 delete(s); Δ trusted as rows appended to samples v1→v2, assuming the Flight server numbers batches in order of arrival, ...
log.shutdown()
```

A restarted job resumes from its sink and skips the recompute. You build the
same nodes again and refresh; a stored node takes the stored rows only if
its plan and source versions match what the sink recorded; otherwise it is
computed, and the report says why. A source of your own resumes too if it
implements `restore(cursor)`: the sink records the source's cursor next to
its version, and the restarted job starts from the table as of that cursor
and reads only what is new since. `from_query` and `from_files` do this; a
cursor whose rows are gone (`restore` returns None) reads the whole table
again:

```python
restarted = DeltaSource(str(lake / "transactions")).pipe(duplicate_payments).write(
    DeltaSink(str(lake / "duplicate_payments")))
print(restarted.refresh())
# duplicate_payments:
#   resumed from .../duplicate_payments@v3
# ...
#   wrote duplicate_payments from transactions@v3: already committed (v3)
```

A `DeltaSink` that writes every minute gathers commits and small files,
which readers replay and open. Its options keep the table small:
`checkpoint_interval` and `log_retention` set the table's checkpoint interval
and log retention, `compact_every=n` compacts the table after every `n`
writes, and `vacuum_retention` then removes the files older versions needed.
`sink.maintain(vacuum_retention=...)` does the same by hand. These commits carry the
contract, and a restarted job resumes past them, as it does past another
writer's `OPTIMIZE`, `VACUUM`, property or constraint change. A commit that
changes rows, by anyone else, makes the job compute the node again. Keep the
log retention longer than the gap between two writes: the contract is read
from the log.

Each refresh report names what it trusted: that the change feed turns the
old snapshot into the new one, and that writers and file statistics are
correct (Delta's millisecond timestamp maxima are widened by 999 µs; with
deletion vectors the statistics cover deleted rows too, which still bounds
the live ones). Iceberg tables with equality deletes can't be read. What is
proved is listed under [Table formats](how-it-works.md#table-formats).

### Credentials

A pipeline names its credentials and holds no value
([#774](https://github.com/AlexanderNenninger/substrait-lean/issues/774)).
The store's default chain comes first: with no options, delta-rs finds
environment variables, `~/.aws` profiles, instance or pod roles, or the
short-lived keys a CI job got through OIDC (the
[pipeline template](../templates/pipelines/docs/for-enterprise.md) does
that). Where a credential has to be fetched, a `sverify.io.Secret` says
where it lives:

| Reference | Where |
|---|---|
| `env:NAME`, `env:PREFIX_*` | environment variables; the prefix form gives fields |
| `file:/run/secrets/lake` | a file: its text, a JSON object, or `KEY=value` lines |
| `bao:kv/pipelines/lake#token` | OpenBao's KV store (`vault:` for Vault) |
| `aws-sm:prod/lake` | AWS Secrets Manager (`sverify[secrets-aws]`) |
| `gcp-sm:projects/p/secrets/lake` | Google Secret Manager (`sverify[secrets-gcp]`) |
| `azure-kv:my-vault/lake` | Azure Key Vault (`sverify[secrets-azure]`) |
| `keychain:service/account` | the OS keychain, for local runs (`sverify[secrets-keychain]`) |

A bare name such as `"lake"` is looked up in `[tool.sverify.secrets]` of the
project's `pyproject.toml`, or in the TOML file `SVERIFY_SECRETS` names;
names it does not list are environment variables (`flight-token` reads
`FLIGHT_TOKEN`). The configuration also says how OpenBao is reached, and
what each credential may read and write:

```toml
[tool.sverify.secrets.bao]
address = "https://bao.example.ts.net:8200"
auth = "jwt"                  # the GitHub Actions OIDC token; "token" reads BAO_TOKEN
role = "pipelines-production"

[tool.sverify.secrets.names]
eurostat = "env:EUROSTAT_TOKEN"
lake = { ref = "bao:kv/pipelines/production", writes = ["s3://lake/production/"] }
```

Sources, sinks and catalogs take the names: `Storage(credentials="lake")`
for a table's object store (the secret's fields are delta-rs options), a
`Secret` as one option's value, `FlightSource(..., secret="flight-token")`,
`Lineage(url, api_key=Secret("env:LINEAGE_TOKEN"))`, and `credentials=` on
`from_query`, `from_frame`, `from_files` and `sink_from`, whose function
reads the value with `Secret(name).value()`. An Iceberg catalog takes
`load_catalog("lake", **Storage({"token": Secret("bao:kv/rest#token")}).options())`.
Sverify reads a value when a table is opened and keeps none: `repr`,
reports, contract records, exports, logs and errors show the name.
[A test](../python/tests/test_secret_leaks.py) plants sentinel values in
every source and sink type and greps every output for them. Answers from
OpenBao and the cloud secret managers are kept for a minute
(`cache_seconds`), so a refresh that opens many tables asks once.

Each refresh entry lists the credentials its node used, by name, for
reading or writing (`StageRefresh.credentials`, `"credentials"` in
`Refresh.to_json`), and `node.credentials()` lists them before any run.
`sverify check` prints them, warns with `[scope]` when a sink lies outside
what its credential may write (`Storage(writes=[...])` or the
configuration's `writes`), and with `[inline_credentials]` when options
hold values or a URI holds them in its userinfo (`s3://key:secret@bucket`).
Every URI sverify records, reports, exports or sends is written without
userinfo, query string or fragment: a sink's `location`, `started`,
`credentials[].location`, the ODCS `physicalName` and the OpenLineage
namespace
([#887](https://github.com/AlexanderNenninger/substrait-lean/issues/887)).
A source's cursor (`Source.restore`) is stored in clear in the sink's
table, so it must not be a credential.

### OpenLineage

[OpenLineage](https://openlineage.io) is the standard for lineage and run
events: Airflow, Spark and dbt emit it, and Marquez, DataHub, OpenMetadata
and the cloud catalogs read it. A refresh emits a run per node, and
`sverify.openlineage` reads what upstream jobs emitted
([#792](https://github.com/AlexanderNenninger/substrait-lean/issues/792)).
The events follow spec 2-0-2, the spec of `openlineage-python` 1.55.0, and
the tests validate every event and facet against it
([tests/standards/](../python/tests/standards/openlineage-1.55.0/),
[test_openlineage.py](../python/tests/test_openlineage.py)).

```python
import tempfile

import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import openlineage
from sverify.io import DeltaSink, StaticSource

lake = tempfile.mkdtemp()
shop_orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]},
    ensures=[_.amount > 10, _.amount < 1000, sv.key("id")],
)
def paid_orders(orders):
    return orders.filter(orders.amount > 10)

paid_sink = DeltaSink(f"{lake}/paid")
stored = shop_orders.pipe(paid_orders).write(paid_sink)
stored.refresh(lineage=openlineage.Lineage("events.jsonl", namespace="shop"))
```

The target is a file (JSON lines), `"console"`, a URL such as
`"http://marquez:5000"`, or `True` for the OpenLineage client's
configuration (`openlineage.yml`, `OPENLINEAGE_*`).

```bash
sverify refresh pipelines/orders.py:paid --lineage http://marquez:5000
```

Sverify sends nothing and opens no connection unless a refresh gets
`lineage=` (`--lineage` on the command line). `OPENLINEAGE_DISABLED=true`
turns it off again, `OPENLINEAGE_NAMESPACE` sets the jobs' namespace and
`OPENLINEAGE_API_KEY` a bearer token (`api_key=` takes a `Secret`). A target that fails warns with
`openlineage.LineageWarning`, and the refresh goes on. The file, console
and HTTP targets need nothing; `lineage=True` reads the OpenLineage
client's configuration (any of its transports, Kafka included) and needs
`pip install 'sverify[openlineage]'`.

Each node is a job named after the node, and each refresh of it a run:
START, then COMPLETE, or FAIL with the error (a node held by a failed
precondition, or an exception), or ABORT for the nodes an earlier failure
kept from running. The run's inputs are the node's sources and the stored
nodes it reads, at their versions, with the `schema`, `dataSource` and
`version` facets, and the preconditions checked on their rows as
`dataQualityAssertions`. Its output is the node's sink, with `schema`,
`dataSource`, `version`, `outputStatistics`, the postconditions checked on
the data as `dataQualityAssertions`, and two more facets:

- `columnLineage`, from the plan Lean checked: each output column with the
  input columns it is copied (`IDENTITY`), computed (`TRANSFORMATION`) or
  aggregated (`AGGREGATION`) from, and the columns that pick the rows
  (`FILTER`, `JOIN`, `GROUP_BY`, `SORT`, `WINDOW`);
- `sverify_contract`, a custom facet with a JSON schema
  ([openlineage-contract-facet.schema.json](../python/src/sverify/schemas/openlineage-contract-facet.schema.json),
  format 1): the node, the sha256 of its plan, each postcondition with its
  status (`proved`, `checked`, `not_proved`), the preconditions, the route
  and class, the outcome, quarantined rows, and the verified plan exported
  to Substrait ([Exporting to Substrait](#exporting-to-substrait);
  `Lineage(plan=False)` leaves it out).

A refresh that raises sends FAIL with the exception's type, and its text
only for sverify's own errors (`sverify.errors.SverifyError`): another
library's message may name a bucket, an endpoint or a catalog URI.
`Lineage(trace=True)` adds the Python stack trace
([#887](https://github.com/AlexanderNenninger/substrait-lean/issues/887)).

Datasets are named by OpenLineage's conventions: a Delta table in object
storage is `s3://bucket` and its path, a local one `file` and its absolute
path, an Iceberg table `iceberg://<catalog>` and its identifier, and other
sources `sverify` and their name.

`openlineage.read(path)` reads events from a JSON lines file (or a list of
events), and `openlineage.marquez(url, namespace, name)` reads a dataset
from Marquez's API. `dataset(source)` gives what upstream jobs said of a
source: its `schema` as an Ibis schema, its `version`, the job that wrote
it (`producer`), and

- `requires`: the postconditions of its `sverify_contract` facet that
  sverify proves again, for a downstream transform's `requires`. The facet
  counts as proved only where it carries its exported plan and the checker
  proves that plan's postconditions (`sv.Report.from_substrait`): a contract
  chains across pipelines, repositories and teams, and each link is proved
  where it is used.
- `evidence`: everything else, as checked evidence: other
  tools' `dataQualityAssertions` (a dbt test, a Great Expectations suite),
  and the claims of a facet sverify could not prove again
  (`why_unverified` says why).

```python
# Another pipeline, in another repository, reads what `shop` wrote.
upstream = openlineage.read("events.jsonl").dataset(paid_sink)

@sv.transform(requires={"paid": upstream.requires}, ensures=[_.doubled > 20])
def doubled_paid(paid):
    return paid.select(paid.id, doubled=paid.amount * 2)

print(upstream.verified, doubled_paid.check(paid=upstream.schema).proved)
# True True
```

To try it with Marquez, `python/scripts/marquez.sh start` runs Marquez
0.51.1 and its Postgres in containers, with the API on port 5000;
`test_marquez_round_trip` runs against it when
`SVERIFY_MARQUEZ_URL` is set. DataHub takes OpenLineage events at
`/openapi/openlineage/api/v1/lineage` on its GMS, so its target is the
GMS's URL with that prefix, such as
`Lineage("http://datahub-gms:8080/openapi/openlineage", api_key=token)` with a
personal access token.

### Time buckets: bounded state

A node that aggregates by a time bucket keeps a row per bucket and group, so
its state grows with every hour it has seen. A bound on how late rows arrive
lets sverify drop the buckets no later batch can change:

```python
from datetime import datetime, timedelta

import pyarrow as pa
import sverify as sv
from deltalake import write_deltalake
from ibis import _
from sverify.io import DeltaSink, DeltaSource

start = datetime(2026, 11, 3)
write_deltalake(
    "lake/samples",
    pa.table({
        "host": ["a", "b"] * 30,
        "ts": [start + timedelta(minutes=10 * (k // 2)) for k in range(60)],
        "cpu": list(range(60)),
    }),
    configuration={"delta.enableChangeDataFeed": "true"},
)


@sv.transform(
    requires={"samples": [
        sv.arrives_within("ts", "PT2H"),
        _.ts >= datetime(2000, 1, 1), _.ts < datetime(2100, 1, 1),
    ]}
)
def hourly(samples):
    return samples.group_by(["host", samples.ts.truncate("h").name("hour")]).aggregate(
        n=samples.count(), peak=samples.cpu.max()
    )


rollup = DeltaSource("lake/samples").pipe(hourly).write(DeltaSink("lake/hourly"))
print(rollup.refresh())  # samples until 4:50, so the hours before 2:00 are final
# hourly:
# ...
#   retention hourly.hour: 3 bucket(s) open (bound 3), 2 retired, 6 state row(s); watermark 2026-11-03 02:50:00
```

- `arrives_within("ts", "PT2H")` says every row a batch inserts has `ts` at
  or after the watermark: the largest `ts` seen before the batch, minus two
  hours. The first refresh checks that `ts` has no NULLs; every later batch
  is checked at refresh, and a late row rejects the batch with
  `PreconditionError`, so nothing is applied. Quarantining late rows instead
  is #184.
- A delete before the watermark is an expiry, the source's own retention (a
  `FlightSource` floor, a Delta `VACUUM` of old partitions), when its row is
  in a final bucket of every view that drops buckets of `ts`. The views and
  their sinks keep those buckets as they were, and the report counts the
  expired rows. Lean proves that the final buckets in the sink and the open
  ones in the state are then a full recompute over every row the source
  received, less the deletes at or after the watermark
  (`Retention.expiry_sound`). A delete before the watermark in a bucket that
  is still open rejects the batch. With no view that drops buckets of `ts`,
  every delete is applied as it is.
- A bucket that ends at or before the watermark is final. Lean proves that
  no admissible batch changes a final bucket, for every measure, so the
  final buckets kept in the sink and the open ones in the state add up to a
  full recompute (`Retention.retention_sound` and `Retention.final_stable` in
  [`SubstraitLean/Retention.lean`](../SubstraitLean/Retention.lean)).
- After the sink has written a refresh, the node drops the final buckets
  from its state. At most `⌈lateness / width⌉ + 1` buckets stay open
  (`Retention.open_buckets_le`), so the state holds that many rows per group.
  The refresh report gives the open and retired buckets, the bound and the
  watermark (`RetentionReport`).
- The bucket is `ts.truncate(unit)` to a second, minute, hour or day, or
  `ts.bucket(...)` with a constant interval of days or less, of a timestamp
  column of the source, under filters and projections that read only their
  own row. Calendar units (weeks, months) and time zones other than UTC for
  hours and days keep every bucket, and the report says why.
- Retention needs a sink that keeps what the state drops: `DeltaSink` does.
  A custom sink that does sets `keeps_retired = True`. With a sink that may rewrite its whole table, such
  as `sink_from`, the node keeps every bucket. A node without a sink holds
  only its open buckets.
- A restarted job resumes from the sink with every bucket, takes the
  watermark from the source's largest `ts`, and drops the final buckets at
  the end of its first refresh.

The refresh still recomputes the aggregate from the source and keeps the
buckets after the last one retired. Windows over time with bounded frames
and interval joins are follow-ups in #294.

### Engines and SQL

```python
from sverify.engines import run

c.refresh(engine="polars")                     # or "duckdb" (the default), "spark"
snowflake_sql = c.to_sql("snowflake")          # or "duckdb", "spark"; UnsupportedError says why
con = sv.connect()                             # or run a plan on tables of your own
con.create("orders", ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
           [(2, "bob", 5), (3, "cy", 50)])
con.create("customers", ibis.schema({"name": "string", "city": "string"}),
           [("ada", "Paris"), ("cy", "Rome")])
run(con, c.internal_plan, "polars")
```

`Node.to_sql` and `Report.to_sql` write the plan a proof checked as DuckDB,
Snowflake or Spark SQL, with its run-time checks, and refuse a plan that is
not proved, as `refresh` and `run` refuse it.

`refresh(engine=...)` picks where a node's plans run; `sv.connect(engine=...)`
and `engine=` on a transform pick where checks on data run.
`run(con, plan, "spark")` runs the Spark SQL on a local session, and
`run(con, plan, session)` on one you pass (the `spark` extra). The generated SQL assumes
the following about the warehouse:

* Snowflake: time columns are `TIMESTAMP_NTZ`, strings have no
  collation, and tables and columns have quoted lower-case names.
* Spark and Databricks: the session uses the settings of
  `sverify.engines.SPARK_CONF` (ANSI mode, a pinned time zone, NTZ
  timestamps, case-sensitive names), and strings use the default
  `UTF8_BINARY` collation.
* Both have no row order, so sorts, `LIMIT` and windows are refused unless
  the report is `deterministic` (a key on the order columns in the
  contract, which `to_sql` reads from the report). A `SUM` or `AVG` of
  doubles runs natively, within the plan's bound of the reference's correctly
  rounded sum (D25). Snowflake has no interval type, so interval-valued
  expressions are refused there.

How the engine translations relate to the reference semantics, and where
that is going, is in [docs/engine-profiles.md](engine-profiles.md).

### Integer division in Ibis and SQL

Ibis's `//` is `FloorDivide` and rounds toward minus infinity. Ibis's `%`
and SQL's `//` and `%` truncate toward zero, so the pair `x // d` and
`x % d` splits a negative `x` into a quotient and remainder that do not add
back up under the reference. Sverify follows each operator as its front end
defines it. On `x = -7`, with `d = 2`:

| Input | `x // 2` | `x % 2` | `q * 2 + r == x` |
|---|---|---|---|
| Ibis, `semantics="reference"` or `"duckdb"` | -4 (floor) | -1 (truncated) | no |
| SQL through `sv.sql` or `sv.verify`, reference | -3 (truncated) | -1 | yes |
| Ibis, `semantics="polars"` | -4 | 1 | yes |

A plan that splits milliseconds into seconds and a remainder with `t.ms // 1000`
and `t.ms % 1000` gets the identity only for non-negative `ms`. State
`_.ms >= 0` in `requires`, or write the plan in SQL, where both operators
truncate. When one plan uses Ibis `//` and `%` on the same operands under the
reference or DuckDB's semantics, its report carries a hint that names the pair.
[`t7b_div_mod.py`](https://github.com/AlexanderNenninger/substrait-lean/blob/f89f83d2b3fc71848f9d5de8547475b99523b9b5/api-critique/tasks/t7b_div_mod.py)
reproduces the table.

### Routes, classes and profiles

A proof is about the plan under one semantics, a profile: sverify's
reference by default, `semantics="duckdb"` for what DuckDB does,
`semantics="polars"` for what Polars does, or
`semantics="substrait"` for Substrait's extension YAMLs, open wherever they
say nothing. An engine computes its own semantics, so running a verified
plan raises a question: does the proof hold for what the engine computes?
A route answers it. `report.run(con, engine, route="auto")` and
`node.refresh(engine=..., route="auto")` pick one of four, and run the plan
only if one applies:

| Route | When |
|---|---|
| `native` | the plan was verified under the engine's own profile (`semantics="duckdb"` on DuckDB, `semantics="polars"` on Polars, `semantics="spark"` on Spark) |
| `translated` | the plan was verified under the reference, and sverify's translation to the engine writes the reference's choices (proved for DuckDB, `Lowering.lower_correct`; shims proved for Polars and Spark). Before 0.6 this route was `reference`, which `route=` still takes, with a `DeprecationWarning` |
| `transfer` | the plan was verified under another profile, and at every option the proof depends on, the engine's choices are within that profile's |
| `recheck` | the checker proves the plan again under the engine's profile |

`report.routes[engine]` records the route, with its class, which says what
you can rely on. A route prints its class first, then
the evidence, and the route where it is not `translated`:
`shim (integer division rewritten to truncate); evidence tested`, or
`exact; transfer: verified under semantics="duckdb"; …`.

| Class (`route.cls`) | What it means for you |
|---|---|
| `exact` | every result the engine gives is one the proof covers |
| `observed` | the result equals one the proof covers up to the report's observation: doubles within the plan's proved bound (`floats="plan"`, the default), or what `ensures` states with `sv.equivalent(...)`, such as rows as a multiset, one zero, or a tolerance `floats=sv.within(...)` the plan's bound meets |
| `shim` | either of the above after the translation adds a small fix (a truncating division, a NULL placement); it costs an expression per row or a sort |
| `refused` | none of the above: the run raises `sverify.errors.RouteError` and nothing runs; for a plan that is not proved, `sverify.errors.UnverifiedRunError`, a `VerificationError` |

`route.evidence` says whether each step rests on a Lean proof (`proved`)
or on tests and probes (`tested`). Before the plan runs, its preconditions,
the inferred bounds and the assumed `SUM`s are checked on the data, and a
batch that breaks one raises `PreconditionError`.

A refusal names its reason: the options where the engine's choices differ,
with the facts that record them (the [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)
list every fact). What to do about one:

- Verify under the reference (the default), whose translation shims most
  differences, in place of an engine's profile.
- State the observation the difference hides: `rows="multiset"` for row
  order, `zeros="canon"` for the sign of a zero. A sum in another order is
  within the plan's bound, which a run accepts by default.
- Add the precondition the reference raises on, such as a bound on a
  column, so the plan never meets the difference.
- Run on the other engine, or pass `route="translated"` (or another) to see
  why that one fails.

`report.run(..., reproducible=sv.equivalent())`, like a sink's
`reproducible=`, asks for the deterministic profile, which fixes the order of
ties
([D24](core-semantics.md#d24-tie-order-belongs-to-the-deterministic-profile)):
it refuses a plan whose result is not determined up to row order, and the
reason names each window, ordered aggregate or `LIMIT` where ties stay open
(`str(report)`), with the `sv.unique(...)` that would close them
(`report.ties`).
Without it the plan runs with the engine's own order of the ties, which every
proof covers. [Example 7](examples.md#7-a-plan-checked-under-duckdbs-profile)
shows a transfer and a refusal, and D13 in
[core-semantics.md](core-semantics.md#d13-choosing-the-route) the rules
behind them.

A postcondition can name what the result's consumer observes:

```python
readings = sv.connect()
readings.put("t", pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}))
t = readings.table("t")
means = sv.verify(
    t.group_by("k").aggregate(mean_x=t.x.mean()).order_by("k"),
    requires={"t": [_.x.between(-1e6, 1e6), sv.max_rows(1_000_000)]},
    ensures=[sv.equivalent(rows="sequence", floats=sv.within(abs=1e-3)), sv.unique("k")],
)
duckdb_result = means.run(readings, "duckdb", route="auto")
polars_result = means.run(readings, "polars", route="auto")
means.equivalence.equal(duckdb_result, polars_result)  # True
```

Polars sums doubles in its own order, so its mean is within the plan's
bound of the reference's: here about `2.2e-4`, from the bounds on `x` and the
row cap (#85; `--contract`'s `epsilon`, `SubstraitLean/Epsilon.lean`). The
values may cancel, so only an absolute bound holds, and the tolerance is
absolute.

Doubles follow one model. Without `sv.equivalent` in `ensures`, rows are a
multiset, doubles are within the plan's bound and other values are exact:
the same observation as `sv.equivalent(floats="plan")`, which
`report.observation` prints with its bound, `equivalent(floats=plan, ≤
2.2e-04)` here. `sv.equivalent(...)` states each component, and one you
leave out is exact. `floats=sv.within(abs=..., rel=..., ulps=...)` states a
tolerance, and `floats="exact"` asks for the same bits. `verify` checks
either against the plan's bound on each engine; where
no engine meets it, the plan is not proved, and the report's `observes:`
line gives the plan's bound, the reason per engine and a tolerance that
would do ([example 5](examples.md#5-doubles-within-the-plans-bound)).

`sv.equivalent` also takes `elements="multiset"`, `zeros="canon"`,
`timestamps="ms"`, `strings="nfc"`, `decimals="value"` and
`errors="kind"`; `Observation.refines` orders observations component by
component. A postcondition that reads what the observation ignores, such as
`_.mean_x <= 100` under a float tolerance, is reported with
`CheckedCondition.ignores`; `sv.approx(_.mean_x <= 100)` allows for the
tolerance. The checker names the components each condition's value depends
on, from the columns it reads, and a condition that depends on none the
observation ignores holds on every result equal to a proved one up to the
observation (`Expr.robust_of_depends`,
[Robust.lean](../SubstraitLean/Robust.lean)). A comparison with a constant
narrowed by the tolerance, `x ≤ c - ε` for `x ≤ c`, keeps the original on
every such result (`Expr.narrow_sound`). A postcondition is proved on every
result the reference allows (`contract_sound_allowed`), and
`CheckedCondition.allowed` says so. Since D25 a double `SUM` or `AVG` is one
value, the exact sum rounded once, so this covers postconditions that read
it; one that reads a statistical aggregate, whose value is still a choice of
the reference, is proved of the plan's own value, and `sv.approx` allows for
the bound.

The bound grows with the row cap and the values: for a `SUM` of `n` values
of at most `M` in absolute value, about `2.2e-16 · n² · M`, and for an
`AVG` that divided by `n` (`2.2e-4` above, with `n = M = 10⁶`). Tighter
`requires` give a tighter bound ([float-bounds.md](float-bounds.md)).

### Exporting to Substrait

`report.to_substrait(format="json" | "binary")` returns a verified plan for
any conforming Substrait consumer, with the conditions under which its proof
holds ([#664](https://github.com/AlexanderNenninger/substrait-lean/issues/664)).
It is the plan the checker verified, written for Substrait 0.106:

- each call declares its YAML's URN and its compound name (`add:i64_i64`),
  and states its output type (`_substrait_extensions.json`, generated from
  the YAMLs by `python -m sverify_dev.substrait_extensions --write`);
- each option the proof depends on is pinned in the
  call's options at the reference's behaviour: `overflow`, `rounding`,
  `division_type`, `on_division_by_zero` and the rest the YAMLs list;
- a plan verified with `semantics="substrait"` goes out as it is, since its
  proof holds for every choice Substrait allows.

Where the proof uses a choice Substrait cannot state, a spec gap
([upstream ledger](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html)),
the export handles it in one of these ways:

| Gap | Handling |
|---|---|
| ST-1, ST-2, ST-5, ST-9 (overflow), ST-11, ST-12 | none needed: the reference raises there, and the preconditions, which travel with the plan, rule those inputs out (`unexercised` in the manifest) |
| ST-9 (rounding of doubles) | IEEE 754's default rounding, which `fp64` follows; recorded with evidence `tested` |
| ST-3, ST-4, ST-6 | a shim, by `shims` |
| ST-7 | none needed: the writer states every sort key's direction |
| ST-8 | none needed where no decimal `+`, `-` or `*` reduces its scale; otherwise by `shims` |
| ST-10 | refused in every mode: `upper` and `lower` of non-ASCII text |

`shims` takes three values, applied to every gap alike:

- `"apply"` (the default) rewrites the plan into well-specified Substrait,
  so that every conforming consumer gives the reference's result. A
  `variance` or `std_dev` of too few values is NULL (ST-3). An equality of
  doubles is `x + 0.0 = y + 0.0 OR (is_nan(x) AND is_nan(y))`, a double
  grouping key is the pair `(is_nan(x), x + 0.0)`, and a double sort key
  sorts by `is_nan(x)` first, so that NaN equals NaN and sorts greatest,
  and the two zeros are one (ST-4). A cast of a double to an integer
  truncates first (ST-6). A gap the plan meets where no shim applies yet,
  such as an ordering comparison of doubles, refuses the export.
- `"annotate"` keeps the plan as written and records each choice in the
  manifest as an assumption the consumer must honour (`assumptions`, class
  `assumed`).
- `"refuse"` refuses the export at any such gap.

A refusal raises `sverify.errors.ExportError`, which names the reason and
the gap. So does an unproved report, a plan verified under an engine's
profile, and a function outside Substrait's YAMLs.

`node.to_substrait()` and `transform.to_substrait()` export the report of
a node and of a transform's last call
([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
A node's plan is its last transform's: a contracted node upstream is a
table of that transform's name, and the contract's `requires` on it are
what that node guarantees. Export each node to cover a pipeline.

The contract travels in the plan's `advanced_extensions.optimization` as an
`io.sverify.substrait.v1.Contract` message
([`substrait_contract.proto`](../python/src/sverify/substrait_contract.proto)),
which a consumer that does not know it ignores. It holds the preconditions
(declared, inferred and assumed) and the postconditions, each in your terms
and as a Substrait plan of one boolean column, and a manifest
([`substrait-manifest.schema.json`](../python/src/sverify/schemas/substrait-manifest.schema.json)).
Within 1.x the message and the manifest only gain fields, and
`sv.Report.from_substrait` reads every earlier 1.x export
([stability.md](stability.md#the-substrait-contract-message)):

| Key | What it holds |
|---|---|
| `format`, `sverify`, `substrait` | the manifest's format version, sverify's version, `0.106.0` |
| `extension_urns` | the YAMLs the plan's calls come from |
| `semantics` | the semantics the plan was verified under |
| `class` | `exact`, `observed` (equal up to `equivalence`) or `assumed` (with annotated choices) |
| `evidence` | `proved`, or `tested` where IEEE 754's default rounding stands in for an option |
| `equivalence`, `equivalence_components` | what the postconditions tell apart (`sv.equivalent`) |
| `pinned` | each pinned option, its values and the calls that state it |
| `shims`, `assumptions`, `unexercised`, `up_to` | each gap and how the export handled it |
| `deterministic`, `rows`, `params`, `output` | as in the report |

`report.substrait_contract()` returns the same contract as JSON, for a
sidecar file. `sv.Report.from_substrait(exported)` reads a plan back, in either
format, and proves its contract again with the checker; the report it
returns has the same postconditions and verdict.
[Example 10](examples.md#10-a-verified-plan-for-any-substrait-consumer)
exports a plan and shows the three modes. DataFusion's Substrait consumer
runs the exports in `tests/test_substrait_export.py` and gives the
reference's results; it does not know Substrait's `variance` or
`shift_left` yet.

### ODCS contracts

The [Open Data Contract Standard](https://bitol-io.github.io/open-data-contract-standard/)
(ODCS, Bitol, Linux Foundation AI & Data) describes a dataset's contract in
YAML: its schema, quality rules, descriptions and owners. Sverify writes a
node's contract as ODCS and reads ODCS contracts as conditions
([#791](https://github.com/AlexanderNenninger/substrait-lean/issues/791)).
It writes ODCS v3.2.0 (`sverify.odcs.ODCS_VERSION`), and the tests validate
every export against that release's JSON schema
([tests/standards/](../python/tests/standards/odcs-json-schema-v3.2.0.json),
[test_odcs.py](../python/tests/test_odcs.py)). YAML needs PyYAML:
`pip install 'sverify[odcs]'`. JSON needs nothing.

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify import odcs
from sverify.io import StaticSource

shop_orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")

@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]},
    ensures=[_.amount > 10, _.amount < 1000, sv.key("id")],
)
def paid_orders(orders):
    """Paid orders over ten."""
    return orders.filter(orders.amount > 10)

odcs.write(shop_orders.pipe(paid_orders), "paid.odcs.yaml", descriptions={"id": "the order's id"})

# Another team reads the contract and builds on it.
paid_contract = odcs.read("paid.odcs.yaml")

@sv.transform(requires={"paid": paid_contract.conditions()}, ensures=[_.doubled > 20])
def doubled_paid(paid):
    return paid.select(paid.id, doubled=paid.amount * 2)

print(doubled_paid.check(paid=paid_contract.schema()).proved)
# True
```

```bash
sverify contract export pipelines/orders.py:paid --format odcs -o paid.odcs.yaml
```

The export is one schema object named after the node, with a property per
column. Each sverify term maps to its ODCS field:

| Sverify | ODCS |
|---------|------|
| a column the node proves NOT NULL | `required: true` |
| `sv.key(...)`, the first key whose columns are all NOT NULL | `primaryKey`, `primaryKeyPosition` |
| `sv.unique(col)` | `unique: true` |
| `sv.unique(a, b)` | a `duplicateValues` rule on the object, `arguments.properties`, `mustBe: 0` |
| `_.col.isin([...])` | an `invalidValues` rule, `arguments.validValues`, `mustBe: 0` |
| `sv.max_rows(n)` | a `rowCount` rule, `mustBeLessOrEqualTo: n` |
| `sv.rows_per(cols, n)` | a `sql` rule counting the keys with more than `n` rows |
| `sv.references(col, to=...)` | a `foreignKey` relationship on the property |
| any other row condition, such as a range | a `sql` rule, `SELECT COUNT(*) FROM {object} WHERE NOT COALESCE(<condition>, FALSE)`, `mustBe: 0` |
| the transform's docstring, `descriptions=` | `description` |

Every flag and rule carries a custom property `sverify` (vendor
`sverify`) with its `status`: `proved` by the checker, `checked` on the
data at every refresh (`on_unproved="check"`), or `declared` and
neither. Its `label` is the condition as the transform states it. The
document's own `sverify` property names the node, the sha256 of its plan
(as the sink's [contract record](stability.md) has it) and whether the
whole contract is proved. Sverify's conditions hold where they are TRUE, so
the SQL rules count a NULL against the condition, and a value set marks its
column `required`.

`odcs.read` takes a file, the text or a dict of ODCS 3.0 to 3.2 and gives
the conditions of each schema object (`conditions(table)`) and its columns
as an Ibis schema (`schema(table)`), for `requires` on an input or
`ensures` on a node. It reads the fields of the table above, `enum`, the
bounds in `logicalTypeOptions`, `nullValues` and `missingValues` rules,
and any `sql` rule of the form `SELECT COUNT(*) FROM {object} WHERE <rows
that break it>` that must be 0. ODCS leaves NULLs to `required`, so on a
column that may be NULL a rule on values lets NULL through. The rules it
cannot read (free text, another engine's rules, patterns, thresholds other
than 0, shares of rows, lower bounds on the row count) are listed in
`unread`, each with the reason, and `read` warns with
`odcs.UnreadRuleWarning`; `strict=True` raises instead. A round trip, ODCS
to sverify and back, keeps every rule sverify reads.

### Reproducible sinks

A stored node's sink commits each epoch once, so a rerun must give the same
result. The sink states what "the same" means (`reproducible=`, D20 in
[core-semantics.md](core-semantics.md)): `sv.equivalent()` asks for exact
bits, and `sv.equivalent(floats=sv.within(...))` accepts doubles within a
tolerance. A refresh whose engine may give another result on a rerun is
refused with a `RouteError`; so is a plan whose ties stay open, since the
sink then needs the deterministic profile (D24), and the error names the
place. Polars's streaming `SUM` of doubles may add in
another order each run, so a double sum on Polars states both: the transform's
`ensures=[sv.equivalent(floats=sv.within(abs=...))]` for the route, and the
sink's `reproducible=sv.equivalent(floats=sv.within(abs=...))` for the
rerun, each at least the plan's bound. With `x` within ±1000 and
`max_rows(1000)` that bound is about `2.2e-7`, so `abs=1e-6` passes:

```python
from sverify.io import DeltaSink

samples = StaticSource(pa.table({"k": [1, 2, 2], "x": [0.1, 0.2, 0.3]}), name="samples")


@sv.transform(
    requires={"samples": [_.x.between(-1000, 1000), sv.max_rows(1000)]},
    ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
)
def sample_sums(samples):
    return samples.group_by("k").aggregate(total=samples.x.sum())


sums = samples.pipe(sample_sums).write(
    DeltaSink("sample_sums", reproducible=sv.equivalent(floats=sv.within(abs=1e-6)))
)
print(sums.refresh(engine="polars", route="auto").nodes[0].route.kind)
# translated
```

A relative tolerance (`rel=`) fails where the values may cancel, since
only an absolute bound holds there. A result not determined up to row
order, such as a `LIMIT` over ties, is refused by every sink.

### Engine settings and versions

A profile's facts were probed under the engine's default settings, at a
pinned version (DuckDB 2.0.0, Polars 2.1.0). Before a routed run, sverify
reads the settings the plan will run under and compares them:

- DuckDB: `default_null_order`, `default_order`, `integer_division`,
  `error_on_division_by_zero`, `ieee_floating_point_ops`,
  `default_collation`, `scalar_subquery_error_on_multiple_rows`,
  `enable_optimizer` and `disabled_optimizers` refuse the run with the
  setting named (`sverify.errors.EngineSettingsError`), since a choice the
  route relies on depends on each; `preserve_insertion_order` warns
  (`EngineSettingsWarning`). `TimeZone` and `Calendar` are not checked:
  the SQL sverify writes never reads them.
- Polars: an engine affinity that forces another engine than streaming
  (`pl.Config.set_engine_affinity("in-memory")`) refuses the run, since
  sverify runs Polars's streaming engine.
- Another engine version warns (`EngineVersionWarning`), and another major
  version is refused (`EngineVersionError`) until the probes are re-run.

`lines.get_backend()`, the backend of a table of the connection, is its Ibis
DuckDB backend, for SQL of your own, such as
`lines.get_backend().raw_sql("SELECT current_setting('threads')")`. Sverify
runs plans on a cursor of its own, so a plain `SET` there leaves sverify's
runs alone, and a `SET GLOBAL` reaches them, which the check sees:

```python
from sverify.errors import EngineSettingsError

lines.get_backend().raw_sql("SET GLOBAL integer_division = true")
try:
    per_line.run(gcon, "duckdb", route="auto")
except EngineSettingsError as e:
    print(e)
# duckdb's integer_division is True, and the facts of semantics="duckdb" hold under False (duckdb-F1): ...
lines.get_backend().raw_sql("SET GLOBAL integer_division = false")
```

### Sharding and other optimizations

`sverify.engines.run_sharded(plan, shards, sharded=[...], broadcast=...)`
runs a plan on each shard of its data and combines the results, with a Lean
proof that this equals the result on all the data. Filters, projections and
joins with a broadcast table are concatenated; `COUNT`, integer `SUM`, `MIN`
and `MAX` combine in two phases; with split keys (`keys={"orders":
["region"]}`, as a partition column guarantees), aggregates grouped by the
key, co-partitioned joins and tie-free windows run per shard. `SUM` and
`AVG` of doubles split where `reproducible=` accepts doubles within a
tolerance, as a sink's `reproducible=` states it:
`sv.equivalent(floats="plan")` accepts the proved bound, and
`sv.equivalent(floats=sv.within(abs=...))` raises where a row's bound exceeds
the tolerance. `tolerance=True` returns the proved bound per row on how far
each is from the one-pass sum
([Sharded `SUM` and `AVG`](float-bounds.md#sharded-sum-and-avg-stage-5)).
Anything else raises `NotShardable` with the reason. The checker also proves
where the per-row overflow checks can go, and rewrites the transformation
with what the preconditions establish (a `DISTINCT` over a key goes, a filter
the preconditions imply goes, a left join on a NOT NULL foreign key becomes an
inner join, an unread join to a dimension goes); the report keeps both
internally, and [docs/optimizations.md](optimizations.md) describes them and
compares them with what the engines already do.

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
picks them). [`python/tests/test_plugin_example.py`](../python/tests/test_plugin_example.py)
is an example test file, and [`python/tests/test_tour.py`](../python/tests/test_tour.py)
tests the tour's transforms the same way.
