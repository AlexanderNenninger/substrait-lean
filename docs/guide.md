# Guide

What sverify does and how to use it, with examples that the test suite
runs. [python/README.md](../python/README.md) is the short version; how it
works inside is in [how-it-works.md](how-it-works.md).

```python
import ibis
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)
orders.apply(sv.Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))  # now orders holds bob and cy
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
   match, as for windows over a Snowflake table with ties.
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

What it doesn't do (yet). Rolling means, `MIN` over a sliding frame,
correlated scalar subqueries and parameters (`ibis.param`) are not in the
model. Incremental maintenance covers filters, projections, inner and cross
joins and `UNION ALL`; an aggregate recomputes only the groups a batch
touches, and a window only the partitions it touches. Other views (left
joins, `DISTINCT`) are recomputed and diffed instead, and `node.status()`
says so. [The Ibis coverage table](../README.md#ibis-coverage) has the full
list.

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
([`pitfalls.toml`](../catalogue/pitfalls.toml), [FINDINGS](../catalogue/FINDINGS.md)).
The most common, and what sverify does about each:

| Pitfall | What the engines do | sverify |
|---|---|---|
| Ties in `ROW_NUMBER`, `LAG`, `LIMIT`, top-N, dedup (44 of the 139 queries) | no engine promises an order among ties; Snowflake and Spark tables have no row order at all | without a key that rules ties out, nothing is proved (`deterministic=False`); Snowflake and Spark SQL is only written with a proved `tie_free=True` |
| NULL join keys | SQL engines never match them; pandas `merge` does, Polars with `nulls_equal=True` | the model's semantics, on every engine; proofs use it (`merchant` is never NULL after `a.merchant = b.merchant`) |
| Integer division | DataFusion and PostgreSQL truncate; DuckDB and Spark give a double; Snowflake a NUMBER with extra scale | truncates on every engine |
| Division by zero (14 queries) | DataFusion, Snowflake and PostgreSQL raise; DuckDB returns NULL; Polars null or inf | proved impossible, or reported as `may fail` before the job runs |
| Integer overflow | DataFusion wraps silently; DuckDB raises; Snowflake's NUMBER(38) doesn't overflow | an error at the declared width, reported as `may fail` unless a precondition rules it out; the engines raise instead of wrapping. A `SUM` that may overflow is assumed to fit (inferred) and checked on the data while the job runs |
| NaN | in SQL engines NaN equals itself and is above every number (`NaN > 30` is TRUE); in Python and pandas it compares False | one NaN, as SQL engines have it, on every engine; contracts see it (`~_.v.isnan()` is refused unless proved) |
| `NOT IN` with a NULL | standard SQL returns no rows; DataFusion gets it wrong | refused; write an anti join |
| Guards that don't guard | DataFusion evaluates both branches of some `CASE`s and merges filters, so `WHERE n <> 0 AND x / n > 1` can still fail | the runtime-error analysis only counts guards that hold: a `CASE` branch, `NULLIF`, a filter below a projection |
| NULL ordering | DataFusion, PostgreSQL and Snowflake put NULLs last ascending and first descending, DuckDB last both ways, Spark first ascending, a Polars sort first | every `ORDER BY` says where NULLs go |

Front ends change meaning too: the catalogue found Ibis rewriting TPC-H Q11's
threshold (a total over all parts) into each part's own sum, so the query
compared each part with itself, and nothing failed. [backend_semantics.py](../catalogue/backend_semantics.py) checks every such quirk
against the model, and its section 8 checks DataFusion as a backend.

## Using sverify

```bash
pip install sverify                 # or: uv add sverify
pip install 'sverify[delta,iceberg,polars,datafusion,spark]'   # or 'sverify[all]'
```

The core runs on DuckDB: contracts, incremental maintenance, and SQL for
DuckDB, Snowflake and Spark. The extras add `datafusion`, `polars`, `spark`
(needs Java 17 or 21), `delta`, `iceberg`, `flight` (`FlightSource`) and
`testing` (Hypothesis strategies). Wheels bundle the Lean checker
as a small native binary, so you need no Lean toolchain; they exist for Linux
(x86_64, aarch64) and macOS (arm64), Python 3.12 and later.

Each night, when `main` has changed, the
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly) gets its wheels, versioned
`<next minor>.dev<commits>+g<sha>`, so they sort after the latest release. They are not on PyPI:

```bash
uv add "sverify>=0.4.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
pip install --pre sverify --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
```

uv keeps the version and drops the page, so add it to your `pyproject.toml`;
`uv lock --upgrade-package sverify` then moves to the latest nightly:

```toml
[tool.uv]
find-links = ["https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly"]
```

Each build's wheels stay on the release for 30 days, so a wheel's own URL pins
one build for that long. `--find-links` sees every build on the page and picks
the newest. Copy a URL from the release page:

```bash
pip install "sverify @ https://github.com/AlexanderNenninger/substrait-lean/releases/download/nightly/sverify-<version>-py3-none-<platform>.whl"
```

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
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

expr = doubled(orders)
print(doubled.last_report)
# requires orders: (_.amount >= 0)
# requires orders: _.id.notnull()
# requires orders: (_.amount < 2**62) (inferred)
# ensures (_.doubled >= 0): proved
# ensures _.doubled.notnull(): proved
# ensures id IS NOT NULL: proved
# known about the output:
#   id: any integer
#   doubled: an integer ≥ 22
```

Lean worked out that `doubled` is at least 22: the filter keeps only
`amount > 10`, and doubling preserves that. Sverify inferred the bound that
keeps `amount * 2` within 64 bits ([Inferred bounds](#inferred-bounds)). A
postcondition that doesn't follow is refused, with what *is* known:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)

from sverify.errors import CompositionError, NotIncremental, VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# could not prove: (_.total > 5) (it may be FALSE on some rows)
# ...
#   total: an integer ≥ 1
```

* Conditions are Ibis expressions (`_.amount >= 0`) or SQL snippets
  (`"amount >= 0"`). SQL transformations are checked with
  `sv.verify(sql, tables=..., requires=..., ensures=...)`, which returns the
  report.
* `requires` maps each input to its conditions. A transformation with one
  input also takes a plain list, `requires=[_.amount >= 0]`. A key that
  names no input raises a `ValueError` that lists the inputs (#408).
* Preconditions describe data that comes from outside. On a source, they
  are checked on the data when the node is first refreshed and then on each
  batch (`PreconditionError`), or proved from the table's metadata; on Ibis
  tables bound to data (`sv.connect()`), at call time.
* Unproved postconditions raise `VerificationError`. With
  `on_unproved="runtime"` they are checked on the output data instead
  (`PostconditionError`): on bound tables at call time, on a node at every
  refresh (see [Nodes](#nodes-composing-storing-refreshing)). With
  `on_unproved="warn"` you get a warning.
* What Lean tracks per column: whether it can be NULL, integer, double
  and timestamp ranges, which booleans it can be, and whether it can be a
  string. Filters (`amount > 10`, `x IN (1, 2, 3)`, `x IS NOT NULL`) refine
  those facts; arithmetic, `CASE`, `COALESCE`, joins and `UNION ALL` carry
  them through. Schemas count: a non-nullable column is never NULL.
* Relations between columns: join and filter conditions such as
  `w1.ts = w0.ts + 60`, `a.ts = b.ts`, `t0 < t1` or `value != -9999` become
  facts about each row, so postconditions like `t1 - t0 == 60` or
  `first_txn < duplicate_txn` follow.
* Keys: `sv.unique("user_id", "ts")` says there is at most one row per
  key. In `requires` it is checked on the data; in `ensures` it is proved
  (keys survive filters, projections, aggregates and joins whose condition
  pins down the other side's key).
* Foreign keys: `sv.references("cust", to=customers.id)` in `requires`
  says every non-NULL `cust` occurs in `customers.id` (checked on the data,
  like `unique`). `to` also takes a pair of names, `("customers", "id")`. Nothing proves it in `ensures`, so it stays an assumption.
* Windows: `LAG`, `LEAD` and `ROW_NUMBER` over `PARTITION BY … ORDER BY`.
  If rows can tie in the order, the engine decides which comes first, so
  every postcondition is `undetermined` and `report.deterministic` is
  `False`; a key on the partition and order columns fixes that.
* ASOF joins: `sv.asof_join(left, right, on="ts", by="device",
  tolerance=...)` matches each row with the latest earlier row of the other
  table, built from a range join and `ROW_NUMBER` that Lean checks like any
  plan.
* Doubles and time: comparisons with constants are exact, including
  sentinels like `-9999.0`, `isnan()` and intervals; doubles compare as SQL
  engines compare them, with one zero and one NaN above every number.
* Sums and means of doubles round. Their signs are exact, and with a row cap
  in `requires`, `sv.max_rows(10_000_000)` (checked on the data), Lean
  bounds them by the proved rounding error ([float bounds](float-bounds.md)).
  `sv.approx(_.cpu_avg <= 100)` states a postcondition up to that rounding;
  the report suggests it when an exact claim misses only by rounding.
* Not tracked yet: string contents, relations beyond
  "column plus constant" (`a < 2 * b`), and counts across rows (so
  `COUNT(*) >= 1` in a group is not known).

### Runtime errors

The report lists every runtime error that may happen on some input that
meets the preconditions, and `@sv.transform` refuses the transformation
while there is one:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, infer=False)
def share(orders):
    return orders.select(orders.id, per_unit=orders.amount // (orders.amount - 30))

try:
    share(orders)
except VerificationError as e:
    print(str(e).splitlines()[0])
# could not prove: no runtime error (division by zero: (($2 - 1) / ($2 - 30))), ...
```

Without `infer=False`, sverify infers the precondition `(_.amount != 30)`
and proves `share` ([Inferred bounds](#inferred-bounds)).

Errors are what an engine fails on: integer division or remainder by zero,
`MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions that may
not compile, and `+`, `-`, `*` leaving their declared width (DataFusion
wraps around there; the reference raises). An integer `SUM` leaving 64 bits
is ruled out where the plan bounds a group's rows (a `VALUES` list, a `FETCH`
count, or a row cap `sv.max_rows(n)` on an input: [Row caps](#row-caps)) and
`requires` bounds the column. Elsewhere sverify assumes the sum fits, as it
assumes inferred bounds, and the job checks it on the data while it runs
(`Report.assumed`; an error with `infer=False`). Guards are
understood where the engine respects them: in a `CASE` branch or
`NULLIF(n, 0)`, and in a filter below a projection. A guard in the same
`AND` doesn't count.

### Inferred bounds

An overflow at the declared width is an error (#202), so `amount * 2` on a
`BIGINT` needs a bound on `amount`. Sverify infers it (#244): for each `+`,
`-`, `*` by a constant, negation, `abs` and timestamp truncation that may
leave its range, it works out the range each input column must stay in, and
adds it to `requires` as if you had written it:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.twice >= 0])
def twice(orders):
    return orders.select(orders.id, twice=orders.amount * 2)

twice(orders)
print(twice.last_report)
# requires orders: (_.amount >= 0)
# requires orders: (_.amount < 2**62) (inferred)
# ensures (_.twice >= 0): proved
# ...
```

An inferred bound is a precondition like the rest. It is checked on the
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
* `infer=False`, on `@sv.transform` and `sv.verify`, infers
  nothing: each overflow fails the proof, and its hint names the bound to
  state.

For what it does not infer, the report's `hint:` lines (`Report.hints`) name
the bound to add. An integer `SUM` gets the range Lean knows for the column it
adds up and the largest group whose sum then fits 64 bits, or a bound to add
when the column has none:

```python
samples = ibis.table({"host": "string", "ts": "timestamp", "cpu": "int64"}, name="samples")
per_minute = samples.group_by(["host", samples.ts.truncate("m").name("minute")]).aggregate(
    cpu=samples.cpu.sum()
)
print(sv.verify(per_minute))
# requires samples: (_.ts >= datetime(1, 1, 1)) (inferred)
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
postcondition again with it added. `Report.suggestions` has them as code,
per postcondition and table, for editors and language servers
([test_suggestions.py](../python/tests/test_suggestions.py)).

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
says which semantics it used (`Report.semantics`, a `semantics:` line). Until
#411 `sv.sql` defaulted to DuckDB's semantics. The lift reads a subset so far (SELECT, WHERE,
joins of every kind, subqueries and CTEs, GROUP BY with grouping sets,
windows, set operations, ORDER BY, LIMIT, CASE, CAST, and the numeric,
string, date and list functions of
[#240](https://github.com/AlexanderNenninger/substrait-lean/issues/240)) and
refuses the rest, saying what.

A node without delta rules (left join, aggregate, window, `DISTINCT`,
`LIMIT`) is recomputed and diffed instead, and `status()` says so. An
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
table, without `PARTITION BY`), from the input rows in that span widened by
the frame. This strategy is tested, not proved: Lean does not yet prove that
a window value depends only on the rows in its frame (#458), so `status()`
says "touched frames recomputed (tested, not proved)", and so does the
refresh summary. The tests
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

A node whose transform has `on_unproved="runtime"` checks the postconditions
Lean could not prove on its output at every refresh: on the full result the
first time, then on the rows each batch inserts, before its sink commits. A
violation raises `PostconditionError`, and the refresh writes nothing. The
report marks those postconditions as checked on data, and transforms
downstream may assume only the proved ones, so such a node is stored with
`.write` before another transform reads it:

```python
@sv.transform(ensures=[_.amount < 1_000], on_unproved="runtime")
def capped(orders):
    return orders.select(orders.id, orders.amount)

n = orders.pipe(capped)    # no VerificationError: checked at refresh
print(capped.last_report)
# ensures (_.amount < 1000): NOT proved: it may be FALSE or NULL on some rows, where a column
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
`"polars"`, `"datafusion"`, `"spark"` or a Spark session. The nodes keep their
state while the process runs; a stored node's table is its durable state.

A job that refreshes every minute logs `summary()`, one line per node, and
`str()` keeps the full report. A node's entry is in full when its refresh did
something notable: its first refresh, a source recomputed for want of a change
feed, a schema change, or a sink overwriting its table. A failed check raises,
and its message says which rows failed what:

```python
customers.apply(sv.Changes(inserts=[("dan", "Oslo")]))
print(c.refresh().summary())
# cities: orders@v1, customers@v1→v2, Δ trusted (change feed)
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
  per state, exactly once (keyed by the source versions).
  The proved guarantees become NOT NULL columns and CHECK constraints (Delta)
  or table properties (Iceberg), and the commit records the plan hash, the
  source versions and the contract. A job that reads the table gets its
  preconditions from them. After the first write, `DeltaSink` MERGEs each
  change in one commit, and `IcebergSink` writes it as one snapshot of
  position delete files and a data file of the new rows.
  `IcebergSink(catalog, identifier, location=..., partition_by=[("ts", "day")],
  properties={...})` creates its table at that location, partitioned and
  with those properties, which a catalog without a default location, such
  as Unity Catalog's, needs (#468).

Schema changes. A batch whose data fits the old schema (added columns,
widened types whose values still fit) is read in it, and the report names
the change. Otherwise the nodes reading the source are planned again and
recomputed, except a node with a contract, whose proof was for the old
schema: `refresh` then raises `SchemaError` and changes nothing.

Tables outside a table format, such as a small lookup table, are
`StaticSource(table, version=1, name="regions")`, so that sinks still have a
version for every input; `regions.apply(sv.Changes(...))` changes some rows,
and `regions.replace(new_table, version=2)` swaps the table, which recomputes
the nodes that read it.

Your own sources and sinks take one method each. A `sverify.io.Source`
implements `read(since)`, which returns the new rows and a cursor;
`from_query(fn, cursor_on="ts")`, `from_frame(fn)` and `from_files(path)`
build one from a function or a directory. Sverify numbers the reads as
versions, works out the change, and says in the report what the reads
assume ("rows only arrive with a greater ts"), which `refresh(audit=True)`
checks. A `sverify.io.Sink` implements `write(change)` and optionally
`committed()`, and sverify writes each state once, with its contract;
`sink_from(fn)` hands the whole table to a function. `Storage` holds object
store credentials, or a function that renews them, for every table that
needs them. [Notebook 5](../notebooks/05_pipelines_and_engines.py) of the tour walks
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
floor. `FlightLog()` is a small in-memory server that keeps such a log
(`keep=` batches per table, or `drop(table, below=n)`), the one
[the tests](../python/tests/test_io_flight.py) run against. With `schema=`, a
`FlightSource` proves contracts without asking the server, and `token=`
sends a bearer token:

```python
import pyarrow.flight as fl
from sverify.io.flight import FlightLog, FlightSource

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
`sink.maintain(vacuum=...)` does the same by hand. These commits carry the
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
        sv.arrives_within("ts", hours=2),
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

- `arrives_within("ts", hours=2)` says every row a batch inserts has `ts` at
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
- Retention needs a sink that keeps what the state drops: `DeltaSink` does
  (`Sink.keeps_retired`). With a sink that may rewrite its whole table, such
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
session or one you pass (the `spark` extra). The generated SQL assumes
the following about the warehouse:

* Snowflake: time columns are `TIMESTAMP_NTZ`, strings have no
  collation, and tables and columns have quoted lower-case names.
* Spark and Databricks: the session uses the settings of
  `sverify.engines.SPARK_CONF` (ANSI mode, a pinned time zone, NTZ
  timestamps, case-sensitive names), and strings use the default
  `UTF8_BINARY` collation.
* Both have no row order, so sorts, `LIMIT` and windows are refused unless
  you pass `tie_free=True` (justified by a report's `deterministic`), and
  so is a `SUM` or `AVG` of doubles, whose rounding depends on the order of
  the additions. Snowflake has no interval type, so interval-valued
  expressions are refused there.

How the engine translations relate to the reference semantics, and where
that is going, is in [docs/engine-profiles.md](engine-profiles.md).

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
it replaces the original on data that meets the preconditions
([Contracts](how-it-works.md#contracts) under How it works lists them).
[docs/optimizations.md](optimizations.md) compares these with what the
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
picks them). [`python/tests/test_plugin_example.py`](../python/tests/test_plugin_example.py)
is an example test file, and [`python/tests/test_tour.py`](../python/tests/test_tour.py)
tests the tour's transforms the same way.
