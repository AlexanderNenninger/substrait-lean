# Upgrading from 0.8 to 0.9

This page gives each breaking change of 0.9.0 a migration note: what to write
instead, with an example. [The changelog](../CHANGELOG.md)'s 0.9.0 section
lists the changes, and [stability.md](stability.md#the-python-api) states
the rule each break follows. The last section names the engine fact or
upstream record behind each soundness fix of 0.9.0.

0.9.0 keeps no deprecated alias. An old spelling raises; a renamed name of a
public module, a removed flag, `sv.sql(as_=)`, `SVERIFY_PREBUILT_CHECK` and a
sink's `_keeps_retired` say what replaced them, and
[`tests/test_breaking_0_9.py`](../python/tests/test_breaking_0_9.py) runs
each old spelling.

## Install

Each engine is an extra of its own, and `pip install sverify` installs none.

```bash
pip install 'sverify[duckdb]'
```

Use `sverify[polars]`, `sverify[spark]` or `sverify[all]` for the others.
`sv.verify`, the SQL dialects and `report.to_sql` need no engine.

## Python names

### `Report.verdict` replaces `Report.proved`

`bool(report.verdict)` raises `TypeError`, so compare with the verdict you
expect.

```python
# 0.8
assert report.proved
# 0.9
assert report.verdict == sv.Verdict.PROVED
# either proved value, as the old `proved` read
assert report.verdict in (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS)
```

### A custom sink sets `keeps_retired`

0.8's custom sinks set `_keeps_retired`. 0.9 reads the class attribute
`keeps_retired` alone, and refuses a sink class that sets the old one.

```python
# 0.8
class ParquetSink(Sink):
    _keeps_retired = True
# 0.9
class ParquetSink(Sink):
    keeps_retired = True
```

### `semantics="portable"`

The semantics every engine reaches is `"portable"`, and `"reference"` is
refused.

```python
# 0.8
sv.verify(expr, semantics="reference")
# 0.9
sv.verify(expr, semantics="portable")  # the default
```

### The deprecated aliases

Each row of "Breaking: deprecated aliases are removed" in the changelog,
old form first:

```python
from sverify.io import Changes                     # was sverify.Changes
report = sv.Report.from_substrait(data)            # was sv.from_substrait(data)
from sverify.testing import FlightLog              # was sverify.io.FlightLog
sink.contract()                                    # was sink.committed()
delta_sink.maintain(vacuum_retention="7d")         # was maintain(vacuum="7d")
iceberg_sink.maintain(snapshot_retention="7d")     # was maintain(expire="7d")
FlightSource(uri, "orders", credentials="flight")  # was FlightSource(..., token=...)
run_sharded(plan, reproducible=sv.equivalent(floats="plan"))  # was float_order="any"
sv.sql(query, name="orders")                       # was sv.sql(query, as_="orders")
sv.arrives_within("ts", timedelta(hours=1))        # was arrives_within("ts", hours=1)
sv.rows_per("a", "b", at_most=3)                   # was rows_per(["a", "b"], 3)
```

`IcebergSink.create_options_ignored`, `Sink.view` and `SinkChange.native`
were internal and have no replacement. For the environment variable:

```bash
export SVERIFY_PREBUILT_CHECKER=path/to/substrait-check  # was SVERIFY_PREBUILT_CHECK
```

### `References` has `cols`, `table` and `others`

A foreign key takes several columns, so its fields are tuples.

```python
fk = sv.references("customer_id", to=customers.id)
# 0.8
fk.col, fk.other
# 0.9
fk.cols, fk.table, fk.others  # ("customer_id",), "customers", ("id",)
```

Export a report again where it was exported before 0.9.0, so that it reads
back.

### Checks on data run the proved plan

A check of `requires`, of `on_unproved="check"` and of `Report.check_inputs`
runs the plan the checker wrote, on the engine of the table's connection. A
condition outside the model raises `UnsupportedError` with the reason; write
it in the subset `verify` reads, which `sv.verify` of the same condition
tells you.

`sv.connect()`'s DuckDB runs at the time zone UTC. Name the zone where raw
SQL turns a `TIMESTAMPTZ` into text or a calendar value:

```sql
-- 0.8: the host's zone
SELECT CAST(ordered_at AS DATE) FROM orders
-- 0.9: the zone you mean
SELECT CAST(timezone('Europe/Berlin', ordered_at) AS DATE) FROM orders
```

### `BatchRefresh` and `SinkChange`

```python
# 0.8
from sverify.types import RefreshReport
SinkChange(view, contract, schema, change)
# 0.9
from sverify.types import BatchRefresh
SinkChange(view=view, contract=contract, schema=schema, change=change)
```

### `Report.from_substrait`

```python
# 0.8
from sverify.substrait_export import recheck
report = recheck(data)
# 0.9
report = sv.Report.from_substrait(data)
```

### One name for each concept

Every rename of "One name for each concept in the public API" in the
changelog, as a job meets it:

```python
from sverify.types import Lenses, Postcondition  # Observation, CheckedCondition
from sverify.errors import SQLError              # SqlError
from sverify.odcs import ODCSContract            # OdcsContract

issue.suggested_requires                         # issue.hint_needs
route.taken, route.why                           # route.kind, route.reason
route.engine_facts, route.theorem_facts          # route.facts, route.proved_facts
route.probed_version                             # route.version
contract.semantics, stored.semantics             # .profile
stored.location, stored.location_key             # stored.where, stored.where_key
write.inserts, write.deletes                     # write.inserted, write.deleted
batch.assumes, batch.mode                        # batch.trusted, batch.kind
SourceBatch.from_changes(0, 1, inserts=rows, assumes="the log")  # trusted=
SourceBatch.from_snapshot(0, 1, table, why="first read")             # reason=
retention.node                                   # retention.view
FlightSource(uri, "orders", credentials="flight")  # secret=
unread.why                                       # unread.reason
upstream.why, upstream.assertions                # .why_unverified, .evidence
sverify.engines.run(con, node.internal_plan)     # run(con, plan_json)
```

A job that reads the JSON reads the new keys: a route's `taken`, `why`,
`engine_facts`, `probed_version` and `theorem_facts`, and a write's
`inserts` and `deletes`. `Report.from_json` and `Contract.from_json` read the
earlier formats.

### `sverify.contracts`

Import public names from `sverify` and `sverify.types`.

```python
# 0.8
from sverify.contracts import unique, Report, Unique
# 0.9
import sverify as sv
from sverify.types import Unique
sv.unique("id"), sv.Report
```

### `RefreshReport.diffed` is a dict

`BatchRefresh.diffed` maps each view recomputed and diffed to why.

```python
# 0.8
for view in batch.diffed: print(view)
batch.diffed[0]
# 0.9
for view, why in batch.diffed.items(): print(view, why)
next(iter(batch.diffed))
```

### `Report.needs`, and keyword-only results

```python
# 0.8
report.needed_text
Batch(rows, n)
# 0.9
[n.text for n in report.needs]
Batch(table=rows, cursor=n)
```

`Report`, `Contract`, `Batch`, `Snapshot`, `SourceBatch` and `SinkWrite` take
keywords only.

### One verb for proving, and the plan layer

```python
# 0.8
report = orders_by_day.check(orders=schema)
@sv.transform(on_unproved="runtime")
from sverify.engines import to_sql
# 0.9
report = orders_by_day.verify(orders=schema)
@sv.transform(on_unproved="check")
from sverify.engines.plan import to_sql
```

`sverify.engines.create_table` and `table_rows` are `con.create` and
`con.rows`.

## Command line

### Exit codes run from the best to the worst

A script that tests a code reads `sverify.cli.ExitCode`, whose members keep
their names.

| Outcome | 0.8.0 | 0.9.0 |
|---|---|---|
| refused: no route to the engine | 3 | 4 |
| budget exceeded | 4 | 5 |
| quarantined | 5 | 6 |
| held | 5 | 7 |
| error | 6 | 8 |

```bash
# 0.8
sverify refresh pipeline.py:orders || [ $? -eq 5 ]   # quarantined is fine
# 0.9
sverify refresh pipeline.py:orders || [ $? -eq 6 ]
```

```python
from sverify.cli import ExitCode
if code == ExitCode.QUARANTINED: ...
worst = max(codes)  # the worst of several runs
```

### `check --require-proved`

A node whose postconditions are only checked on the data exits 1 under
`--require-proved`. Drop the flag where such a node is accepted, or state
what the proof needs:

```bash
sverify check pipeline.py --require-proved
```

### `--format`

`--output-format` and `--json` are removed, and the error says what to write.

```bash
# 0.8
sverify check pipeline.py --output-format sarif
sverify check pipeline.py --json
# 0.9
sverify check pipeline.py --format sarif
sverify check pipeline.py --format json
```

`sverify contract export` writes ODCS alone, so drop its `--format odcs`.

## Defaults that changed

### The default lenses read one zero and a multiset of elements

Name the lens to keep observing what 0.8 observed.

```python
# 0.9: -0.0 equals 0.0, and a list's elements are a multiset
@sv.transform(ensures=[sv.unique("id")])
# 0.8's reading
@sv.transform(ensures=[sv.unique("id"), sv.equivalent(zeros="exact", elements="sequence")])
```

### An integer cast of a double in DuckDB SQL

Under `semantics="portable"`, DuckDB SQL's integer cast of a double is
refused, since DuckDB rounds it. Say which rounding you mean:

```sql
-- 0.8
SELECT CAST(price AS BIGINT) FROM orders
-- 0.9
SELECT CAST(round(price) AS BIGINT) FROM orders  -- or floor(price), ceil(price)
```

## sverify-dbt

```python
# 0.8
doc["models"]; result.proved; test.status == "not proved"
# 0.9
doc["items"]; result.proved_tests; test.status == "not_proved"
```

`sverify_dbt.Needed` is `NeededTest`, `because` is `why` on it and on
`Suggestion`, and its result types take keywords.

```bash
# 0.8
sverify-dbt check . --output-format json
# 0.9
sverify-dbt check . --format json
```

## Soundness fixes and their evidence

Each soundness fix of 0.9.0 that refuses or changes a proof, with the engine
fact or upstream record that holds its evidence. Facts are under
[`engines/<engine>/facts/`](../engines/), upstream records under
[`upstream/bugs/`](../upstream/bugs/).

| Changelog entry (0.9.0) | Evidence |
|---|---|
| An Ibis table with a DuckDB ENUM column is refused (#1253) | `duckdb-enum-order` |
| DuckDB UUID, ENUM, BIT and BIGNUM columns are refused with their exit | `duckdb-enum-order`, `duckdb-uuid-text-order`, `duckdb-uuid-string-cast` |
| Breaking for raw SQL: an integer cast of a double under the default semantics (D54) | `duckdb-R9` |
| A FLOAT cast to an integer in DuckDB SQL is refused (#2152) | `duckdb-R9` |
| SQL lift: `MEDIAN` of a date, timestamp or FLOAT is refused (#2153) | `duckdb-quantile-cont-interpolation` |
| A cast to a type that holds a struct is refused (#2376) | `duckdb-struct-cast-by-name`, `polars-struct-cast-by-name`, `spark-struct-cast-by-position` |
| Polars refuses a variance beside a list in one grouping (#2507) | `polars-var-std-streaming` |
| Polars raises where its variance of finite values is NaN (#1486) | `polars-var-bound`, `polars-var-std-streaming` |
| DuckDB's integer mean depends on the plan's shape and the platform (#1608) | `duckdb-avg-int` |
| A decision on DuckDB's integer `AVG` is refused where DuckDB may take it the other way (#1735) | `duckdb-avg-int` |
| Fixed: Spark's IEEE division by `-0.0` | `spark-double-divide` |
| Fixed: a rounded, cast or compared double that an engine computes within a bound (#1849) | `polars-double-scalar-divisor` |
| QUANTILE_CONT of infinities reads nan_creation (#1475) | `duckdb-quantile-cont-interpolation`, `polars-quantile`, `spark-quantile` |
| `signbit` at zero, and black-box refusals in a long-lived checker (#2154) | `duckdb-signbit` |
| Polars runs no Python: five operations refused | `polars-ulp-libm` |
| Decimal `+` and `-` raise where DuckDB's operand cast does | `duckdb-decimal-addsub-operand-cast` |
| Spark refuses a decimal comparison it would round | `spark-decimal-compare-scale` |
| An integer literal next to a TINYINT or SMALLINT column has the column's type | `duckdb-coerce-int-literal-width` |
| float32 columns, interval casts, and unread columns under SQL conditions | `duckdb-coerce-real` |
| A double→integer cast in `to_substrait` carries ST-6's shim or assumption | `ST-6` |
| A cast of a double to a decimal, and a decimal cast to a smaller scale, in `to_substrait` | `ST-8` |
| A `MIN` or `MAX` of doubles in `to_substrait` is no longer reported as shimmed | `ST-4` |
| Spark names a parser refusal | `spark-exec-parser-depth` |
| Spark's refusal of a time of day names the setting | `spark-time-type` |

These fixes rest on sverify's own reading of a plan, so no engine fact or
upstream record applies:

| Changelog entry (0.9.0) | What was wrong |
|---|---|
| A `VALUES` row that raises or misses its type is refused (#1491) | the parser folded computed rows |
| Refused: a sample of a series, and a percent limit (#321) | the SQL lift read a percent limit as a row count |
| The SQL lift refuses what DuckDB refuses for `if` and `iff` (#328) | the lift read a two-argument `if` that DuckDB's binder refuses |
| `power` is strict in a NULL base (D71) | the parser folded `power(x, 0)` to 1 |
| A postcondition that reads an unbounded double is refused with its exit (#1045) | a route ran what it refused with a row cap |
| Substrait export: a set relation whose inputs differ in type is refused | the export wrote what Substrait does not allow |
| Checks on data run the proved plan by default (F219) | Ibis read a condition as its backend does |
