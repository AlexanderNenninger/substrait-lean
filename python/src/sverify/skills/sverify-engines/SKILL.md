---
name: sverify-engines
description: >
  Run a sverify-checked query plan on DuckDB, Polars or DataFusion, or write
  it as DuckDB, Snowflake or Spark SQL with the same semantics. Use when a
  user wants the same result on several engines, moves a pipeline between
  engines or to a warehouse, gets `sverify.sql.Unsupported` and wants to know
  why, needs `tie_free=True`, or aligns two time series with `asof_join`.
---

# sverify engines: one plan, the same answer everywhere

The same SQL text means different things on different engines: integer `/`
truncates in DataFusion and PostgreSQL but gives a double in DuckDB and
Spark; DataFusion wraps on integer overflow where DuckDB raises; NULLs sort
first or last depending on the engine; ties in a sort or window break
differently. sverify translates the plan Lean checked for each engine with
every such choice spelled out, or refuses it where an engine can't match.

## Run a checked plan on each engine

`view.plan` (or `sv.written_plan(sv.substrait_json(con, sql))`) is the plan
in Lean's written form. `sv.run_plan` runs it over the connection's tables:

```python
import json

import ibis
import sverify as sv

con = sv.connect()  # plans run on DuckDB by default; sv.connect(engine="polars") etc.
sv.create_table(
    con, "orders", ibis.schema({"id": "int64", "amount": "int64"}), [(1, 7), (2, -7), (3, None)]
)
orders = con.table("orders")
view = sv.IncrementalView(con, orders.select(orders.id, half=orders.amount // 2), "halves")

results = {e: sv.run_plan(con, view.plan, e).to_pylist() for e in sv.ENGINES}
print(sorted(results))
# ['datafusion', 'duckdb', 'polars']
assert len({repr(r) for r in results.values()}) == 1  # the same rows everywhere
```

`sv.ENGINES` lists the engines installed with their extras (`polars`,
`datafusion`). `engine=` on `sv.connect`, a view or `@sv.transform` picks
where plans and checks on data run.

## Write it as warehouse SQL

```python
from sverify.sql import Unsupported, to_sql
from sverify.sql.duckdb import DUCKDB
from sverify.sql.snowflake import SNOWFLAKE
from sverify.sql.spark import SPARK

plan = json.loads(view.plan)
for dialect in (DUCKDB, SNOWFLAKE, SPARK):
    assert to_sql(plan, dialect).startswith("SELECT")
```

`sverify.spark_engine.run(plan, tables)` runs the Spark SQL on a local
session or one you pass (the `spark` extra, Java 17 or 21).

## Why a plan is refused

`to_sql` and `run_plan` raise `Unsupported` (with the reason) instead of
answering differently from the model:

```python
plan = json.loads(
    sv.written_plan(
        sv.substrait_json(
            con, "select id, row_number() over (partition by id order by amount) as rn from orders"
        )
    )
)
try:
    to_sql(plan, SNOWFLAKE)
except Unsupported as e:
    print(str(e).split(",")[0])
# Snowflake tables have no row order
print(to_sql(plan, SNOWFLAKE, tie_free=True)[:6])
# SELECT
```

* **Snowflake and Spark tables have no row order**, so sorts, `LIMIT` and
  windows are refused unless you pass `tie_free=True`, and so is `SUM` or
  `AVG` of doubles (the rounding depends on the order of additions). Pass
  `tie_free=True` only when a contract report says `deterministic` (a key on
  the partition and order columns rules out ties).
* **Snowflake has no interval type**: interval-valued expressions are refused.
* **Warehouse setup the SQL assumes:** Snowflake time columns are
  `TIMESTAMP_NTZ`, strings have no collation, names are quoted lower case;
  Spark sessions use `sverify.spark_engine.SPARK_CONF` (ANSI mode, a pinned
  time zone, NTZ timestamps) and the `UTF8_BINARY` collation.

## Align two time series: `asof_join`

`sv.asof_join(left, right, on="ts", by="device", tolerance=...)` matches each
left row with the latest right row at or before it, at most `tolerance`
earlier, built from a range join and `ROW_NUMBER` that Lean checks like any
plan. The right side needs a key on `(by, on)`, or the result is
undetermined:

```python
from ibis import _

acc = ibis.table({"device": "!int64", "ts": "!timestamp", "ax": "float64"}, name="acc")
gyr = ibis.table({"device": "!int64", "ts": "!timestamp", "gx": "float64"}, name="gyr")


@sv.transform(
    requires={"acc": [sv.unique("device", "ts")], "gyr": [sv.unique("device", "ts")]},
    ensures=[sv.unique("device", "ts"), _.ts_right.isnull() | (_.ts_right <= _.ts)],
)
def aligned(acc, gyr):
    return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=ibis.interval(milliseconds=10))


aligned(acc, gyr)
assert aligned.last_report.proved
```

## More

[references/semantics.md](references/semantics.md): how each engine is made
to agree with the model (NULLs, integers, doubles, strings, time).
