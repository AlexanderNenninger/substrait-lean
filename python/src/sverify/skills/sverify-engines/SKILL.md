---
name: sverify-engines
description: >
  Run sverify-checked transforms on DuckDB, Polars, DataFusion or Spark, or
  write their plans as DuckDB, Snowflake or Spark SQL with the same
  semantics. Use when a user wants the same result on several engines, moves
  a job between engines or to a warehouse, gets
  `sverify.engines.Unsupported` and wants to know why, needs
  `tie_free=True`, or aligns two time series with `asof_join`.
---

# sverify engines: one plan, the same answer everywhere

The same SQL text means different things on different engines: integer `/`
truncates in DataFusion and PostgreSQL but gives a double in DuckDB and
Spark; DataFusion wraps on integer overflow where DuckDB raises; NULLs sort
first or last depending on the engine; ties in a sort or window break
differently. sverify translates the plan Lean checked for each engine with
every such choice spelled out, or refuses it where an engine can't match.

## Pick the engine when you refresh

A node runs the plan Lean checked; the engine is chosen at refresh time, and
the rows are the same on each:

```python
import json

import ibis
import pyarrow as pa

import sverify as sv
from sverify.engines import ENGINES
from sverify.io import StaticSource

orders = StaticSource(pa.table({"id": [1, 2, 3], "amount": [7, -7, None]}), name="orders")


@sv.transform()
def halves(orders):
    return orders.select(orders.id, half=orders.amount // 2)


results = {}
for engine in ENGINES:  # "duckdb", and with their extras "polars" and "datafusion"
    node = halves(orders)
    node.refresh(engine=engine)
    results[engine] = node.to_arrow().to_pylist()
print(sorted(results))
# ['datafusion', 'duckdb', 'polars']
assert len({repr(r) for r in results.values()}) == 1  # the same rows everywhere
```

`refresh(engine="spark")` or a Spark session runs on Spark (the `spark`
extra, Java 17 or 21). `node.to_polars()` and `node.to_pandas()` return the
rows in those libraries.

## Write the plan as warehouse SQL

`node.plan` is the plan in Lean's written form. `sverify.engines.to_sql`
writes it as SQL whose meaning is the model's:

```python
from sverify.engines import DUCKDB, SNOWFLAKE, SPARK, Unsupported, to_sql

plan = json.loads(node.plan)
for dialect in (DUCKDB, SNOWFLAKE, SPARK):
    assert to_sql(plan, dialect).startswith("SELECT")
```

`sverify.engines.run(con, plan, engine)` runs a written plan over a
connection's tables, and `run_spark(plan, tables)` on a Spark session
configured with `SPARK_CONF`.

## Why a plan is refused

`to_sql` and the engines raise `Unsupported` (with the reason) instead of
answering differently from the model:

```python
@sv.transform()
def numbered(orders):
    w = ibis.window(group_by="id", order_by="amount")
    return orders.mutate(rn=ibis.row_number().over(w))


plan = json.loads(numbered(orders).plan)
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
  Spark sessions use `sverify.engines.SPARK_CONF` (ANSI mode, a pinned time
  zone, NTZ timestamps) and the `UTF8_BINARY` collation.

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


aligned(acc, gyr)  # on Ibis tables: checks the contract, returns an expression
assert aligned.last_report.proved
```

## More

[references/semantics.md](references/semantics.md): how each engine is made
to agree with the model (NULLs, integers, doubles, strings, time).
