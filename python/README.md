# sverify

**Prove a data pipeline's contracts before it runs, get the same result on
[DuckDB](https://duckdb.org), [Polars](https://pola.rs),
[DataFusion](https://datafusion.apache.org), [Spark](https://spark.apache.org)
and Snowflake, and keep it up to date from Delta Lake and Iceberg change
feeds.**

You write a transformation in [Ibis](https://ibis-project.org) or SQL and say
what it assumes about its inputs (`requires`) and what it guarantees about
its output (`ensures`). A checker written in [Lean](https://lean-lang.org)
proves the guarantees for every possible input, or says why it can't. Then:

* **Contracts are proved, not tested.** `not_null`, `unique`, ranges and
  relations between columns hold on every input that meets the
  preconditions, and division by zero, overflow and bad casts are ruled out
  before the job runs. Preconditions are checked on the data, or proved from
  Delta and Iceberg metadata.
* **One plan gives the same answer on every engine.** The checked plan runs
  on DuckDB, Polars or DataFusion, or is written as Snowflake or Spark SQL,
  with NULLs, integer division, NaN, ties and overflow spelled out, or it is
  refused where an engine can't match.
* **Results are kept up to date from the changes,** by delta plans proved
  equal to a full recompute, read from Delta's Change Data Feed or Iceberg's
  appends, and written to sinks exactly once, with the contract attached.

```bash
pip install sverify                # or: uv add sverify
pip install 'sverify[all]'         # with every engine and table format
```

The core runs on DuckDB and writes DuckDB, Snowflake and Spark SQL. Extras:
`datafusion` (also compiles SQL strings), `polars`, `spark` (needs Java 17 or
21), `delta`, `iceberg`, or `all`. Wheels bundle the checker as a small
native binary, for Linux (x86_64, aarch64) and macOS (arm64, x86_64), Python
3.12 and later; elsewhere pip builds from the sdist, which needs
[elan](https://github.com/leanprover/elan).

The [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents every public function and class, for the released version.

## In thirty lines

```python
import ibis
import sverify as sv
from ibis import _

con = sv.connect()  # in-memory tables; plans run on DuckDB by default
sv.create_table(
    con,
    "orders",
    ibis.schema({"id": "int64", "customer": "string", "amount": "int64"}),
    [(1, "ada", 30), (2, "bob", 5)],
)
orders = con.table("orders")


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


view = sv.IncrementalView(con, big_orders(orders), "big_orders")  # proved, then computed
view.apply({"orders": sv.Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)])})
assert view.rows() == [(3, 100)] == view.recompute()
print(big_orders.last_report)
# requires orders: (_.amount >= 0)
# requires orders: unique(id)
# ensures (_.doubled >= 22): proved
```

A postcondition that doesn't follow is refused before anything runs:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)


try:
    plus_one(orders)
except sv.VerificationError as e:
    print(e)
# could not prove: (_.total > 5) (it is TRUE or FALSE)
```

## Workflows

Three complete jobs from a catalogue of 139 real analytical queries, each
from source tables to a sink, with what goes wrong without the checker. Open
them in the browser:

* [Duplicate card payments](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/main/notebooks/01_duplicate_payments.py):
  a self-join over a Delta table, refreshed from its Change Data Feed, where
  a watermark job would miss a late duplicate and keep a reversed one.
* [Sensor alerts](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/main/notebooks/02_sensor_alerts.py):
  `LAG` over an Iceberg table, where ties and a NaN reading change the alerts,
  and Snowflake and Spark need proved tie-freedom.
* [An orders mart](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/main/notebooks/03_orders_mart.py):
  dbt tests as a proved contract on a point-in-time join to a type-2
  dimension, in Ibis and in SQL.

The [whole tour](https://github.com/AlexanderNenninger/substrait-lean/tree/main/notebooks)
explains every feature in a chapter of its own; it runs locally with
`uvx marimo edit --sandbox notebooks` from a clone.

## The API in brief

```python
from sverify.io import DeltaSink, DeltaSource  # IcebergSource, IcebergSink likewise
from sverify.sql import to_sql
from sverify.sql.snowflake import SNOWFLAKE  # also sverify.sql.duckdb, sverify.sql.spark
import json

sv.verify(
    "select id, amount from orders where amount > 0",
    tables={"orders": orders},
    ensures=["amount > 0"],
)  # SQL, checked; returns the report
sv.run_plan(con, view.plan, "polars")  # the checked plan on another engine
to_sql(json.loads(view.plan), SNOWFLAKE)  # or sverify.sql.Unsupported, saying why

pipe = sv.Pipeline(sv.connect())  # views over views; sources with versions
# big = pipe.view("big", big_orders(pipe.source("orders", DeltaSource("s3://.../orders"))))
# DeltaSink("s3://.../big", big).write(); pipe.refresh(); ...
```

* `@sv.transform(requires=..., ensures=..., on_unproved="error" | "runtime" | "warn")`
  proves a contract on each call; `.last_report` says what was proved and
  what is known about every output column. `sv.unique(...)` states keys.
* Contracted steps compose: a downstream precondition is proved from the
  upstream contract (`CompositionError` names a broken link).
* `sv.IncrementalView` maintains filters, projections, inner and cross joins
  and `UNION ALL`, and refuses anything else up front (`NotIncremental`); in
  a `sv.Pipeline` other views are recomputed and diffed instead.
* `sverify.partition.run_sharded` runs a plan per shard and combines the
  results, with a proof that the result is the same.

**Not supported yet:** DECIMAL columns (keep money as integer cents),
framed window aggregates, `RANK` and `NTILE`. The repository's README has
the coverage table, the full guide, and what is proved and what is trusted.

## Configuration

* `SVERIFY_CHECK`: path to a `substrait-check` binary to use instead of the
  bundled one, for example your own `lake build`.
* `SVERIFY_ISTHMUS`: path to an [Isthmus](https://github.com/substrait-io/substrait-java/releases)
  binary (otherwise `isthmus` on `PATH`), to compile SQL strings without
  DataFusion; `sv.connect(sql_producer="isthmus")` picks it, and it is the
  default when DataFusion is not installed. sverify doesn't ship it (~120 MB);
  `scripts/fetch_isthmus.sh <dir>` downloads the pinned release.
* DataFusion is pinned to 51, because Ibis 12's DataFusion backend doesn't
  connect to later versions.

## Development

```bash
git clone https://github.com/AlexanderNenninger/substrait-lean
cd substrait-lean/python
uv sync                          # builds substrait-check with lake (needs elan) and links it in
uv run poe qa                    # proofs, lint, typecheck, golden, Python tests, notebooks
```

See the [repository](https://github.com/AlexanderNenninger/substrait-lean) for setup details.
