# sverify

**Prove a data pipeline's contracts before it runs, get the same result on
[DuckDB](https://duckdb.org), [Polars](https://pola.rs),
[DataFusion](https://datafusion.apache.org) and
[Spark](https://spark.apache.org), and keep it up to date from Delta Lake and
Iceberg change feeds.**

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
  on DuckDB, Polars or DataFusion, or is written as Spark SQL,
  with NULLs, integer division, NaN, ties and overflow spelled out, or it is
  refused where an engine can't match.
* **Results are kept up to date from the changes,** by delta plans proved
  equal to a full recompute, read from Delta's Change Data Feed or Iceberg's
  appends, and written to sinks exactly once, with the contract attached.

sverify is a young, independent project, and for now it is purely
observational: it tells you what it can and can't prove, and describes how
each engine behaves as observed at pinned versions, without certifying or
ranking them. It isn't affiliated with any engine's project or vendor. Use it
as a careful second pair of eyes rather than a gate production depends on,
and expect the API to keep changing between minor releases. What it's for is
making data engineering more joyful: fewer 3 a.m. pages, fewer surprises
between engines, more trust in the tables you hand on.

**Snowflake support is mostly aspirational for now.** sverify writes
Snowflake SQL, but has only checked it on an emulator, [fakesnow](https://github.com/tekumara/fakesnow), not on a
real account ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)).

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
documents every public function and class, for the released version. For
coding agents, the site also publishes
[skills](https://alexandernenninger.github.io/substrait-lean/skills.html) for
writing contracts, pipelines and engine code with sverify
(`npx skills add https://alexandernenninger.github.io/substrait-lean/`); they
ship in the wheel too, under `sverify/skills/`.

## In thirty lines

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import StaticSource

orders = StaticSource(  # in memory; DeltaSource and IcebergSource work the same way
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


big = orders.pipe(big_orders)  # proved here, before any data runs
big.refresh()  # computed, on DuckDB by default
orders.apply(sv.Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))
big.refresh(engine="polars")  # updated from the changes alone, on another engine
assert big.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
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


from sverify.errors import VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# could not prove: (_.total > 5) (it is TRUE or FALSE)
```

## Testing with pytest

`sverify.testing` has assertions for your test suite, and installing sverify
registers a pytest plugin with two fixtures: `sv_source` makes an in-memory
source from rows, and a test that takes `sv_engine` runs once per installed
engine.

```python
from sverify.testing import assert_contract, assert_engines_agree, source


def test_big_orders():
    orders = source([], {"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    node = orders.pipe(big_orders)
    assert_contract(node)  # the contract is proved
    data = {"orders": [(1, "ada", 30), (2, "bob", 5)]}
    assert_contract(node, data=data, expected=[(1, 60)])  # and holds on these rows
    assert_engines_agree(node, data)  # DuckDB, Polars and DataFusion agree


test_big_orders()
```

A failure lists the rows: those of the test data that break a precondition,
or the expected rows that are missing and the ones that were not expected.
`sverify.testing.cases(node)` is a Hypothesis strategy of inputs that meet
the preconditions, for property tests of the code around a node
(`pip install 'sverify[testing]'`).

## SQL models

A transform's body can be SQL, over its inputs by name. It is proved,
composed and refreshed like any other:

```python
@sv.transform(
    requires={"orders": ["amount >= 0", "amount IS NOT NULL"]},
    ensures=["total >= 0", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, coalesce(sum(amount), 0) AS total FROM orders GROUP BY customer",
        orders=orders,
    )


totals = orders.pipe(per_customer)  # proved here, like an Ibis transform
totals.refresh()
assert sorted(totals.to_arrow().to_pylist(), key=str) == [
    {"customer": "bob", "total": 5},
    {"customer": "cy", "total": 50},
]
```

Several inputs are several keywords (`sv.sql(query, orders=orders,
customers=customers)`). The SQL is planned by DataFusion
(`pip install 'sverify[datafusion]'`), or by Isthmus without it.

## Workflows

Three complete jobs from a catalogue of 139 real analytical queries, each
from source tables to a sink, with what goes wrong without the checker. Open
them in the browser:

* [Duplicate card payments](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/01_duplicate_payments.py):
  a self-join over a Delta table, refreshed from its Change Data Feed, where
  a watermark job would miss a late duplicate and keep a reversed one.
* [Sensor alerts](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/02_sensor_alerts.py):
  `LAG` over an Iceberg table, where ties and a NaN reading change the alerts,
  and Snowflake and Spark need proved tie-freedom.
* [An orders mart](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/03_orders_mart.py):
  dbt tests as a proved contract on a point-in-time join to a type-2
  dimension, in Ibis and in SQL.

The [whole tour](https://github.com/AlexanderNenninger/substrait-lean/tree/main/notebooks)
explains every feature in a chapter of its own; it runs locally with
`uvx marimo edit --sandbox notebooks` from a clone.

## The API in brief

```python
import json

import ibis
from sverify.engines import SNOWFLAKE, to_sql  # also DUCKDB, SPARK
from sverify.io import DeltaSink, DeltaSource  # IcebergSource, IcebergSink likewise

sv.verify(
    "select id, amount from orders where amount > 0",
    tables={"orders": ibis.table({"id": "int64", "amount": "int64"}, name="orders")},
    ensures=["amount > 0"],
)  # SQL, checked; returns the report
to_sql(json.loads(big.plan), SNOWFLAKE)  # the checked plan, or sverify.engines.Unsupported

# p = DeltaSource("s3://.../orders").pipe(paid).write(DeltaSink("s3://.../paid"))  # stored
# r = p.pipe(revenue, regions=regions).write(DeltaSink("s3://.../revenue"))
# r.refresh(engine="polars"); sv.group(r, other).refresh(); r.to_pandas()
```

* `@sv.transform(requires=..., ensures=..., on_unproved="error" | "runtime" | "warn")`
  proves a contract on each call; `.last_report` says what was proved and
  what is known about every output column. `sv.unique(...)` states keys.
* `source.pipe(paid).pipe(revenue, regions=regions)` builds nodes left to
  right, in the order the data flows (the call form `revenue(paid(source),
  regions=regions)` is the same node). A step is a transform, SQL
  (`sv.sql(query)`, which binds the chained node to the one table the
  keywords leave over) or a plain function. A downstream precondition is
  proved from the upstream contract (`CompositionError` names a broken
  link).
* Without `.write` in between, transforms fuse into one plan; `.write(sink)`
  stores a node, exactly once per state, and nodes downstream read it as a
  versioned source. `refresh(engine=...)` updates the whole lineage, and
  `sv.group(a, b)` several outputs against the same source versions.
* Filters, projections, inner and cross joins and `UNION ALL` are
  maintained from the changes; anything else is recomputed and diffed.
* `sverify.io` has Delta, Iceberg and in-memory sources and sinks, and
  base classes for your own: a `Source` implements `read(since)`
  (`from_query`, `from_frame` and `from_files` build one), a `Sink`
  implements `write(change)` (`sink_from` wraps a function).
* `sverify.testing` has `assert_contract`, `assert_engines_agree` and the
  Hypothesis strategy `cases` for pytest, with the plugin's `sv_engine` and
  `sv_source` fixtures.
* `sverify.engines` has the engines, SQL dialects and plans
  (`run_sharded` runs a plan per shard and combines the results, with a
  proof that the result is the same); `sverify.errors` the exceptions.

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

## License

sverify is licensed under the [Mozilla Public License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/src/sverify/ibis_substrait/LICENSE).
