# How to

One page per task. [Getting started](getting-started.md) is the on-ramp, in
ten steps; this page is for looking a task up. Its examples run in order
(`python/tests/test_readme.py`), from this setup:

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
it promises about its output (`ensures`); `refresh` runs it, here on Polars
by a route that says how the proof carries over
([Routes](how-to-engines-and-sql.md#routes-classes-and-profiles)):

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

The [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents every public function and class, for the released version (built
from `python/great-docs.yml` with `uv run poe docs`), and so do
[agent skills](https://alexandernenninger.github.io/substrait-lean/skills.html)
for coding agents that write sverify code (`npx skills add
https://alexandernenninger.github.io/substrait-lean/`, or `sverify/skills/` in
the wheel). The [tour](../README.md#the-tour)
covers each feature in notebooks 4 and 5.

## The API in brief

```python
import ibis
from sverify.io import DeltaSink, DeltaSource  # IcebergSource, IcebergSink likewise

sv.verify(
    "select id, amount from orders where amount > 0",
    tables={"orders": ibis.table({"id": "int64", "amount": "int64"}, name="orders")},
    ensures=["amount > 0"],
)  # SQL, checked; returns the report
# the checked plan as SQL: "snowflake", "duckdb" or "spark", or sverify.engines.UnsupportedError
first.to_sql("snowflake")

# p = DeltaSource("s3://.../orders").pipe(paid).write(DeltaSink("s3://.../paid"))  # stored
# r = p.pipe(revenue, regions=regions).write(DeltaSink("s3://.../revenue"))
# r.refresh(engine="polars"); sv.group(r, other).refresh(); r.to_pandas()
```

* `@sv.transform(requires=..., ensures=..., on_unproved="error" | "check" | "warn")`
  proves a contract on each call; `.report` says what was proved and
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
* Filters, projections, inner, cross, semi and anti joins, `UNION ALL`,
  `DISTINCT`, and `COUNT`, exact `SUM` and `AVG`, `MIN` and `MAX` per group
  are maintained from the changes. Another aggregate recomputes only the
  groups a batch touches, and a window only the partitions it touches;
  anything else is recomputed and diffed
  ([what refresh maintains](how-to-nodes.md#nodes-composing-storing-refreshing)).
* `sverify.io` has Delta, Iceberg and in-memory sources and sinks, and
  base classes for your own: a `Source` implements `read(since)`
  (`from_query`, `from_frame` and `from_files` build one), a `Sink`
  implements `write(change)` (`sink_from` wraps a function).
* `sverify.testing` has `assert_contract`, `assert_engines_agree` and the
  Hypothesis strategy `cases` for pytest, with the plugin's `sv_engine` and
  `sv_source` fixtures.
* `report.run(con, engine, route="auto")` runs a proved plan on an
  engine by a route (`report.routes` records it, with its class), and
  `refresh(engine=..., route="auto")` does the same for each node.
  `sv.equivalent(...)` in `ensures` names the observation, and
  `reproducible=` on a sink what a rerun must reproduce.
* `sverify.engines` has the engines, SQL dialects and plans
  (`run_sharded` runs a plan per shard and combines the results, with a
  proof that the result is the same); `sverify.errors` the exceptions.

Refused for now: correlated scalar subqueries, unbound parameters
(`sv.verify(expr, params={p: 10})` checks an `ibis.param` with its value),
`sample`, `random()` and `now()`, among the operations
[the Ibis coverage table](../README.md#ibis-coverage)
marks ✗. The repository has
[a how-to page](tasks.md), [getting started](https://alexandernenninger.github.io/substrait-lean/examples/examples.html),
the Ibis coverage table in its README, and
[what is proved and what is trusted](how-it-works.md).

## Pages

| Page | Task |
|---|---|
| [Contracts](how-to-contracts.md) | State what a transform assumes and promises, and read the report |
| [Runtime errors and guards](how-to-guards.md) | Division by zero, overflow and bad casts, and the guards that rule them out |
| [Bounds, row caps and suggested preconditions](how-to-bounds.md) | Inferred bounds, row caps, non-overlapping ranges and rows per key |
| [Checking without running, and the command line](how-to-command-line.md) | `sverify check`, its formats and exit codes, and the environment variables |
| [Nodes and composing contracts](how-to-nodes.md) | Pipe transforms into nodes, refresh them from changes, store the results |
| [Bad rows: quarantine and hold](how-to-quarantine.md) | What a refresh does with rows that break a precondition |
| [Delta Lake and Iceberg](how-to-table-formats.md) | A complete job in outline, and Delta and Iceberg sources and sinks |
| [Credentials](how-to-credentials.md) | Name the secrets a node uses |
| [OpenLineage](how-to-openlineage.md) | Emit lineage events with the contract |
| [Time buckets: bounded state](how-to-time-buckets.md) | Keep the state of a late-arriving stream bounded |
| [Engines, SQL and routes](how-to-engines-and-sql.md) | Run a proved plan on an engine, write its SQL, and read a route |
| [Exporting to Substrait and ODCS](how-to-export.md) | Hand the contract to other tools |
| [Reproducible sinks, engine settings, sharding and pytest](how-to-production.md) | Run it in production and test it |
