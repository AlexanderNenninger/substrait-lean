# Changelog

## Unreleased

### Nodes compose left to right with `.pipe`

A job now reads in the order its data flows
([#189](https://github.com/AlexanderNenninger/substrait-lean/issues/189)).
It adds to the API and changes nothing that exists.

```python
paid_orders = orders.pipe(paid).write(DeltaSink("lake/paid"))     # chain, then store
enriched = paid_orders.pipe(enrich, customers=customers)          # fan-in by keyword
regional = paid_orders.pipe(
    sv.sql("SELECT o.*, c.region FROM orders o JOIN customers c ON c.cid = o.cid"),
    customers=customers,
)                                                                 # SQL is a step
quick = orders.pipe(lambda t: t.filter(_.amount > 0))             # no contract
sv.group(paid_orders.pipe(daily_totals), enriched).refresh()      # fan-out
```

- `Node.pipe(step, /, **inputs)`, and `pipe` on every source in
  `sverify.io`, apply a step to the node: the chained node fills the step's
  first table parameter, and the other inputs come by keyword. It builds the
  same node and plan as the call form `paid(orders)`, which stays public.
  A missing, duplicate or unknown input raises `TypeError` naming the step's
  parameters.
- A step is a contracted transform, a plain function from Ibis tables to an
  Ibis table (a transform with no contract), or `sv.sql(query)`.
- `sv.sql(query, *, as_=None)` without tables is a step whose inputs are the
  tables the query reads (not its CTEs, and each once). The keyword inputs
  bind their own names, and the chained node binds to the one table left
  over. A table with no input, an unused chained node, a keyword the query
  doesn't read, or an `as_` that isn't the table left over raises
  `TypeError`. `sv.sql(query, orders=orders)` inside a transform is
  unchanged.
- The README, the tour and the API reference lead with `.pipe`.

## 0.2.0 (2026-11-01)

A new public API, built around transforms that compose
([#164](https://github.com/AlexanderNenninger/substrait-lean/issues/164)).
It is a clean break: the old names are gone, with no deprecated aliases. The
proofs, the Lean model and what each engine computes are unchanged.

### Transforms compose; there is no pipeline object

```python
import sverify as sv
from sverify.io import DeltaSink, DeltaSource

orders = DeltaSource("s3://lake/orders")
p = paid(orders).write(DeltaSink("s3://lake/paid"))      # stored, and a source downstream
r = revenue(p).write(DeltaSink("s3://lake/revenue"))

r.refresh()                    # DuckDB in memory by default
r.refresh(engine="polars")     # or "datafusion", "spark", a Spark session
r.to_arrow(); r.to_polars(); r.to_pandas(); r.table
```

- A contracted transform (`@sv.transform`) called on a source or a node
  builds a `Node`. The contract is checked when the node is built: a link
  whose upstream guarantees don't imply the downstream assumptions raises
  `CompositionError` at once. Called on Ibis tables, a transform still
  returns an Ibis expression.
- Without a `.write` between transforms, they fuse into one plan and one
  incremental view, and the intermediate rows are never stored.
- `.write(sink)` stores a node, in the middle of a job or at its end, exactly
  once per state. It returns a node that downstream transforms read as a
  versioned source (Delta's Change Data Feed, Iceberg's snapshots), building
  on the contract its own stage proved.
- `refresh()` on any node brings its whole lineage up to date, upstream
  first, refreshing every node once per call and writing every stored node
  once. A restarted job rebuilds the same nodes; the first refresh resumes
  each stored node from its table.
- The engine is chosen at refresh time, not when the job is built.
  `"spark"` and Spark sessions are new as engines for maintained results.
- `sv.group(a, b).refresh()` refreshes several outputs against the same
  source versions and shares the stored nodes they read; `.status()` reports
  on each.
- `node.plan` is the plan Lean checked, for `sverify.engines`.

### SQL models

A transform's body can be SQL over its inputs, by keyword name:

```python
@sv.transform(requires={"orders": ["amount_cents >= 0"]}, ensures=["revenue_cents >= 0"])
def revenue(orders):
    return sv.sql("""
        SELECT region, coalesce(sum(amount_cents), 0) AS revenue_cents
        FROM orders GROUP BY region
    """, orders=orders)
```

`sv.sql(query, **tables)` returns an Ibis table, so a SQL model is an
ordinary node. It fuses with its neighbours, can be stored with `.write`,
composes with Ibis transforms on either side and reads several inputs. Its
schema and plan come from DataFusion's SQL producer, or Isthmus's without
DataFusion, and work on the placeholder tables nodes are built from. A query
the producer can't plan, or a plan Lean refuses, raises `Unsupported` saying
which part; without either producer the error names the `datafusion` extra.

### A small namespace

`import sverify as sv` holds eleven names: `transform`, `sql`, `verify`,
`unique`, `references`, `Report`, `Changes`, `group`, `connect`, `asof_join`
and `Node`. Three submodules hold the rest:

- `sverify.io`: `DeltaSource`, `DeltaSink`, `IcebergSource`, `IcebergSink`,
  `SinkWrite`, `Contract`, `StaticSource`.
- `sverify.engines`: running plans, SQL dialects and plan tools.
- `sverify.errors`: the exceptions.

Every other module (`sverify.incremental`, `sverify.contracts`,
`sverify.engine`, `sverify.sql`, `sverify.partition`, the per-engine modules,
`sverify.ibis_substrait`, `sverify.catalogue`, `sverify.coverage`,
`sverify.fuzz`, `sverify.testing`, `sverify.counterexample`,
`sverify.display`, `sverify.examples`, `sverify.io.delta`,
`sverify.io.iceberg`) is internal and may change in any release.

### Other changes

- Sinks no longer take a view: `DeltaSink(uri)`, `IcebergSink(catalog,
  identifier)`, attached by `node.write(sink)`. There is no public
  `sink.write()`: refresh writes. Delta and Iceberg sinks report through one
  type, `SinkWrite` (it replaces `IcebergWrite`).
- Sources and sinks take `name=`, the table's name in the plans that read
  them. It defaults to the last part of the URI or identifier.
- `StaticSource.apply(sv.Changes(...))` changes some rows of an in-memory
  source; the next refresh gets exactly that change, where `replace` makes
  it diff the whole table. `StaticSource` takes `name=`.
- A node without delta rules (left join, aggregate, window, `DISTINCT`,
  `LIMIT`) is recomputed and diffed, as views were inside a `Pipeline`. The
  standalone `IncrementalView`'s refusal (`NotIncremental`) is no longer on
  the public path.
- Incremental views over SQL strings become transforms whose body is
  `sv.sql(...)`.
### Fixes

- Arithmetic on double literals (`3.0 / 2.0`, a `CASE` of double literals
  plus `1.0`) used the integer operators on the literals' codes, which gave
  false proofs; the parser now reads a double literal, a cast to a double or
  such a `CASE` as a double
  ([#97](https://github.com/AlexanderNenninger/substrait-lean/issues/97),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- Booleans are ordered FALSE < TRUE, as DataFusion orders them; `b < TRUE`
  was NULL in the model
  ([#154](https://github.com/AlexanderNenninger/substrait-lean/issues/154),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- A bare double literal (`SELECT 1.5 AS c`) is written as an `fp64` literal,
  not as an integer holding its code, and `substrait-check` prints such a
  column as doubles. `0.0` and `CAST(NULL AS DOUBLE)` still come out with an
  integer column type (part of
  [#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96),
  [#166](https://github.com/AlexanderNenninger/substrait-lean/pull/166)).
- A `DeltaSink` refused its second write when a guarantee had parentheses
  that Delta drops when it stores a CHECK constraint
  (`(x IS NULL) OR (x > 0)`).

### Moved

| 0.1 | 0.2 |
|---|---|
| `sv.Pipeline`, `pipe.source`, `pipe.view`, `pipe.refresh` | transforms on sources, `node.write(sink)`, `node.refresh()`, `sv.group(...)` (`Pipeline` is internal: `sverify.incremental`) |
| `sv.IncrementalView(con, query, name)`, `view.apply`, `view.rows()` | a transform on a `StaticSource`, `source.apply(sv.Changes(...))`, `node.refresh()`, `node.to_arrow()` (`IncrementalView` is internal) |
| `pipe.view(..., resume=source.stored())` | build the nodes again; the first refresh resumes |
| `DeltaSink(uri, view).write()` | `node.write(DeltaSink(uri))`, written by `refresh` |
| `IcebergSink(catalog, identifier, view).write()` | `node.write(IcebergSink(catalog, identifier))` |
| `sverify.io.SinkWrite`, `sverify.io.IcebergWrite` | `sverify.io.SinkWrite` |
| `sv.StaticSource` | `sverify.io.StaticSource` |
| `sv.Changes` | `sv.Changes` (unchanged) |
| `sv.connect`, `sv.transform`, `sv.verify`, `sv.unique`, `sv.references`, `sv.Report`, `sv.asof_join` | unchanged |
| `sv.run_plan` | `sverify.engines.run` |
| `sv.run_substrait_json` | `sverify.engines.run_substrait_json` |
| `sv.create_table` | `sverify.engines.create_table` |
| `sv.table_rows` | `sverify.engines.table_rows` |
| `sv.ENGINES` | `sverify.engines.ENGINES` |
| `sv.SQL_PRODUCERS` | `sverify.engines.SQL_PRODUCERS` |
| `sv.Connection` | `sverify.engines.Connection` |
| `sv.substrait_json` | `sverify.engines.substrait_json` |
| `sv.isthmus_json` | `sverify.engines.isthmus_json` |
| `sv.written_plan` | `sverify.engines.written_plan` |
| `sv.delta_plans` | `sverify.engines.delta_plans` |
| `sverify.sql.to_sql`, `Dialect`, `Unsupported` | `sverify.engines.to_sql`, `Dialect`, `Unsupported` |
| `sverify.sql.duckdb.DUCKDB`, `sverify.sql.snowflake.SNOWFLAKE`, `sverify.sql.spark.SPARK` | `sverify.engines.DUCKDB`, `SNOWFLAKE`, `SPARK` |
| `sverify.partition.run_sharded` | `sverify.engines.run_sharded` |
| `sverify.spark_engine.run` | `sverify.engines.run_spark` |
| `sverify.spark_engine.SPARK_CONF` | `sverify.engines.SPARK_CONF` |
| `sv.VerificationError` | `sverify.errors.VerificationError` |
| `sv.PreconditionError` | `sverify.errors.PreconditionError` |
| `sv.PostconditionError` | `sverify.errors.PostconditionError` |
| `sv.CompositionError` | `sverify.errors.CompositionError` |
| `sv.NotIncremental` | `sverify.errors.NotIncremental` |
| `sv.SqlError` | `sverify.errors.SqlError` |
| `sverify.incremental.SchemaError` | `sverify.errors.SchemaError` |
| `sverify.incremental.AuditError` | `sverify.errors.AuditError` |
| `sv.Issue`, `sv.References`, `sv.Unique` | internal (`sverify.contracts`); `sv.unique` and `sv.references` build them |
| `sverify.io.ColumnStats`, `sverify.io.stats_facts`, `sverify.io.Stored` | internal (`sverify.io._common`, `sverify.incremental`) |
