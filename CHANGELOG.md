# Changelog

## Unreleased

### Maintainer tooling leaves the wheel

The coverage harness, the query catalogue, the fuzzers, DuckDB's
sqllogictest replay and the example pipelines (`sverify.coverage`,
`sverify.catalogue`, `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`,
`sverify.examples`) were internal, and only the tests and CI used them. They
now live in `python/tools/sverify_dev` in the repository and are no longer
installed with sverify: about 4,000 lines fewer in the wheel.

### Fixed: a sink kept another plan's rows after the plan changed

If you use 0.3.0 and change a node's transform while keeping its sink,
upgrade. The sink recorded which plan wrote each state, but only compared
the state's epoch (the sum of the source versions) when deciding what to
write. So a job restarted with a new plan, at source versions the sink had
already committed, skipped the write: the table kept the old plan's rows and
its contract, while the node held the new plan's state. On the next source
change it merged the new plan's change on top of the old plan's rows, and
the table was wrong from then on, without an error. This affected
`DeltaSink`, `IcebergSink`, `sink_from` and sinks of your own that override
`committed()`.

A sink whose last commit came from another plan (`Contract.plan` differs) is
now overwritten with the new plan's whole state, and the refresh reports the
write as `overwrite`. `DeltaSink` replaces the table's schema and drops the
CHECK constraints it added for the old plan that the new one does not prove,
then adds the new plan's in the commit that records the epoch, so a job
stopped in between writes the state again. `IcebergSink` replaces the
table's schema in the overwrite's transaction. Constraints that another
writer added still stop the write.

A table is affected if you restarted a job with a changed plan before its
sources moved on. If it has not written a change since, the first refresh
after upgrading overwrites the table. If it has, that MERGE recorded the new
plan, and the fix cannot tell the table is wrong: delete the table, or point
the sink at a new location, and refresh to write it in full.

### Fixed: a node without a contract is planned again after a schema change

A node of a plain function, such as `orders.pipe(lambda t: t.select(t.id))`,
counted as contracted, so a dropped column, or a column widened beyond what
its values used to fit, raised `SchemaError` instead of planning the node
again. It is now planned again and recomputed, and its sink is overwritten.

### Fixed: `%` of doubles gave wrong values

A plan that takes the remainder of doubles, such as `x % 2.5`, passed the
check but was evaluated on the doubles' internal codes, so its values were
wrong (`7.5 % 2.0` came out as a 300-digit integer). It is now C's `fmod`,
as DuckDB, DataFusion and Spark compute `%`: the result has the sign of the
dividend (`-7.5 % 2.0` is `-1.5`), an infinite dividend or a NaN give NaN,
and an infinite divisor gives the dividend. The value is exact. A zero
divisor is an error, as for integers, so `verify` reports "division by zero"
unless the plan rules it out (`WHERE y <> 0.0`). The Polars translation gives
the same results, although Polars' own `%` takes the divisor's sign.
Substrait itself defines no `modulus` of doubles (#203).

## 0.3.0 (2026-11-01)

### Licensed under the MPL-2.0

sverify now has a license, the Mozilla Public License 2.0; 0.2.0 and earlier
were published without one. You can use sverify in open and proprietary
products alike. If you distribute changes to sverify's own files, they stay
under the MPL. The vendored `ibis_substrait` stays under Apache-2.0.

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

### Your own sources and sinks

Writing a source or a sink no longer means knowing sverify's internals
([#156](https://github.com/AlexanderNenninger/substrait-lean/issues/156)).

- `sverify.io.Source`: implement `read(since)`, which returns new rows and a
  cursor as a `Batch` (`kind="append"`, `"snapshot"` or `"changes"`).
  sverify numbers the reads as versions, keeps the table, and hands nodes
  the exact change. The refresh report says what the batches assume, and
  `refresh(audit=True)` reads the table again in full to check it, also
  when no batch arrived. `from_query(fn, cursor_on=...)`, `from_frame(fn)`
  and `from_files(path)` build one.
- `sverify.io.Sink`: implement `write(change)`, which gets a `SinkChange`
  (rows added and removed, or the whole table, and the contract), and
  optionally `committed()`. Exactly-once skipping and contract recording
  happen once, in the base class. `sink_from(fn)` hands the whole table to
  a function. Nodes reading a stored node of your own sink read what was
  written, with its exact changes. `DeltaSink` and `IcebergSink` are now
  subclasses, and every sink reports a `SinkWrite` (new mode `"update"`;
  `version` may be None).
- The full protocol for table formats is public as
  `sverify.io.VersionedSource`, with `Snapshot` and `SourceBatch`, whose
  `unchanged`, `from_changes` and `from_snapshot` build what `changes`
  returns. `Pipeline` no longer special-cases `StaticSource`: any source
  with a `digest` gets it recorded.
- `sverify.io.Storage` holds object store options shared by several tables:
  a mapping, or a function returning fresh options whenever a table is
  opened, so expiring tokens renew; `repr` shows option names only.
  `DeltaSource` and `DeltaSink` take one, or a function, as
  `storage_options`.
- A sink's `app_id` now defaults to `sverify:<sink name>` (it was the
  node's name, which is the same unless it clashed with a source's).
- `Contract.from_json` ignores fields it does not know, so contracts can
  gain fields without breaking the readers of this version.

### A pytest plugin for transforms and contracts

`sverify.testing` is now public
([#180](https://github.com/AlexanderNenninger/substrait-lean/issues/180)), and
installing sverify registers a pytest plugin (the `pytest11` entry point
`sverify`, off with `-p no:sverify`).

- `assert_contract(node)` asserts that every contract in a node's lineage is
  proved. With `data=` it runs the node on those rows: test data that breaks
  a precondition is reported with its rows, the output is checked against
  the postconditions, and with `expected=` it is diffed against the expected
  rows (missing and unexpected rows, as bags).
- `assert_engines_agree(node, data)` runs the node on every installed engine
  and diffs their results.
- `cases(node, max_rows=5)` is a Hypothesis strategy of input tables that
  meet a node's preconditions, for property tests of the code around it.
  It needs the new `testing` extra (`pip install 'sverify[testing]'`).
- The fixtures `sv_source(rows, schema, name=...)` (an in-memory source,
  also `sverify.testing.source`) and `sv_engine`, which runs a test once per
  installed engine (`installed_engines()`), or per engine of
  `--sv-engines=duckdb,polars`.

`python/tests/test_plugin_example.py` is an example test file, and
`python/tests/test_tour.py` tests the tour's transforms with the plugin.

### Ibis string functions

More of Ibis's string API is checked and runs on every engine
([#49](https://github.com/AlexanderNenninger/substrait-lean/issues/49)):
`lpad`/`rpad`, `repeat`, `reverse`, `replace`, `ilike`, `ascii`,
`levenshtein`, `right`, `find` with a start, `join` (`concat_ws`),
`find_in_set`, `capitalize` and slices. Each has the meaning of Ibis's
DataFusion SQL, by code point. A `repeat` past 2³¹ − 1 bytes is an
`overflow` error, which the checker rules out for a constant string with a
bounded count.

- Polars computes all of them exactly. DuckDB, Snowflake and Spark raise
  "non-ASCII text differs between engines" for `reverse`, `ascii`,
  `levenshtein` and `ilike` on non-ASCII text, and refuse `replace` with an
  empty pattern.
- `translate` is refused: DataFusion translates grapheme clusters.

### Fixes

- Written plans keep a projected literal's declared type: doubles,
  timestamps and typed NULLs no longer come out integer-typed
  ([#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96)).
- The tour notebooks declare the extras they use (`sverify[datafusion]`,
  `sverify[datafusion,polars]`), so they run in their own sandbox, as molab
  runs them
  ([#197](https://github.com/AlexanderNenninger/substrait-lean/issues/197)).

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
