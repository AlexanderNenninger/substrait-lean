# Engines and installs

Sverify runs a proved plan on DuckDB, Polars and Spark, and writes it as
DuckDB, Snowflake or Spark SQL. This page says which engines there are,
how to pick one, and how to install what you need.

## The engines

| Engine | Runs plans | Writes its SQL | Verify under its profile | Installed by |
|---|---|---|---|---|
| DuckDB | `engine="duckdb"`, the default | `"duckdb"` | `semantics="duckdb"` | `sverify` |
| Polars, on its streaming engine | `engine="polars"` | | `semantics="polars"` | `sverify[polars]` |
| Spark 4 | `engine="spark"`, or a Spark session | `"spark"` | `semantics="spark"` | `sverify[spark]` |
| Snowflake | in your account, from the written SQL | `"snowflake"` | | `sverify` |

- `node.refresh(engine=...)`, `report.run(con, engine)` and
  `sv.connect(engine=...)` pick the engine that runs a plan, and a route
  says how the proof reaches it ([Verifying: the two paths](verifying.md)).
- `node.to_sql(dialect)`, `report.to_sql(dialect)` and
  `sverify.engines.to_sql(plan, dialect)` write the checked plan as SQL in
  the dialect named, among the installed engines'. What a dialect cannot
  write is refused (`UnsupportedError`).
- `semantics=` on `verify` picks the profile the proof is under: the
  reference by default, or an engine's own
  ([The core and the profiles](core-and-profiles.md)).

DuckDB, Polars and Spark are in the 1.x promise, and so is Snowflake's
written SQL; the `all` extra installs every engine in it
([stability.md](stability.md#engines)).

## Installing

```bash
pip install sverify                    # DuckDB, contracts, incremental maintenance, DuckDB and Snowflake SQL
pip install 'sverify[polars]'          # and Polars
pip install 'sverify[spark]'           # and Spark (needs Java 17 or 21)
pip install 'sverify[all]'             # every engine in the promise, Delta, Iceberg and the rest
```

- Each engine is a package of its own, released with sverify at the same
  version: `sverify-duckdb`, `sverify-polars` and `sverify-spark`. A
  package carries the engine's plugin, its dialect where it has one, and
  its facts; its `[run]` extra brings the runtime (`duckdb`, `polars` and
  `numpy`, or `pyspark`).
- `sverify` itself brings `sverify-duckdb` with DuckDB, which is also its
  table store, and Ibis, PyArrow and SQLGlot, with the checker as a native
  binary in the wheel. `sverify[polars]` and `sverify[spark]` install the
  engine's package with its runtime.
- `pip install sverify-spark` without the extra verifies under Spark's
  profile and writes Spark SQL without PySpark.
- Sverify finds every installed engine through its plugin, registered in
  the entry-point group `sverify.profiles` (`sverify.profiles.ProfilePlugin`).
- The other extras: `delta`, `iceberg`, `flight`, `testing`, `odcs`,
  `openlineage` and the secret backends (`secrets-aws`, `secrets-gcp`,
  `secrets-azure`, `secrets-keychain`).

## What each engine does

What an engine computes, option by option, is in its facts, each with its
evidence and the engine version it was probed at:

- DuckDB: [`engines/duckdb/facts/`](../engines/duckdb/facts/)
- Polars: [`engines/polars/facts/`](../engines/polars/facts/)
- Spark: [`engines/spark/facts/`](../engines/spark/facts/)

The [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)
render them, searchable by id, function and option, and the
[realizability table](realizability.md) gives each engine's class on every
option. [engine-profiles.md](engine-profiles.md) describes each engine's
translation and shims.
