### Engines' function support and shims come from their plugins

- Which functions an engine runs, those it refuses with a reason of their own,
  the guards its dialect writes and what its shims do are the engine's plugin's
  (`ProfilePlugin.functions`, `window_functions`, `refuses`, `guards`,
  `shim_text`), no longer tables in sverify
  ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
- `sverify.engines.to_sql` takes a dialect by name: `to_sql(plan, "snowflake")`.
- Breaking: `sverify.engines.DUCKDB`, `SNOWFLAKE` and `SPARK` are removed;
  name the dialect (`"duckdb"`, `"snowflake"`, `"spark"`), or get its object
  with `sverify.sql.dialect_of`. `sverify.engines.run_spark` is removed; write
  `run(con, plan, "spark")`, or `run(con, plan, spark_session)` for a session
  of your own.
