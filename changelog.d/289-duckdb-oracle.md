### DuckDB is the test oracle; the docs describe SQL as DuckDB SQL

The tests check the reference model and the engines against DuckDB, the Tier 1
engine, wherever they used to run raw SQL or Ibis's SQL on DataFusion as an
oracle. DataFusion keeps the tests about it as a backend: checked plans
running on it, and the native behaviours that motivate a refusal.
`sverify.engine.run_sql` (internal) is gone. Raw DuckDB SQL over a
connection's tables is `sverify.testing.duckdb_sql`, and an Ibis expression's
own DuckDB SQL is `sverify.testing.duckdb_ibis`. The coverage harness's
`DATAFUSION_SQL` and `NO_DATAFUSION_SQL` are replaced by one list,
`NO_DUCKDB_SQL`: the cases where DuckDB's own SQL computes something other
than the plan. `sverify.testing.parse_row` is private now (`parse_rows`
stays). The README, `python/README.md`, `docs/reference-semantics.md`, the
tour's chapters 12 and 14 and the agent skills describe SQL as DuckDB SQL,
read by sverify's lift with `semantics="duckdb"` or `"reference"`, and
DataFusion as an optional backend.
