### `to_sql` writes the rows the engine's runner writes

`to_sql`'s default for `rows` follows the engine (`"multiset"` for Spark and Snowflake, `"sequence"` for DuckDB), so a bare `to_sql(plan, "spark")` writes FETCH and windows over a named table with ties open, as a run on Spark sends them, where it refused them. `rows="sequence"` stays refused there; the message names `rows="multiset"` and the report's `deterministic` as the ways on. `Node.to_sql("spark")` of a node without a report writes what its refresh runs.
