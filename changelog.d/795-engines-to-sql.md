### Breaking: SQL from a node or a report, one way to run on Spark, `Connection` methods (api-review F1 to F4)

From the API review before 1.0
([#795](https://github.com/AlexanderNenninger/substrait-lean/pull/795),
`api-review/PROPOSAL.md` F1 to F4). The deprecated names still work in
0.6 with a `DeprecationWarning` that names the replacement, and go in 0.7.

- `node.to_sql(dialect)` and `report.to_sql(dialect)` write the plan a proof
  checked as DuckDB, Snowflake or Spark SQL (`"duckdb"`, `"snowflake"`,
  `"spark"`, or a `Dialect`), with its run-time checks. They refuse a plan
  that is not proved (`UnverifiedRunError`), as `refresh` and `run` do, and a
  report's `deterministic` lets windows run without a row-order tiebreak.
  Before, the way to SQL was `to_sql(json.loads(node.internal_plan), dialect)`.
- `con.create(name, schema, rows)` and `con.rows(name)` replace
  `sverify.engines.create_table(con, name, schema, rows)` and
  `table_rows(con, name)`, which warn.
- `Connection.arrow` and `Connection.ibis` are deprecated: `con.get(name)`,
  `con.rows(name)` and `con.put(name, table)` read and write the tables, and
  `con.table(name).get_backend()` is the Ibis backend, for SQL of your own.
- `sverify.engines.run(con, plan, "spark")`, or a Spark session as the
  engine, is the one way to run a plan on Spark; `run_spark(plan, tables)`
  warns. A window without a row order runs on Spark when the contract
  states its order key (`sv.unique(...)`), through `node.to_sql("spark")`
  or `report.to_sql("spark")`; `run` takes no tie flag.
- `sverify.engines.substrait_json(con, sql)` now lifts the SQL under the
  reference semantics, as `sv.verify` and `sv.sql` do. Pass
  `semantics="duckdb"` for what DuckDB computes, the old default.
- The API reference documents `Dialect` by its fields (`name`, `guards`,
  `finite`, `decimals`). Its SQL-writing methods, subclasses of it, and the
  plan layer (`to_sql`, `substrait_json`, `written_plan`,
  `run_substrait_json`, `delta_plans`) are outside the 1.x promise
  ([docs/stability.md](docs/stability.md)).

Migration:

```python
# before
from sverify.engines import SNOWFLAKE, create_table, run_spark, table_rows, to_sql
create_table(con, "orders", schema, rows)
table_rows(con, "orders")
to_sql(json.loads(node.internal_plan), SNOWFLAKE)
run_spark(plan, {"orders": orders_table})
con.ibis.raw_sql("SELECT 1")

# after
con.create("orders", schema, rows)
con.rows("orders")
node.to_sql("snowflake")
run(con, plan, "spark")  # con holds the orders table
con.table("orders").get_backend().raw_sql("SELECT 1")
```

### `round(x, d)` follows DuckDB 2.0 where the result overflows

`round(x, d)` with a negative `d` gives `x` itself where the rounded value
would overflow, as DuckDB 2.0 does (`round(1.5e308, -308)` is `1.5e308`),
where the model gave 0, DuckDB 1.4's answer. The Polars and SQL writers
follow, and the engine fact `duckdb-round-digits-2` supersedes
`duckdb-R15-round-digits`, whose probes missed the case.

### Faster rows in and out of a connection

`con.create`, `con.rows` and the row lists a refresh reads build and read
Arrow tables column by column, without a dictionary per row: 100,000 rows of
four columns go into a table in 22 ms (88 ms before) and out in 71 ms (92 ms
before), with a quarter and three fifths of the Python memory.
