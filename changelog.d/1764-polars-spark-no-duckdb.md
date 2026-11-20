### A Polars connection needs no DuckDB

`sv.connect("polars")` holds its tables as Arrow and runs with no `duckdb` installed (#1764), and the `polars` extra no longer brings `sverify[duckdb]`. Without DuckDB, an Ibis expression bound to such a connection (`con.table(name)`) does not execute through Ibis: it names the engine to run on (`Report.run(con, "polars")`). With DuckDB installed it executes there as before. Spark does not hold tables (a connection runs on DuckDB or Polars), so the `spark` extra keeps `sverify[duckdb]`.
