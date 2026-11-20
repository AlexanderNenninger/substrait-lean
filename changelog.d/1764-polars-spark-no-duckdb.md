### A Polars or Spark connection needs no DuckDB

`sv.connect("polars")` and `sv.connect("spark")` hold their tables as Arrow and run with no `duckdb` installed (#1764). The `polars` and `spark` extras no longer bring `sverify[duckdb]`. Without DuckDB, an Ibis expression bound to such a connection (`con.table(name)`) does not execute through Ibis: it names the engine to run on (`Report.run(con, "polars")`). With DuckDB installed it executes there as before.
