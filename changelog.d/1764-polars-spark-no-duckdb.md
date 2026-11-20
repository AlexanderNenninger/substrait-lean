### A Polars or Spark connection needs no DuckDB

`sv.connect("polars")` and `sv.connect("spark")` hold their tables as Arrow and run with no `duckdb` installed (#1764). The `polars` and `spark` extras no longer bring `sverify[duckdb]`. An Ibis expression bound to such a connection (`con.table(name)`) no longer executes through Ibis: it names the engine to run on (`Report.run(con, "polars")`) or a DuckDB connection.
