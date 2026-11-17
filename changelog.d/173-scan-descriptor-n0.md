### Internal: a Parquet scan is plain data, and DuckDB's reader of it lives in `sverify_duckdb`

`sverify._scan.Scan` no longer holds SQL: `sverify_duckdb.scan` reads a scan (`attach_scan`, `read_scan`), as the Polars and Spark plugins will read it (#173). `Scan.to_arrow()` stays the reference reader. No behaviour changes.
