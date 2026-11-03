### DuckDB's SQL writes the proved lowering

Where DuckDB computes a function differently from the reference, the SQL
sverify writes for DuckDB is now the template the Lean build generated and
proved (`substrait-check --lowering-table`, read by `sverify.sql.lowering`):
the guards for NaN and ±inf, the elementary functions' domains, division and
`%` by zero, `MIN % -1`, `<<`, and `overflow` = `SILENT` or `SATURATE`. The
hand-written versions in `sverify.sql.duckdb` are gone. Polars no longer
raises on a shift of NULL by an out-of-range amount, which the reference
leaves NULL (#241).
