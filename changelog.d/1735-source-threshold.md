### A decision on DuckDB's integer `AVG` is refused where DuckDB may take it the other way

Under `semantics="duckdb"`, DuckDB's own `avg` of integers returns a double
within a band of the mean Sverify verifies
([#1735](https://github.com/AlexanderNenninger/substrait-lean/issues/1735)).
The lift marks that mean (D52), and a plan that reads it is proved only where
every filter, sort, `DISTINCT`, join condition, grouping key, postcondition and
key that reads the mean has one outcome over the band, and every output column
that reads it has a bound in `Report.epsilon`. Elsewhere the report holds a
`source_threshold` error and its verdict is `unproved`, so `to_sql`, `run`, the
SQL-file CLI and sverify-dbt refuse it. The way out is a precondition that keeps
the mean away from the threshold, or exact columns: `SUM(y) > c * COUNT(y)` for
an integer `c`.
