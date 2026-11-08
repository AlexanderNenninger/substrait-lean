### Spark's variances lose DuckDB's NaN guard

The NaN guard on `VAR_*` and `STDDEV_*` (DD-3) is now a dialect hook,
`Dialect.var_nan`, kept on DuckDB, whose variance of one NaN is 0, and on
Snowflake, where that case is not recorded. Spark gives NaN on its own
(spark-var-pop-one-nan), so its written SQL drops one `COUNT` aggregate per
variance and each copy of it, 30 % of the SQL of a grouped variance. A new
fact records that Polars's streaming `group_by` of a one-row frame gives 0 for
a NaN (polars-var-pop-one-nan, #54).
