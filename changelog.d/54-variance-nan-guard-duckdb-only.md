### Spark's variances lose DuckDB's NaN guard

The NaN guard on `VAR_*` and `STDDEV_*` (DD-3) is a dialect hook,
`Dialect.var_nan`, on by default. A dialect leaves it out where its engine's
profile states the `agg.var` `stat_algo` row without the shim: Spark's, whose
own variance of one NaN is NaN (spark-var-pop-one-nan). Spark's written SQL
drops one `COUNT` aggregate per variance and each copy of it, 30 % of the SQL
of a grouped variance. DuckDB and Snowflake keep the guard.
