### Quantile of a decimal: the refusal names the cast

`median()` and `quantile()` of a decimal column stay refused, by design: DuckDB truncates a double interpolation, and Spark and Polars return doubles, so no engine gives one value ([#1921](https://github.com/AlexanderNenninger/substrait-lean/issues/1921)). The message says to cast the column first (`x.cast("float64").quantile(q)`), which verifies and runs on DuckDB.
