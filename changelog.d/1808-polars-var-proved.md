### Polars's `VAR_*` and `STDDEV_*` bounds are proved

`Report.epsilon` of a `VAR_*` or `STDDEV_*` column of doubles is now proved on
Polars as on DuckDB and Spark: two-pass blocks, Welford's update and Schubert
and Gertz's merge, in any order and tree, keep the variance within the
reported bound (`FloatBounds.StdModel.core_var_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808)).
Polars's `COVAR_*` stays tested.
