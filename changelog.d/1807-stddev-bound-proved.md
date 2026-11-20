### `STDDEV_*` bounds are proved

`Report.epsilon` of a `STDDEV_*` column of doubles is now proved on DuckDB
and Spark, as `VAR_*` and `COVAR_*` already were: an engine's square root of
its variance is within the reported bound of the reference's correctly
rounded root (`FloatBounds.StdModel.epsilon_stddev_cr`,
[#1807](https://github.com/AlexanderNenninger/substrait-lean/issues/1807)).
Polars stays tested until its `VAR_*` algorithm is proved (#1808).
