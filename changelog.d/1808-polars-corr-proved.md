### Polars's `COVAR_*` and `CORR` rows are proved

Polars's `CORR` is now proved within `StatProps`' bound, at the same constants
as DuckDB's (`FloatBounds.StdModel.core_corr_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808),
ruling 271). Polars's `agg.stat` `stat_algo` row, which `COVAR_*` and `CORR`
share, is now proved, so `proved_on` lists Polars for `COVAR_*` columns.
