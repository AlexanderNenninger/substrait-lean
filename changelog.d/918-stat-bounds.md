### Bounds for statistical aggregates

- `Report.epsilon` gives `COVAR_SAMP` and `COVAR_POP` columns a bound, from
  the ranges of the pair's two sides, and marks a `VAR_*` or `COVAR_*`
  bound proved on the engines whose algorithm a theorem covers (DuckDB and
  Spark, `epsilon_var_cr` and `epsilon_cov_cr`; `"proved_on"`); on Polars it
  is tested. A `CORR` column has no bound, and says why (#918).
- Snowflake's `VAR_*` and `STDDEV_*` of doubles are written again, on values
  shifted by their group's mean ([#1023](https://github.com/AlexanderNenninger/substrait-lean/issues/1023)),
  where the plain formula cancels catastrophically. A `DISTINCT` one is
  still refused.
