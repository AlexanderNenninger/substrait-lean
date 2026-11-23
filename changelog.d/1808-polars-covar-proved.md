### Polars's `COVAR_*` bound is proved, with a looser leading constant

Polars's `COVAR_*` is now proved within `StatProps`' bound at Schubert and
Gertz's constants (`stat_algo` `SCHUBERT_GERTZ`, `StatTol.sg`,
`FloatBounds.StdModel.core_cov_polars`,
[#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808),
ruling 271). Its leading constant loosens from 71 to 107, so a plan whose
stated tolerance sits between the two can change from verified to not verified
on Polars. DuckDB's and Spark's bounds are unchanged. Polars's `COVAR_*` and
`CORR` share one `stat_algo` row, which stays tested until Polars's `CORR` is
proved.
