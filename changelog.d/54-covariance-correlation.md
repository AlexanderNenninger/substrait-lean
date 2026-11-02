### Covariance and correlation

Ibis's `cov()` and `corr()` (DuckDB's `COVAR_SAMP`, `COVAR_POP` and `CORR`)
are verified on DuckDB, grouped, with DuckDB's own algorithm (#54). `CORR`
is NULL for fewer than two pairs and where one side's values are all equal,
as the SQL standard says, rather than DuckDB's NaN. The other engines refuse
them until #271.
