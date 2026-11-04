### The SQL lift reads the variance family

`sv.sql` and SQL transformations now lift `STDDEV_SAMP`, `STDDEV_POP`,
`VAR_SAMP`, `VAR_POP`, the aliases `STDDEV` and `VARIANCE`, `COVAR_SAMP`,
`COVAR_POP` and `CORR`, of integers and doubles, to the Substrait functions the
Ibis producer writes. With `semantics="duckdb"`, `CORR` is DuckDB's: NaN for
one pair or a side whose values are all equal, where the reference's is NULL
(`duckdb-corr`). The SQL writer now runs a `FILTER` on `COVAR_*` and `CORR`. Sverify proves what it proves for Ibis's `std()`, so
`SELECT workflow, stddev_samp(duration_s) FROM jobs GROUP BY workflow` gives
"a double ≥ 0.0 or NULL", with `GROUP BY ROLLUP` too. Of a `DECIMAL` they are
refused for now
([#433](https://github.com/AlexanderNenninger/substrait-lean/issues/433)).
