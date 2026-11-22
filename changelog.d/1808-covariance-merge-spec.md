### The covariance proof is stated for any merge

The covariance's error invariant is now proved for any merge of pairs that meets
`CMergeSpec` (`cInv_merge_of`), with DuckDB's merge as one instance
(`chan_spec`). This is the first step toward proving Polars's `COVAR_*` and
`CORR` (`stat_algo`), whose merge is Schubert and Gertz's
([#1808](https://github.com/AlexanderNenninger/substrait-lean/issues/1808)).
