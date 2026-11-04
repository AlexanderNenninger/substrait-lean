### Statistical aggregates as black boxes

The SQL lift reads more of DuckDB's aggregates as black boxes
([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)):
`product`, `kahan_sum` (also `fsum`, `sumkahan`), `favg`, `sem` and `mad`, not
NULL over values, `sem` and `mad` at least 0; and `kurtosis`, `kurtosis_pop`
and `skewness`, which DuckDB raises on for infinite or huge values, so
`verify` reports a domain error. Black-box aggregates may now raise. Integers
are converted to doubles, as DuckDB converts them. `bit_count` of a BIGINT is
exact, in [0, 64]. `histogram` (a MAP) and `weighted_avg` (two arguments) are
refused with a reason. The engine facts `duckdb-moments` and
`duckdb-statistical-aggregates` record what DuckDB 2.0.0 does.
