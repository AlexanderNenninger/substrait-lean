### `verify` reports a decimal `SUM` that may leave its precision

A `SUM` of decimals has a declared precision: ten more digits than its
argument, at most 38. DuckDB raises past it ("Overflow in SUM of DECIMAL"),
while `verify` let a contract over the sum be proved. It now reports the
overflow as it does an integer `SUM` that may leave 64 bits: with `infer`,
the sum is assumed to fit and checked on the data while the job runs
(`Report.assumed`), and row caps with a bound on the column prove it fits
([#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316)).
