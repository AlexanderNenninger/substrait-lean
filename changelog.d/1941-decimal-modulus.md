### `%` of decimals is read

Sverify reads `a % b` of two decimals, or a decimal and an integer: the
remainder of the two values at the larger scale, with the dividend's sign
(`-7.50 % 2.0` is `-1.50`), of type
`DECIMAL(min(p₁ − s₁, p₂ − s₂) + max(s₁, s₂), max(s₁, s₂))`. A zero divisor
raises. It runs on DuckDB, Polars and Spark, and DuckDB SQL's `%` of decimals
lifts in DuckDB's own result type. Where an operand at the larger scale needs
more than 38 digits, DuckDB computes a `DOUBLE`, so Sverify refuses it and
names the cast that fits
([#1941](https://github.com/AlexanderNenninger/substrait-lean/issues/1941)).
