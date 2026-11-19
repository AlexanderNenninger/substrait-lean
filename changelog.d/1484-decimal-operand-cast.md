### Decimal `+` and `-` raise where DuckDB's operand cast does

DuckDB casts each operand of a decimal `+` or `-` to the result type and raises there, also where the exact sum fits (`DECIMAL(38,0) + DECIMAL(38,10)` at `10^28` against `-0.0000000001`). The reference returned the value. It now checks an operand that can exceed 38 digits at the result's scale and raises, and the inferred precondition is `|a| < 10^(38 - s)` (D56, [#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), `duckdb-decimal-addsub-operand-cast`).
