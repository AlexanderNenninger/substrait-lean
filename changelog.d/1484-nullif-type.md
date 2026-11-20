### `NULLIF` in SQL has the type of its first argument

DuckDB's `NULLIF(a, b)` compares in the common type of `a` and `b` and returns `a` itself. The lift typed the result as the common type, so `NULLIF(int_column, double_column)` was a double and an addition on it did not raise where DuckDB's integer addition does. Where the two types differ, the lift now writes `CASE WHEN a = b THEN NULL ELSE a END`; `NULLIF` of two values of one type is unchanged ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), `duckdb-nullif-type`).
