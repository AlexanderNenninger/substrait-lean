### `AND` and `OR` guard the next operand (D50)

`WHERE qty <> 0 AND total / qty > 1` is now proved: the SQL and Ibis frontends
lift an `AND` or `OR` over a raising operand so the operand runs only where the
earlier ones do not decide the result. `semantics="duckdb"` keeps DuckDB's
eager reading.
