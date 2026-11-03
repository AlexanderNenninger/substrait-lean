### A double divided by zero raises

`x / y` and `x % y` on doubles raise on a zero divisor, as on integers, when
the plan omits `on_division_by_zero` or asks for `ERROR` (#204). `verify`
reports "division by zero" unless the plan rules it out (`y > 0` in
`requires`, a filter, `NULLIF(y, 0)` or `CASE WHEN y <> 0`). A plan that asks
for `IEEE`, `LIMIT` or `NULL` gets that. Under `semantics="duckdb"`, SQL
divides as DuckDB does, giving `±inf` or NaN.
