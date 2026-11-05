### Guarded double arithmetic raises nothing, and keeps its sign

Under `semantics="duckdb"`, `+`, `-`, `*` and `/` of doubles no longer
report a domain error. DuckDB gives NaN for `inf - inf`, `0 * inf` and
`inf / inf`, and the lift writes that NaN as a `CASE` around the
operation. The check now sees that the `CASE` rules the NaN out: a
condition joined with `AND` leaves its `ELSE` branch with alternatives
(`Expr.cstrAlts`), and `x ≠ 0` or `x ≠ ±inf` rule out a NaN case
([#702](https://github.com/AlexanderNenninger/substrait-lean/issues/702)).
A query's own `CASE WHEN x <> 0 AND y <> 0 THEN x * y END` benefits too.

A sum or product of non-negative doubles, and a quotient of one by a
positive one, is proved at least `0`: rounding keeps the sign. `x * y` of
`x, y ≥ 0` used to be bounded below by `-8.9e-16`, so `SUM(qty * price) >= 0`
was not proved. The three facts this rests on are proved in
`float-bounds/` ([#441](https://github.com/AlexanderNenninger/substrait-lean/issues/441)).
