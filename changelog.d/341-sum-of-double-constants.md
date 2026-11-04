### A SUM of a double constant is a double SUM in the written SQL

The SQL writer read a double constant in an aggregate as an integer, as Lean's
`Expr.kind` does for a double's code, where Lean's parser goes by the plan's
literal. So `SUM('inf'::DOUBLE)` was written as an integer `SUM` and raised
"integer overflow in SUM: inf", where `Rel.eval` and DuckDB give `inf`. The
writer now reads the declared type as Lean does (`doubleJ`), for `SUM`, `AVG`
and the sides of `COVAR_*` and `CORR`
([#341](https://github.com/AlexanderNenninger/substrait-lean/issues/341)).
