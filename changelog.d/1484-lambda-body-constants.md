### A raising constant in a lambda's body is reported under a guard too

`Expr.constIssues` read a lambda's list and not its body, so `ifelse(id > 5, xs.map(e -> e + 1 // 0), NULL)` under a precondition that no row passes was proved, where D21 counts every constant subexpression that raises as raising for the whole plan. The body is read now ([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484), K5 of ruling 100). No engine run raised: DuckDB has no SQL form for lambdas yet and Polars returned NULLs.
