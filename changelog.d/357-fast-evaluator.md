### Hash joins and hash aggregation in Lean's evaluator

`substrait-check` evaluates plans with inlined data through `Rel.evalFast`
(`SubstraitLean/EvalFast.lean`), which Lean proves equal to `Rel.eval`, rows and
order included (`Rel.evalFast_eq`). Equi-joins, semi-joins, `EXCEPT` and `INTERSECT` hash the right
side, and `DISTINCT`, `fn(DISTINCT …)` and `GROUP BY` use hash sets and maps,
where `Rel.eval` compares every pair of rows. The query of DuckDB's
`hash_join_dict_surviving_outer_build.test` (3,532 rows) evaluates in 0.41 s,
down from 9.2 s, and its larger variant in 0.33 s, down from 54 s.
`substrait-check --eval-spec` evaluates with `Rel.eval`, for tests
([#357](https://github.com/AlexanderNenninger/substrait-lean/issues/357)).
