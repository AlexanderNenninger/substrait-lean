### Tolerances compose along a plan

Sverify proves that a result within a tolerance of the reference in its double columns stays within a computed tolerance after each operator of a plan, and node after node in a pipeline (`Rel.plan_near`, `Rel.pipeline_near` in `SubstraitLean/Lipschitz.lean`, [#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)). A filter, join key, group key or `DISTINCT` on a tolerated column has no such bound and is left out. `sverify.testing.allows_rows` indexes the choice rows on their fixed columns: 2,000 rows take 3 ms instead of 2.1 s.
