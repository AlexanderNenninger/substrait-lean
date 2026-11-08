### Contracts on double sums proved on Polars and Spark

- The route of a contract on a double `SUM` or `AVG` with a row cap
  (`sv.max_rows(n)`) now has evidence `proved` on Polars and Spark where its
  other rows are proved
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  Before, the engine's rounding of each addition rested on a probe. The plan's
  bound, `StdModel.epsilon_sum_cr`, holds whatever tie rule the engine rounds
  with. In the contract census, Spark's proved contracts go from 3 to 7 and
  Polars's from 1 to 4. DuckDB's stay tested on its `nan_creation` and
  `float_overflow` rows.
- Fixed: a shim no longer hides a plan's bound on doubles. DuckDB's `VAR`
  and `STDDEV` row shims NaN only (`nan_through`), yet a contract asking
  `sv.within(rel=1e-9)` of a variance whose bound is `abs = 1.78e-7` was
  accepted on DuckDB. It is now refused there, as on the other engines, with
  the tolerance that the bound does meet.
