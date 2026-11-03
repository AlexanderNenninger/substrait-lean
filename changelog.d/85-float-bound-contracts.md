### Contracts on `SUM` and `AVG` of doubles, up to rounding

Rollups of doubles get proved bounds (#85).

- `sv.max_rows(n)` caps an input's rows, checked on the data. With a cap, a
  `SUM` or `AVG` of doubles in `[lo, hi]` is bounded by the exact result's
  interval widened by the proved rounding error (`docs/float-bounds.md`).
- `sv.approx(cond)` states a postcondition up to that rounding:
  `sv.approx(_.cpu_avg <= 100)` is proved where `_.cpu_avg <= 100` is not,
  and runs as `_.cpu_avg <= 100.0001`. A report hints at it when an exact
  claim fails only by rounding.
- Signs are exact without a cap: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.
