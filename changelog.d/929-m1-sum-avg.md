### Tolerance composition: double `SUM` and `AVG` summed over rows

- The `M₁` fold (`Rel.tol1`, `Rel.plan_nearL1`) now bounds a `SUM` or `AVG`
  of a tolerated double grouped by exact keys: the column's budget once, plus
  a cost per input row
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  Proofs only: no route or report changes.
