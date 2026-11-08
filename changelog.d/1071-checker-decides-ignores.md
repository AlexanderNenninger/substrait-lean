### The checker decides what a postcondition ignores

- What an observation (`sv.equivalent`) ignores of a postcondition, and which
  open choices of the plan it reads, now come from the checker
  ([#1071](https://github.com/AlexanderNenninger/substrait-lean/issues/1071)).
  That a postcondition does not depend on the sign of a zero is a theorem
  (`Expr.robust_of_depends_canon`) where it was an assumption.
- A postcondition proved on every order of the reference, but not on every
  result it allows, reads an open measure (`VAR_*`, `STDDEV_*`, `COVAR_*`,
  `CORR`, `QUANTILE_CONT`, a double `SUM` or `AVG` added in another order).
  Under an observation other than the plan's bound, its route's evidence is
  now `tested`, not `proved`. Nothing that ran is refused.
