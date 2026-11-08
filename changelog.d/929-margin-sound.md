### The margin check is proved in the core's doubles

- The margin check of a threshold on a double `SUM` or `AVG`
  ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)) is
  proved against `Rel.AllowedP`'s sums and means in the core's own doubles
  (`MarginSound.lean`): a group the check passes has every sum or mean an
  engine's `sum_order` allows, and the reference's, on one side of the
  threshold. Its constants are defined once, as codes the check and the proof
  share. What stays trusted is that the check and the plan read the same rows
  from one snapshot, and that a group's `Σ|x|` stays below a quarter of the
  largest double.
- `AvgOrder.bound` gives an engine's double `AVG` a computable range (D35),
  as `SumOrder.bound` does for `SUM`.
