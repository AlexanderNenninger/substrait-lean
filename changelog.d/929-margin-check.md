### Thresholds on double sums run, checked on the data

- A filter on a double `SUM` or `AVG` against a constant (`HAVING SUM(amount) > 1000`)
  is no longer refused on DuckDB, Polars and Spark when no static bound
  decides it ([#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  The run first checks, per group, that the engine's sum is farther from the
  threshold than twice its bound, a bound from the group's count and
  `Σ|x|` (`StdModel.margin_check`). Then the engine keeps the reference's
  groups. A group that fails refuses the run with a `PreconditionError` that
  counts them; with `verify(on_inferred="warn")` the run warns, keeps them
  with the count in the warning. `on_inferred="off"`
  refuses the plan, as before.
