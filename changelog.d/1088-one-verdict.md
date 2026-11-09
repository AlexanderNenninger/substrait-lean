### One report per checker answer

- `sv.verify` and `sv.from_substrait` build their reports in one place from
  the checker's answer, so a re-checked import now carries everything a
  verified plan does
  ([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)):
  - its assumed issues (a `SUM` that may leave its type, an overflow to `±∞`)
    are listed in `report.assumed` and checked on the data while the job runs,
    where the import used to drop them;
  - the checks the checker discharged (`unchecked`), the optimized plan, the
    per-relation row bounds, `rows_exact` and the margin checks of threshold
    filters (#929).
