### Per-expression guard elimination

Guard elimination dropped the run-time checks of a whole plan or none of
them (`Report.guard_free`). A report now lists the expressions that cannot
raise on data that meets the preconditions, `Report.unchecked`, and
`to_sql(plan, dialect, unchecked=report.unchecked)` leaves out only their
checks: in `SELECT a // b, a * b` with `b >= 1`, the division loses its
`CASE` and the product keeps its overflow check. `Rel.evalG_marks` in
`SubstraitLean/Guards.lean` proves the result unchanged
([#83](https://github.com/AlexanderNenninger/substrait-lean/issues/83)).
