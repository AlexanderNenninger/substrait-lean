### A filter's deep `AND`/`OR` nest checks in time linear in its depth

Beyond the top three levels, a filter's `AND` and `OR` chains are now bound as
guarded columns below the filter, one projection per operand that may raise,
each operand written once (D50-d,
[#1719](https://github.com/AlexanderNenninger/substrait-lean/issues/1719)).
The plan keeps the lift's rows and raises where it raises (`Rel.guardedFilter_eval`,
`Rel.guardedFilter_raises`). A guard below the third level is still reported as an
inferred precondition until the analysis reads guarded columns (D50-d3c).
Elsewhere (projections, aggregates, join conditions, lambdas) the levels below
the third stay eager, as before.
