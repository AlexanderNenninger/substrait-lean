### A deep `AND`/`OR` nest in a filter or projection checks in time linear in its depth

Beyond the top three levels, a filter's `AND` and `OR` chains are now bound as
guarded columns below the filter, one projection per operand that may raise,
each operand written once (D50-d,
[#1719](https://github.com/AlexanderNenninger/substrait-lean/issues/1719)).
The same holds for a projection's expressions. The plan keeps the lift's rows
and raises where it raises (`Rel.guardedFilter_eval`, `Rel.guardedFilter_raises`,
and the projection's), and a guard below the third level is proved where the
analysis already reads it, in the level's `CASE` condition. Elsewhere
(aggregates, join conditions, lambdas) the levels below the third stay eager,
as before.
