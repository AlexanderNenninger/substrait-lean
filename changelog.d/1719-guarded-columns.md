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

On Spark 4.3, Spark's parser refuses the SQL sverify writes for an alternating
nest 80 levels deep (299 KB) and nothing runs; 70 levels (231 KB) parse and run
in 16 to 31 s, most of it in Spark's optimizer (measured on homelab,
[#2030](https://github.com/AlexanderNenninger/substrait-lean/pull/2030#issuecomment-7056408687),
[phases](https://github.com/AlexanderNenninger/substrait-lean/pull/2030#issuecomment-7057113974)).
Sverify sets no depth limit of its own.
