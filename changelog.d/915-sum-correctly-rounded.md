### `SUM` and `AVG` of doubles are the exact sum rounded once (D25)

The reference's `SUM` of doubles is now the exact sum of the values rounded
once to the nearest double, and `AVG` the exact mean rounded once
([#915](https://github.com/AlexanderNenninger/substrait-lean/issues/915), epic
[#919](https://github.com/AlexanderNenninger/substrait-lean/issues/919)). It no
longer depends on the order of the rows, so a plan with double sums leaves the
engine no choice but the row order (`Rel.detPlan`), and its contracts hold of
every result the reference allows. Results can differ from 0.7 by an ulp: the
mean of three `0.1` is now `0.1`. Engines run as before, within the plan's
bound, which is now the engine's order plus half an ulp in place of twice the
order's bound, so `Report.epsilon` halves. A `GROUP BY` on the split key shards
a double `SUM` exactly, and `run_sharded` reports the larger of the two proved
tolerances of a split double sum.
