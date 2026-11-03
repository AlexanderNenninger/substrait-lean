# spark: facts

Generated from [facts/](facts/) by `uv run python -m sverify_dev.facts --write`; do not edit by hand. One JSON document per finding, in the format of [fact.schema.json](../fact.schema.json). Version checked: 4.3.0.

| Id | Finding | Area | Status | Verdict | ≈ entries | Last checked |
|---|---|---|---|---|---:|---|
| [spark-avg-double](#spark-avg-double) | `AVG` of doubles: plain sum by the count | aggregates | open | plain sum / n |  | 2026-11-03 |
| [spark-corr](#spark-corr) | `CORR`: shared Welford state; NULL for one pair or zero variance | aggregates | open | ck / sqrt(xMk · yMk); NULL as in the reference; no clamp |  | 2026-11-03 |
| [spark-covar](#spark-covar) | `COVAR_*`: Welford co-moment, Chan merge | aggregates | open | Welford co-moment; Chan merge |  | 2026-11-03 |
| [spark-sum-double](#spark-sum-double) | `SUM` of doubles: plain, order by partitioning | aggregates | open | plain recursive summation; order depends on partitioning |  | 2026-11-03 |
| [spark-var-stddev](#spark-var-stddev) | `VAR_*` and `STDDEV_*`: Welford/West, Chan merge | aggregates | open | Welford/West; Chan merge; no clamp |  | 2026-11-03 |

Settings the facts depend on, at one value:

- `spark.sql.ansi.enabled`: spark-corr
- `spark.sql.legacy.statisticalAggregate`: spark-corr, spark-covar, spark-var-stddev

## <a id="spark-avg-double"></a>spark-avg-double. `AVG` of doubles: plain sum by the count

spark 4.3.0 · aggregates · open · `avg` · #54, #85

`AVG(DOUBLE)` keeps a sum and a count and returns `Divide(sum, count, LEGACY)`, NULL for a count of 0. The sum is spark-sum-double's.

Reference:

`AggFn.avg` is `floatSum` / n, NULL without values.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Average.scala#L102-L126](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Average.scala#L102-L126). Read at tag v4.3.0 (commit 98bc0212).

## <a id="spark-corr"></a>spark-corr. `CORR`: shared Welford state; NULL for one pair or zero variance

spark 4.3.0 · aggregates · open · `corr` · `spark.sql.legacy.statisticalAggregate = false`, `spark.sql.ansi.enabled = true` · #54, #85

One shared Welford state (`ck`, `xMk`, `yMk`); the result is `ck / sqrt(xMk * yMk)`. One pair is NULL (NaN under `spark.sql.legacy.statisticalAggregate`); `xMk == 0` or `yMk == 0` is NULL. Not clamped to [-1, 1].

If `xMk * yMk` underflows to 0 with neither side 0, the division raises under ANSI mode (the 4.x default) and gives NULL otherwise.

Reference:

`AggFn.corr` (`corrOf`): NULL for fewer than two pairs, or for a side whose values are all equal; else the co-deviation sum by the square root of the product of the two squared-deviation sums. It is not clamped to [-1, 1]. Engines may differ in the last bits (#54) until #85 bounds the error.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L85-L95](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L85-L95); [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L63-L83](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L63-L83); [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L137-L144](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Corr.scala#L137-L144). Read at tag v4.3.0 (commit 98bc0212). Inferred, not run: the underflow case, from `DivModLike` in arithmetic.scala.

## <a id="spark-covar"></a>spark-covar. `COVAR_*`: Welford co-moment, Chan merge

spark 4.3.0 · aggregates · open · `covar_samp`, `covar_pop` · `spark.sql.legacy.statisticalAggregate = false` · #54, #85

`ck += dx * (y - newYAvg)`; partial states merge as `ck.l + ck.r + dx * dyN * n1 * n2`. No pairs is NULL; the sample covariance of one pair is NULL (NaN under `spark.sql.legacy.statisticalAggregate`).

Reference:

`AggFn.cov` (`covOf`) is two-pass: the two means, then the products of the deviations added in list order from +0.0, by n or n - 1. No pairs is NULL, and so is a sample of one pair. Engines may differ in the last bits (#54) until #85 bounds the error.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Covariance.scala#L77-L84](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Covariance.scala#L77-L84). Read at tag v4.3.0 (commit 98bc0212).

## <a id="spark-sum-double"></a>spark-sum-double. `SUM` of doubles: plain, order by partitioning

spark 4.3.0 · aggregates · open · `sum` · #54, #85

`SUM(DOUBLE)` adds with a plain `Add` and no overflow check; partial sums merge plainly. The order of the additions depends on the partitioning.

Reference:

`AggFn.fsum` (`floatSum`) adds the doubles one by one in list order from +0.0; the writers that need that order exactly use `Dialect.float_sum`. NULL without values.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Sum.scala#L94-L97](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/Sum.scala#L94-L97). Read at tag v4.3.0 (commit 98bc0212).

## <a id="spark-var-stddev"></a>spark-var-stddev. `VAR_*` and `STDDEV_*`: Welford/West, Chan merge

spark 4.3.0 · aggregates · open · `var_samp`, `var_pop`, `stddev_samp`, `stddev_pop`, `variance`, `stddev` · `spark.sql.legacy.statisticalAggregate = false` · #54, #85

All state is `DoubleType`, the count too. The update is Welford/West: `delta = x - avg`, `deltaN = delta / (n + 1)`, `avg += deltaN`, `m2 += delta * (delta - deltaN)`. Partial states merge as `m2.l + m2.r + delta * deltaN * n1 * n2`, with `delta` forced to 0 when a side is empty.

No values is NULL; the sample variance of one value is NULL (NaN under `spark.sql.legacy.statisticalAggregate`). No clamp.

Reference:

`AggFn.var` (`varOf`, `SubstraitLean/Aggregate.lean`) is two-pass with native doubles in list order: the mean (`floatSum` / n), then the squared deviations from it, added from +0.0, by n or n - 1, and never below 0. A sample of one value is NULL. Only NULL and the sign are exact; engines may differ in the last bits (#54) until #85 bounds the error.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/CentralMomentAgg.scala#L122-L127](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/CentralMomentAgg.scala#L122-L127); [https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/CentralMomentAgg.scala#L83-L101](https://github.com/apache/spark/blob/v4.3.0/sql/catalyst/src/main/scala/org/apache/spark/sql/catalyst/expressions/aggregate/CentralMomentAgg.scala#L83-L101). Read at tag v4.3.0 (commit 98bc0212).
