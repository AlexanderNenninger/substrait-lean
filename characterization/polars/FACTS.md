# polars: facts

Generated from [facts/](facts/) by `uv run python -m sverify_dev.facts --write`; do not edit by hand. One JSON document per finding, in the format of [fact.schema.json](../fact.schema.json). Version checked: py-2.1.0.

| Id | Finding | Area | Status | Verdict | ≈ entries | Last checked |
|---|---|---|---|---|---:|---|
| [polars-corr](#polars-corr) | `corr`: shared state; NaN for one pair or zero variance | aggregates | open | dp_xy / sqrt(dp_xx · dp_yy); NaN where the reference is NULL; no clamp |  | 2026-11-03 |
| [polars-cov](#polars-cov) | `cov`: two-pass blocks with Chan merge; Welford when streaming | aggregates | open | two-pass per block + Chan (in memory); Welford (streaming); no clamp |  | 2026-11-03 |
| [polars-mean-float](#polars-mean-float) | `mean` of floats: the sum by the count | aggregates | open | sum / n |  | 2026-11-03 |
| [polars-sum-float](#polars-sum-float) | `sum` of floats: pairwise, Kahan when grouped | aggregates | open | pairwise (full); Kahan (grouped by index); plain across chunks |  | 2026-11-03 |
| [polars-var-std](#polars-var-std) | `var` and `std`: two-pass blocks of 128, or Welford, by path | aggregates | open | two-pass per 128-block with Chan merge (ungrouped); Welford (grouped); clamps below 0 |  | 2026-11-03 |

## <a id="polars-corr"></a>polars-corr. `corr`: shared state; NaN for one pair or zero variance

polars py-2.1.0 · aggregates · open · `corr`, `pearson_corr` · #54, #85

`PearsonState` returns `dp_xy / sqrt(dp_xx * dp_yy)` if `dp_xx * dp_yy > 0`, else NaN: one pair or a zero variance is NaN. Not clamped to [-1, 1]. `dp_xx * dp_yy` can overflow or underflow before the square root.

No pairs: null in the streaming reducer; the in-memory path (`polars-ops` `cov.rs`) returns NaN.

Reference:

`AggFn.corr` (`corrOf`): NULL for fewer than two pairs, or for a side whose values are all equal; else the co-deviation sum by the square root of the product of the two squared-deviation sums. It is not clamped to [-1, 1]. Engines may differ in the last bits (#54) until #85 bounds the error.

Where the reference is NULL (one pair, a constant side), Polars gives NaN.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L273-L280](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L273-L280); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/cov.rs#L297-L305](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/cov.rs#L297-L305); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-ops/src/chunked_array/cov.rs#L28-L43](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-ops/src/chunked_array/cov.rs#L28-L43). Read at tag py-2.1.0 (commit 7f902bd3). Unverified: what the SQL layer (polars-sql) returns for no pairs; only the Rust paths were read.

## <a id="polars-cov"></a>polars-cov. `cov`: two-pass blocks with Chan merge; Welford when streaming

polars py-2.1.0 · aggregates · open · `cov` · #54, #85

`CovState` follows `var` (polars-var-std): two-pass per block of 128 merged by Chan's combine in memory, Welford's update in the streaming reducer. A weight at most `ddof` is null. `CovState` does not clamp.

Reference:

`AggFn.cov` (`covOf`) is two-pass: the two means, then the products of the deviations added in list order from +0.0, by n or n - 1. No pairs is NULL, and so is a sample of one pair. Engines may differ in the last bits (#54) until #85 bounds the error.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/cov.rs](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/cov.rs). Read at tag py-2.1.0 (commit 7f902bd3).

## <a id="polars-mean-float"></a>polars-mean-float. `mean` of floats: the sum by the count

polars py-2.1.0 · aggregates · open · `mean`, `avg` · #54, #85

`mean` is the sum (polars-sum-float, pairwise or Kahan by path) divided by the count.

Reference:

`AggFn.avg` is `floatSum` / n, NULL without values.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L867-L891](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L867-L891); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L194-L215](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L194-L215). Read at tag py-2.1.0 (commit 7f902bd3).

## <a id="polars-sum-float"></a>polars-sum-float. `sum` of floats: pairwise, Kahan when grouped

polars py-2.1.0 · aggregates · open · `sum` · #54, #85

A full aggregation sums pairwise: blocks of 128 in 16 SIMD stripes, combined pairwise, the remainder added in turn. Groups of indices use Kahan summation with a finiteness guard. Streaming merges partial sums plainly.

The sum of no values (or only nulls) is 0 in the Series API.

Reference:

`AggFn.fsum` (`floatSum`) adds the doubles one by one in list order from +0.0; the writers that need that order exactly use `Dialect.float_sum`. NULL without values.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L194-L215](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L194-L215); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L254-L265](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/float_sum.rs#L254-L265); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-utils/src/kahan_sum.rs](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-utils/src/kahan_sum.rs); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L867-L891](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L867-L891). Read at tag py-2.1.0 (commit 7f902bd3). Unverified: the sum of no values through polars-sql.

## <a id="polars-var-std"></a>polars-var-std. `var` and `std`: two-pass blocks of 128, or Welford, by path

polars py-2.1.0 · aggregates · open · `var`, `std` · #54, #85

Ungrouped: two-pass per block of 128 values (`mean = alg_sum(x) / n`, then `dp = alg_sum((x - mean)^2)`; `alg_sum` is a plain left fold, reassociated only on nightly Rust), blocks merged in turn by Chan's combine. The chunks of a ChunkedArray merge the same way.

Grouped, in memory: groups of indices use Welford's online variance; slice groups use the block algorithm; overlapping slices use rolling `VarState` windows. The streaming reducers insert one value at a time (Welford) or combine per chunk. So grouped and ungrouped results come from different algorithms.

A weight at most `ddof` is null: no values is null, the sample variance of one value is null, the population variance of one value is 0. `VarState::finalize` clamps a negative variance to 0 and propagates NaN; the Welford path does not clamp.

Reference:

`AggFn.var` (`varOf`, `SubstraitLean/Aggregate.lean`) is two-pass with native doubles in list order: the mean (`floatSum` / n), then the squared deviations from it, added from +0.0, by n or n - 1, and never below 0. A sample of one value is NULL. Only NULL and the sign are exact; engines may differ in the last bits (#54) until #85 bounds the error.

Checked:

- 2026-11-03, source-reading, by coordinator subagent of session local_974f7865 (aggregate-algorithms research): [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L37](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L37); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L71-L83](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L71-L83); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L105-L118](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L105-L118); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L120-L133](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L120-L133); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L629-L644](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-compute/src/moment.rs#L629-L644); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/chunked_array/ops/aggregate/var.rs#L17-L23](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/chunked_array/ops/aggregate/var.rs#L17-L23); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-arrow/src/legacy/kernels/take_agg/var.rs#L11-L40](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-arrow/src/legacy/kernels/take_agg/var.rs#L11-L40); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L1033-L1110](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-core/src/frame/group_by/aggregations/mod.rs#L1033-L1110); [https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/var_std.rs](https://github.com/pola-rs/polars/blob/py-2.1.0/crates/polars-expr/src/reduce/var_std.rs). Read at tag py-2.1.0 (commit 7f902bd3).
