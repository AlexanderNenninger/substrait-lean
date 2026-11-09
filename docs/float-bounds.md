# Float error bounds

Doubles round. Sverify models them exactly where it can (comparisons, `MIN`,
`MAX`), computes `+ − × ÷` as the exact result rounded once ([double arithmetic](reference-semantics.md#floating-point)),
and computes `pow`, `log` and the other libm functions with Lean's native
`Float`. Proved error bounds cover the aggregates that add up doubles: `SUM`,
`AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`. This note records the model,
where the proofs live, and what each bound says.

## Where the proofs live

The proofs are in a separate Lake package, [`float-bounds/`](../float-bounds),
that depends on Mathlib (`v4.35.0`, the tag for our toolchain). The core
package `SubstraitLean` stays free of Mathlib, so its build, CI cache and
toolchain pin are unchanged. CI's `float-bounds` job builds the package with
Mathlib's prebuilt oleans; `poe prove-floats` does the same locally. It is
not part of `poe qa`, because of the Mathlib download.

The core cross-references the bound formulas to the proofs here and proves
the arithmetic ones itself (`core/Sverify/Core/FloatArith.lean`);
`FloatCode.exp_fin` stays a trusted fact, next to its other trust in native
`Float` (`core/Sverify/Core/Float.lean`).

## The model of rounding

[`Model.lean`](../float-bounds/FloatBounds/Model.lean) states the standard
model of rounding (Higham, *Accuracy and Stability of Numerical Algorithms*,
§2.1) with its underflow term: without overflow, a rounded result is the
exact one `z` up to

    |fl(z) − z| ≤ u · (|z| + tiny),   u = 2⁻⁵³, tiny = 2⁻¹⁰²²,

where `u · tiny = 2⁻¹⁰⁷⁵` is half the spacing of the subnormals. Without that
term, no rounding meets the model: `2⁻¹⁰⁸⁰` rounds to `0` or `2⁻¹⁰⁷⁴`.
Rounding also keeps the sign of a result, as rounding to nearest does.
`StdModel` is a structure that theorems take as a hypothesis.
`γ n = n·u / (1 − n·u)` bounds the relative error of `n` roundings.

[`Link.lean`](../float-bounds/FloatBounds/Link.lean) states the trusted link to
Lean's `Float`: `NativeLink` says that addition, subtraction,
multiplication, division and square root of finite doubles round as one
`StdModel` does, and give a finite double when the exact result is at most the
largest finite double. This is IEEE 754 binary64 with round to nearest. Like
`Impl.Faithful` in `analysis/Sverify/Analysis/Guards.lean`, it is a hypothesis.
`native_sum_error` and `native_avg_error` apply the bounds below to a fold of
native doubles, `xs.foldl (· + ·) 0`, which is what `floatSum` computes.
Since Lean 4.35, `Float` has a logical model in the kernel
(`Init/Data/Float/Model`), so the link could be proved from it once Lean has
lemmas about that model.

## `SUM` and `AVG`

[`Sum.lean`](../float-bounds/FloatBounds/Sum.lean), with
`mag xs = Σ (|xᵢ| + tiny)`:

| Theorem | Bound |
|---|---|
| `sum_error` | `\|Σ̃ xs − Σ xs\| ≤ γ n · mag xs` |
| `sharded_error` | `k` shards of at most `m` values, added in two phases: `γ (m + k) · (mag xs + k · tiny)` |
| `avg_error` | the mean: `γ (n + 2) · mag xs / n` |
| `sharded_avg_error` | the sharded mean: `γ (m + k + 2) · (mag xs + k · tiny) / n` |
| `sum_error_of_bound`, `avg_error_of_bound` | with every `\|xᵢ\| ≤ B`: `γ n · n · (B + tiny)` and `γ (n + 2) · (B + tiny)` |

Each assumes that no partial result overflows, as a condition on the exact
values, `(1 + γ) · mag xs ≤ maxFinite`. With `sum_error`, `sharded_error`
bounds how far a sharded sum is from the sequential one.

[`Core.lean`](../float-bounds/FloatBounds/Core.lean) proves the bounds of the
sequential sum in the integer form the contract checker uses (a value `x` scaled to
`x · 2¹⁰⁷⁴`): `core_sum` and `core_avg`. A sum of `n ≤ N` values in
`[lo, hi]`, with `N ≤ 2³²` and `|x| ≤ 2⁴⁰⁰`, lies in
`[min(lo, N·lo) − τ, max(hi, N·hi) + τ]`, and their mean in
`[lo − τ', hi + τ']`, where `τ = sumTolScaled N Bs / 2¹⁰⁷⁴` and
`τ' = avgTolScaled N Bs / 2¹⁰⁷⁴` round the bounds above up. They allow for the
decoding of codes with more than 53 significant bits (`Decoded`). `core_sign`
keeps signs exact: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.

## Sharded `SUM` and `AVG`

`--shard` with `float_order="any"`, and `sverify.engines.run_sharded` with a
`reproducible=` that accepts a tolerance on doubles, add each
shard's doubles, then the partial sums (`floatPartial`, `floatCombine` in
`analysis/Sverify/Analysis/Partition.lean`), where the reference adds all of them in one
pass. [`Shard.lean`](../float-bounds/FloatBounds/Shard.lean) bounds the
difference from what the partial rows report:

| Theorem | Bound |
|---|---|
| `sharded_near` | two phases against one pass over the same `n` values in any order: `(γ (m + k) + γ n) · (mag xs + k · tiny)` |
| `sharded_avg_near` | the same for the means: `(γ (m + k + 2) + γ (n + 2)) · (mag xs + k · tiny) / n` |
| `mag_le_absSum`, `mag_flatten_le` | the shards' rounded `SUM(\|x\|)`s, adding up to `A`, bound the magnitude: `(1 − γ m) · mag xs ≤ A + n · tiny` |
| `shardTol_le`, `shardAvgTol_le` | both bounds with `mag xs ≤ (A + n · tiny) / (1 − γ m)`, scaled by `2¹⁰⁷⁴` and rounded up: `shardTolScaled n m k As`, `shardAvgTolScaled` |
| `core_shard_sum`, `core_shard_avg` | the same in the core's integer form, for codes of magnitude at most `Bs` with `n ≤ 2³²` and `n (Bs + 2·2⁵²) ≤ 2²⁰⁹⁶` |
| `sharded_near_of_bound`, `sharded_avg_near_of_bound` | before running, with at most `N` values, each `\|x\| ≤ B`, in at most `k` shards: `(γ (N + k) + γ N) · (N (B + tiny) + k · tiny)` and `(γ (N + k + 2) + γ (N + 2)) · (B + tiny + k · tiny)` |

Each shard reports `SUM(|x|)`, `COUNT(x)` and `MAX(|x|)` per split double,
after the columns `floatCombine` reads (`floatBoundParts`). The counts give
`n`, `m` and `k`, the `SUM(|x|)`s give `A`, and the `MAX(|x|)`s show the
values far from overflow. These bound an engine's own two-phase sum. The
core proves Lean's own split on integers, without axioms
(`twoPhaseSum_near`, `twoPhaseAvg_near` in `Partition.lean`, the mean with
`FloatCode.div_scaled_err` for its division), and `floatSplit_sum` and
`floatSplit_avg` apply them to a group's shards:
`floatPartial`'s `SUM` and `COUNT`, combined as `floatCombine` combines them,
against the measure on the whole group. `absPart_eval` says what the
`SUM(|x|)` column holds.

`run_sharded(..., tolerance=True)` computes the bound per group from the
partial rows, with exact rationals, and `sverify.partition.apriori_tolerance`
gives it before running from a row cap and a bound on `|x|`. A bounded column
is a plain copy of a split `SUM` or `AVG`; an expression of one gets no
bound, and a `HAVING` that reads one may keep a group near its threshold that
the reference drops (`Sharded.rows_exact`). The bound is about the two-phase
plan as Lean evaluates it, each shard adding its values in one pass.

## `VARIANCE`, `STDDEV`, `COVAR` and `CORR`

Engines compute the co-moment `C = Σ (xᵢ − x̄)(yᵢ − ȳ)` (the variance is the
case `y = x`) with different algorithms, and none documents which. The bounds
assume no particular one. Each of the three common algorithms is within the
same, generous bound

    |Ĉ − C| ≤ 64 · n² · u · B²

for `n ≤ 2³²` pairs, all at most `B` in magnitude, with `2⁻⁵⁰⁰ ≤ B ≤ 2⁴⁰⁰`
(`Scale`; raising `B` is always allowed):

| Algorithm | Theorem | Used by |
|---|---|---|
| Two-pass: the means, then `Σ (xᵢ − x̄)(yᵢ − ȳ)` added in order | `twoPass_error` ([`TwoPass.lean`](../float-bounds/FloatBounds/TwoPass.lean)) | Lean's reference (`sqDevSum`, `coDevSum`) |
| Textbook: `Σxy − Σx · Σy / n` | `textbook_error` ([`Textbook.lean`](../float-bounds/FloatBounds/Textbook.lean)) | the weakest, absolute error `O(n · u · Σx²)` |
| Welford's update and Chan's merge, in any tree | `plan_good` ([`Welford.lean`](../float-bounds/FloatBounds/Welford.lean)) | DuckDB, in its order of operations |

`64 · n² · u · B²` is of the form `γ_{cn} · Σxᵢ²` with `Σxᵢ² ≤ n · B²`. If an
engine ever pins its algorithm, a tighter bound for that one can come later.

[`Variance.lean`](../float-bounds/FloatBounds/Variance.lean) derives the
results from any co-moment within `E` of `C`:

- `covar_error`: `VAR_*` and `COVAR_*` divide by `d = n` or `n − 1`, within
  `E / d + 3u · Cm / d` of `C / d`, where `|C| ≤ Cm`.
- `stddev_error`, `stddev_le`: `STDDEV_*`, the square root of a variance
  within `E`, is within `√E + u · (√V + √E + tiny)`, and at most
  `(1 + u)·√W + u · tiny` for any upper bound `W` of the variance.
- `corr_le`: `CORR` is at most `1 + 3E/L + 8u` in magnitude when the
  co-moments of both sides are at least `L ≥ 8E` (Cauchy–Schwarz,
  `sq_comoment_le`). Without such a lower bound it can be any double: with
  `Sxx` or `Syy` near `0`, `C / √(Sxx · Syy)` divides rounding errors by
  almost nothing.

## In contracts

The contract checker uses `floatSumCR_mem`, `floatAvgCR_mem` and
`floatSumCR_sign` (`core/Sverify/Core/FloatExact.lean`), theorems about the
reference's correctly rounded sum, with the tolerances
`FloatCode.sumTolScaled` and `avgTolScaled` defined there as here.
`core_sum`, `core_avg` and `core_sign` prove the same bounds here for the
sequential sum. They cost a few integer operations per measure.

- Signs are exact: a `SUM` or `AVG` of doubles `≥ 0` is `≥ 0`, and of
  doubles `≤ 0` is `≤ 0`.
- The reference rounds the exact sum or mean once, and rounding is monotone, so an
  `AVG` of finite doubles in `[lo, hi]` lies in `[lo, hi]` rounded, which is
  `[lo, hi]` itself where `lo` and `hi` are doubles: the mean of `cpu` in
  `[0, 100]` is in `[0, 100]` (`crBound`, `crBound_sound`,
  `FloatCode.ofExactDiv_mul`). A mean needs no row count.
- A `SUM` needs one. `sv.max_rows(n)` in `requires` caps an input
  and is checked on the data (`COUNT(*) <= n`), or proved from the record
  counts of a Delta or Iceberg table's files. The same cap proves integer
  `SUM`s fit 64 bits ([Row caps](tasks.md#row-caps)). The checker reads capped
  tables through a `FETCH` of `n` rows (`Rel.capReads`), which keeps their
  rows (`Rel.capReads_eval`), and bounds every relation's rows from it
  (`Rel.maxRows`, `Rel.maxRows_sound`). With a cap `n`, a `SUM` of doubles
  in `[lo, hi]` lies in `[min(lo, n·lo), max(hi, n·hi)]` rounded once.
- The sequential sum's tolerances hold too: with a cap `n ≤ 2³²` and an input interval
  `[lo, hi]` within `2⁴⁰⁰`, a `SUM` lies in `[min(lo, n·lo) − τ, max(hi, n·hi) + τ]`
  and an `AVG` in `[lo − τ', hi + τ']` (`floatSumCR_mem`, `floatAvgCR_mem`).
  Rounded once, the result lies inside them, so they add nothing.
  `floatBound` (`Measure.abs`) is the bound above, with the sign kept where
  the values have no finite bound or a `SUM` no cap (`signBound`).
- Casts carry these bounds on. A cast to an integer truncates both ends of
  the interval, so `CAST(AVG(cpu) AS BIGINT)` is in `[0, 100]`, and a cast
  to a decimal rounds them. Both are monotone, and `verify` reports no failed
  cast or overflow where the casts of the ends fit (`Rel.issuesCapped` decides
  every issue on the plan with capped reads, `Rel.hasIssue_capReads`). A
  `SUM` of integers cast to doubles adds the doubles they convert to, and
  their bounds are the conversions of the integers' bounds
  (`FloatCode.ofInt_mono`), so each conversion's rounding beyond `2⁵³` is in
  them already.
- `sv.approx(cond, rel=1e-6)` relaxes each comparison of a column with a
  number `k` in `cond` by `rel · max(1, |k|)`, for a bound that is not a
  double or an engine whose order of additions differs from the reference
  ([The engines' orders](#the-engines-orders-and-epsilon)). A report
  hints at it when an exact claim fails only by rounding.

A metrics rollup states its contract this way:

```python
@sv.transform(
    requires={"metrics": [_.cpu >= 0, _.cpu <= 100, _.cpu.notnull(), sv.max_rows(10_000_000)]},
    ensures=[_.cpu_avg >= 0, _.cpu_avg <= 100],
)
```

<a id="the-engines-orders-and-epsilon-444"></a>

## The engines' orders and `epsilon`

An engine may add a double `SUM` in another order than the reference, so a
contract's double `SUM` or `AVG` is `observed`: within a per-plan `ε` of a
result the reference allows. `substrait-check --contract` reports it per
output column (`"epsilon"`, `SubstraitLean/Epsilon.lean`), and
[`Epsilon.lean`](../float-bounds/FloatBounds/Epsilon.lean) proves it for every
order the engine profiles allow (`sum_order`):

| Behaviour | Algorithm | Theorem |
|---|---|---|
| `SEQUENTIAL`, `ANY`, `PAIRWISE` | a tree of rounded additions in any order (`FloatSums`, `core/Sverify/Core/AllowedP.lean`) | `Rnd.Tree.error`, `TreeSum.tree` ([`Tree.lean`](../float-bounds/FloatBounds/Tree.lean)) |
| `SCALED_CONSTANT` | DuckDB's constant run, one `fl(k · x)` ([duckdb-sum-double](../characterization/duckdb/facts/duckdb-sum-double.json)) | `TreeSum.const` |
| `COMPENSATED` | Kahan's sum, Polars's grouped sum in memory ([polars-sum-float](../engines/polars/facts/polars-sum-float.json)) | `Rnd.kahan_near` ([`Kahan.lean`](../float-bounds/FloatBounds/Kahan.lean)) |

Each is within `γ n · Σ (|xᵢ| + tiny)` of the exact sum, the sequential
sum's bound, for `n ≤ 2³²` doubles. For a tree, an error grows with the
additions on one value's path to the root (Higham, §4.2). For Kahan's sum the
proof is cruder than Knuth's `(2u + O(n u²)) Σ |xᵢ|`: each step after the
second adds at most `2u |x| + 3u · tiny + 14 u² A` to the error of `s − c`,
and the first two steps are exact or nearly so, which keeps `n = 3` within
`γ 3`. So two results of any of these orders are within twice the core's
tolerance of each other, and one of them is within the tolerance plus `u` of
the reference's correctly rounded sum, which `"epsilon"` reports:

| Theorem | `"epsilon"` |
|---|---|
| `epsilon_sum`, `epsilon_avg` | two engine orders: `2 · sumTolScaled N Bs`, `2 · avgTolScaled N Bs`, scaled by `2¹⁰⁷⁴` |
| `epsilon_sum_cr`, `epsilon_avg_cr` | `"abs"`, an engine order against the reference: `sumTolScaled N Bs + u · N · Bs`, `avgTolScaled N Bs + u · Bs` |
| `epsilon_sum_rel` | `"rel"` of a `SUM` of values of one sign: `2γ/(1 − γ)`, `γ = γ n` |
| `epsilon_avg_rel` | `"rel"` of an `AVG` of values of one sign whose mean is at least `2⁻¹⁰²²` in magnitude: `γ = γ (n + 2)` |

The relative bounds need more of IEEE 754 than the standard model has:
every rounded value is a multiple of `2⁻¹⁰⁷⁴`, and such a multiple rounds
with a relative error, since one below the normal range is a double
(`StdModel.Grid`; a sum that underflows is exact, Hauser 1996). The bounds
are proved once for a rounding `Rnd` with error `u · (|z| + τ)` on a set of
values closed under `+` and `−`: the standard model is `τ = tiny` on every
value, `Grid` is `τ = 0` on the multiples of `2⁻¹⁰⁷⁴`.

The checker marks a bound `"proved"` where these theorems cover it: every
engine's `sum_order` is in the table above, the plan has no `fp32` column
(Polars sums `Float32` in single precision), and the measure's argument,
filter and groups are the same values on every engine. A route that rests on
a proved bound has evidence `proved`, and the `sum_order` rows of DuckDB and
Polars cite `StdModel.epsilon_sum` ([realizability](realizability.md)).

### Against the correctly rounded sum

The reference's `SUM` of doubles is the exact sum of the values rounded once
([float aggregates](reference-semantics.md#of-doubles)),
and its `AVG` the exact mean rounded once (`floatSumCR`, `floatAvgCR`,
[`FloatExact.lean`](../core/Sverify/Core/FloatExact.lean)). The core computes
them on integers, since every finite double is a multiple of `2⁻¹⁰⁷⁴`, and
proves without axioms that the result is the nearest double
(`FloatCode.ofExactDiv_within`), within `u` of the exact value relatively
(`FloatCode.ofExact_rel`), monotone, and a function of the multiset
(`floatSumCR_perm`). `floatSumCR_mem`, `floatAvgCR_mem` and `floatSumCR_sign`
state the checker's bounds as theorems of it.

An engine's result is then within its order's bound of the exact sum plus
`u` of it:

| Theorem | Distance to the reference |
|---|---|
| `epsilon_sum_cr` | `sumTolScaled N Bs + u · N · Bs`, scaled by `2¹⁰⁷⁴` |
| `epsilon_avg_cr` | `avgTolScaled N Bs + u · Bs`, scaled by `2¹⁰⁷⁴` |

`float-bounds` cannot see the core's definitions, so the reference's value
enters these as a hypothesis, `|r − Σ| ≤ u · |Σ|`, which `ofExact_rel` proves
of it. `test_duckdb_is_within_the_bound_of_the_correctly_rounded_sum`
(`python/tests/test_float_bounds.py`) checks both against DuckDB and Python's
`math.fsum`.

### Through arithmetic

`"epsilon_by_engine"` carries each column's `ε` through the double arithmetic
between the aggregates and the output (forward mode).
[`Propagate.lean`](../float-bounds/FloatBounds/Propagate.lean) proves the
rules: the reference rounds the exact result `z` of its inputs once, the
engine rounds `z'` of its own, and `StdModel.transfer` adds the two roundings
to the difference `Δ` of the exact results. With `|a| ≤ ma`, `|b| ≤ mb`:

| Operation | Rule |
|---|---|
| `a ± b` (`rule_add`, `rule_sub`) | `(εa + εb)(1 + u) + 2u (ma + mb + tiny)` |
| `a · b` (`rule_mul`) | `(ma εb + mb εa + εa εb)(1 + u) + 2u (ma mb + tiny)` |
| `a / b`, `b` the same on both sides, `\|b\| ≥ lb > 0` (`rule_div`) | `(εa / lb)(1 + u) + 2u (ma / lb + tiny)` |
| Polars's `a / b` by a literal, `fl(a · fl(1/b))` (`rule_div_recip`) | `(εa / lb)(1 + u)² + (3u + u²) ma / lb + (u (1 + u)(ma + εa) + 2u) tiny` |
| `abs a`, `-a` (`rule_abs`) | `εa` |
| `FLOOR`, `CEIL`, `ROUND` (`rule_floor`, `rule_ceil`, `rule_round`) | `εa + 1` |
| a cast to an integer, by truncation (`rule_trunc`) | `εa + 2` |
| `sqrt a`, `a ≥ εa` on both sides (`rule_sqrt`) | `Δ (1 + u) + 2u (√ha + tiny)`, `Δ = min(√εa, εa / (√(la − εa) + √la))` |

A comparison is exact where the ranges of its sides, widened by their `ε`,
do not meet (`rule_threshold`): a filter, `CASE` condition, grouping key or
sort key on it keeps the same rows on both sides. Where they meet, the rows
may differ, and no column's bound below or after it is marked proved.

A comparison whose ranges meet can still be decided on the data.
[`Margin.lean`](../float-bounds/FloatBounds/Margin.lean) bounds a group's
sum against the reference's from its own row count `n` and `Σ |xᵢ|`, in any
order an engine adds: `(γₙ + u) · Σ(|xᵢ| + tiny)` (`StdModel.epsilon_group`).
The engine computes a check per group from its `SUM(ABS(x))` `A`:
`|fl(v − t)| > fl(cₙ · fl(A + n · tiny))`, `cₙ = (8n + 16) · 2⁻⁵³`, exact in
doubles but for its two roundings. A group that passes is farther than twice
the bound from `t` (`StdModel.check_sound`), so every evaluation of its sum,
the check's and the filter's, lies on the reference's side of `t`
(`margin_sound`, `StdModel.margin_check`). The factor 2 covers an engine
that computes the sum twice, in two orders.
An `AVG`'s threshold has the same check over `n`: the engine's mean is
within `(γₙ + 4u) · Σ(|xᵢ| + tiny) / n` of the reference's
(`StdModel.epsilon_group_avg`), and the check is
`|fl(v − t)| > fl(cₙ · fl(fl(A + n · tiny) / n))`, `cₙ = (8n + 32) · 2⁻⁵³`
(`StdModel.check_sound_avg`, `StdModel.margin_check_avg`).
A row's value against its partition's window `SUM` or `AVG` over the whole
partition (`x > AVG(x) OVER (PARTITION BY k)`) has the same check per row,
the bound from the partition's count and `Σ|x|`, the threshold the row's own
value. The check plan computes `v − t` and the margin once each in a
projection, so that an engine's SQL does not repeat a window's aggregate.
The checker writes the check as a plan of its own (`Rel.marginCheck`,
`"margin_checks"` of `--contract`), and the threshold filter it covers keeps
the reference's rows given it. `Report.run` runs it on the engine before the
plan: a flagged group refuses the run with a `PreconditionError` that counts
them, or, verified with `on_inferred="warn"`, a warning, the flagged groups
kept up to the bound, the warning counting them.
A double `SUM` of exact values with no row cap has no number that bounds
every group, but each group has its own bound: `"epsilon"` reports it as
`"per_group"`, proved by `StdModel.epsilon_group`, in place of a missing
`"abs"`.

Each column whose range leaves out zero also has a relative bound, `ε`
over the least magnitude of the reference's value. A difference of nearly
equal values has a range that reaches zero, so it gets none: cancellation
loses relative accuracy, and the report does not claim it.

`exp` is the platform's `libm` on both sides, which IEEE 754 does not
require to round correctly. `NativeLink.exp` trusts it to one ulp, as glibc's
manual states and the probes measured (0.502 ulp on macOS,
[duckdb-ulp-libm](../characterization/duckdb/facts/duckdb-ulp-libm.json)), and
`rule_exp` bounds `exp a`, `a ≤ ha`, by
`εa · exp(ha + εa)(1 + 2u) + 4u (exp ha + tiny)`. The other elementary
functions stay tested. The checker evaluates the formulas in
doubles; every term is nonnegative, so each rounding is relative, and a
factor `1 + 2⁻⁴⁰` covers them.

### One operation's bounds and overflow

The checker bounds a double `+`, `-`, `*` and `/` from its inputs' bounds
(`faddBound`, `fmulBound`, `fdivBound` in `analysis/Sverify/Analysis/Contracts.lean`), so
chains such as `(a + b) * c` have bounds, and a result the bounds keep below
the largest double needs no "stays finite" precondition on the data
(`BinFn.mayInf`). The core states one fact per operation on scaled values
and proves all but `exp_fin` in `FloatArith.lean`;
[`Arith.lean`](../float-bounds/FloatBounds/Arith.lean) proves each for native
doubles decoded within `2u` of the codes' values:

| Core fact | Theorem | Where | Result, against the exact one |
|---|---|---|---|
| `FloatCode.add_scaled`, `sub_scaled` | `core_add`, `core_sub` | `\|A\| + \|B\| ≤ 2¹⁰²³` | finite, within `(\|A\| + \|B\|) / 2⁵¹ + u · tiny` |
| `FloatCode.mul_scaled` | `core_mul` | `\|A B\| ≤ 2¹⁰²³` | finite, within `\|A B\| / 2⁵⁰ + u · tiny` |
| `FloatCode.div_scaled` | `core_div` | `B ≠ 0`, `\|A / B\| ≤ 2¹⁰²³` | finite, within `\|A / B\| / 2⁵⁰ + u · tiny` |
| `FloatCode.exp_fin` | `core_exp` | `A ≤ 709` | finite (`709 < 1023 · ln 2`) |
| `FloatCode.add_nonneg`, `mul_nonneg`, `div_nonneg` | `core_add_nonneg`, `core_mul_nonneg`, `core_div_nonneg` | as `add_scaled` …, and both inputs at least `0` (the divisor not `0`) | at least `0` |

Scaled by `2¹⁰⁷⁴`, `u · tiny` is `1/2`, which the core's integer forms round
up to `1`.

The error term alone would let the bound of `x * y`, `x + y` or `x / y` of
non-negative doubles dip below `0`. Rounding keeps the sign
(`StdModel.nonneg`), so the last row raises those bounds to `0`
(`faddBoundS` …): a revenue `SUM(qty * price)` of non-negative factors
is proved at least `0`.

## The generic properties of statistical aggregates

An engine's `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` have the generic
properties (`StatProps`, [reference
semantics](reference-semantics.md#statistical-aggregates)), and the
reference's own value is the exact moments rounded once
([statistical aggregates](reference-semantics.md#statistical-aggregates)), within half an
ulp of the exact value, so an engine is within these bounds plus that of it
(`Epsilon.statEps`).
[`CoreKappa.lean`](../float-bounds/FloatBounds/CoreKappa.lean) proves the
properties of Lean's native two-pass results:
`core_var_k`, `core_cov_k` and `core_corr_k` for two-pass on the decoded
doubles, and `core_stddev` with `sd_mono` for the deviation. Decoding moves a
co-moment by `2u (√(S_xx Q'_y) + √(S_yy Q'_x)) + 4u² √(Q'_x Q'_y)`
(`decode_cov`), which the bounds absorb. The bounds are the ones below, with
the constants rounded up to cover DuckDB's algorithm and the final division;
for `CORR` one witness `R` stands for all the square roots, which keeps the
statement small.

The generic bound, `128 n² u B²` with `B = max |xᵢ|`
([`CoreStats.lean`](../float-bounds/FloatBounds/CoreStats.lean)), does not
scale with the spread. For a variance it is about `128 · n · u · B²`: far
below the last digit that matters for CPU percentages (`B = 100`), and
`1.4 · 10⁴` for `10⁶` values near `10⁶` that vary by about `1` (timestamps in
seconds), against a variance of about `1`.

Bounds that scale with the spread are proved for three of the algorithms:

- Two-pass ([`TwoPassRel.lean`](../float-bounds/FloatBounds/TwoPassRel.lean),
  `twoPass_var_rel`): `|Ŝ − S| ≤ 8 n u S + 80 n² u² Σx² + 8 n² u · tiny`.
  The error of the mean adds `n ε²` to the sum of squares, because the
  deviations from the exact mean sum to `0`, so the bound is first order in
  `u` relative to `S` itself.
- Welford's update within one thread
  ([`WelfordRel.lean`](../float-bounds/FloatBounds/WelfordRel.lean),
  `welfordVar_rel`): `|Ŝ − S| ≤ 32 n u √(Q' S) + 104 n² u² Q' + 4 n u · tiny`,
  `Q' = Σ (|x| + tiny)²`. This is the first-order behaviour Chan, Golub and
  LeVeque (1983) describe. It needs the model to know that a double rounds
  to itself (`StdModel.idem`, `StdModel.zero`), which makes Welford's first
  step exact.
- DuckDB's parallel aggregation, Welford's update in each thread and Chan's
  merge of the threads' states in any order
  ([`MergeRel.lean`](../float-bounds/FloatBounds/MergeRel.lean),
  `chanVar_rel`): `|Ŝ − S| ≤ 148 n u √(Q' S) + 3961 n² u² Q' + 793 n u · tiny`.
  DuckDB's merge computes the mean with a fused multiply-add
  (`dmean_spec`). A merge of `a` and `b` values adds `2 min(a, b)` to a
  weight that stays below `2 n (⌈log₂ n⌉ + 1)` (`Lw_merge`), and the
  constants take `⌈log₂ n⌉ ≤ 32`.

The covariance has the same kind of bounds, with `S_xx`, `S_yy` the
co-moments of each side and `Q'_x = Σ (|x| + tiny)²`:

- Two-pass ([`CovTwoPass.lean`](../float-bounds/FloatBounds/CovTwoPass.lean),
  `twoPass_cov_rel`):
  `|Ĉ − C| ≤ 6 n u √(S_xx S_yy) + 1.1 u (√(Q'_y S_xx) + √(Q'_x S_yy)) + 120 n² u² √(Q'_x Q'_y) + 4 n² u · tiny`.
- DuckDB's parallel aggregation, Welford's update and the merge with the
  weighted mean ([`CovRel.lean`](../float-bounds/FloatBounds/CovRel.lean),
  `chanCov_rel`):
  `|Ĉ − C| ≤ 70 n u (√(Q'_x S_yy) + √(Q'_y S_xx)) + 11 n u √(S_xx S_yy) + 3961 n² u² √(Q'_x Q'_y) + 793 n u · tiny`.

By Cauchy–Schwarz every partial co-moment and every increment is at most
`√(S_xx S_yy)` (`comoment_sq_le`), which is what the proofs scale with.

For those timestamps (`10⁶` rows near `10⁶`, spread `1`), Welford's bound
on the variance is about `32 · 10⁶ · 1.1 · 10⁻¹⁶ · 10⁶ ≈ 3.6 · 10⁻³`, the
parallel one's about `1.6 · 10⁻²`, and two-pass's about `10⁻⁶`, against a
variance of `1`.


DuckDB's own results have the properties the reference allows:
[`Chan.lean`](../float-bounds/FloatBounds/Chan.lean) and
[`ChanCorr.lean`](../float-bounds/FloatBounds/ChanCorr.lean) prove them for
Welford's update with Chan's merge in any tree, as DuckDB computes them:

| Theorem | Property |
|---|---|
| `vEval_nonneg` | the co-moment is `≥ 0` |
| `core_var_chan` | `VAR_*` is `≥ 0` and within `varTol` (`STDDEV_*` follows by `core_stddev`) |
| `core_cov_chan` | `COVAR_*` is within `covTol` |
| `corr_duck_le`, `core_corr_chan` | DuckDB's `CORR`, `COVAR_POP / (STDDEV_POP_x · STDDEV_POP_y)` from three states, is at most `1 + 3E/L + 8u` |
| `epsilon_var_cr` | `"abs"` of a `VAR_*` against the reference: `varTol + u · abs(S / d)` |
| `epsilon_cov_cr` | `"abs"` of a `COVAR_*` against the reference: `covTol + u · abs(C / d)` |

`vEval_nonneg` needs two facts of IEEE rounding beyond the standard model:
rounding is monotone (`StdModel.Mono`), and doubles are multiples of `2⁻¹⁰⁷⁴`
that round relatively (`Grid`). With them Welford's new mean lies between the
old one and the value, so the two differences it multiplies have one sign.
DuckDB's and Spark's `stat_algo` rows cite `core_var_chan` ([realizability](realizability.md)).
Polars's algorithms (a reassociated two-pass per block, Schubert and Gertz's
merge) are not proved, and its row stays tested.

`Epsilon.statEps` reports these bounds per column: a `VAR_*`'s and a
`COVAR_*`'s are `epsilon_var_cr` and `epsilon_cov_cr` for ranges `[-B, B]`
(a pair's two sides each, `BinFn.pair`) and the row cap `n`, proved on the
engines `statsProvedOn` names (`"proved_on"`: DuckDB and Spark) and tested on
the others. A `STDDEV_*`'s goes through the square root, not mechanised.
`CORR` has none: its error grows as a side's variance shrinks, and ranges
give no lower bound on a variance. Snowflake's textbook formula on values
shifted by their group's mean is the corrected two-pass algorithm;
the shift keeps the reference's value (`momentNum_shift`), and its bound is
recorded privately.

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` keep their descriptions in the
checker ("a double ≥ 0 or NULL", "a double or NULL"): a useful upper bound of
the variance also needs Popoviciu's inequality, the arguments of `COVAR` and
`CORR` are pairs whose components the abstract domain does not bound, and no
contract can state the lower bound on the variances that `corr_le` needs.

## Checking the proofs

```bash
uv run --project python poe -C python prove-floats
```

The package builds in about a minute on a laptop once Mathlib's oleans are
fetched, and every theorem depends only on Lean's standard axioms.

## Alternatives considered

- Mathlib in the core package: simplest to wire, but every build would pull
  Mathlib, the toolchain would follow Mathlib's releases, and cold CI builds
  would get much slower.
- FloatSpec (a Flocq port) or Flean: more faithful (round to nearest even,
  ulps), but they pin other Lean versions and are incomplete. The standard
  model is all the bounds need; it can later be derived from one of them, or
  from Lean's own `Float` model.
