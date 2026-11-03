# Float error bounds

Doubles round. Sverify models them exactly where it can (comparisons, `MIN`,
`MAX`) and computes their arithmetic with Lean's native `Float`. Epic #85
adds proved error bounds for the aggregates that add up doubles: `SUM`,
`AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`. This note records the model,
where the proofs live, and what each bound says.

## Where the proofs live

The proofs are in a separate Lake package, [`float-bounds/`](../float-bounds),
that depends on Mathlib (`v4.35.0`, the tag for our toolchain). The core
package `SubstraitLean` stays free of Mathlib, so its build, CI cache and
toolchain pin are unchanged. CI's `float-bounds` job builds the package with
Mathlib's prebuilt oleans; `poe prove-floats` does the same locally. It is
not part of `poe qa`, because of the Mathlib download.

The core uses the bound formulas as trusted facts, next to its other trust in
native `Float` (`SubstraitLean/Float.lean`), and cross-references them to the
proofs here.

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
Lean's `Float` (stage 2): `NativeLink` says that addition, subtraction,
multiplication, division and square root of finite doubles round as one
`StdModel` does, and give a finite double when the exact result is at most the
largest finite double. This is IEEE 754 binary64 with round to nearest. Like
`Impl.Faithful` in `SubstraitLean/Guards.lean`, it is a hypothesis.
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
| `sum_error` (stage 3) | `\|Σ̃ xs − Σ xs\| ≤ γ n · mag xs` |
| `sharded_error` (stage 4) | `k` shards of at most `m` values, added in two phases: `γ (m + k) · (mag xs + k · tiny)` |
| `avg_error` | the mean: `γ (n + 2) · mag xs / n` |
| `sharded_avg_error` | the sharded mean: `γ (m + k + 2) · (mag xs + k · tiny) / n` |
| `sum_error_of_bound`, `avg_error_of_bound` | with every `\|xᵢ\| ≤ B`: `γ n · n · (B + tiny)` and `γ (n + 2) · (B + tiny)` |

Each assumes that no partial result overflows, as a condition on the exact
values, `(1 + γ) · mag xs ≤ maxFinite`. With `sum_error`, `sharded_error`
bounds how far a sharded sum is from the sequential one.

[`Core.lean`](../float-bounds/FloatBounds/Core.lean) proves the two facts the
contract checker trusts, in the integer form it uses (a value `x` scaled to
`x · 2¹⁰⁷⁴`): `core_sum` and `core_avg`. A sum of `n ≤ N` values in
`[lo, hi]`, with `N ≤ 2³²` and `|x| ≤ 2⁴⁰⁰`, lies in
`[min(lo, N·lo) − τ, max(hi, N·hi) + τ]`, and their mean in
`[lo − τ', hi + τ']`, where `τ = sumTolScaled N Bs / 2¹⁰⁷⁴` and
`τ' = avgTolScaled N Bs / 2¹⁰⁷⁴` round the bounds above up. They allow for the
decoding of codes with more than 53 significant bits (`Decoded`). `core_sign`
keeps signs exact: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.

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

The contract checker trusts `core_sum`, `core_avg` and `core_sign` as three
axioms in `SubstraitLean/Aggregate.lean` (`floatSum_mem`, `floatAvg_mem`,
`floatSum_sign`), with the tolerances `FloatCode.sumTolScaled` and
`avgTolScaled` defined there as here. They cost a few integer operations per
measure. `#print axioms Substrait.contract_sound` lists them.

- Signs are exact: a `SUM` or `AVG` of doubles `≥ 0` is `≥ 0`, and of
  doubles `≤ 0` is `≤ 0`.
- The bounds need a row count. `sv.max_rows(n)` in `requires` caps an input
  and is checked on the data (`COUNT(*) <= n`). The checker reads capped
  tables through a `FETCH` of `n` rows (`Rel.capReads`), which keeps their
  rows (`Rel.capReads_eval`), and bounds every relation's rows from it
  (`Rel.maxRows`, `Rel.maxRows_sound`).
- With a cap `n ≤ 2³²` and an input interval `[lo, hi]` within `2⁴⁰⁰`, a
  `SUM` lies in `[min(lo, n·lo) − τ, max(hi, n·hi) + τ]` and an `AVG` in
  `[lo − τ', hi + τ']` (`floatBound`, `Measure.abs`).
- `sv.approx(cond, rel=1e-6)` relaxes each comparison of a column with a
  number `k` in `cond` by `rel · max(1, |k|)`. The default covers a `SUM` or
  `AVG` over any cap up to `2³²` rows. A report hints at it when an exact
  claim fails only by rounding.

The homelab metrics rollup states its contract this way:

```python
@sv.transform(
    requires={"metrics": [_.cpu >= 0, _.cpu <= 100, _.cpu.notnull(), sv.max_rows(10_000_000)]},
    ensures=[_.cpu_avg >= 0, sv.approx(_.cpu_avg <= 100)],
)
```

## The generic properties of statistical aggregates

The reference allows any result of `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`
with the generic properties (`StatProps`, [reference
semantics](reference-semantics.md#statistical-aggregates)). Lean's own results
have them by three trusted facts in `SubstraitLean/StatProps.lean`
(`varOf_props`, `covOf_props`, `corrOf_props`), stated over Lean's `Rat`.
[`CoreStats.lean`](../float-bounds/FloatBounds/CoreStats.lean) proves them:
`core_var`, `core_stddev`, `core_cov` and `core_corr`, for two-pass on the
decoded doubles, with `E = 128 n² u B²`, which covers the decoding
(`comoment_decoded`, `12 n B δ`) and `64 n² u B'²` with `B' = (1 + 2u) B`.

How loose this is depends on how far the values sit from zero relative to
their spread. For a variance the bound is about `128 · n · u · B²`, or
`1.4 · 10⁻⁸ · B²` at `10⁶` rows and `1.4 · 10⁻⁶ · B²` at `10⁸`. For CPU
percentages (`B = 100`, a variance in the hundreds) that is far below the last
digit that matters. For values near `10⁶` that vary by about `1` (timestamps in
seconds, say), it is `1.4 · 10⁴` at `10⁶` rows, against a variance of about
`1`: no useful bound.

The expected first-order behaviour of Welford's algorithm and of two-pass is
`|Ŝ − S| ≲ c · n · u · √(S · Σx²)` (Chan, Golub and LeVeque, 1983), which
scales with the spread and stays useful there; its proof is in progress. A
tighter proved bound only narrows the allowed set, so it replaces this one
without changing the interface.

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
