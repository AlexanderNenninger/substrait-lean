# Float error bounds: model and dependency

Epic #85 asks for proved error bounds for sharded floating-point `SUM` and
`AVG`, so that `--shard` can split them with a stated tolerance instead of
refusing. Stage 1 is the choice of a floating-point model and of where it
lives. This note records it.

## Decision

* **A separate Lake package, `float-bounds/`**, that depends on Mathlib
  (`v4.35.0`, the tag for our toolchain). The core package `SubstraitLean`
  stays free of Mathlib: its build, CI cache and toolchain pin are unchanged,
  and `float-bounds` fetches Mathlib's prebuilt oleans (`lake exe cache get`).
* **Our own minimal model**, the standard model of rounding (Higham §2.2),
  in `float-bounds/FloatBounds/Model.lean`: without overflow,
  `fl(x) = x · (1 + δ)` with `|δ| ≤ u = 2⁻⁵³`. It is a structure
  (`StdModel`) that theorems take as a hypothesis, not an axiom.
* **The link to native floats is a separate trusted assumption** (stage 2):
  that Lean's `Float.add`, which `FloatCode.lift₂` uses, rounds as some
  `StdModel` does on finite inputs. It plays the role `Impl.Faithful` plays
  for guard elimination.

## Alternatives considered

* *Mathlib in the core package.* Simplest to wire, but every build pulls
  Mathlib, the toolchain would follow Mathlib's releases, and cold CI builds
  get much slower.
* *FloatSpec (a Flocq port) or Flean.* More faithful (round to nearest even,
  ulps), but they pin other Lean versions and are incomplete. The standard
  model is all the summation bounds need; it can later be derived from one of
  them instead of assumed.

## Done in stage 1

`StdModel.add_error`: one rounded addition is within `u · |a + b|` of the
exact sum. It builds in CI (job `float-bounds`) and with
`poe prove-floats` locally, which is not part of `poe qa` because of the
Mathlib download.

## Next stages

2. State the trusted link from `FloatCode` / `Float.add` to a `StdModel`.
3. Sequential bound: `floatSum` of `n` values is within `γₙ₋₁ · Σ|xᵢ|` of the
   exact sum, `γₙ = n·u / (1 − n·u)`, when no partial sum overflows.
4. Two-phase bound for shards of sizes `n₁ … n_k`: `γ_{max nᵢ + k − 1} · Σ|xᵢ|`,
   and `AVG` with one more rounded division.
5. Report it: a `--shard` mode that splits float `SUM`/`AVG` and marks those
   columns as within the bound, with `sverify.partition` summing `|x|`
   alongside the partials.
