import Sverify.Core.Aggregate

/-!
# What a statistical aggregate may give (#85)

`VARIANCE`, `STDDEV`, `COVAR_SAMP`/`COVAR_POP` and `CORR` are computed by each
engine's own algorithm, and none documents which (DuckDB, Spark and grouped
Polars use Welford's update with Chan's merge, ungrouped Polars a blockwise
two-pass). Before D30 the reference allowed any value with the generic
properties every reasonable algorithm keeps; since D30 it is the exact moments
rounded once, and these properties (`StatProps`) are what an engine's
algorithm may give (`SubstraitLean/AllowedP.lean`). An engine profile may
name a stricter algorithm (`Profile.statAlgo`); without one, these hold.

For `n ≤ 2³²` finite values at most `2³⁹⁸` in magnitude, with `u = 2⁻⁵³`,
the exact co-moments `C = Σxy − Σx · Σy / n`, `S_xx`, `S_yy`, and
`Q' = Σ (|xᵢ| + tiny)²` of each side:

* `NULL` exactly where the reference says: no values, a sample of one value,
  and for `CORR` fewer than two pairs or a side whose values are all equal;
* a variance or deviation is `≥ 0`;
* `VAR_*`, `S / d` with `d = n − 1` (sample) or `n` (population), is within
  `(160 n u √(Q' S) + 3970 n² u² Q' + 800 n² u · tiny) / d` (`varTol`);
* `COVAR_*`, `C / d`, is within
  `(71 n u (√(Q'_x S_yy) + √(Q'_y S_xx)) + 15 n u √(S_xx S_yy) + 3970 n² u² √(Q'_x Q'_y) + 800 n² u · tiny) / d`
  (`covTol`);
* `STDDEV_*` is within `(1 ± u)` of `√(V ± τ)`, stated squared;
* `|CORR| ≤ 1 + 3E/L + 8u`, `E = 447 n u R + 11883 n² u² (Q'_x + Q'_y) + 2379 n² u · tiny`
  (`corrErr`), for an `R` at least `√(Q' S)` of each side, `√(Q'_x S_yy)`,
  `√(Q'_y S_xx)` and `√(S_xx S_yy)`, when the co-moments of both sides are
  at least `L ≥ 8E` (and `L ≥ 2⁻⁵⁰⁰`, their product at most `2¹⁰⁰⁰`).
  Without such a lower bound `CORR` may be any double.

The core has no square roots, so each property holds for every rational
witness `r ≥ 0` with `r² ≥` the product it bounds. The bounds scale with the
spread of the values: they stay small for values far from zero that vary
little. They hold for the two-pass algorithm (the reference's own,
`twoPass_var_rel`, `twoPass_cov_rel`) and for Welford's update with Chan's
merge in any tree, in DuckDB's order of operations (`chanVar_rel`,
`chanCov_rel`; with `core_var_chan`, `core_cov_chan` and `core_corr_chan` the
properties themselves, DuckDB's `CORR` formula included), all in
`float-bounds/`. The textbook formula `Σx² − (Σx)²/n`
cancels catastrophically and is not covered. Outside the finite range above,
the reference's own value is the one allowed.

Since D30 the reference's own value is one value, the exact moments rounded
once (`varOf`, `covOf`, `corrOf` in `Aggregate.lean`), and `StatProps` is what
an engine's algorithm may give (`StatAlgo "GENERIC"` and `"WELFORD_CHAN"`,
`SubstraitLean/AllowedP.lean`). The three axioms that made Lean's native
two-pass results meet these properties (`varOf_props`, `covOf_props`,
`corrOf_props`) are retired with it.
-/

namespace Substrait.Stat

/-- The unit roundoff, `2⁻⁵³`. -/
def u : Rat := 1 / 2 ^ 53

/-- The smallest normal double, `2⁻¹⁰²²`. -/
def tiny : Rat := 1 / 2 ^ 1022

/-- The value of a finite double code (`FloatCode.scaled` is it times `2¹⁰⁷⁴`). -/
def val (c : Int) : Rat := (FloatCode.scaled c : Rat) / 2 ^ 1074

def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- `Q' = Σ (|xᵢ| + tiny)²`, the magnitude the bounds scale with. -/
def qsum (xs : List Rat) : Rat := (xs.map fun x => (absQ x + tiny) ^ 2).sum

/-- The co-moment `Σxy − Σx · Σy / n` of exact values. -/
def comoment (ps : List (Rat × Rat)) : Rat :=
  (ps.map fun p => p.1 * p.2).sum - (ps.map (·.1)).sum * (ps.map (·.2)).sum / ps.length

/-- The error bound of `VAR_*`, `S / d`, for an `r ≥ √(Q' S)`. -/
def varTol (n d : Nat) (r Q : Rat) : Rat :=
  (160 * n * u * r + 3970 * n ^ 2 * u ^ 2 * Q + 800 * n ^ 2 * u * tiny) / d

/-- The error bound of `COVAR_*`, `C / d`, for `r₁ ≥ √(Q'_x S_yy)`,
`r₂ ≥ √(Q'_y S_xx)`, `r_s ≥ √(S_xx S_yy)` and `r_q ≥ √(Q'_x Q'_y)`. -/
def covTol (n d : Nat) (r1 r2 rs rq : Rat) : Rat :=
  (71 * n * u * (r1 + r2) + 15 * n * u * rs + 3970 * n ^ 2 * u ^ 2 * rq
    + 800 * n ^ 2 * u * tiny) / d

/-- The error bound of the three co-moments of `CORR`, for an `R` at least
`√(Q' S)` of each side, `√(Q'_x S_yy)`, `√(Q'_y S_xx)` and `√(S_xx S_yy)`, and
`Q = Q'_x + Q'_y`. -/
def corrErr (n : Nat) (R Q : Rat) : Rat :=
  447 * n * u * R + 11883 * n ^ 2 * u ^ 2 * Q + 2379 * n ^ 2 * u * tiny

/-- At most `2³²` doubles, each at most `2³⁹⁸` in magnitude (finite). -/
def fits (cs : List Int) : Bool :=
  cs.length ≤ 2 ^ 32 && cs.all fun c => (FloatCode.scaled c).natAbs ≤ 2 ^ 1472

/-- A deviation `σ` near `√V` with `V` within `τ`: squared,
`(σ − u·tiny)² ≤ (1 + u)² (V + τ)` (where `σ > u·tiny`) and
`(1 − u)² (V − τ) ≤ (σ + u·tiny)²`. -/
def sdNear (σ V τ : Rat) : Prop :=
  (σ ≤ u * tiny ∨ (σ - u * tiny) ^ 2 ≤ (1 + u) ^ 2 * (V + τ)) ∧
    (1 - u) ^ 2 * (V - τ) ≤ (σ + u * tiny) ^ 2

/-- Every value a double. -/
def allInts (vs : List Value) : Prop := ∀ w ∈ vs, ∃ i, w = .float i

instance (vs : List Value) : Decidable (allInts vs) :=
  if h : vs.all (fun | .float _ => true | _ => false) then
    isTrue fun w hw => by
      have := List.all_eq_true.mp h w hw
      cases w <;> simp_all
  else isFalse fun h' => h (List.all_eq_true.mpr fun w hw => by
    obtain ⟨i, rfl⟩ := h' w hw; rfl)

/-- The properties of `VAR_*` (`sqrt = false`) or `STDDEV_*` of the doubles
`cs`, for a non-`NULL` result `c`: `≥ 0`, and within `varTol r` of
`V = S / d` for every `r ≥ √(Q' S)`. -/
def varProps (sample sqrt : Bool) (cs : List Int) (c : Int) : Prop :=
  let xs := cs.map val
  let d := if sample then cs.length - 1 else cs.length
  let S := comoment (xs.map fun x => (x, x))
  let Q := qsum xs
  0 ≤ c ∧ ∀ r : Rat, 0 ≤ r → Q * S ≤ r * r →
    let τ := varTol cs.length d r Q
    if sqrt then sdNear (val c) (S / d) τ else absQ (val c - S / d) ≤ τ

/-- The property of `COVAR_*` of the pairs `ps`, for a non-`NULL` result `c`:
within `covTol` of `C / d` for every set of witnesses. -/
def covProps (sample : Bool) (ps : List (Int × Int)) (c : Int) : Prop :=
  let qs := ps.map fun p => (val p.1, val p.2)
  let d := if sample then ps.length - 1 else ps.length
  let sx := comoment (qs.map fun q => (q.1, q.1))
  let sy := comoment (qs.map fun q => (q.2, q.2))
  let Qx := qsum (qs.map (·.1))
  let Qy := qsum (qs.map (·.2))
  ∀ r1 r2 rs rq : Rat, 0 ≤ r1 → 0 ≤ r2 → 0 ≤ rs → 0 ≤ rq →
    Qx * sy ≤ r1 * r1 → Qy * sx ≤ r2 * r2 → sx * sy ≤ rs * rs → Qx * Qy ≤ rq * rq →
    absQ (val c - comoment qs / d) ≤ covTol ps.length d r1 r2 rs rq

/-- The property of `CORR` of the pairs `ps`, for a non-`NULL` result `c`. -/
def corrProps (ps : List (Int × Int)) (c : Int) : Prop :=
  let qs := ps.map fun p => (val p.1, val p.2)
  let sx := comoment (qs.map fun q => (q.1, q.1))
  let sy := comoment (qs.map fun q => (q.2, q.2))
  let Qx := qsum (qs.map (·.1))
  let Qy := qsum (qs.map (·.2))
  ∀ R L : Rat, 0 ≤ R →
    (∀ a ∈ [Qx, Qy, sx], ∀ b ∈ [sx, sy], a * b ≤ R * R) →
    8 * corrErr ps.length R (Qx + Qy) ≤ L → 1 / 2 ^ 500 ≤ L → L ≤ sx → L ≤ sy →
      sx * sy ≤ 2 ^ 1000 →
      absQ (val c) ≤ 1 + 3 * corrErr ps.length R (Qx + Qy) / L + 8 * u

end Stat

open Stat

/-- `VAR_*` / `STDDEV_*` of `vs` may give `v`. -/
def varStat (sample sqrt : Bool) (vs : List Value) (v : Value) : Prop :=
  if vs = [] ∨ (sample = true ∧ vs.length = 1) then v = .null
  else if allInts vs ∧ fits (floatsOf vs) = true then
    ∃ c, v = .float c ∧ varProps sample sqrt (floatsOf vs) c
  else v = (AggFn.var sample sqrt).apply vs

/-- `COVAR_*` of `vs` may give `v`. -/
def covStat (sample : Bool) (vs : List Value) (v : Value) : Prop :=
  if (pairsOf vs).isEmpty = true ∨ (sample = true ∧ (pairsOf vs).length = 1) then v = .null
  else if fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true then
    ∃ c, v = .float c ∧ covProps sample (pairsOf vs) c
  else v = (AggFn.cov sample).apply vs

/-- `CORR` of `vs` may give `v`. -/
def corrStat (vs : List Value) (v : Value) : Prop :=
  if (pairsOf vs).length < 2 ∨ ((pairsOf vs).map (·.1)).all
        (· == ((pairsOf vs).map (·.1)).headD 0) = true ∨
      ((pairsOf vs).map (·.2)).all (· == ((pairsOf vs).map (·.2)).headD 0) = true then
    v = .null
  else if fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true then
    ∃ c, v = .float c ∧ corrProps (pairsOf vs) c
  else v = AggFn.corr.apply vs

/-- The values a statistical aggregate `f` of `vs` may give: `NULL` where the
reference says, otherwise a result with the generic properties for finite
values in range, and the reference's own value outside it. -/
def StatProps (f : AggFn) (vs : List Value) (v : Value) : Prop :=
  match f with
  | .var sample sqrt => varStat sample sqrt vs v
  | .cov sample => covStat sample vs v
  | .corr => corrStat vs v
  | _ => v = f.apply vs

/-! ## The NaN guard of a written variance (DD-3)

DuckDB's `VAR_POP` and `STDDEV_POP` of one value are `0` whatever the value,
NaN included (`duckdb-var-pop-one-value`, upstream DD-3), where `varStat`
asks for the reference's NaN. Sverify's SQL writes the aggregate as
`CASE WHEN n ≤ k THEN NULL WHEN COUNT(isnan(x)) > 0 THEN NaN ELSE body END`
(`nan_through` in `python/src/sverify/sql/core/_base.py`, grouped and
windowed), and raises on an infinity first (#257). `Stat.nanGuard` is that
expression; `Stat.nanGuard_varStat` says it gives what `varStat` allows
whenever the engine's `body` does on finite values. -/

namespace Stat

/-- The written variance: `NULL` for no values or a sample of one, NaN where
a value is NaN, else the engine's `body`. -/
def nanGuard (sample : Bool) (vs : List Value) (body : Value) : Value :=
  if vs = [] ∨ (sample = true ∧ vs.length = 1) then .null
  else if anyCode (fun c => decide (FloatCode.nan ≤ c)) vs then .float FloatCode.nan
  else body

set_option exponentiation.threshold 2100 in
/-- A NaN's code is past `fits`'s range. -/
private theorem not_fits_of_nan {vs : List Value} {c : Int} (hc : .float c ∈ vs)
    (hn : FloatCode.nan ≤ c) : fits (floatsOf vs) = false := by
  have hM : 2 ^ 1472 < FloatCode.maxMag := by
    rw [FloatCode.maxMag_def]
    exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by decide))
      (Nat.le_mul_of_pos_left _ (by decide))
  have hnan := nan_eq
  have hs : ¬ (FloatCode.scaled c).natAbs ≤ 2 ^ 1472 := by
    unfold FloatCode.scaled
    generalize (2 : Nat) ^ 1472 = A at hM ⊢
    generalize FloatCode.maxMag = M at hM hnan
    split <;> omega
  simp only [fits, Bool.and_eq_false_iff, List.all_eq_false]
  exact .inr ⟨c, mem_floatsOf.mpr hc, by simpa using hs⟩

/-- **The NaN guard is sound for `VAR_*` and `STDDEV_*`.** If the engine's
`body` meets `varStat` on finite values, the guarded expression meets it on
every input without an infinity (where the written plan raises, #257). -/
theorem nanGuard_varStat {sample sqrt : Bool} {vs : List Value} {body : Value}
    (hfin : (∀ c ∈ floatsOf vs, FloatCode.IsFin c) → varStat sample sqrt vs body)
    (hinf : ∀ c ∈ floatsOf vs, ¬ FloatCode.IsFin c → FloatCode.nan ≤ c) :
    varStat sample sqrt vs (nanGuard sample vs body) := by
  unfold nanGuard
  by_cases hd : vs = [] ∨ (sample = true ∧ vs.length = 1)
  · simp only [varStat, hd, ite_true]
  by_cases ha : anyCode (fun c => decide (FloatCode.nan ≤ c)) vs = true
  · obtain ⟨w, hw, hp⟩ := List.any_eq_true.mp ha
    cases w with
    | float c =>
      have hn : FloatCode.nan ≤ c := by simpa using hp
      have hnf : nonFinite vs = some FloatCode.nan := by simp [nonFinite, ha]
      have hs : (sample && vs.length == 1) = false := by
        cases sample <;> simp_all
      simp only [varStat, hd, ite_false, not_fits_of_nan hw hn, Bool.false_eq_true, and_false,
        ha, ite_true]
      rcases vs with _ | ⟨v0, vs'⟩
      · simp at hw
      · simp only [AggFn.apply, varOf, hs, hnf, Bool.false_eq_true, ite_false]
    | _ => simp at hp
  · simp only [ha, ite_false, Bool.false_eq_true, hd]
    exact hfin fun c hc => Classical.byContradiction fun h => ha (List.any_eq_true.mpr
      ⟨.float c, mem_floatsOf.mp hc, by simpa using hinf c hc h⟩)

end Stat

end Substrait
