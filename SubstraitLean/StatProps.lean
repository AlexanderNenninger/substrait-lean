import SubstraitLean.Aggregate

/-!
# What a statistical aggregate may give (#85)

`VARIANCE`, `STDDEV`, `COVAR_SAMP`/`COVAR_POP` and `CORR` are computed by each
engine's own algorithm, and none documents which (DuckDB, Spark and grouped
Polars use Welford's update with Chan's merge, ungrouped Polars a blockwise
two-pass). The reference does not pick one: it allows any value with the
generic properties every reasonable algorithm keeps (`StatProps`, the set
`AggFn.Allowed` uses in `SubstraitLean/Allowed.lean`). An engine profile may
name a stricter algorithm (`Profile.statAlgo`); without one, these hold.

For `n ≤ 2³²` finite values at most `2³⁹⁹` in magnitude, with
`B = max(max |xᵢ|, 2⁻⁵⁰⁰)`, `u = 2⁻⁵³` and the exact co-moment
`C = Σxy − Σx · Σy / n`:

* `NULL` exactly where the reference says: no values, a sample of one value,
  and for `CORR` fewer than two pairs or a side whose values are all equal;
* a variance or deviation is `≥ 0`;
* `VAR_*` and `COVAR_*`, `C / d` with `d = n − 1` (sample) or `n`
  (population), are within `τ = (128 n² u B² + 12 n u B²) / d`;
* `STDDEV_*` is within `(1 ± u)` of `√(V ± τ)`, stated squared;
* `|CORR| ≤ 1 + 3E/L + 8u`, `E = 128 n² u B²`, when the co-moments of both
  sides are at least `L ≥ 8E` (and `L ≥ 2⁻⁵⁰⁰`, their product at most
  `2¹⁰⁰⁰`). Without such a lower bound `CORR` may be any double.

The co-moment bound holds for the two-pass algorithm (the reference's own),
for Welford's update with Chan's merge in any tree, and for the textbook
formula `Σx² − (Σx)²/n` (`docs/float-bounds.md`). Outside the finite range
above, the reference's own value is the one allowed.

Lean's own results have these properties by three trusted facts,
`varOf_props`, `covOf_props` and `corrOf_props`, proved for IEEE rounding in
`float-bounds/` (`core_var`, `core_stddev`, `core_cov`, `core_corr` in
`FloatBounds/CoreStats.lean`), so the core needs no Mathlib. They make
`StatProps.apply`, the witness, hold.
-/

namespace Substrait.Stat

/-- The unit roundoff, `2⁻⁵³`. -/
def u : Rat := 1 / 2 ^ 53

/-- The smallest normal double, `2⁻¹⁰²²`. -/
def tiny : Rat := 1 / 2 ^ 1022

/-- The value of a finite double code (`FloatCode.scaled` is it times `2¹⁰⁷⁴`). -/
def val (c : Int) : Rat := (FloatCode.scaled c : Rat) / 2 ^ 1074

def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- `max (max |xᵢ|) 2⁻⁵⁰⁰`: the `B` of the bounds. -/
def bound (xs : List Rat) : Rat := xs.foldl (fun m x => max m (absQ x)) (1 / 2 ^ 500)

/-- The co-moment `Σxy − Σx · Σy / n` of exact values. -/
def comoment (ps : List (Rat × Rat)) : Rat :=
  (ps.map fun p => p.1 * p.2).sum - (ps.map (·.1)).sum * (ps.map (·.2)).sum / ps.length

/-- `E = 128 n² u B²`, the error bound of a co-moment. -/
def err (n : Nat) (B : Rat) : Rat := 128 * n ^ 2 * u * B ^ 2

/-- The error bound of `C / d`: `(E + 12 n u B²) / d`. -/
def tol (n d : Nat) (B : Rat) : Rat := (err n B + 12 * n * u * B ^ 2) / d

/-- At most `2³²` doubles, each at most `2³⁹⁹` in magnitude (finite). -/
def fits (cs : List Int) : Bool :=
  cs.length ≤ 2 ^ 32 && cs.all fun c => (FloatCode.scaled c).natAbs ≤ 2 ^ 1473

/-- A deviation `σ` near `√V` with `V` within `τ`: squared,
`(σ − u·tiny)² ≤ (1 + u)² (V + τ)` (where `σ > u·tiny`) and
`(1 − u)² (V − τ) ≤ (σ + u·tiny)²`. -/
def sdNear (σ V τ : Rat) : Prop :=
  (σ ≤ u * tiny ∨ (σ - u * tiny) ^ 2 ≤ (1 + u) ^ 2 * (V + τ)) ∧
    (1 - u) ^ 2 * (V - τ) ≤ (σ + u * tiny) ^ 2

/-- Every value a double (an integer code). -/
def allInts (vs : List Value) : Prop := ∀ w ∈ vs, ∃ i, w = .int i

instance (vs : List Value) : Decidable (allInts vs) :=
  if h : vs.all (fun | .int _ => true | _ => false) then
    isTrue fun w hw => by
      have := List.all_eq_true.mp h w hw
      cases w <;> simp_all
  else isFalse fun h' => h (List.all_eq_true.mpr fun w hw => by
    obtain ⟨i, rfl⟩ := h' w hw; rfl)

/-- The properties of `VAR_*` (`sqrt = false`) or `STDDEV_*` of the doubles
`cs`, for a non-`NULL` result `c`. -/
def varProps (sample sqrt : Bool) (cs : List Int) (c : Int) : Prop :=
  let xs := cs.map val
  let d := if sample then cs.length - 1 else cs.length
  let V := comoment (xs.map fun x => (x, x)) / d
  let τ := tol cs.length d (bound xs)
  0 ≤ c ∧ if sqrt then sdNear (val c) V τ else absQ (val c - V) ≤ τ

/-- The property of `COVAR_*` of the pairs `ps`, for a non-`NULL` result `c`. -/
def covProps (sample : Bool) (ps : List (Int × Int)) (c : Int) : Prop :=
  let qs := ps.map fun p => (val p.1, val p.2)
  let d := if sample then ps.length - 1 else ps.length
  absQ (val c - comoment qs / d) ≤ tol ps.length d (bound (qs.map (·.1) ++ qs.map (·.2)))

/-- The property of `CORR` of the pairs `ps`, for a non-`NULL` result `c`. -/
def corrProps (ps : List (Int × Int)) (c : Int) : Prop :=
  let qs := ps.map fun p => (val p.1, val p.2)
  let E := err ps.length (bound (qs.map (·.1) ++ qs.map (·.2)))
  let sx := comoment (qs.map fun q => (q.1, q.1))
  let sy := comoment (qs.map fun q => (q.2, q.2))
  ∀ L : Rat, 8 * E ≤ L → 1 / 2 ^ 500 ≤ L → L ≤ sx → L ≤ sy → sx * sy ≤ 2 ^ 1000 →
    absQ (val c) ≤ 1 + 3 * E / L + 8 * u

end Stat

open Stat

/-! ## Trusted: Lean's results have the properties

`varOf`, `covOf` and `corrOf` compute with native doubles. Proved for IEEE
rounding to nearest in `float-bounds/FloatBounds/CoreStats.lean` (`core_var`,
`core_stddev`, `core_cov`, `core_corr`), given `NativeLink` and the code
conversions of `Float.lean`, like `floatSum_mem` in `Aggregate.lean`. -/

axiom varOf_props {sample sqrt : Bool} {vs : List Value} (hne : vs ≠ [])
    (hs : ¬(sample = true ∧ vs.length = 1)) (hi : allInts vs) (hf : fits (intsOf vs) = true) :
    ∃ c, varOf sample sqrt vs = .int c ∧ varProps sample sqrt (intsOf vs) c

axiom covOf_props {sample : Bool} {vs : List Value}
    (hne : (pairsOf vs).isEmpty = false) (hs : ¬(sample = true ∧ (pairsOf vs).length = 1))
    (hf : fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true) :
    ∃ c, covOf sample vs = .int c ∧ covProps sample (pairsOf vs) c

axiom corrOf_props {vs : List Value}
    (hn : ¬((pairsOf vs).length < 2 ∨ ((pairsOf vs).map (·.1)).all
        (· == ((pairsOf vs).map (·.1)).headD 0) = true ∨
      ((pairsOf vs).map (·.2)).all (· == ((pairsOf vs).map (·.2)).headD 0) = true))
    (hf : fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true) :
    ∃ c, corrOf vs = .int c ∧ corrProps (pairsOf vs) c

/-- `VAR_*` / `STDDEV_*` of `vs` may give `v`. -/
def varStat (sample sqrt : Bool) (vs : List Value) (v : Value) : Prop :=
  if vs = [] ∨ (sample = true ∧ vs.length = 1) then v = .null
  else if allInts vs ∧ fits (intsOf vs) = true then
    ∃ c, v = .int c ∧ varProps sample sqrt (intsOf vs) c
  else v = (AggFn.var sample sqrt).apply vs

/-- `COVAR_*` of `vs` may give `v`. -/
def covStat (sample : Bool) (vs : List Value) (v : Value) : Prop :=
  if (pairsOf vs).isEmpty = true ∨ (sample = true ∧ (pairsOf vs).length = 1) then v = .null
  else if fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true then
    ∃ c, v = .int c ∧ covProps sample (pairsOf vs) c
  else v = (AggFn.cov sample).apply vs

/-- `CORR` of `vs` may give `v`. -/
def corrStat (vs : List Value) (v : Value) : Prop :=
  if (pairsOf vs).length < 2 ∨ ((pairsOf vs).map (·.1)).all
        (· == ((pairsOf vs).map (·.1)).headD 0) = true ∨
      ((pairsOf vs).map (·.2)).all (· == ((pairsOf vs).map (·.2)).headD 0) = true then
    v = .null
  else if fits ((pairsOf vs).map (·.1) ++ (pairsOf vs).map (·.2)) = true then
    ∃ c, v = .int c ∧ corrProps (pairsOf vs) c
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

theorem varStat_apply (sample sqrt : Bool) (vs : List Value) :
    varStat sample sqrt vs ((AggFn.var sample sqrt).apply vs) := by
  unfold varStat
  split
  · rename_i h
    rcases h with h | ⟨hs, h1⟩
    · subst h; rfl
    · cases vs with
      | nil => rfl
      | cons w ws => simp [AggFn.apply, varOf, hs, h1]
  · rename_i h
    split
    · rename_i hif
      have hne : vs ≠ [] := fun h' => h (.inl h')
      have hs : ¬(sample = true ∧ vs.length = 1) := fun h' => h (.inr h')
      obtain ⟨c, hc, hp⟩ := varOf_props hne hs hif.1 hif.2
      refine ⟨c, ?_, hp⟩
      cases vs with
      | nil => exact absurd rfl hne
      | cons w ws => simpa [AggFn.apply] using hc
    · rfl

theorem covStat_apply (sample : Bool) (vs : List Value) :
    covStat sample vs ((AggFn.cov sample).apply vs) := by
  unfold covStat
  split
  · rename_i h
    cases vs with
    | nil => rfl
    | cons w ws =>
      simp only [AggFn.apply, covOf]
      have : ((pairsOf (w :: ws)).isEmpty || (sample && (pairsOf (w :: ws)).length == 1)) = true := by
        rcases h with h | ⟨h1, h2⟩ <;> simp_all
      simp [this]
  · rename_i h
    split
    · rename_i hf
      have hne : (pairsOf vs).isEmpty = false := by
        cases hh : (pairsOf vs).isEmpty
        · rfl
        · exact absurd (.inl hh) h
      obtain ⟨c, hc, hp⟩ := covOf_props hne (fun h' => h (.inr h')) hf
      refine ⟨c, ?_, hp⟩
      cases vs with
      | nil => simp [pairsOf] at hne
      | cons w ws => simpa [AggFn.apply] using hc
    · rfl

theorem corrStat_apply (vs : List Value) : corrStat vs (AggFn.corr.apply vs) := by
  unfold corrStat
  split
  · rename_i h
    cases vs with
    | nil => rfl
    | cons w ws =>
      simp only [AggFn.apply]
      unfold corrOf
      have : ((decide ((pairsOf (w :: ws)).length < 2) ||
          ((pairsOf (w :: ws)).map (·.1)).all (· == ((pairsOf (w :: ws)).map (·.1)).headD 0)) ||
          ((pairsOf (w :: ws)).map (·.2)).all (· == ((pairsOf (w :: ws)).map (·.2)).headD 0))
          = true := by
        rcases h with h | h | h <;> simp only [Bool.or_eq_true, decide_eq_true_eq, h, true_or,
          or_true]
      simp only [this, ↓reduceIte]
  · rename_i h
    split
    · rename_i hf
      obtain ⟨c, hc, hp⟩ := corrOf_props h hf
      refine ⟨c, ?_, hp⟩
      cases vs with
      | nil => simp [pairsOf] at h
      | cons w ws => simpa [AggFn.apply] using hc
    · rfl

/-- The reference's own value is allowed. -/
theorem StatProps.apply (f : AggFn) (vs : List Value) : StatProps f vs (f.apply vs) := by
  cases f
  case var sample sqrt => exact varStat_apply sample sqrt vs
  case cov sample => exact covStat_apply sample vs
  case corr => exact corrStat_apply vs
  all_goals rfl

end Substrait
