import SubstraitLean.Lipschitz.Basic

/-!
# Tolerance composition: the `SUM` and `AVG` rows (#929)

The columns the analysis bounds (`Rel.refCols`), and the fold's `SUM` and
`AVG` rows (`Measure.tolOut`, `Measure.tolOut_cell`).
-/

namespace Substrait

open FloatCode

/-! ### Columns the analysis bounds

The tolerance compares codes after `canon`, and D31's operations and
aggregates read their inputs up to `canon`, so the bounds hold on any codes.
`Rel.refCols` names the columns the analysis bounds: copies of source
columns, D31's operations, and `SUM` and `AVG` results. -/

/-- The first `n` columns from `a`, the rest from `b`. -/
def maskCat (n : Nat) (a b : Nat → Bool) : Nat → Bool := fun j => if j < n then a j else b (j - n)

/-- A copy of a column `mask` names. -/
def Expr.refCol (mask : Nat → Bool) : Expr → Bool
  | .field i => mask i
  -- D31's operations end in `canon`: a reference code.
  | .bin .fadd _ _ | .bin .fsub _ _ | .bin .fmul _ _ | .bin .fdiv _ _ => true
  | _ => false

/-- A measure whose value is a reference code or NULL: `SUM` and `AVG` of
doubles (`floatSumCR`, `floatAvgCR`). -/
def Measure.refOut (m : Measure) : Bool :=
  match m.fn with
  | .fsum | .avg => true
  | _ => false

/-- The output columns that hold reference codes when the sources do. -/
def Rel.refCols (cat : Catalog) : Rel → Nat → Bool
  | .read _ => fun _ => true
  | .values _ _ | .window .. | .unnest .. => fun _ => false
  | .filter r _ | .orderBy r _ | .distinct r | .fetch r _ _ => r.refCols cat
  | .project r es =>
      maskCat (r.arity cat) (r.refCols cat) fun k => (es[k]?).any (·.refCol (r.refCols cat))
  | .emit r m => fun j => (m[j]?).any (r.refCols cat)
  | .cross a b | .join a b _ _ => maskCat (a.arity cat) (a.refCols cat) (b.refCols cat)
  | .unionAll a b => fun j => a.refCols cat j && b.refCols cat j
  | .semi a _ _ _ => a.refCols cat
  | .aggregate r gs ms =>
      maskCat gs.length (fun k => (gs[k]?).any (·.refCol (r.refCols cat))) fun k => (ms[k]?).any Measure.refOut

/-- What D31's operations give before `canon`: one of the special codes, or a
rounding. -/
theorem isRef_canon_of {c : Int}
    (h : c = nan ∨ c = posInf ∨ c = negInf ∨ c = 0 ∨ c = negZero ∨ ∃ v n, c = FloatCode.rnd v n) :
    IsRef (canon c) := by
  have h1 := fp64.posInf_lt_nan; have h2 := fp64.negInf_lt_zero; have h3 := fp64.zero_lt_posInf
  have hN : IsRef fp64.nan := ⟨by omega, by omega⟩
  have hP : IsRef fp64.posInf := ⟨by omega, by omega⟩
  have hM : IsRef fp64.negInf := ⟨by omega, by omega⟩
  have hZ : IsRef 0 := ⟨by omega, by omega⟩
  rcases h with rfl | rfl | rfl | rfl | rfl | ⟨v, n, rfl⟩
  · rw [canon_of_isRef hN]; exact hN
  · rw [canon_of_isRef hP]; exact hP
  · rw [canon_of_isRef hM]; exact hM
  · rw [canon_of_isRef hZ]; exact hZ
  · rw [show canon negZero = 0 from fp64.canon_negZero]; exact hZ
  · rw [FloatCode.canon_rnd]; exact FloatCode.isRef_ofExactDiv _ _

theorem zeroOf_cases (b : Bool) : FloatCode.zeroOf b = 0 ∨ FloatCode.zeroOf b = negZero := by
  cases b <;> simp [FloatCode.zeroOf]

theorem infOf_cases (b : Bool) : FloatCode.infOf b = posInf ∨ FloatCode.infOf b = negInf := by
  cases b <;> simp [FloatCode.infOf]

theorem fadd_isRef (a b : Int) : IsRef (canon (fadd a b)) := by
  unfold fadd addI
  dsimp only
  repeat' split
  all_goals first
    | exact isRef_canon_of (by simp)
    | (rename_i hb; simp only [FloatCode.isInfCode, Bool.or_eq_true, beq_iff_eq] at hb
       rcases hb with rfl | rfl <;> exact isRef_canon_of (by simp))
    | (rcases zeroOf_cases (decide (a < 0) && decide (negI b < 0)) with h | h <;>
        rw [h] <;> exact isRef_canon_of (by simp))
    | (rcases zeroOf_cases (decide (a < 0) && decide (b < 0)) with h | h <;>
        rw [h] <;> exact isRef_canon_of (by simp))
    | exact isRef_canon_of (.inr (.inr (.inr (.inr (.inr ⟨_, _, rfl⟩)))))

theorem fsub_isRef (a b : Int) : IsRef (canon (fsub a b)) := fadd_isRef a (negI b)

theorem fmul_isRef (a b : Int) : IsRef (canon (fmul a b)) := by
  unfold fmul mulI
  dsimp only
  repeat' split
  all_goals first
    | exact isRef_canon_of (by simp)
    | (rcases infOf_cases (decide (a < 0) != decide (b < 0)) with h | h <;> rw [h] <;>
        exact isRef_canon_of (by simp))
    | (rcases zeroOf_cases (decide (a < 0) != decide (b < 0)) with h | h <;> rw [h] <;>
        exact isRef_canon_of (by simp))
    | exact isRef_canon_of (.inr (.inr (.inr (.inr (.inr ⟨_, _, rfl⟩)))))

theorem fdiv_isRef (a b : Int) : IsRef (canon (fdiv a b)) := by
  unfold fdiv divI
  dsimp only
  repeat' split
  all_goals first
    | exact isRef_canon_of (by simp)
    | (rcases infOf_cases (decide (a < 0) != decide (b < 0)) with h | h <;> rw [h] <;>
        exact isRef_canon_of (by simp))
    | (rcases zeroOf_cases (decide (a < 0) != decide (b < 0)) with h | h <;> rw [h] <;>
        exact isRef_canon_of (by simp))
    | exact isRef_canon_of (.inr (.inr (.inr (.inr (.inr ⟨_, _, rfl⟩)))))

/-! ### The `SUM` and `AVG` rows of the fold (#929 step 3c)

A `SUM` or `AVG` of a tolerated column `i`, within `e` codes, has a bound
when the reference's analysis gives column `i` a range of codes `[lo, hi]`
that stays finite `e` codes beyond each end, and the input at most `N` rows:
the values are finite on both sides, and their exact sums at most
`N · (M + e)` in units of `2⁻¹⁰⁷⁴`, `M` the larger magnitude of `lo` and
`hi`. Codes compare after `canon`: `-0.0` is within any tolerance of
`+0.0`. -/

/-- The larger magnitude of the ends of a range of codes. -/
def magOf (lo hi : Int) : Nat := max (scaled lo).natAbs (scaled hi).natAbs

/-- A `SUM`'s bound: `N` values within `e`, and the two roundings. -/
def sumTol (N e M : Nat) : Nat := N * (e + 1) + 2 * ulpDiv ((N * (M + e) : Nat) : Int) 1 + 4

/-- An `AVG`'s bound. -/
def avgTol (e M : Nat) : Nat := (e + 1) + 2 * ulpDiv ((M + e : Nat) : Int) 1 + 4

/-- The range of codes the analysis gives column `i`, where it bounds both ends. -/
def colRange (env : List AVal) (i : Nat) : Option (Int × Int) :=
  match (env.getD i AVal.top).int with
  | some ⟨some lo, some hi⟩ => some (lo, hi)
  | _ => none

set_option exponentiation.threshold 2100 in
/-- **A measure's output tolerance**, its input within `t`: `some none` for a
measure that reads exact columns only, `some (some b)` for a `SUM` or `AVG`
of a tolerated column it bounds, `none` otherwise. `mask` names the input's
columns of reference codes, `env` its abstract values, `N` its row bound. -/
def Measure.tolOut (t : Tol) (mask : Nat → Bool) (env : List AVal) (N : Option Nat)
    (m : Measure) : Option (Option Nat) :=
  if m.tolOk t then some none else
  match m.arg, N with
  | .field i, some N =>
    match t i, colRange env i with
    | some e, some (lo, hi) =>
      if !m.distinct && (m.filter.all fun c => t.exactOn c.cols) && mask i &&
          decide (negInf < lo - e) && decide (hi + e < posInf) &&
          decide (N * (magOf lo hi + e) ≤ 2 ^ 2097) then
        match m.fn with
        | .fsum => some (some (sumTol N e (magOf lo hi)))
        | .avg => some (some (avgTol e (magOf lo hi)))
        | _ => none
      else none
    | _, _ => none
  | _, _ => none

theorem Forall2.mem_left {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : Forall2 R l l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', R a b :=
  Forall2.mem_right (Forall2.flip h) ha

theorem scaled_natAbs_le {lo hi c : Int} (h1 : lo ≤ c) (h2 : c ≤ hi) :
    (scaled c).natAbs ≤ magOf lo hi := by
  have a := scaled_mono h1; have b := scaled_mono h2
  unfold magOf
  generalize scaled lo = x at *; generalize scaled hi = y at *; generalize scaled c = z at *
  omega

theorem exactSum_natAbs_le_mul {B : Nat} :
    ∀ {vs : List Value}, (∀ c, Value.float c ∈ vs → (scaled (canon c)).natAbs ≤ B) →
      (exactSum vs).natAbs ≤ vs.length * B
  | [], _ => by simp [exactSum]
  | v :: vs, h => by
    have ih := exactSum_natAbs_le_mul (vs := vs) fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [exactSum_cons]
    have hv : (exactOf v).natAbs ≤ B := by
      cases v with
      | float c => exact h c (List.mem_cons_self ..)
      | _ => simp [exactOf]
    have := Int.natAbs_add_le (exactOf v) (exactSum vs)
    simp only [List.length_cons, Nat.succ_mul]
    omega

variable [Boxes.Ambient]
omit [Boxes.Ambient] in
theorem ulpDiv_mono {v w : Int} (n : Nat) (h : v.natAbs ≤ w.natAbs) : ulpDiv v n ≤ ulpDiv w n :=
  Nat.pow_le_pow_right (by decide) (gridExp_mono n h)

omit [Boxes.Ambient] in
/-- The ulp of a mean is at most the ulp of a bound on its values. -/
theorem ulpDiv_le_of_mean {S : Int} {n B : Nat} (h : S.natAbs ≤ n * B) :
    ulpDiv S n ≤ ulpDiv (B : Int) 1 := by
  unfold ulpDiv
  apply Nat.pow_le_pow_right (by decide)
  unfold gridExp
  have : S.natAbs / n ≤ B := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Nat.div_le_of_le_mul h
  have := log2_mono this
  simp only [Int.natAbs_natCast, Nat.div_one]
  omega

omit [Boxes.Ambient] in
theorem Tol.cell_float {t : Tol} {j e : Nat} (hj : t j = some e) {a b : Int}
    (h : (fp64.canon a - fp64.canon b).natAbs ≤ e) : t.Cell j (.float a) (.float b) := by
  show IntEquiv nearObs t.ctx j a b
  simp only [IntEquiv, Tol.ctx, ObsCtx.ofTol, Tol.kind, hj, Option.isSome_some, ite_true, nearObs,
    Tol.near]
  exact h

omit [Boxes.Ambient] in
theorem Tol.cell_float_iff {e : Nat} {a b : Int} :
    (Tol.all e).Cell 0 (.float a) (.float b) ↔ (fp64.canon a - fp64.canon b).natAbs ≤ e := by
  show IntEquiv nearObs (Tol.all e).ctx 0 a b ↔ _
  simp [IntEquiv, Tol.ctx, ObsCtx.ofTol, Tol.kind, Tol.all, nearObs, Tol.near]

/-- The inputs of a measure, value by value within `e` (`Measure.inputs_near`
without the finiteness). -/
theorem Measure.inputs_cells {t : Tol} {m : Measure} {e : Nat} (hd : m.distinct = false)
    (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e)) {g g' : Relation}
    (f : Forall2 t.Rows g g') : Forall2 ((Tol.all e).Cell 0) (m.inputs g) (m.inputs g') := by
  obtain ⟨o, ho, hle⟩ := ha
  have hk : Forall2 t.Rows (m.kept g) (m.kept g') := by
    unfold Measure.kept
    cases hc : m.filter with
    | none => exact f
    | some c =>
      simp only [hc, Option.all_some] at hf
      exact f.filter fun x y r => by rw [Expr.eval_rows hf r]
  have hm : Forall2 ((Tol.all e).Cell 0) ((m.kept g).map fun row => m.arg.eval row)
      ((m.kept g').map fun row => m.arg.eval row) :=
    hk.map (f := fun row => m.arg.eval row) (g := fun row => m.arg.eval row)
      fun x y r => Expr.tol?_sound ho r (t' := Tol.all e) (j := 0) hle
  have hn := hm.filter (p := (· != .null)) (p' := (· != .null)) fun v w h => Tol.cell_null_iff h
  unfold Measure.inputs
  simp only [hd, Bool.false_eq_true, ite_false]
  exact hn

omit [Boxes.Ambient] in
/-- One pair of a `SUM`'s values: the engine's a reference code, the
reference's in `[lo, hi]`, within `e` after `canon`. Then both are finite,
within `e` as codes, and the engine's magnitude at most `M + e`. -/
theorem pair_near {e : Nat} {lo hi : Int} (hlo : negInf < lo - e) (hhi : hi + e < posInf)
    {v w : Value} (hc : (Tol.all e).Cell 0 v w)
    (hw : ∀ c, w = .float c → lo ≤ canon c ∧ canon c ≤ hi) :
    CodeNear e v w ∧
      (∀ c, v = .float c → IsFin (canon c) ∧ (scaled (canon c)).natAbs ≤ magOf lo hi + e) ∧
      (∀ c, w = .float c → IsFin (canon c) ∧ (scaled (canon c)).natAbs ≤ magOf lo hi) := by
  cases w with
  | float b =>
    cases v with
    | float a =>
      obtain ⟨hb1, hb2⟩ := hw b rfl
      have fb : IsFin (canon b) := ⟨by omega, by omega⟩
      have h : (canon a - canon b).natAbs ≤ e := Tol.cell_float_iff.1 hc
      have fa : IsFin (canon a) := ⟨by omega, by omega⟩
      have hs := scaled_sub_le (canon a) (canon b)
      have hmb := scaled_natAbs_le hb1 hb2
      refine ⟨h, fun c hc' => ?_, fun c hc' => ?_⟩
      · cases hc'
        refine ⟨fa, ?_⟩
        have := Int.natAbs_add_le (scaled (canon a) - scaled (canon b)) (scaled (canon b))
        rw [Int.sub_add_cancel] at this
        omega
      · cases hc'; exact ⟨fb, hmb⟩
    | _ => exact hc.elim
  | _ =>
    cases v with
    | float a => exact hc.elim
    | _ =>
      exact ⟨⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩, fun _ h => (nomatch h),
        fun _ h => (nomatch h)⟩

/-- A `SUM`'s or `AVG`'s inputs on two groups within `t`: paired within `e`,
finite, of bounded magnitude, at most `N` of them. -/
theorem Measure.sum_facts {t : Tol} {m : Measure} {env : List AVal}
    {i e N : Nat} {lo hi : Int} (harg : m.arg = .field i) (hti : t i = some e)
    (hcr : colRange env i = some (lo, hi)) (hd : m.distinct = false)
    (hf : m.filter.all (fun c => t.exactOn c.cols) = true)
    (hlo : negInf < lo - e) (hhi : hi + e < posInf) {g g' : Relation} (f : Forall2 t.Rows g g')
    (henv : ∀ row ∈ g', EnvMem env row) (hN : g'.length ≤ N) :
    Forall2 (CodeNear e) (m.inputs g) (m.inputs g') ∧ FinCodes (m.inputs g) ∧
      FinCodes (m.inputs g') ∧
      (exactSum (m.inputs g)).natAbs ≤ (m.inputs g).length * (magOf lo hi + e) ∧
      (exactSum (m.inputs g')).natAbs ≤ (m.inputs g').length * (magOf lo hi + e) ∧
      (m.inputs g).length ≤ N ∧ (m.inputs g').length ≤ N := by
  have ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e) :=
    ⟨some e, by simp [harg, Expr.tol?, hti], by simp [OLe]⟩
  have hcells := Measure.inputs_cells hd hf ha f
  have hQ : ∀ w ∈ m.inputs g', ∀ c, w = .float c → lo ≤ canon c ∧ canon c ≤ hi := by
    intro w hw c hc
    obtain ⟨-, row, hr, rfl⟩ := Measure.mem_inputs hw
    rw [harg] at hc
    have hm := henv row hr i
    simp only [Expr.eval] at hc
    rw [hc] at hm
    obtain ⟨b, hb, hbm, -⟩ := hm
    unfold colRange at hcr
    split at hcr
    · rename_i lo' hi' hint
      simp only [Option.some.injEq, Prod.mk.injEq] at hcr
      obtain ⟨rfl, rfl⟩ := hcr
      rw [hint] at hb; cases hb
      exact ⟨hbm.1 _ rfl, hbm.2 _ rfl⟩
    · cases hcr
  have hpairs := (hcells.and_mem (P := fun _ => True) (fun _ _ => trivial) hQ).imp
    fun v w ⟨h, _, qw⟩ => pair_near hlo hhi h qw
  have hlen := hcells.length_eq
  have hl' := Nat.le_trans (Measure.inputs_length_le m g') hN
  refine ⟨hpairs.imp fun _ _ h => h.1, fun c hc => ?_, fun c hc => ?_, ?_, ?_, by omega, hl'⟩
  · obtain ⟨w, -, h⟩ := hpairs.mem_left hc; exact (h.2.1 c rfl).1
  · obtain ⟨v, -, h⟩ := hpairs.mem_right hc; exact (h.2.2 c rfl).1
  · exact exactSum_natAbs_le_mul fun c hc => by
      obtain ⟨w, -, h⟩ := hpairs.mem_left hc; exact (h.2.1 c rfl).2
  · exact exactSum_natAbs_le_mul fun c hc => by
      obtain ⟨v, -, h⟩ := hpairs.mem_right hc
      have := (h.2.2 c rfl).2; omega

omit [Boxes.Ambient] in
theorem nonFinite_isRef {vs : List Value} {c : Int} (h : nonFinite vs = some c) : IsRef c := by
  have h1 := fp64.posInf_lt_nan; have h2 := fp64.negInf_lt_zero; have h3 := fp64.zero_lt_posInf
  have hp : IsRef fp64.posInf := ⟨by omega, by omega⟩
  have hn : IsRef fp64.negInf := ⟨by omega, by omega⟩
  have hN : IsRef fp64.nan := ⟨by omega, by omega⟩
  unfold nonFinite at h
  split at h
  · cases h; exact hN
  split at h
  · cases h; exact hp
  split at h
  · cases h; exact hn
  · cases h

omit [Boxes.Ambient] in
theorem floatSumCR_isRef (vs : List Value) : IsRef (floatSumCR vs) := by
  unfold floatSumCR
  cases h : nonFinite vs with
  | none => exact isRef_ofExactDiv _ _
  | some c => exact nonFinite_isRef h

omit [Boxes.Ambient] in
theorem floatAvgCR_isRef (vs : List Value) : IsRef (floatAvgCR vs) := by
  unfold floatAvgCR
  cases h : nonFinite vs with
  | none => exact isRef_ofExactDiv _ _
  | some c => exact nonFinite_isRef h

theorem Measure.refOut_sound {m : Measure} (hm : m.refOut = true) (rows : Relation) {c : Int}
    (hc : m.eval rows = .float c) : IsRef c := by
  unfold Measure.refOut at hm
  cases hfn : m.fn <;> simp only [hfn, Bool.false_eq_true] at hm
  all_goals
    have hs : m.fn.sorts = false := by rw [hfn]; rfl
    rw [Measure.eval_eq hs, hfn] at hc
    cases h : m.inputs rows <;> rw [h] at hc <;> simp only [AggFn.apply, reduceCtorEq, Value.float.injEq] at hc
  · rw [← hc]; exact floatSumCR_isRef _
  · rw [← hc]; exact floatAvgCR_isRef _

/-- A `SUM`'s or `AVG`'s value: NULL, or a reference code. -/
theorem Measure.eval_refOut {m : Measure} (hm : m.refOut = true) (rows : Relation) :
    m.eval rows = .null ∨ ∃ a, m.eval rows = .float a ∧ IsRef a := by
  cases h : m.eval rows with
  | null => exact .inl rfl
  | float a => exact .inr ⟨a, rfl, Measure.refOut_sound hm rows h⟩
  | _ =>
    exfalso
    unfold Measure.refOut at hm
    have hs : m.fn.sorts = false := by
      cases hfn : m.fn <;> simp only [hfn, Bool.false_eq_true] at hm <;> rfl
    rw [Measure.eval_eq hs] at h
    cases hfn : m.fn <;> simp only [hfn, Bool.false_eq_true] at hm <;> rw [hfn] at h <;>
      cases hi : m.inputs rows <;> rw [hi] at h <;> simp [AggFn.apply] at h

omit [Boxes.Ambient] in
theorem Tol.cell_of_codeNear {tm : Tol} {j B B' : Nat} (hj : tm j = some B') (hB : B ≤ B')
    {v w : Value} (hv : v = .null ∨ ∃ a, v = .float a ∧ IsRef a)
    (hw : w = .null ∨ ∃ b, w = .float b ∧ IsRef b) (h : CodeNear B v w) : tm.Cell j v w := by
  rcases hv with rfl | ⟨a, rfl, ra⟩ <;> rcases hw with rfl | ⟨b, rfl, rb⟩
  · exact Tol.cell_null _ _
  · exact absurd rfl (h.2 b)
  · exact absurd rfl (h.1 a)
  · exact Tol.cell_float hj (Nat.le_trans h hB)

set_option exponentiation.threshold 2100 in
/-- **A measure's output on two groups within `t` is within its output
tolerance.** -/
theorem Measure.tolOut_cell {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {o : Option Nat} (h : m.tolOut t mask env N = some o) {g g' : Relation}
    (f : Forall2 t.Rows g g') (henv : ∀ row ∈ g', EnvMem env row)
    (hN : ∀ n, N = some n → g'.length ≤ n) {tm : Tol} {j : Nat}
    (hj : tm j = o) : tm.Cell j (m.eval g) (m.eval g') := by
  unfold Measure.tolOut at h
  by_cases hok : m.tolOk t = true
  · rw [Measure.eval_rows hok f]; exact Tol.cell_refl _ _ _
  simp only [hok, Bool.false_eq_true, ite_false] at h
  cases harg : m.arg with
  | field i =>
    rw [harg] at h
    cases N with
    | none => simp at h
    | some n =>
      simp only at h
      cases hti : t i with
      | none => simp [hti] at h
      | some e =>
        cases hcr : colRange env i with
        | none => simp [hti, hcr] at h
        | some r =>
          obtain ⟨lo, hi⟩ := r
          simp only [hti, hcr] at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
            obtain ⟨⟨⟨⟨⟨hd, hf⟩, hmask⟩, hlo⟩, hhi⟩, hbig⟩ := hc
            obtain ⟨hp, hv, hw, hS, hS', hl, hl'⟩ :=
              Measure.sum_facts harg hti hcr hd hf hlo hhi f henv (hN n rfl)
            have ha : ∃ o, m.arg.tol? t = some o ∧ OLe o (some e) :=
              ⟨some e, by simp [harg, Expr.tol?, hti], by simp [OLe]⟩
            have hlen := hp.length_eq
            generalize hM : magOf lo hi = M at hS hS' hbig h
            cases hfn : m.fn <;> simp only [hfn, reduceCtorEq] at h
            · -- SUM
              simp only [Option.some.injEq] at h; subst h
              have hro : m.refOut = true := by simp [Measure.refOut, hfn]
              have big : ((n * (M + e) : Nat) : Int).natAbs = n * (M + e) := Int.natAbs_natCast _
              have hS1 : (exactSum (m.inputs g)).natAbs ≤ n * (M + e) :=
                Nat.le_trans hS (Nat.mul_le_mul_right _ hl)
              have hS2 : (exactSum (m.inputs g')).natAbs ≤ n * (M + e) :=
                Nat.le_trans hS' (Nat.mul_le_mul_right _ hl')
              have rv := ofExactDiv_fin (v := exactSum (m.inputs g)) (n := 1) (by omega) (by omega)
              have rw' := ofExactDiv_fin (v := exactSum (m.inputs g')) (n := 1) (by omega) (by omega)
              have hc := Measure.fsum_near hfn hd hf ha f hv hw rv rw'
              refine Tol.cell_of_codeNear hj ?_ (Measure.eval_refOut hro g)
                (Measure.eval_refOut hro g') hc
              have u1 := ulpDiv_mono (v := exactSum (m.inputs g))
                (w := ((n * (M + e) : Nat) : Int)) 1 (by rw [big]; exact hS1)
              have u2 := ulpDiv_mono (v := exactSum (m.inputs g'))
                (w := ((n * (M + e) : Nat) : Int)) 1 (by rw [big]; exact hS2)
              have := Nat.mul_le_mul_right (e + 1) hl
              unfold sumTol; omega
            · -- AVG
              simp only [Option.some.injEq] at h; subst h
              have hro : m.refOut = true := by simp [Measure.refOut, hfn]
              have hfin : ∀ {I : List Value}, (exactSum I).natAbs ≤ I.length * (M + e) →
                  I.length ≤ n → IsFin (ofExactDiv (exactSum I) I.length) := by
                intro I hI hIn
                rcases Nat.eq_zero_or_pos I.length with h0 | hpos
                · rw [h0] at hI ⊢
                  have : exactSum I = 0 := by omega
                  rw [this, ofExactDiv_zero]
                  exact ⟨by have := negInf_eq; omega, by have := posInf_eq; omega⟩
                · refine ofExactDiv_fin hpos (Nat.le_trans hI (Nat.mul_le_mul_left _ ?_))
                  have : 1 * (M + e) ≤ n * (M + e) := Nat.mul_le_mul_right _ (by omega)
                  omega
              have hc := Measure.avg_near hfn hd hf ha f hv hw (hfin hS hl) (hfin hS' hl')
              refine Tol.cell_of_codeNear hj ?_ (Measure.eval_refOut hro g)
                (Measure.eval_refOut hro g') hc
              have u1 := ulpDiv_le_of_mean hS
              have u2 := ulpDiv_le_of_mean hS'
              simp only [Int.natCast_add] at u1 u2
              unfold avgTol; push_cast; omega
          · cases h
  | _ => rw [harg] at h; simp at h

/-- The tolerance of a list of measure outputs. -/
def Tol.ofOuts (os : List (Option (Option Nat))) : Tol := fun k => (os.getD k none).getD none

omit [Boxes.Ambient] in
set_option exponentiation.threshold 2100 in
theorem Measure.tolOut_orderFree {t : Tol} {mask : Nat → Bool} {env : List AVal} {N : Option Nat}
    {m : Measure} {o : Option Nat} (h : m.tolOut t mask env N = some o) : m.orderFree = true := by
  by_cases hok : m.tolOk t = true
  · simp only [Measure.tolOk, Bool.and_eq_true] at hok; exact hok.1.1.1
  unfold Measure.orderFree
  cases hfn : m.fn <;> first
    | (simp [AggFn.orderFree, AggFn.decomposable]; done)
    | (exfalso
       unfold Measure.tolOut at h
       simp only [hok, Bool.false_eq_true, ite_false] at h
       repeat' (split at h)
       all_goals simp_all)

omit [Boxes.Ambient] in
theorem Tol.cell_float_iff' {t : Tol} {k ε : Nat} (h : t k = some ε) {a b : Int}
    (hc : t.Cell k (.float a) (.float b)) : (fp64.canon a - fp64.canon b).natAbs ≤ ε := by
  have : IntEquiv nearObs t.ctx k a b := hc
  simpa [IntEquiv, Tol.ctx, ObsCtx.ofTol, Tol.kind, h, nearObs, Tol.near] using this

end Substrait
