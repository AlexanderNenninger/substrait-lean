import Sverify.Core.FloatExact
import Sverify.Core.Forall2

/-!
# Double sums near each other (#929 step 3b)

Two lists of doubles paired value by value within `e` codes have correctly
rounded sums and means within a bound in codes (`floatSumCR_near`,
`floatAvgCR_near`). `Lipschitz.lean` lifts them to `SUM` and `AVG`
measures over groups within a tolerance.
-/

namespace Substrait

/-! ## `SUM` and `AVG` of a tolerated column (#929 step 3b)

The reference's `SUM` of doubles is the exact sum rounded once (D25,
`floatSumCR`). Two lists paired value by value within `e` codes have exact
sums within `g·(e + 1)/2` units of `2⁻¹⁰⁷⁴` (`g` values; a code is twice its
value, plus its sign), and rounding moves each by half an ulp: the results
are within `g·(e + 1) + ulp + ulp' + 4` codes (`floatSumCR_near`), the
table's `g·ε + r`. An `AVG` divides the exact sums' distance by `g`:
`(e + 1) + ulp + ulp' + 4` (`floatAvgCR_near`), the table's `ε + r`. The
ulps are at most `2⁻⁵²` of the exact sums, or `1` below `2⁵³`
(`FloatCode.ulpDiv_le`).

Both need the values finite on both sides (`FinCodes`), as the reference's
are: a NaN or an infinity on one side has no distance to the other's finite
value. And the results finite (`IsFin`): an exact sum past the largest double
on one side only rounds to `±∞`. Both are named, not folded in. -/

open FloatCode in
/-- Every double among `vs` is finite (a canonical code: `-0.0`'s and the
negative NaN's codes lie below `-∞`'s). -/
def FinCodes (vs : List Value) : Prop := ∀ c, Value.float c ∈ vs → IsFin (canon c)

/-- Two values within `e` codes: two doubles, or one value that is not a
double. -/
def CodeNear (e : Nat) : Value → Value → Prop
  | .float a, .float b => (FloatCode.canon a - FloatCode.canon b).natAbs ≤ e
  | v, w => (∀ c, v ≠ .float c) ∧ ∀ c, w ≠ .float c

namespace FloatCode

theorem scaled_sub_le (a b : Int) : 2 * (scaled a - scaled b).natAbs ≤ (a - b).natAbs + 1 := by
  unfold scaled; split <;> split <;> omega

theorem code_sub_scaled (c : Int) : (c - 2 * scaled c).natAbs ≤ 2 := by
  unfold scaled; split <;> omega

end FloatCode

open FloatCode

/-- A value's exact part of a sum. -/
def exactOf : Value → Int
  | .float c => scaled (canon c)
  | _ => 0

theorem exactSum_cons (v : Value) (vs : List Value) : exactSum (v :: vs) = exactOf v + exactSum vs := by
  cases v <;> simp [exactSum, exactOf]

theorem CodeNear.exactOf {e : Nat} {v w : Value} (h : CodeNear e v w) :
    2 * (exactOf v - exactOf w).natAbs ≤ e + 1 := by
  cases v <;> cases w
  case float.float a b =>
    have := scaled_sub_le (canon a) (canon b); simp only [CodeNear] at h
    simp only [Substrait.exactOf]; omega
  all_goals first
    | exact absurd rfl (h.1 _) | exact absurd rfl (h.2 _) | simp [Substrait.exactOf]

theorem exactSum_near {e : Nat} : ∀ {vs ws : List Value}, Forall2 (CodeNear e) vs ws →
    2 * (exactSum vs - exactSum ws).natAbs ≤ vs.length * (e + 1)
  | _, _, .nil => by simp [exactSum]
  | _, _, .cons h t => by
    have ih := exactSum_near t
    have := h.exactOf
    simp only [exactSum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem nonFinite_of_finCodes {vs : List Value} (h : FinCodes vs) : nonFinite vs = none := by
  have hf : ∀ p : Int → Bool, (∀ c, IsFin c → p c = false) → anyCode p vs = false := by
    intro p hp
    simp only [anyCode, List.any_eq_false]
    intro v hv
    cases v with
    | float c => simp only [hp _ (h c hv)]; decide
    | _ => simp
  have := nan_eq; have := posInf_eq; have := negInf_eq
  unfold nonFinite
  rw [hf (fun c => decide (nan ≤ c)) (fun c hc => by simp; unfold IsFin at hc; omega),
    hf (fun c => decide (posInf ≤ c ∧ c < nan)) (fun c hc => by simp; unfold IsFin at hc; omega),
    hf (fun c => decide (c ≤ negInf)) (fun c hc => by simp; unfold IsFin at hc; omega)]
  rfl

/-- The triangle inequality along a chain of three steps. -/
theorem natAbs_add3_le (a b c : Int) : (a + b + c).natAbs ≤ a.natAbs + b.natAbs + c.natAbs :=
  Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_right (Int.natAbs_add_le _ _) _)

/-- Two rounded results from their exact parts: `r = 2s ± 2` and `s` within
`u/2` of the exact `S`, on each side, so `|r − r'| ≤ 4 + u + u' + 2|S − S'|`.
Stated once so `omega` sees no absolute values. -/
theorem round_chain {r₁ r₂ s₁ s₂ S₁ S₂ : Int} {u₁ u₂ : Nat} (c₁ : (r₁ - 2 * s₁).natAbs ≤ 2)
    (c₂ : (r₂ - 2 * s₂).natAbs ≤ 2) (h₁ : 2 * (s₁ - S₁).natAbs ≤ u₁)
    (h₂ : 2 * (s₂ - S₂).natAbs ≤ u₂) :
    (r₁ - r₂).natAbs ≤ 4 + u₁ + u₂ + 2 * (S₁ - S₂).natAbs := by
  have e : r₁ - r₂ = (r₁ - 2 * s₁) + 2 * ((s₁ - S₁) + (S₁ - S₂) + (S₂ - s₂)) + (2 * s₂ - r₂) := by
    omega
  have t := natAbs_add3_le (s₁ - S₁) (S₁ - S₂) (S₂ - s₂)
  have hc₂ : (2 * s₂ - r₂).natAbs = (r₂ - 2 * s₂).natAbs := by
    rw [← Int.natAbs_neg, Int.neg_sub]
  have hs₂ : (S₂ - s₂).natAbs = (s₂ - S₂).natAbs := by rw [← Int.natAbs_neg, Int.neg_sub]
  rw [e]
  refine Nat.le_trans (natAbs_add3_le _ _ _) ?_
  rw [Int.natAbs_mul, hc₂]
  rw [hs₂] at t
  generalize (s₁ - S₁ + (S₁ - S₂) + (S₂ - s₂)).natAbs = X at *
  have : (2 : Int).natAbs = 2 := rfl
  rw [this]
  omega

theorem CodeNear.length_eq {e : Nat} {vs ws : List Value} (h : Forall2 (CodeNear e) vs ws) :
    vs.length = ws.length := h.length_eq

/-- **A correctly rounded `SUM` from its exact sum**: exact sums within
`B/2` units of `2⁻¹⁰⁷⁴` give results within `B + ulp + ulp' + 4` codes.
`floatSumCR_near` (`M∞`) and `floatSumCR_nearL1` (`M₁`) bound `B`. -/
theorem floatSumCR_of_exact {B : Nat} {vs ws : List Value}
    (hS : 2 * (exactSum vs - exactSum ws).natAbs ≤ B) (hv : FinCodes vs) (hw : FinCodes ws)
    (rv : IsFin (ofExact (exactSum vs))) (rw' : IsFin (ofExact (exactSum ws))) :
    (floatSumCR vs - floatSumCR ws).natAbs ≤
      B + ulpDiv (exactSum vs) 1 + ulpDiv (exactSum ws) 1 + 4 := by
  simp only [floatSumCR, nonFinite_of_finCodes hv, nonFinite_of_finCodes hw, Option.getD_none]
  have h1 := ofExactDiv_within (v := exactSum vs) (n := 1) (by omega) rv
  have h2 := ofExactDiv_within (v := exactSum ws) (n := 1) (by omega) rw'
  rw [ofExactDiv_one] at h1 h2
  simp only [Int.natCast_one, Int.one_mul, Nat.one_mul] at h1 h2
  have := round_chain (code_sub_scaled _) (code_sub_scaled _) h1 h2
  generalize (exactSum vs - exactSum ws).natAbs = D at *
  omega

/-- **A correctly rounded `SUM` is Lipschitz** with constant `g` in one cell,
plus the rounding of both sides. -/
theorem floatSumCR_near {e : Nat} {vs ws : List Value} (h : Forall2 (CodeNear e) vs ws)
    (hv : FinCodes vs) (hw : FinCodes ws) (rv : IsFin (ofExact (exactSum vs)))
    (rw' : IsFin (ofExact (exactSum ws))) :
    (floatSumCR vs - floatSumCR ws).natAbs ≤
      vs.length * (e + 1) + ulpDiv (exactSum vs) 1 + ulpDiv (exactSum ws) 1 + 4 :=
  floatSumCR_of_exact (exactSum_near h) hv hw rv rw'

/-- **A correctly rounded `AVG` from its exact sum**: `n` values on each side
whose exact sums are within `n·(E + 1)/2` units give means within
`(E + 1) + ulp + ulp' + 4` codes. -/
theorem floatAvgCR_of_exact {E : Nat} {vs ws : List Value} (hl : vs.length = ws.length)
    (hS : 2 * (exactSum vs - exactSum ws).natAbs ≤ vs.length * (E + 1))
    (hv : FinCodes vs) (hw : FinCodes ws)
    (rv : IsFin (ofExactDiv (exactSum vs) vs.length))
    (rw' : IsFin (ofExactDiv (exactSum ws) ws.length)) :
    (floatAvgCR vs - floatAvgCR ws).natAbs ≤
      (E + 1) + ulpDiv (exactSum vs) vs.length + ulpDiv (exactSum ws) ws.length + 4 := by
  simp only [floatAvgCR, nonFinite_of_finCodes hv, nonFinite_of_finCodes hw, Option.getD_none]
  rcases Nat.eq_zero_or_pos vs.length with h0 | hpos
  · have e1 : vs = [] := List.eq_nil_of_length_eq_zero h0
    have e2 : ws = [] := List.eq_nil_of_length_eq_zero (hl ▸ h0)
    subst e1; subst e2; simp
  have h1 := ofExactDiv_within hpos rv
  have h2 := ofExactDiv_within (hl ▸ hpos) rw'
  rw [← hl] at h2 ⊢
  generalize ofExactDiv (exactSum vs) vs.length = r₁ at *
  generalize ofExactDiv (exactSum ws) vs.length = r₂ at *
  generalize exactSum vs = S₁ at *
  generalize exactSum ws = S₂ at *
  generalize ulpDiv S₁ vs.length = u₁ at *
  generalize ulpDiv S₂ vs.length = u₂ at *
  generalize vs.length = n at *
  -- `2n·|s₁ − s₂| ≤ n·(u₁ + u₂) + n·(E + 1)`, divided by `n`.
  have t : ((n : Int) * scaled r₁ - (n : Int) * scaled r₂).natAbs =
      n * (scaled r₁ - scaled r₂).natAbs := by
    rw [← Int.mul_sub, Int.natAbs_mul, Int.natAbs_natCast]
  have tri := natAbs_add3_le ((n : Int) * scaled r₁ - S₁) (S₁ - S₂) (S₂ - (n : Int) * scaled r₂)
  have hs₂ : (S₂ - (n : Int) * scaled r₂).natAbs = ((n : Int) * scaled r₂ - S₂).natAbs := by
    rw [← Int.natAbs_neg, Int.neg_sub]
  rw [show (n : Int) * scaled r₁ - S₁ + (S₁ - S₂) + (S₂ - (n : Int) * scaled r₂) =
    (n : Int) * scaled r₁ - (n : Int) * scaled r₂ by omega, t, hs₂] at tri
  have rc := round_chain (r₁ := r₁) (r₂ := r₂) (S₁ := scaled r₁) (S₂ := scaled r₂) (u₁ := 0)
    (u₂ := 0) (code_sub_scaled _) (code_sub_scaled _) (by simp) (by simp)
  generalize (scaled r₁ - scaled r₂).natAbs = D at *
  generalize ((n : Int) * scaled r₁ - S₁).natAbs = A₁ at *
  generalize ((n : Int) * scaled r₂ - S₂).natAbs = A₂ at *
  generalize (S₁ - S₂).natAbs = B at *
  have hD : n * (2 * D) ≤ n * (u₁ + u₂ + (E + 1)) := by
    rw [Nat.mul_left_comm, Nat.mul_add, Nat.mul_add]; omega
  have := Nat.le_of_mul_le_mul_left hD hpos
  generalize (r₁ - r₂).natAbs = R at *
  omega

/-- **A correctly rounded `AVG` is Lipschitz** with constant `1` in one cell,
plus the rounding of both sides. -/
theorem floatAvgCR_near {e : Nat} {vs ws : List Value} (h : Forall2 (CodeNear e) vs ws)
    (hv : FinCodes vs) (hw : FinCodes ws)
    (rv : IsFin (ofExactDiv (exactSum vs) vs.length))
    (rw' : IsFin (ofExactDiv (exactSum ws) ws.length)) :
    (floatAvgCR vs - floatAvgCR ws).natAbs ≤
      (e + 1) + ulpDiv (exactSum vs) vs.length + ulpDiv (exactSum ws) ws.length + 4 :=
  floatAvgCR_of_exact h.length_eq (exactSum_near h) hv hw rv rw'

/-! ## The `M₁` form: distances summed over the pairs -/

/-- **Two lists paired within a budget**: the `k`-th pair related by `R dₖ`,
with `Σ dₖ ≤ D`. The `M₁` form of `Forall2 (R e)`, what a `SUM` over the
pairs sees. -/
def ListL1 {α β : Type} (R : Nat → α → β → Prop) : List α → List β → Nat → Prop
  | [], [], _ => True
  | x :: xs, y :: ys, D => ∃ d r, R d x y ∧ ListL1 R xs ys r ∧ d + r ≤ D
  | _, _, _ => False

section
variable {α β : Type} {R S : Nat → α → β → Prop}

theorem ListL1.mono : ∀ {xs : List α} {ys : List β} {D D' : Nat}, ListL1 R xs ys D → D ≤ D' →
    ListL1 R xs ys D'
  | [], [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _, _, ⟨d, r, h, t, le⟩, hD => ⟨d, r, h, t, by omega⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem ListL1.length_eq : ∀ {xs : List α} {ys : List β} {D : Nat}, ListL1 R xs ys D →
    xs.length = ys.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, ⟨_, _, _, t, _⟩ => by simp [ListL1.length_eq t]
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem ListL1.of_forall2 {e : Nat} : ∀ {xs : List α} {ys : List β}, Forall2 (R e) xs ys →
    ListL1 R xs ys (xs.length * e)
  | _, _, .nil => trivial
  | _, _, .cons h t => ⟨e, _, h, ListL1.of_forall2 t, by simp [Nat.succ_mul]; omega⟩

/-- Each pair's own distance is within the budget. -/
theorem ListL1.imp (hS : ∀ d x y, d ≤ D₀ → x ∈ xs₀ → y ∈ ys₀ → R d x y → S d x y) :
    ∀ {xs : List α} {ys : List β} {D : Nat}, ListL1 R xs ys D → D ≤ D₀ → xs ⊆ xs₀ → ys ⊆ ys₀ →
      ListL1 S xs ys D
  | [], [], _, _, _, _, _ => trivial
  | x :: _, y :: _, _, ⟨d, r, h, t, le⟩, hD, hx, hy =>
    ⟨d, r, hS d x y (by omega) (hx (List.mem_cons_self ..)) (hy (List.mem_cons_self ..)) h,
      ListL1.imp hS t (by omega) (fun _ h' => hx (List.mem_cons_of_mem _ h'))
        (fun _ h' => hy (List.mem_cons_of_mem _ h')), le⟩
  | [], _ :: _, _, h, _, _, _ | _ :: _, [], _, h, _, _, _ => h.elim

theorem ListL1.map {γ δ : Type} {S : Nat → γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hf : ∀ d x y, R d x y → S d (f x) (g y)) :
    ∀ {xs : List α} {ys : List β} {D : Nat}, ListL1 R xs ys D → ListL1 S (xs.map f) (ys.map g) D
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, _, ⟨d, r, h, t, le⟩ => ⟨d, r, hf _ _ _ h, ListL1.map hf t, le⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- **Fewer pairs** sum to less. -/
theorem ListL1.filter {p : α → Bool} {p' : β → Bool} (hp : ∀ d x y, R d x y → p x = p' y) :
    ∀ {xs : List α} {ys : List β} {D : Nat}, ListL1 R xs ys D →
      ListL1 R (xs.filter p) (ys.filter p') D
  | [], [], _, _ => trivial
  | x :: _, y :: _, _, ⟨d, r, h, t, le⟩ => by
    rw [List.filter_cons, List.filter_cons, hp d x y h]
    split
    · exact ⟨d, r, h, ListL1.filter hp t, le⟩
    · exact (ListL1.filter hp t).mono (by omega)
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

end

theorem exactSum_nearL1 : ∀ {vs ws : List Value} {D : Nat}, ListL1 CodeNear vs ws D →
    2 * (exactSum vs - exactSum ws).natAbs ≤ D + vs.length
  | [], [], _, _ => by simp [exactSum]
  | _ :: _, _ :: _, _, ⟨d, r, h, t, le⟩ => by
    have ih := exactSum_nearL1 t
    have := h.exactOf
    simp only [exactSum_cons, List.length_cons]
    omega
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

/-- **A correctly rounded `SUM` in `M₁`**: values whose distances sum to at
most `D` codes give sums within `D + g + ulp + ulp' + 4` codes, `g` values. -/
theorem floatSumCR_nearL1 {D : Nat} {vs ws : List Value} (h : ListL1 CodeNear vs ws D)
    (hv : FinCodes vs) (hw : FinCodes ws) (rv : IsFin (ofExact (exactSum vs)))
    (rw' : IsFin (ofExact (exactSum ws))) :
    (floatSumCR vs - floatSumCR ws).natAbs ≤
      D + vs.length + ulpDiv (exactSum vs) 1 + ulpDiv (exactSum ws) 1 + 4 :=
  floatSumCR_of_exact (exactSum_nearL1 h) hv hw rv rw'

/-- **A correctly rounded `AVG` in `M₁`**: values whose distances sum to at
most `D` codes give means within `(D + 1) + ulp + ulp' + 4` codes. -/
theorem floatAvgCR_nearL1 {D : Nat} {vs ws : List Value} (h : ListL1 CodeNear vs ws D)
    (hv : FinCodes vs) (hw : FinCodes ws)
    (rv : IsFin (ofExactDiv (exactSum vs) vs.length))
    (rw' : IsFin (ofExactDiv (exactSum ws) ws.length)) :
    (floatAvgCR vs - floatAvgCR ws).natAbs ≤
      (D + 1) + ulpDiv (exactSum vs) vs.length + ulpDiv (exactSum ws) ws.length + 4 := by
  refine floatAvgCR_of_exact h.length_eq ?_ hv hw rv rw'
  have := exactSum_nearL1 h
  rcases Nat.eq_zero_or_pos vs.length with h0 | hpos
  · have e1 : vs = [] := List.eq_nil_of_length_eq_zero h0
    have e2 : ws = [] := List.eq_nil_of_length_eq_zero (h.length_eq ▸ h0)
    subst e1; subst e2; simp [exactSum]
  · have : D ≤ vs.length * D := Nat.le_mul_of_pos_left D hpos
    rw [Nat.mul_add]; omega

end Substrait
