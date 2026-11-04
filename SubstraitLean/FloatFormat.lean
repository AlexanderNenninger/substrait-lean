/-!
# Binary floating-point formats (#417)

A format is its precision `p` (significand bits, the leading one included)
and its largest exponent `emax`, not its width in bits: binary64 is `p = 53`,
`emax = 1023`, binary32 is `p = 24`, `emax = 127`, and binary16 and
bfloat16 are both 16 bits wide, with `p = 11` and `p = 8`.

Every finite value is `±m · 2^-scale` with `scale = emax + p - 2` and an
integer magnitude `m`, so a value has an integer *code* in the SQL order
(`SubstraitLean/Float.lean`): `±(2m + 1)` for the magnitude `m`, `0` for the
one zero, `M + 1` for ∞ and `M + 2` for the one NaN, where `M` is the largest
finite magnitude. `-0.0` and the negative NaN have codes of their own
outside that range (#444 step 1b), which `canon` maps to `0` and NaN. What is
stated here holds for every format: the codes,
their order and what the checker knows of a cast into the format. `fp64`, on
Lean's native `Float`, is the only instance so far (`SubstraitLean/Float.lean`).
-/

namespace Substrait

/-- A binary floating-point format: its precision and its largest exponent. -/
structure FloatFormat where
  /-- Significand bits, the leading one included. -/
  p : Nat
  /-- The largest exponent; the smallest normal one is `1 - emax`. -/
  emax : Nat
  deriving Repr, DecidableEq

namespace FloatFormat

variable (F : FloatFormat)

/-- `|x| · 2^scale` is an integer for every finite `x`: the spacing of the
subnormals is `2^(1 - emax - (p - 1))`. -/
def scale : Nat := F.emax + F.p - 2

/-- The magnitude of the largest finite value, `(2ᵖ − 1) · 2^(emax + 1 − p)`. -/
@[irreducible] def maxMag : Nat := (2 ^ F.p - 1) * 2 ^ (F.emax + 1 - F.p + F.scale)

def infMag : Nat := F.maxMag + 1
def nanMag : Nat := F.maxMag + 2

/-- The code of magnitude `m`: zero has one code, `0`, and NaN is never
negative. -/
def ofMag (negative : Bool) (m : Nat) : Int :=
  let c : Int := 2 * m + 1
  if m = 0 then 0 else if negative ∧ m ≠ F.nanMag then -c else c

def posInf : Int := F.ofMag false F.infMag
def negInf : Int := F.ofMag true F.infMag
def nan : Int := F.ofMag false F.nanMag

/-- A code strictly between `-∞` and `+∞`: other codes become the largest
finite value of their sign. -/
def finite (c : Int) : Int :=
  if F.posInf ≤ c then F.ofMag false F.maxMag else if c ≤ F.negInf then F.ofMag true F.maxMag else c

/-- The code of an integer that is a value of the format exactly (`|i| ≤ 2ᵖ`). -/
def exactCode (i : Int) : Int :=
  let m : Int := (i.natAbs * 2 ^ F.scale : Nat)
  if i = 0 then 0 else if i < 0 then -(2 * m + 1) else 2 * m + 1

/-- The code of magnitude `m`, negative if `neg` (the same in every format). -/
def _root_.Substrait.FloatFormat.signedCode (neg : Bool) (m : Nat) : Int :=
  if m = 0 then 0 else if neg then -(2 * (m : Int) + 1) else 2 * (m : Int) + 1

/-! ## The order of the codes

`-∞ < negatives < 0 < positives < +∞ < NaN`. -/

theorem posInf_eq : F.posInf = 2 * F.maxMag + 3 := by
  simp only [posInf, ofMag, infMag, Nat.add_one_ne_zero, ite_false, Bool.false_eq_true,
    false_and]
  omega

theorem negInf_eq : F.negInf = -(2 * F.maxMag + 3) := by
  have : F.maxMag + 1 ≠ F.nanMag := by simp [nanMag]
  simp only [negInf, ofMag, infMag, Nat.add_one_ne_zero, ite_false, true_and, this, ne_eq,
    not_false_eq_true, ite_true]
  omega

theorem nan_eq : F.nan = 2 * F.maxMag + 5 := by
  have h : F.maxMag + 2 ≠ 0 := by omega
  simp only [nan, ofMag, nanMag, h, ite_false, Bool.false_eq_true, false_and]
  omega

theorem posInf_lt_nan : F.posInf < F.nan := by rw [posInf_eq, nan_eq]; omega

theorem negInf_lt_zero : F.negInf < 0 := by rw [negInf_eq]; omega

theorem zero_lt_posInf : 0 < F.posInf := by rw [posInf_eq]; omega

theorem maxMag_pos (hp : 1 ≤ F.p) : 0 < F.maxMag := by
  unfold maxMag
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))) (Nat.two_pow_pos _)

theorem finite_bounds (hp : 1 ≤ F.p) (c : Int) : F.negInf < F.finite c ∧ F.finite c < F.posInf := by
  have hM := F.maxMag_pos hp
  have hn : F.maxMag ≠ F.nanMag := by simp [nanMag]
  simp only [finite, ofMag, posInf_eq, negInf_eq, Nat.pos_iff_ne_zero.1 hM, ite_false, hn,
    Bool.false_eq_true, false_and, true_and, ne_eq, not_false_eq_true, ite_true]
  split <;> (try split) <;> omega

/-! ## `-0.0` and the negative NaN (#444 step 1b)

Two codes outside the range `[-∞, NaN]` of the codes above: `negNan`, the
code negation of NaN, and `negZero`, the even code below it. The reference
never produces them, so its codes keep their values and their order. `canon`
maps `-0.0` to `+0.0` and the negative NaN to the NaN (`ONE_ZERO` and
`ONE_NAN`, `docs/core-semantics.md`); `key` orders the full set as the
`IEEE` behaviours of `zero_sign` and `nan_order` do: `-0.0` right below
`+0.0`, the negative NaN above `+∞` and below the NaN (`GREATEST`). -/

/-- The negative NaN: the code negation of NaN. -/
def negNan : Int := -F.nan

/-- `-0.0`: an even code below every other, so no magnitude has it. -/
def negZero : Int := -(F.nan + 1)

/-- A code of the reference: from `-∞` to NaN. -/
def IsRef (c : Int) : Prop := F.negInf ≤ c ∧ c ≤ F.nan

instance (c : Int) : Decidable (F.IsRef c) := inferInstanceAs (Decidable (_ ∧ _))

/-- One zero and one NaN: `-0.0` becomes `+0.0`, the negative NaN the NaN. -/
def canon (c : Int) : Int := if c = F.negZero then 0 else if c = F.negNan then F.nan else c

/-- The order of the full set: twice the code for the others, `-0.0` right
below `+0.0` and the negative NaN right below the NaN. -/
def key (c : Int) : Int := if c = F.negZero then -1 else if c = F.negNan then 2 * F.nan - 1 else 2 * c

theorem negNan_eq : F.negNan = -(2 * F.maxMag + 5) := by rw [negNan, nan_eq]

theorem negZero_eq : F.negZero = -(2 * F.maxMag + 6) := by rw [negZero, nan_eq]; omega

theorem negZero_ne_negNan : F.negZero ≠ F.negNan := by rw [negZero_eq, negNan_eq]; omega

theorem not_isRef_negZero : ¬ F.IsRef F.negZero := by
  simp only [IsRef, negZero_eq, negInf_eq]; omega

theorem not_isRef_negNan : ¬ F.IsRef F.negNan := by
  simp only [IsRef, negNan_eq, negInf_eq]; omega

/-- The reference's codes are fixed. -/
theorem canon_of_isRef {c : Int} (h : F.IsRef c) : F.canon c = c := by
  have h1 : c ≠ F.negZero := fun e => F.not_isRef_negZero (e ▸ h)
  have h2 : c ≠ F.negNan := fun e => F.not_isRef_negNan (e ▸ h)
  simp [canon, h1, h2]

theorem canon_negZero : F.canon F.negZero = 0 := by simp [canon]

theorem canon_negNan : F.canon F.negNan = F.nan := by simp [canon, F.negZero_ne_negNan.symm]

theorem isRef_canon_of_isRef_or {c : Int} (h : F.IsRef c ∨ c = F.negZero ∨ c = F.negNan) :
    F.IsRef (F.canon c) := by
  have := F.posInf_lt_nan; have := F.negInf_lt_zero; have := F.zero_lt_posInf
  rcases h with h | rfl | rfl
  · rwa [F.canon_of_isRef h]
  · rw [canon_negZero]; exact ⟨by omega, by omega⟩
  · rw [canon_negNan]; exact ⟨by omega, Int.le_refl _⟩

/-- `canon` never gives a new code. -/
theorem canon_ne (c : Int) : F.canon c ≠ F.negZero ∧ F.canon c ≠ F.negNan := by
  have := F.nan_eq; have := F.negNan_eq; have := F.negZero_eq
  unfold canon
  by_cases h1 : c = F.negZero
  · simp only [h1, ite_true]; omega
  · by_cases h2 : c = F.negNan
    · simp only [h2, ite_true]; omega
    · simp only [h1, h2, ite_false]; exact ⟨h1, h2⟩

theorem canon_eq_self {c : Int} (h : c ≠ F.negZero ∧ c ≠ F.negNan) : F.canon c = c := by
  simp [canon, h.1, h.2]

theorem canon_idem (c : Int) : F.canon (F.canon c) = F.canon c :=
  F.canon_eq_self (F.canon_ne c)

/-- `canon` is order-preserving: from the full set's order to the
reference's. -/
theorem canon_mono {a b : Int} (h : F.key a ≤ F.key b) : F.canon a ≤ F.canon b := by
  have := F.nan_eq; have := F.negNan_eq; have := F.negZero_eq
  unfold key at h; unfold canon
  by_cases a1 : a = F.negZero <;> by_cases a2 : a = F.negNan <;>
    by_cases b1 : b = F.negZero <;> by_cases b2 : b = F.negNan <;>
    simp only [a1, a2, b1, b2, ite_true, ite_false] at h ⊢ <;> omega

/-- On the reference's codes, `key` is the order of the codes. -/
theorem key_of_isRef {c : Int} (h : F.IsRef c) : F.key c = 2 * c := by
  have h1 : c ≠ F.negZero := fun e => F.not_isRef_negZero (e ▸ h)
  have h2 : c ≠ F.negNan := fun e => F.not_isRef_negNan (e ▸ h)
  simp [key, h1, h2]

theorem key_le_iff {a b : Int} (ha : F.IsRef a) (hb : F.IsRef b) : F.key a ≤ F.key b ↔ a ≤ b := by
  rw [F.key_of_isRef ha, F.key_of_isRef hb]; omega

/-- `-0.0` is right below `+0.0`, and the negative NaN right below the NaN,
above `+∞`. -/
theorem key_negZero : F.key F.negZero + 1 = F.key 0 := by
  have := F.posInf_lt_nan; have := F.negInf_lt_zero; have := F.zero_lt_posInf
  rw [F.key_of_isRef (c := 0) ⟨by omega, by omega⟩]
  simp [key]

theorem key_negNan : F.key F.negNan + 1 = F.key F.nan ∧ F.key F.posInf < F.key F.negNan := by
  have := F.posInf_lt_nan; have := F.negInf_lt_zero; have := F.zero_lt_posInf
  rw [F.key_of_isRef (c := F.nan) ⟨by omega, Int.le_refl _⟩,
    F.key_of_isRef (c := F.posInf) ⟨by omega, by omega⟩]
  simp only [key, F.negZero_ne_negNan.symm, ite_false, ite_true]
  omega

/-- No magnitude has a new code: what `ofMag` gives is fixed by `canon`. -/
theorem canon_ofMag (neg : Bool) (m : Nat) : F.canon (F.ofMag neg m) = F.ofMag neg m := by
  apply F.canon_eq_self
  have := F.negNan_eq; have := F.negZero_eq
  have hn : F.nanMag = F.maxMag + 2 := rfl
  unfold ofMag; dsimp only
  by_cases h0 : m = 0
  · simp only [h0, ite_true]; omega
  · by_cases h1 : neg = true ∧ m ≠ F.nanMag
    · simp only [h0, h1, ite_false]; have := h1.2; omega
    · simp only [h0, h1, ite_false]; omega

/-- The reference's finite codes are fixed. -/
theorem canon_finite (c : Int) : F.canon (F.finite c) = F.finite c := by
  unfold finite; split
  · exact F.canon_ofMag _ _
  · split
    · exact F.canon_ofMag _ _
    · rename_i h1 h2
      apply F.canon_eq_self
      have := F.negInf_eq; have := F.posInf_eq; have := F.negNan_eq; have := F.negZero_eq
      omega

/-! ## Casts into the format

The checker reasons about a cast only through these contracts; each instance
proves them of its computation and puts it behind an `opaque` constant. -/

/-- A monotone cast into the finite values of the format: of integers, or of
decimals at one scale. The checker bounds its results by the casts of the
ends. -/
structure FiniteMonoConv where
  conv : Int → Int
  bounds : ∀ i, F.negInf < conv i ∧ conv i < F.posInf
  mono : ∀ {i j}, i ≤ j → conv i ≤ conv j

/-- A cast of integers into the format: integers up to `2ᵖ` are values
exactly, and up to `2^emax` the cast is within half a unit in the last place,
`2⁻ᵖ` relatively (as magnitudes `· 2^scale`). -/
structure IntConv extends F.FiniteMonoConv where
  ne_zero : ∀ {i}, i ≠ 0 → conv i ≠ 0
  exact : ∀ {i}, i.natAbs ≤ 2 ^ F.p → conv i = F.exactCode i
  rel : ∀ {i}, i ≠ 0 → i.natAbs ≤ 2 ^ F.emax → ∃ M, conv i = signedCode (decide (i < 0)) M ∧
    2 ^ F.p * M ≤ (2 ^ F.p + 1) * (i.natAbs * 2 ^ F.scale) ∧
    (2 ^ F.p - 1) * (i.natAbs * 2 ^ F.scale) ≤ 2 ^ F.p * M

end FloatFormat

/-- binary64, the double: Lean's native `Float`. -/
def fp64 : FloatFormat := ⟨53, 1023⟩

theorem fp64_scale : fp64.scale = 1074 := rfl

set_option exponentiation.threshold 2100 in
theorem fp64_maxMag : fp64.maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := by
  unfold FloatFormat.maxMag; rfl

end Substrait
