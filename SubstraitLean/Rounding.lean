import SubstraitLean.Float

/-!
# Exact rounding of doubles

`FLOOR`, `CEIL`, `ROUND` (to an integer) and `CAST(double AS BIGINT)` are
computed exactly on double codes (see `SubstraitLean/Float.lean`), not with
native floats, so that their monotonicity, and the range of a cast, can be
proved.

A finite double is `±m · 2⁻¹⁰⁷⁴`, so rounding it to an integer rounds the
magnitude `m` to a multiple of `K = 2¹⁰⁷⁴`. The sign is kept, except that a
zero result is the one zero (`CEIL(-0.5)` is `0.0`); NaN and ±∞ are left alone. Every multiple of `K` up to `maxMag` is a
double, so the results are doubles.
-/

namespace Substrait.FloatCode

-- Doubles involve powers of two up to 2²⁰⁴⁵.
set_option exponentiation.threshold 2100

def K : Nat := 2 ^ 1074

def floorMag (m : Nat) : Nat := m / K * K
def ceilMag (m : Nat) : Nat := (m + K - 1) / K * K
/-- Halves round away from zero, as SQL's `ROUND` does. -/
def roundMag (m : Nat) : Nat := (m + K / 2) / K * K

/-- The magnitude of a code (for finite codes, `|x| · 2¹⁰⁷⁴`). -/
def mag (c : Int) : Nat := (c.natAbs - 1) / 2

/-- The non-negative code of magnitude `m` (`0` for zero). -/
def code (m : Nat) : Int := if m = 0 then 0 else 2 * (m : Int) + 1

/-- Apply `pos` to the magnitude of a non-negative finite code and `neg` to
that of a negative one; NaN and ±∞ stay. -/
def onMag (pos neg : Nat → Nat) (c : Int) : Int :=
  if maxMag < mag c then c
  else if c < 0 then -code (neg (mag c)) else code (pos (mag c))

def floor : Int → Int := onMag floorMag ceilMag
def ceil : Int → Int := onMag ceilMag floorMag
def round : Int → Int := onMag roundMag roundMag

/-- `CAST(x AS BIGINT)`: truncation toward zero, or `none` for NaN and ±∞.
(The 64-bit range is checked separately.) -/
def toInt? (c : Int) : Option Int :=
  if maxMag < mag c then none
  else some (if c < 0 then -((mag c / K : Nat) : Int) else ((mag c / K : Nat) : Int))

/-! ## Monotonicity -/

theorem maxMag_eq : maxMag = (2 ^ 53 - 1) * 2 ^ 971 * K := by
  unfold maxMag K; rw [Nat.mul_assoc, ← Nat.pow_add]

theorem floorMag_mono {m n : Nat} (h : m ≤ n) : floorMag m ≤ floorMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

theorem ceilMag_mono {m n : Nat} (h : m ≤ n) : ceilMag m ≤ ceilMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem roundMag_mono {m n : Nat} (h : m ≤ n) : roundMag m ≤ roundMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem K_pos : 0 < K := Nat.pow_pos (by decide)

theorem ceilMag_le {m N : Nat} (hm : m ≤ N * K) : ceilMag m ≤ N * K := by
  unfold ceilMag
  apply Nat.mul_le_mul_right
  have := K_pos
  have h : (m + K - 1) / K < N + 1 := (Nat.div_lt_iff_lt_mul K_pos).mpr (by rw [Nat.succ_mul]; omega)
  omega

theorem floorMag_le (m : Nat) : floorMag m ≤ m := Nat.div_mul_le_self m K

theorem roundMag_le_ceilMag (m : Nat) : roundMag m ≤ ceilMag m := by
  unfold roundMag ceilMag
  apply Nat.mul_le_mul_right
  apply Nat.div_le_div_right
  have := K_pos
  omega

theorem maxMag_bound {f : Nat → Nat} (hf : ∀ m, m ≤ maxMag → f m ≤ maxMag) {m : Nat}
    (hm : m ≤ maxMag) : f m ≤ maxMag := hf m hm

theorem floorMag_bound (m : Nat) (hm : m ≤ maxMag) : floorMag m ≤ maxMag :=
  Nat.le_trans (floorMag_le m) hm

theorem ceilMag_bound (m : Nat) (hm : m ≤ maxMag) : ceilMag m ≤ maxMag := by
  rw [maxMag_eq] at *; exact ceilMag_le hm

theorem roundMag_bound (m : Nat) (hm : m ≤ maxMag) : roundMag m ≤ maxMag :=
  Nat.le_trans (roundMag_le_ceilMag m) (ceilMag_bound m hm)

theorem mag_le_of_nonneg {c d : Int} (hc : 0 ≤ c) (h : c ≤ d) : mag c ≤ mag d :=
  Nat.div_le_div_right (by omega)

theorem mag_le_of_neg {c d : Int} (hd : d < 0) (h : c ≤ d) : mag d ≤ mag c :=
  Nat.div_le_div_right (by omega)

theorem code_mono {m n : Nat} (h : m ≤ n) : code m ≤ code n := by
  unfold code; split <;> split <;> omega

theorem code_nonneg (m : Nat) : 0 ≤ code m := by unfold code; split <;> omega

theorem code_le (m : Nat) : code m ≤ 2 * (m : Int) + 1 := by unfold code; split <;> omega

/-- `onMag` is monotone when both magnitude maps are, and keep finite
magnitudes finite. -/
theorem onMag_mono {pos neg : Nat → Nat}
    (hp : ∀ {m n}, m ≤ n → pos m ≤ pos n) (hn : ∀ {m n}, m ≤ n → neg m ≤ neg n)
    (hpb : ∀ m, m ≤ maxMag → pos m ≤ maxMag) (hnb : ∀ m, m ≤ maxMag → neg m ≤ maxMag)
    {c d : Int} (h : c ≤ d) : onMag pos neg c ≤ onMag pos neg d := by
  unfold onMag
  have hmc : mag c = (c.natAbs - 1) / 2 := rfl
  have hmd : mag d = (d.natAbs - 1) / 2 := rfl
  have := code_nonneg (pos (mag c)); have := code_nonneg (pos (mag d))
  have := code_nonneg (neg (mag c)); have := code_nonneg (neg (mag d))
  have := code_le (pos (mag c)); have := code_le (neg (mag d))
  by_cases hd : d < 0
  · have hc : c < 0 := by omega
    have := code_mono (hn (mag_le_of_neg hd h))
    by_cases h₁ : maxMag < mag c <;> by_cases h₂ : maxMag < mag d <;> simp only [h₁, h₂, hc, hd,
      ite_true, ite_false] <;> first | omega | (have := hnb _ (Nat.not_lt.mp h₂); omega)
  · by_cases hc : c < 0
    · by_cases h₁ : maxMag < mag c <;> by_cases h₂ : maxMag < mag d <;> simp only [h₁, h₂, hc, hd,
        ite_true, ite_false] <;> omega
    · have := code_mono (hp (mag_le_of_nonneg (by omega) h))
      by_cases h₁ : maxMag < mag c <;> by_cases h₂ : maxMag < mag d <;> simp only [h₁, h₂, hc, hd,
        ite_true, ite_false] <;> first | omega | (have := hpb _ (Nat.not_lt.mp h₁); omega)

theorem floor_mono {c d : Int} (h : c ≤ d) : floor c ≤ floor d :=
  onMag_mono floorMag_mono ceilMag_mono floorMag_bound ceilMag_bound h

theorem ceil_mono {c d : Int} (h : c ≤ d) : ceil c ≤ ceil d :=
  onMag_mono ceilMag_mono floorMag_mono ceilMag_bound floorMag_bound h

theorem round_mono {c d : Int} (h : c ≤ d) : round c ≤ round d :=
  onMag_mono roundMag_mono roundMag_mono roundMag_bound roundMag_bound h

theorem toInt?_mono {c d : Int} {x y : Int} (h : c ≤ d) (hx : toInt? c = some x)
    (hy : toInt? d = some y) : x ≤ y := by
  unfold toInt? at hx hy
  split at hx <;> split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hx hy
  subst hx hy
  by_cases hd : d < 0
  · have hc : c < 0 := by omega
    have := Nat.div_le_div_right (c := K) (mag_le_of_neg hd h)
    simp only [hc, hd, ite_true]
    generalize mag c / K = p at *; generalize mag d / K = q at *; omega
  · have hq := Nat.div_le_div_right (c := K) (mag_le_of_nonneg (c := 0) (by omega) (by omega : 0 ≤ d))
    by_cases hc : c < 0
    · simp only [hc, hd, ite_true, ite_false]
      generalize mag c / K = p at *; generalize mag d / K = q at *; omega
    · have := Nat.div_le_div_right (c := K) (mag_le_of_nonneg (by omega) h)
      simp only [hc, hd, ite_false]
      generalize mag c / K = p at *; generalize mag d / K = q at *; omega

/-- Codes between two finite codes are finite. -/
theorem toInt?_between {lo hi c x y : Int} (hl : lo ≤ c) (hh : c ≤ hi)
    (hx : toInt? lo = some x) (hy : toInt? hi = some y) : ∃ z, toInt? c = some z := by
  unfold toInt? at *
  split at hx <;> split at hy <;> simp only [Option.some.injEq, reduceCtorEq] at hx hy
  rename_i h₁ h₂
  have : mag c ≤ maxMag := by
    by_cases hc : c < 0
    · have := mag_le_of_neg hc hl; omega
    · have := mag_le_of_nonneg (by omega) hh; omega
  exact ⟨_, by simp only [show ¬ maxMag < mag c from by omega, ↓reduceIte]; rfl⟩

/-! ## The 64-bit range of a cast -/

def minI64 : Int := -(2 ^ 63)
def maxI64 : Int := 2 ^ 63 - 1

/-- Codes of `-2⁶³` and just below `2⁶³`: every code in between casts to a
`BIGINT`. -/
def castLo : Int := -(2 * ((2 ^ 63 * K : Nat) : Int) + 1)
def castHi : Int := 2 * ((2 ^ 63 * K : Nat) : Int)

theorem big_lt_maxMag : 2 ^ 63 * K < maxMag := by
  have h₁ : 2 ^ 63 < 2 ^ 971 := Nat.pow_lt_pow_right (by decide) (by decide)
  have h₂ : 2 ^ 971 ≤ (2 ^ 53 - 1) * 2 ^ 971 := Nat.le_mul_of_pos_left _ (by decide)
  rw [maxMag_eq]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_lt_of_le h₁ h₂) K_pos

theorem toInt?_of_range {c : Int} (hlo : castLo ≤ c) (hhi : c ≤ castHi) :
    ∃ x, toInt? c = some x ∧ minI64 ≤ x ∧ x ≤ maxI64 := by
  have hK := K_pos
  have hbig := big_lt_maxMag
  simp only [castLo, castHi] at hlo hhi
  have hm : mag c ≤ 2 ^ 63 * K := by unfold mag; omega
  refine ⟨_, by unfold toInt?; simp only [show ¬ maxMag < mag c from by omega, ↓reduceIte]; rfl, ?_⟩
  by_cases hc : c < 0 <;> simp only [hc, ite_true, ite_false, minI64, maxI64]
  · have : mag c / K ≤ 2 ^ 63 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
    generalize mag c / K = p at *; omega
  · have hm' : mag c < 2 ^ 63 * K := by unfold mag; omega
    have : mag c / K < 2 ^ 63 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hm')
    generalize mag c / K = p at *; omega

-- Other files reason about these only through the lemmas above; unfolding them
-- would make `simp` evaluate `2²⁰⁴⁵`.
attribute [irreducible] floor ceil round toInt?

/-! ## Checks against DataFusion -/

#guard floor (ofFloat 2.5) == ofFloat 2.0 && floor (ofFloat (-2.5)) == ofFloat (-3.0)
#guard ceil (ofFloat 2.5) == ofFloat 3.0 && ceil (ofFloat (-2.5)) == ofFloat (-2.0)
#guard ceil (ofFloat (-0.5)) == 0 && floor (ofFloat 0.5) == 0
#guard round (ofFloat 2.5) == ofFloat 3.0 && round (ofFloat (-2.5)) == ofFloat (-3.0)
#guard round (ofFloat 2.4) == ofFloat 2.0 && round (ofFloat (-0.4)) == 0
#guard floor posInf == posInf && round nan == nan
#guard floor (ofFloat 1e300) == ofFloat 1e300
#guard toInt? (ofFloat 2.7) == some 2 && toInt? (ofFloat (-2.7)) == some (-2)
#guard toInt? (ofFloat 9.2e18) == some 9200000000000000000
#guard toInt? nan == none && toInt? negInf == none
#guard castHi < ofFloat 9.223372036854775808e18 && castLo == ofFloat (-9.223372036854775808e18)

end Substrait.FloatCode
