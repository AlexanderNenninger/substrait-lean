import Sverify.Core.Float

/-!
# Exact rounding of doubles

`FLOOR`, `CEIL`, `ROUND` (to an integer) and `CAST(double AS BIGINT)` are
computed exactly on double codes (see `core/Sverify/Core/Float.lean`), not with
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

/-- `m / K` rounded to the nearest integer, halves to the even one: the integer
part of a double's magnitude `m` as IEEE 754's roundToIntegralTiesToEven takes it
(D55), and as DuckDB's cast takes it (R9). -/
def evenQuot (m : Nat) : Nat :=
  if 2 * (m % K) < K then m / K
  else if K < 2 * (m % K) then m / K + 1
  else if m / K % 2 = 0 then m / K else m / K + 1
/-- Halves round to the even integer, as `round_even` and `bround` do. -/
def evenMag (m : Nat) : Nat := evenQuot m * K
def roundEven : Int → Int := onMag evenMag evenMag

/-- `CAST(x AS BIGINT)`: truncation toward zero, or `none` for NaN and ±∞.
(The 64-bit range is checked separately.) -/
def toInt? (c : Int) : Option Int :=
  if maxMag < mag c then none
  else some (if c < 0 then -((mag c / K : Nat) : Int) else ((mag c / K : Nat) : Int))

/-! ## Monotonicity -/

theorem maxMag_eq : maxMag = (2 ^ 53 - 1) * 2 ^ 971 * K := by
  rw [maxMag_def]; unfold K; rw [Nat.mul_assoc, ← Nat.pow_add]

theorem floorMag_mono {m n : Nat} (h : m ≤ n) : floorMag m ≤ floorMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

theorem ceilMag_mono {m n : Nat} (h : m ≤ n) : ceilMag m ≤ ceilMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem roundMag_mono {m n : Nat} (h : m ≤ n) : roundMag m ≤ roundMag n :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

theorem K_pos : 0 < K := Nat.pow_pos (by decide)

theorem K_even : K = 2 * (K / 2) := by unfold K; decide +kernel

theorem evenQuot_spec (m : Nat) : m / K ≤ evenQuot m ∧ evenQuot m ≤ m / K + 1 ∧
    (2 * (m % K) < K → evenQuot m = m / K) ∧ (K < 2 * (m % K) → evenQuot m = m / K + 1) ∧
    (2 * (m % K) = K → (m / K % 2 = 0 → evenQuot m = m / K) ∧
      (m / K % 2 ≠ 0 → evenQuot m = m / K + 1)) := by
  unfold evenQuot
  split <;> (try split) <;> (try split) <;> omega

theorem evenMag_le_roundMag (m : Nat) : evenMag m ≤ roundMag m := by
  have hK := K_pos
  have he := K_even
  have hs := evenQuot_spec m
  unfold evenMag roundMag
  apply Nat.mul_le_mul_right
  apply (Nat.le_div_iff_mul_le hK).2
  have h1 := Nat.div_add_mod m K
  have h2 := Nat.mod_lt m hK
  have h3 := Nat.div_mul_le_self m K
  obtain ⟨a, b, c, d, e⟩ := hs
  generalize evenQuot m = u at *
  generalize m / K = q at *
  generalize m % K = r at *
  generalize K / 2 = h at *
  rw [Nat.mul_comm K q] at h1
  rcases Nat.lt_or_ge u (q + 1) with hu | hu
  · have : u = q := by omega
    subst this; omega
  · have : u = q + 1 := by omega
    subst this
    rw [Nat.add_mul, Nat.one_mul]
    have : K ≤ r + h := by omega
    omega

theorem evenMag_mono {m n : Nat} (h : m ≤ n) : evenMag m ≤ evenMag n := by
  apply Nat.mul_le_mul_right
  have hK := K_pos
  have hq : m / K ≤ n / K := Nat.div_le_div_right h
  have h1 := Nat.div_add_mod m K
  have h2 := Nat.mod_lt m hK
  have h3 := Nat.div_add_mod n K
  have h4 := Nat.mod_lt n hK
  have hs := evenQuot_spec m
  have ht := evenQuot_spec n
  generalize evenQuot m = u at *
  generalize evenQuot n = v at *
  generalize m / K = q at *
  generalize m % K = r at *
  generalize n / K = q' at *
  generalize n % K = r' at *
  rw [Nat.mul_comm K q] at h1
  rw [Nat.mul_comm K q'] at h3
  rcases Nat.lt_or_ge q q' with hlt | hge
  · omega
  · have : q = q' := by omega
    subst this
    have : r ≤ r' := by omega
    omega

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

theorem evenMag_zero : evenMag 0 = 0 := by
  have hK := K_pos
  unfold evenMag evenQuot
  rw [Nat.zero_div, Nat.zero_mod]
  simp only [Nat.mul_zero, hK, ↓reduceIte, Nat.zero_mul]

theorem evenMag_bound (m : Nat) (hm : m ≤ maxMag) : evenMag m ≤ maxMag :=
  Nat.le_trans (evenMag_le_roundMag m) (roundMag_bound m hm)

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

/-- Rounding a canonical code keeps it canonical: a finite result is `0` or
odd, of magnitude at most `maxMag`, and NaN and `±∞` stay (D31). -/
theorem canon_onMag {pos neg : Nat → Nat} (hp : ∀ m, m ≤ maxMag → pos m ≤ maxMag)
    (hn : ∀ m, m ≤ maxMag → neg m ≤ maxMag) {c : Int} (hc : canon c = c) :
    canon (onMag pos neg c) = onMag pos neg c := by
  unfold onMag
  split
  · exact hc
  · rename_i hm
    have hm' : mag c ≤ maxMag := by omega
    have := fp64.negZero_eq; have := fp64.negNan_eq
    have : (fp64.maxMag : Int) = maxMag := rfl
    apply fp64.canon_eq_self
    show _ ≠ fp64.negZero ∧ _ ≠ fp64.negNan
    have h1 := hn _ hm'; have h2 := hp _ hm'
    split <;> (unfold code; split) <;> constructor <;> omega

theorem canon_floor {c : Int} (hc : canon c = c) : canon (floor c) = floor c :=
  canon_onMag floorMag_bound ceilMag_bound hc

theorem canon_ceil {c : Int} (hc : canon c = c) : canon (ceil c) = ceil c :=
  canon_onMag ceilMag_bound floorMag_bound hc

theorem canon_round {c : Int} (hc : canon c = c) : canon (round c) = round c :=
  canon_onMag roundMag_bound roundMag_bound hc

theorem canon_roundEven {c : Int} (hc : canon c = c) : canon (roundEven c) = roundEven c :=
  canon_onMag evenMag_bound evenMag_bound hc

theorem onMag_of_big {pos neg : Nat → Nat} {c : Int} (h : maxMag < mag c) : onMag pos neg c = c := by
  unfold onMag; exact ite_eq_left h

theorem onMag_zero {pos neg : Nat → Nat} (hp : pos 0 = 0) : onMag pos neg 0 = 0 := by
  simp [onMag, mag, code, hp]

theorem maxMag_lt_mag_special : maxMag < mag negZero ∧ maxMag < mag negNan ∧ maxMag < mag nan := by
  have h1 : negZero = -(2 * (maxMag : Int) + 6) := fp64.negZero_eq
  have h2 : negNan = -(2 * (maxMag : Int) + 5) := fp64.negNan_eq
  have h3 : nan = 2 * (maxMag : Int) + 5 := fp64.nan_eq
  refine ⟨?_, ?_, ?_⟩ <;> unfold mag <;> omega

/-- `floor`, `ceil` and `round` read a double up to `canon` (D31): they keep
`-0.0` and the negative NaN, which `canon` makes `0` and the NaN. -/
theorem canon_onMag_canon {pos neg : Nat → Nat} (hp : pos 0 = 0) (c : Int) :
    canon (onMag pos neg (canon c)) = canon (onMag pos neg c) := by
  obtain ⟨m0, m1, m2⟩ := maxMag_lt_mag_special
  by_cases h0 : c = negZero
  · subst h0
    rw [show canon negZero = 0 from fp64.canon_negZero, onMag_zero hp, onMag_of_big m0,
      show canon negZero = 0 from fp64.canon_negZero, canon_zero]
  by_cases h1 : c = negNan
  · subst h1
    rw [show canon negNan = nan from fp64.canon_negNan, onMag_of_big m2, onMag_of_big m1,
      show canon negNan = nan from fp64.canon_negNan, canon_of_isRef isRef_nan]
  · rw [show canon c = c from fp64.canon_eq_self ⟨h0, h1⟩]

theorem canon_floor_canon (c : Int) : canon (floor (canon c)) = canon (floor c) :=
  canon_onMag_canon (by decide) c

theorem canon_ceil_canon (c : Int) : canon (ceil (canon c)) = canon (ceil c) :=
  canon_onMag_canon (by decide) c

theorem canon_round_canon (c : Int) : canon (round (canon c)) = canon (round c) :=
  canon_onMag_canon (by simp [roundMag, K]) c

theorem canon_roundEven_canon (c : Int) : canon (roundEven (canon c)) = canon (roundEven c) :=
  canon_onMag_canon evenMag_zero c

theorem floor_mono {c d : Int} (h : c ≤ d) : floor c ≤ floor d :=
  onMag_mono floorMag_mono ceilMag_mono floorMag_bound ceilMag_bound h

theorem ceil_mono {c d : Int} (h : c ≤ d) : ceil c ≤ ceil d :=
  onMag_mono ceilMag_mono floorMag_mono ceilMag_bound floorMag_bound h

theorem round_mono {c d : Int} (h : c ≤ d) : round c ≤ round d :=
  onMag_mono roundMag_mono roundMag_mono roundMag_bound roundMag_bound h

theorem roundEven_mono {c d : Int} (h : c ≤ d) : roundEven c ≤ roundEven d :=
  onMag_mono evenMag_mono evenMag_mono evenMag_bound evenMag_bound h

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

/-! ## Checks -/

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
