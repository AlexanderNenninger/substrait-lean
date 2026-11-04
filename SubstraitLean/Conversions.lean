import SubstraitLean.Rounding

/-!
# Conversions between doubles, decimals and integers

The conversions round, and contracts need what IEEE promises of them: they
are monotone, and within half a unit in the last place. Lean's native floats
promise nothing a proof can use, so each conversion is computed here exactly,
on the codes of `SubstraitLean/Float.lean`, and `#guard`s compare it with the
native one. The computation sits behind an `opaque` constant with its proved
properties (as `FloatCode.intToDouble` does): the kernel never unfolds it, and
proofs about plans use only the properties.

The one rounding all of them share is `roundRat N D`: the double nearest to
`N / D`, as a magnitude (`|x| · 2¹⁰⁷⁴`), halves to even. It takes the
quotient with two more bits and a sticky bit (`wOf`), which round as the exact
quotient does (`roundW_wOf_near`).
-/

namespace Substrait.FloatCode

-- Doubles involve powers of two up to 2²⁰⁴⁵.
set_option exponentiation.threshold 2100

/-! ## Rounding a quotient to the double grid -/

/-- `8 · N / D` with its fractional part as one sticky bit: odd exactly when
`4 · N / D` has a remainder. -/
def wOf (N D : Nat) : Nat := 2 * (4 * N / D) + (if 4 * N % D = 0 then 0 else 1)

/-- The grid `wOf` rounds to: multiples of `2ˢ`, at least `2³` (a magnitude
step of one, the subnormals'), else 53 significant bits. -/
def shiftW (w : Nat) : Nat := max 3 (bitLen w w - 53)

def roundW (w : Nat) : Nat := roundTo2 (shiftW w) w

/-- The magnitude of the double nearest to `N / D` (`N / D` in units of
`2⁻¹⁰⁷⁴`), halves to even, without a bound on the exponent. -/
def roundRat (N D : Nat) : Nat := roundW (wOf N D) / 8

theorem bitLen_self {w F : Nat} (h : w < 2 ^ F) : bitLen w w = bitLen F w :=
  bitLen_fuel _ _ w Nat.lt_two_pow_self h

theorem roundW_mono {w w' : Nat} (h : w ≤ w') : roundW w ≤ roundW w' := by
  unfold roundW shiftW
  have hF : w < 2 ^ w' := Nat.lt_of_le_of_lt h Nat.lt_two_pow_self
  rw [bitLen_self hF, bitLen_self (F := w') Nat.lt_two_pow_self]
  have hl := bitLen_mono w' h
  by_cases hs : max 3 (bitLen w' w - 53) = max 3 (bitLen w' w' - 53)
  · rw [hs]; exact roundTo2_mono _ h
  · have hw' : w' ≠ 0 := by
      intro h0; subst h0
      have : w = 0 := by omega
      subst this; exact hs rfl
    have h1 : w < 2 ^ 53 * 2 ^ max 3 (bitLen w' w - 53) := by
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le (lt_two_pow_bitLen _ _ hF) (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : 2 ^ 52 * 2 ^ max 3 (bitLen w' w' - 53) ≤ w' := by
      have := two_pow_bitLen_le w' w' hw'
      have e : bitLen w' w' = 53 + max 3 (bitLen w' w' - 53) := by omega
      rw [e, Nat.pow_add, show (2 : Nat) ^ 53 = 2 * 2 ^ 52 by decide, Nat.mul_assoc] at this
      omega
    have h3 : 2 ^ 53 * 2 ^ max 3 (bitLen w' w - 53) ≤ 2 ^ 52 * 2 ^ max 3 (bitLen w' w' - 53) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    calc roundTo2 (max 3 (bitLen w' w - 53)) w
        ≤ roundTo2 (max 3 (bitLen w' w - 53)) (2 ^ 53 * 2 ^ max 3 (bitLen w' w - 53)) :=
          roundTo2_mono _ (Nat.le_of_lt h1)
      _ = 2 ^ 53 * 2 ^ max 3 (bitLen w' w - 53) := roundTo2_mul _ _
      _ ≤ 2 ^ 52 * 2 ^ max 3 (bitLen w' w' - 53) := h3
      _ = roundTo2 (max 3 (bitLen w' w' - 53)) (2 ^ 52 * 2 ^ max 3 (bitLen w' w' - 53)) :=
          (roundTo2_mul _ _).symm
      _ ≤ roundTo2 (max 3 (bitLen w' w' - 53)) w' := roundTo2_mono _ h2

theorem wOf_mono {N N' D : Nat} (_hD : 0 < D) (h : N ≤ N') : wOf N D ≤ wOf N' D := by
  unfold wOf
  have hv : 4 * N / D ≤ 4 * N' / D := Nat.div_le_div_right (by omega)
  have d1 := Nat.div_add_mod (4 * N) D
  have d2 := Nat.div_add_mod (4 * N') D
  rcases Nat.lt_or_eq_of_le hv with hlt | heq
  · split <;> split <;> omega
  · -- Same quotient: the remainder only grows.
    have hm : 4 * N % D ≤ 4 * N' % D := by
      have : D * (4 * N / D) = D * (4 * N' / D) := by rw [heq]
      omega
    split <;> split <;> omega

theorem roundRat_mono {N N' D : Nat} (hD : 0 < D) (h : N ≤ N') : roundRat N D ≤ roundRat N' D :=
  Nat.div_le_div_right (roundW_mono (wOf_mono hD h))

/-- The grid point `roundTo2` picks for `w` is within half a step of `y = 8N / D`
when `w` stands for `y` as `wOf` makes it: `w = y` exactly, or `w = 2v + 1` with
`2v < y < 2v + 2`. The midpoints between grid points are even, so `w` and `y`
lie between the same ones. In integers, scaled by `D`. -/
theorem roundTo2_near {S v w D N : Nat} (hS : 2 ≤ S)
    (hw : (w = 2 * v ∧ D * (2 * v) = 8 * N) ∨ (w = 2 * v + 1 ∧ D * (2 * v) < 8 * N))
    (hhi : 8 * N < D * (2 * v + 2)) :
    D * roundTo2 S w ≤ 8 * N + D * 2 ^ (S - 1) ∧ 8 * N ≤ D * roundTo2 S w + D * 2 ^ (S - 1) := by
  have hP : 2 ^ S = 2 * 2 ^ (S - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hP2 : 2 ^ (S - 1) = 2 * 2 ^ (S - 2) := by rw [← Nat.pow_succ']; congr 1; omega
  generalize 2 ^ (S - 2) = H at hP2
  generalize hG : 2 ^ (S - 1) = G at hP hP2 ⊢
  have hd := Nat.div_add_mod w (2 ^ S)
  have hrl := Nat.mod_lt w (Nat.two_pow_pos S)
  unfold roundTo2
  rw [hP] at hd hrl ⊢
  generalize w / (2 * G) = q at hd ⊢
  generalize w % (2 * G) = r at hd hrl ⊢
  -- `q · 2G` and its products by `D` as atoms.
  have eA : 2 * G * q = 2 * (q * G) := by rw [Nat.mul_assoc, Nat.mul_comm G q]
  have eB : q * (2 * G) = 2 * (q * G) := by rw [Nat.mul_left_comm]
  have eC : (q + 1) * (2 * G) = 2 * (q * G) + 2 * G := by rw [Nat.add_mul, Nat.one_mul, eB]
  rw [eA] at hd
  rw [eB, eC]
  generalize q * G = QG at hd ⊢
  have m1 : D * (2 * QG + 2 * G) = D * (2 * QG + G) + D * G := by
    rw [show 2 * QG + 2 * G = (2 * QG + G) + G by omega, Nat.mul_add]
  have m2 : D * (2 * QG + G) = D * (2 * QG) + D * G := Nat.mul_add _ _ _
  have m3 : D * (2 * v + 2) = D * (2 * v) + 2 * D := by rw [Nat.mul_add]; omega
  have mono : ∀ a b : Nat, a ≤ b → D * a ≤ D * b := fun a b h => Nat.mul_le_mul_left D h
  split
  · -- Rounded up, to `2QG + 2G`: `w`, and so `y`, is at least the midpoint.
    have hmid : 2 * QG + G ≤ w := by omega
    have hcell : 2 * v + 2 ≤ 2 * QG + 2 * G := by omega
    have := mono _ _ hcell
    have hy : D * (2 * QG + G) ≤ 8 * N := by
      rcases hw with ⟨rfl, he⟩ | ⟨rfl, hl⟩
      · have := mono _ _ hmid; omega
      · have := mono (2 * QG + G) (2 * v) (by omega); omega
    constructor <;> omega
  · -- Rounded down, to `2QG`: `w`, and so `y`, is at most the midpoint.
    have hmid : w ≤ 2 * QG + G := by omega
    have hcell : 2 * QG ≤ 2 * v := by omega
    have := mono _ _ hcell
    have hy : 8 * N ≤ D * (2 * QG + G) := by
      rcases hw with ⟨rfl, he⟩ | ⟨rfl, hl⟩
      · have := mono _ _ hmid; omega
      · have := mono (2 * v + 2) (2 * QG + G) (by omega); omega
    constructor <;> omega

theorem roundW_near {N D : Nat} (hD : 0 < D) :
    D * roundW (wOf N D) ≤ 8 * N + D * 2 ^ (shiftW (wOf N D) - 1) ∧
      8 * N ≤ D * roundW (wOf N D) + D * 2 ^ (shiftW (wOf N D) - 1) := by
  have hd := Nat.div_add_mod (4 * N) D
  have hm := Nat.mod_lt (4 * N) hD
  have e1 : D * (2 * (4 * N / D)) = 2 * (D * (4 * N / D)) := Nat.mul_left_comm _ _ _
  have e2 : D * (2 * (4 * N / D) + 2) = 2 * (D * (4 * N / D)) + 2 * D := by
    rw [Nat.mul_add, e1]; omega
  apply roundTo2_near (v := 4 * N / D) (Nat.le_trans (by decide) (Nat.le_max_left _ _))
  · unfold wOf; split
    · exact .inl ⟨rfl, by omega⟩
    · exact .inr ⟨rfl, by omega⟩
  · omega

/-- `roundW` gives a multiple of 8, so `roundRat` loses nothing in its division. -/
theorem roundW_dvd (w : Nat) : roundW w = 8 * (roundW w / 8) := by
  have h : 2 ^ 3 ∣ 2 ^ shiftW w := Nat.pow_dvd_pow 2 (Nat.le_max_left _ _)
  have h8 : 8 ∣ roundW w := by
    unfold roundW roundTo2
    split <;> exact Nat.dvd_trans h (Nat.dvd_mul_left _ _)
  exact (Nat.mul_div_cancel' h8).symm

/-- In the normal range (`N / D ≥ 2⁵²`), the rounded quotient is within
`2⁻⁵³` of the exact one, relatively: half a unit in the last place. -/
theorem roundRat_rel {N D : Nat} (hD : 0 < D) (hN : D * 2 ^ 52 ≤ N) :
    2 ^ 53 * (D * roundRat N D) ≤ (2 ^ 53 + 1) * N ∧
      (2 ^ 53 - 1) * N ≤ 2 ^ 53 * (D * roundRat N D) := by
  obtain ⟨h1, h2⟩ := roundW_near (N := N) hD
  have h8 := roundW_dvd (wOf N D)
  -- The half step `E` is at most `8N · 2⁻⁵³`.
  have hE : D * 2 ^ (shiftW (wOf N D) - 1) * 2 ^ 53 ≤ 8 * N := by
    have hS : 3 ≤ shiftW (wOf N D) := Nat.le_max_left _ _
    have e : 2 ^ (shiftW (wOf N D) - 1) * 2 ^ 53 = 2 ^ (shiftW (wOf N D) + 52) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.mul_assoc, e]
    by_cases h3 : shiftW (wOf N D) = 3
    · rw [h3, show (2 : Nat) ^ (3 + 52) = 8 * 2 ^ 52 by decide, Nat.mul_left_comm]
      exact Nat.mul_le_mul_left 8 hN
    · -- A larger step: `w` has `S + 53` bits, so `2^(S+52) ≤ w`, and `D · w ≤ 8N`
      -- up to the sticky bit, which an even bound does not cross.
      have hw0 : wOf N D ≠ 0 := by
        intro h0; unfold shiftW at h3; rw [h0] at h3; simp [bitLen_zero] at h3
      have hb := two_pow_bitLen_le (wOf N D) (wOf N D) hw0
      have hbits : bitLen (wOf N D) (wOf N D) = shiftW (wOf N D) + 53 := by
        unfold shiftW at h3 ⊢; omega
      rw [hbits, Nat.pow_succ] at hb
      have hpow : 2 ^ (shiftW (wOf N D) + 52) ≤ wOf N D := by omega
      have hd := Nat.div_add_mod (4 * N) D
      have heven : 2 ^ (shiftW (wOf N D) + 52) = 2 * 2 ^ (shiftW (wOf N D) + 51) := by
        rw [← Nat.pow_succ']
      have hle : 2 ^ (shiftW (wOf N D) + 52) ≤ 2 * (4 * N / D) := by
        rw [heven] at hpow ⊢
        generalize 2 ^ (shiftW (wOf N D) + 51) = A at hpow ⊢
        unfold wOf at hpow; split at hpow <;> omega
      have := Nat.mul_le_mul_left D hle
      have e1 : D * (2 * (4 * N / D)) = 2 * (D * (4 * N / D)) := Nat.mul_left_comm _ _ _
      omega
  have eR : D * roundW (wOf N D) = 8 * (D * roundRat N D) := by
    unfold roundRat; rw [h8, ← Nat.mul_assoc, Nat.mul_comm D 8, Nat.mul_assoc]
    rw [Nat.mul_div_cancel_left _ (by decide)]
  rw [eR] at h1 h2
  generalize D * 2 ^ (shiftW (wOf N D) - 1) = E at h1 h2 hE
  generalize D * roundRat N D = M at h1 h2 ⊢
  have p53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
  rw [p53] at hE ⊢
  constructor <;> omega

/-! ## Signed magnitudes -/

/-- A monotone magnitude function, with zero at zero, gives a monotone
function of integers through their signs. -/
theorem signedCode_mono {f : Nat → Nat} (hf : ∀ {a b}, a ≤ b → f a ≤ f b) (_h0 : f 0 = 0)
    {i j : Int} (h : i ≤ j) :
    signedCode (decide (i < 0)) (f i.natAbs) ≤ signedCode (decide (j < 0)) (f j.natAbs) := by
  unfold signedCode
  by_cases hi : i < 0 <;> by_cases hj : j < 0
  · have := hf (a := j.natAbs) (b := i.natAbs) (by omega)
    simp only [hi, hj, decide_true, ↓reduceIte]
    split <;> split <;> omega
  · simp only [hi, hj, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    split <;> split <;> omega
  · omega
  · have := hf (a := i.natAbs) (b := j.natAbs) (by omega)
    simp only [hi, hj, decide_false, ↓reduceIte, Bool.false_eq_true]
    split <;> split <;> omega

theorem roundRat_zero (D : Nat) : roundRat 0 D = 0 := by
  simp [roundRat, wOf, roundW, roundTo2]

/-! ## Decimals to doubles -/

/-- A decimal's unscaled integer `n` at scale `s` as a double's code: the
double nearest to `n / 10ˢ` (`roundRat`), halves to even, as IEEE converts.
`ofDecimalNative` computes it with native floats; the `#guard`s below compare
them. -/
def ofDecimalExact (n : Int) (s : Nat) : Int :=
  max (-(2 * (maxMag : Int) + 1)) (min (2 * (maxMag : Int) + 1)
    (signedCode (decide (n < 0)) (roundRat (n.natAbs * 2 ^ 1074) (10 ^ s))))

theorem ofDecimalExact_bounds (n : Int) (s : Nat) :
    negInf < ofDecimalExact n s ∧ ofDecimalExact n s < posInf := by
  simp only [ofDecimalExact, posInf_eq, negInf_eq]; omega

theorem ofDecimalExact_mono {n n' : Int} (s : Nat) (h : n ≤ n') :
    ofDecimalExact n s ≤ ofDecimalExact n' s := by
  have := signedCode_mono (f := fun a => roundRat (a * 2 ^ 1074) (10 ^ s))
    (fun hab => roundRat_mono (Nat.pow_pos (by decide)) (Nat.mul_le_mul_right _ hab))
    (by simp [roundRat_zero]) h
  simp only [ofDecimalExact]; omega

set_option exponentiation.threshold 2100 in
theorem ofDecimalExact_rel {n : Int} {s : Nat} (h0 : n ≠ 0) (hn : n.natAbs < 2 ^ 127)
    (hs : s ≤ 307) :
    ∃ M, ofDecimalExact n s = signedCode (decide (n < 0)) M ∧
      2 ^ 53 * (10 ^ s * M) ≤ (2 ^ 53 + 1) * (n.natAbs * 2 ^ 1074) ∧
      (2 ^ 53 - 1) * (n.natAbs * 2 ^ 1074) ≤ 2 ^ 53 * (10 ^ s * M) := by
  have hD : 0 < 10 ^ s := Nat.pow_pos (by decide)
  -- Every non-zero decimal is in the normal range.
  have hN : 10 ^ s * 2 ^ 52 ≤ n.natAbs * 2 ^ 1074 := by
    have h1 : 10 ^ s ≤ 10 ^ 307 := Nat.pow_le_pow_right (by decide) hs
    have h2 : 10 ^ 307 * 2 ^ 52 ≤ 2 ^ 1074 := by decide +kernel
    have h3 : 2 ^ 1074 ≤ n.natAbs * 2 ^ 1074 := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.le_trans (Nat.mul_le_mul_right _ h1) (Nat.le_trans h2 h3)
  obtain ⟨r1, r2⟩ := roundRat_rel hD hN
  refine ⟨roundRat (n.natAbs * 2 ^ 1074) (10 ^ s), ?_, r1, r2⟩
  -- Far below overflow: `M ≤ 2 · |n| · 2¹⁰⁷⁴ < 2¹²⁰²`.
  have hM : roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) ≤ maxMag := by
    have hm : maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := by unfold maxMag; rfl
    have hDM : roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) ≤ 10 ^ s * roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) :=
      Nat.le_mul_of_pos_left _ hD
    have hbig : n.natAbs * 2 ^ 1074 ≤ 2 ^ 127 * 2 ^ 1074 := Nat.mul_le_mul_right _ (Nat.le_of_lt hn)
    have hcap : 2 * (2 ^ 127 * 2 ^ 1074) ≤ (2 ^ 53 - 1) * 2 ^ 2045 := by decide +kernel
    have p53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
    have hM2 : roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) ≤ 2 * (n.natAbs * 2 ^ 1074) := by
      generalize roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) = M at r1 hDM ⊢
      generalize 10 ^ s * M = DM at r1 hDM
      generalize n.natAbs * 2 ^ 1074 = X at r1 ⊢
      rw [p53] at r1
      omega
    rw [hm]
    exact Nat.le_trans hM2 (Nat.le_trans (Nat.mul_le_mul_left 2 hbig) hcap)
  have hMi : ((roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) : Nat) : Int) ≤ maxMag := by exact_mod_cast hM
  unfold ofDecimalExact signedCode
  generalize roundRat (n.natAbs * 2 ^ 1074) (10 ^ s) = M at hMi ⊢
  generalize (maxMag : Int) = X at hMi ⊢
  split <;> (try split) <;> omega

/-- A conversion of decimals to doubles, with what the checker knows of it. -/
structure DecToDouble where
  conv : Int → Nat → Int
  bounds : ∀ n s, negInf < conv n s ∧ conv n s < posInf
  mono : ∀ {n n'} s, n ≤ n' → conv n s ≤ conv n' s
  /-- Correctly rounded: within half a unit in the last place, `2⁻⁵³`
  relatively, of `n / 10ˢ` (as magnitudes `· 2¹⁰⁷⁴`). -/
  rel : ∀ {n s}, n ≠ 0 → n.natAbs < 2 ^ 127 → s ≤ 307 →
    ∃ M, conv n s = signedCode (decide (n < 0)) M ∧
      2 ^ 53 * (10 ^ s * M) ≤ (2 ^ 53 + 1) * (n.natAbs * 2 ^ 1074) ∧
      (2 ^ 53 - 1) * (n.natAbs * 2 ^ 1074) ≤ 2 ^ 53 * (10 ^ s * M)

/-- `ofDecimalExact`, behind a constant the kernel does not unfold. -/
opaque decToDouble : DecToDouble :=
  ⟨ofDecimalExact, ofDecimalExact_bounds, ofDecimalExact_mono, ofDecimalExact_rel⟩

/-- A decimal's unscaled integer `n` at scale `s` as a double's code,
correctly rounded (#27): `CAST(d AS DOUBLE)`. -/
def ofDecimal (n : Int) (s : Nat) : Int := decToDouble.conv n s

theorem ofDecimal_bounds (n : Int) (s : Nat) : negInf < ofDecimal n s ∧ ofDecimal n s < posInf :=
  decToDouble.bounds n s

theorem ofDecimal_mono {n n' : Int} (s : Nat) (h : n ≤ n') : ofDecimal n s ≤ ofDecimal n' s :=
  decToDouble.mono s h

/-- `CAST(d AS DOUBLE)` at scale `s` as a `FiniteMonoConv`. -/
def decConv (s : Nat) : FiniteMonoConv := ⟨(ofDecimal · s), (ofDecimal_bounds · s), ofDecimal_mono s⟩

theorem ofDecimal_rel {n : Int} {s : Nat} (h0 : n ≠ 0) (hn : n.natAbs < 2 ^ 127) (hs : s ≤ 307) :
    ∃ M, ofDecimal n s = signedCode (decide (n < 0)) M ∧
      2 ^ 53 * (10 ^ s * M) ≤ (2 ^ 53 + 1) * (n.natAbs * 2 ^ 1074) ∧
      (2 ^ 53 - 1) * (n.natAbs * 2 ^ 1074) ≤ 2 ^ 53 * (10 ^ s * M) :=
  decToDouble.rel h0 hn hs

-- The native conversion agrees, also at a tie (`2⁵³ + 1`) and past 53 bits.
#guard [(1234, 2), (-5, 2), (145, 3), (0, 5), (9007199254740993, 0), (99999999999999999999, 2),
  (-(10 ^ 38 - 1), 10), (1, 38), (123456789012345678901234567890, 7), (-7, 0), (3, 1)].all
    fun (n, s) => ofDecimal n s == ofDecimalNative n s

/-! ## Doubles to decimals -/

/-- The magnitude of `x · 10ˢ` in doubles, for a double of magnitude `m`:
`10ˢ` rounded to a double, then the product rounded. -/
def decQ (s m : Nat) : Nat := roundRat (m * roundRat (10 ^ s * 2 ^ 1074) 1) (2 ^ 1074)

/-- That product rounded to an integer, halves away from zero. -/
def decR (s m : Nat) : Int := ((roundMag (decQ s m) / K : Nat) : Int)

/-- `CAST(x AS DECIMAL(_, s))` of a double, as the decimal's unscaled integer:
`round(x · 10ˢ)` computed in doubles, halves away from zero, as DuckDB and
DataFusion cast (#27). NaN, `±∞`, and products that overflow to `±∞` have
none. `toDecimalNative?` computes it with native floats; the `#guard`s below
compare them. -/
def toDecimalExact (c : Int) (s : Nat) : Option Int :=
  if infMag ≤ mag c ∨ maxMag < decQ s (mag c) then none
  else some (if c < 0 then -decR s (mag c) else decR s (mag c))

theorem decQ_mono (s : Nat) {m m' : Nat} (h : m ≤ m') : decQ s m ≤ decQ s m' :=
  roundRat_mono (Nat.two_pow_pos _) (Nat.mul_le_mul_right _ h)

theorem decR_mono (s : Nat) {m m' : Nat} (h : m ≤ m') : decR s m ≤ decR s m' := by
  unfold decR
  exact Int.ofNat_le.2 (Nat.div_le_div_right (roundMag_mono (decQ_mono s h)))

/-- The cast is monotone, and defined between two codes where it is defined
at both: what the checker needs to bound it from its argument's bounds (#223). -/
theorem toDecimalExact_between {lo hi c : Int} {s : Nat} {a b : Int} (hl : lo ≤ c) (hh : c ≤ hi)
    (ha : toDecimalExact lo s = some a) (hb : toDecimalExact hi s = some b) :
    ∃ q, toDecimalExact c s = some q ∧ a ≤ q ∧ q ≤ b := by
  unfold toDecimalExact at ha hb ⊢
  split at ha
  · cases ha
  split at hb
  · cases hb
  rename_i hlo hhi
  simp only [not_or, Nat.not_le, Nat.not_lt] at hlo hhi
  simp only [Option.some.injEq] at ha hb
  subst ha hb
  have hR : ∀ m, 0 ≤ decR s m := fun m => by unfold decR; exact Int.natCast_nonneg _
  by_cases hc : c < 0
  · -- `lo ≤ c < 0`: `c` is no larger in magnitude than `lo`.
    have hm : mag c ≤ mag lo := mag_le_of_neg hc hl
    have hq := decQ_mono s hm
    simp only [show ¬(infMag ≤ mag c ∨ maxMag < decQ s (mag c)) by omega, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_⟩
    · have := decR_mono s hm
      simp only [show lo < 0 by omega, hc, ↓reduceIte]; omega
    · simp only [hc, ↓reduceIte]
      split
      · rename_i hhn
        have := decR_mono s (mag_le_of_neg hhn hh); omega
      · have := hR (mag hi); have := hR (mag c); omega
  · -- `0 ≤ c ≤ hi`: no larger in magnitude than `hi`.
    have hm : mag c ≤ mag hi := mag_le_of_nonneg (by omega) hh
    have hq := decQ_mono s hm
    simp only [show ¬(infMag ≤ mag c ∨ maxMag < decQ s (mag c)) by omega, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [hc, ↓reduceIte]
      split
      · have := hR (mag lo); have := hR (mag c); omega
      · rename_i hln
        have := decR_mono s (mag_le_of_nonneg (by omega) hl); omega
    · have := decR_mono s hm
      simp only [hc, show ¬hi < 0 by omega, ↓reduceIte]; omega

/-- A conversion of doubles to decimals, with what the checker knows of it. -/
structure DoubleToDecimal where
  conv : Int → Nat → Option Int
  between : ∀ {lo hi c : Int} {s : Nat} {a b : Int}, lo ≤ c → c ≤ hi →
    conv lo s = some a → conv hi s = some b → ∃ q, conv c s = some q ∧ a ≤ q ∧ q ≤ b

/-- `toDecimalExact`, behind a constant the kernel does not unfold. -/
opaque doubleToDecimal : DoubleToDecimal := ⟨toDecimalExact, toDecimalExact_between⟩

/-- `CAST(x AS DECIMAL(_, s))` of a double (`toDecimalExact`). -/
def toDecimal? (c : Int) (s : Nat) : Option Int := doubleToDecimal.conv c s

theorem toDecimal?_between {lo hi c : Int} {s : Nat} {a b : Int} (hl : lo ≤ c) (hh : c ≤ hi)
    (ha : toDecimal? lo s = some a) (hb : toDecimal? hi s = some b) :
    ∃ q, toDecimal? c s = some q ∧ a ≤ q ∧ q ≤ b :=
  doubleToDecimal.between hl hh ha hb

-- The native cast agrees: halves away from zero after the product rounds,
-- infinities, NaN, overflow of the product, and scales past 22 (`10ˢ` rounds).
#guard ([0.125, -2.675, 0.135, 0.145, 2.5, -2.5, 1e20, 0.0, 1.7976931348623157e308, 5e-324,
    123.456, -0.0049999999999999992, 1e300].map ofFloat ++ [nan, posInf, negInf]).all fun c =>
  [0, 1, 2, 3, 10, 22, 23, 30, 38].all fun s => toDecimal? c s == toDecimalNative? c s

/-! ## Integers to doubles and back -/

/-- An integer up to `2⁵³` in magnitude survives the round trip through a
double: `CAST(CAST(n AS DOUBLE) AS BIGINT) = n`. -/
theorem toInt?_ofInt {n : Int} (h : n.natAbs ≤ 2 ^ 53) : toInt? (ofInt n) = some n := by
  rw [ofInt_exact h]
  have hbig : n.natAbs * K ≤ maxMag := by
    have hm' : maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := by unfold maxMag; rfl
    rw [hm']; unfold K
    exact Nat.le_trans (Nat.mul_le_mul_right _ h) (by decide +kernel)
  have hdiv : n.natAbs * K / K = n.natAbs := Nat.mul_div_cancel _ K_pos
  unfold toInt? exactCode
  by_cases h0 : n = 0
  · subst h0; simp [mag]
  have hm : ∀ M : Nat, ((2 * (M : Int) + 1).natAbs - 1) / 2 = M ∧
      ((-(2 * (M : Int) + 1)).natAbs - 1) / 2 = M := fun M => by
    rw [Int.natAbs_neg, show 2 * (M : Int) + 1 = ((2 * M + 1 : Nat) : Int) by push_cast; rfl,
      Int.natAbs_natCast]
    omega
  unfold mag
  by_cases hn : n < 0
  · simp only [h0, hn, ↓reduceIte, (hm _).2, show (n.natAbs * 2 ^ 1074 : Nat) = n.natAbs * K from rfl,
      Nat.not_lt.2 hbig, hdiv]
    simp only [show -(2 * ((n.natAbs * K : Nat) : Int) + 1) < 0 by omega, ↓reduceIte,
      Option.some.injEq]
    omega
  · simp only [h0, hn, ↓reduceIte, (hm _).1, show (n.natAbs * 2 ^ 1074 : Nat) = n.natAbs * K from rfl,
      Nat.not_lt.2 hbig, hdiv]
    simp only [show ¬(2 * ((n.natAbs * K : Nat) : Int) + 1 < 0) by omega, ↓reduceIte,
      Option.some.injEq]
    omega

end Substrait.FloatCode
