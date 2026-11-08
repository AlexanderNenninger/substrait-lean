import Sverify.Core.FloatExact

/-!
# Double arithmetic, rounded once (D31)

A double `+`, `-`, `*` or `/` is the exact result of its operands' values
rounded once to binary64, to nearest with ties to even, with IEEE 754's rules
for infinities, NaN and the sign of zero (D31, `docs/core-semantics.md`).
Every finite double is an integer multiple of `2⁻¹⁰⁷⁴` (`scaled`), so the
exact sum, difference and product are integers in that unit (the product in
`2⁻²¹⁴⁸`), and the quotient is a fraction of two; `ofExactDiv` rounds each,
as it rounds D25's sums.

`addI`, `subI`, `mulI` and `divI` are IEEE 754's operations on the full set of
codes, `-0.0` (`negZero`) and the negative NaN included:

* an exact zero from operands that are not both `-0.0` is `+0.0`, so
  `x - x` is `+0.0` and `(-0.0) + (-0.0)` is `-0.0`;
* a product or quotient has the XOR of the operands' signs, a zero or an
  infinity included: `x / ±0` is `±∞` by that XOR;
* a non-zero result that rounds to zero keeps its sign;
* NaN in gives NaN, as do `∞ - ∞`, `0 · ∞`, `∞ / ∞` and `0 / 0`. The sign of
  a NaN an operation produces is open; these give the NaN code.

The reference has one zero and one NaN (`zero_sign` `ONE_ZERO`, #89), so its
operations `fadd`, `fsub`, `fmul` and `fdiv` are these followed by `canon`. On
finite operands they are `ofExact` and `ofExactDiv` of the exact result
(`fadd_fin` …), from which the bounds the contract checker used to trust as
axioms (#582) follow: `add_scaled`, `sub_scaled`, `mul_scaled`, `div_scaled`,
`div_scaled_err`, `add_nonneg`, `mul_nonneg` and `div_nonneg`.

Everything here is integer arithmetic. `tests/test_float_arith.py` checks it
bit for bit against native doubles.
-/

namespace Substrait.FloatCode

set_option exponentiation.threshold 3200

/-- `2¹⁰⁷⁴`: a product of two scaled values is in units of `2⁻²¹⁴⁸`. -/
def unitK : Nat := 2 ^ 1074

/-- A NaN code: the NaN or the negative NaN. -/
def isNanCode (c : Int) : Bool := c == nan || c == negNan

/-- An infinity's code. -/
def isInfCode (c : Int) : Bool := c == posInf || c == negInf

/-- A zero's code: `+0.0` or `-0.0`. -/
def isZeroCode (c : Int) : Bool := c == 0 || c == negZero

/-- A finite code's value in units of `2⁻¹⁰⁷⁴`; `-0.0` is `0`. -/
def sv (c : Int) : Int := if c = negZero then 0 else scaled c

/-- The zero of sign `neg`. -/
def zeroOf (neg : Bool) : Int := if neg then negZero else 0

/-- The infinity of sign `neg`. -/
def infOf (neg : Bool) : Int := if neg then negInf else posInf

/-- `v / n` rounded once; a negative value that rounds to zero is `-0.0`. -/
def rnd (v : Int) (n : Nat) : Int :=
  let r := ofExactDiv v n
  if r = 0 ∧ v < 0 then negZero else r

/-- IEEE 754's negation: the sign flips, of a zero and a NaN too. -/
def negI (c : Int) : Int := if c = 0 then negZero else if c = negZero then 0 else -c

/-- IEEE 754's `a + b`. -/
def addI (a b : Int) : Int :=
  if isNanCode a || isNanCode b then nan
  else if a = posInf then (if b = negInf then nan else posInf)
  else if a = negInf then (if b = posInf then nan else negInf)
  else if isInfCode b then b
  else
    let v := sv a + sv b
    if v = 0 then zeroOf (a < 0 && b < 0) else rnd v 1

/-- IEEE 754's `a - b`. -/
def subI (a b : Int) : Int := addI a (negI b)

/-- IEEE 754's `a · b`. -/
def mulI (a b : Int) : Int :=
  if isNanCode a || isNanCode b then nan
  else
    let s := decide (a < 0) != decide (b < 0)
    if (isInfCode a && isZeroCode b) || (isZeroCode a && isInfCode b) then nan
    else if isInfCode a || isInfCode b then infOf s
    else
      let v := sv a * sv b
      if v = 0 then zeroOf s else rnd v unitK

/-- IEEE 754's `a / b`. -/
def divI (a b : Int) : Int :=
  if isNanCode a || isNanCode b then nan
  else
    let s := decide (a < 0) != decide (b < 0)
    if isInfCode a && isInfCode b then nan
    else if isInfCode a then infOf s
    else if isInfCode b then zeroOf s
    else if isZeroCode b then (if isZeroCode a then nan else infOf s)
    else if isZeroCode a then zeroOf s
    else rnd ((if sv b < 0 then -sv a else sv a) * unitK) (sv b).natAbs

/-- The reference's `+` on doubles (D31): IEEE 754's, with one zero and one NaN. -/
def fadd (a b : Int) : Int := canon (addI a b)

/-- The reference's `-` on doubles (D31). -/
def fsub (a b : Int) : Int := canon (subI a b)

/-- The reference's `*` on doubles (D31). -/
def fmul (a b : Int) : Int := canon (mulI a b)

/-- The reference's `/` on doubles (D31). -/
def fdiv (a b : Int) : Int := canon (divI a b)

/-! ### Finite operands -/

theorem negZero_eq' : negZero = -(2 * (maxMag : Int) + 6) := fp64.negZero_eq

theorem negNan_eq' : negNan = -(2 * (maxMag : Int) + 5) := fp64.negNan_eq

theorem posCode_le_posInf (m : Nat) : posCode m ≤ posInf := by
  have := posInf_eq; unfold posCode; split
  · exact Int.le_refl _
  · split <;> omega

theorem isRef_ofExactDiv (v : Int) (n : Nat) : IsRef (ofExactDiv v n) := by
  have h1 := posCode_le_posInf (roundMagDiv v.natAbs n)
  have h2 := posCode_nonneg (roundMagDiv v.natAbs n)
  have := posInf_eq; have := negInf_eq; have := nan_eq
  show negInf ≤ _ ∧ _ ≤ nan
  unfold ofExactDiv; split <;> omega

theorem canon_rnd (v : Int) (n : Nat) : canon (rnd v n) = ofExactDiv v n := by
  unfold rnd; dsimp only; split
  · rename_i h; rw [h.1]; exact fp64.canon_negZero
  · exact canon_of_isRef (isRef_ofExactDiv v n)

theorem ofExactDiv_zero (n : Nat) : ofExactDiv 0 n = 0 := by
  simp [ofExactDiv, roundMagDiv_zero, posCode]

theorem canon_zeroOf (neg : Bool) : canon (zeroOf neg) = 0 := by
  cases neg
  · rfl
  · exact fp64.canon_negZero

/-- What a finite code is not. -/
theorem IsFin.ne {c : Int} (h : IsFin c) :
    c ≠ nan ∧ c ≠ negNan ∧ c ≠ posInf ∧ c ≠ negInf ∧ c ≠ negZero := by
  have := posInf_eq; have := negInf_eq; have := nan_eq
  have := negZero_eq'; have := negNan_eq'
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> simp_all <;> omega

theorem IsFin.sv_eq {c : Int} (h : IsFin c) : sv c = scaled c := by
  simp [FloatCode.sv, h.ne.2.2.2.2]

theorem IsFin.not_nan {c : Int} (h : IsFin c) : isNanCode c = false := by
  simp [isNanCode, h.ne.1, h.ne.2.1]

theorem IsFin.not_inf {c : Int} (h : IsFin c) : isInfCode c = false := by
  simp [isInfCode, h.ne.2.2.1, h.ne.2.2.2.1]

theorem fadd_fin {a b : Int} (ha : IsFin a) (hb : IsFin b) :
    fadd a b = ofExact (scaled a + scaled b) := by
  unfold fadd addI
  simp only [ha.not_nan, hb.not_nan, hb.not_inf, ha.ne.2.2.1, ha.ne.2.2.2.1, ha.sv_eq, hb.sv_eq,
    Bool.or_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h; rw [canon_zeroOf, h]; exact (ofExactDiv_zero 1).symm
  · exact canon_rnd _ 1

theorem IsFin.negI_parts {b : Int} (hb : IsFin b) :
    isNanCode (FloatCode.negI b) = false ∧ isInfCode (FloatCode.negI b) = false ∧
      FloatCode.sv (FloatCode.negI b) = -scaled b := by
  have := posInf_eq; have := negInf_eq; have := nan_eq
  have := negZero_eq'; have := negNan_eq'
  have hz := hb.ne.2.2.2.2
  obtain ⟨h1, h2⟩ := hb
  unfold FloatCode.negI
  by_cases h0 : b = 0
  · subst h0
    refine ⟨?_, ?_, ?_⟩ <;> simp [isNanCode, isInfCode, FloatCode.sv, scaled] <;> omega
  · simp only [h0, hz, ite_false]
    have e : -b ≠ negZero := by omega
    refine ⟨by simp [isNanCode]; omega, by simp [isInfCode]; omega, ?_⟩
    simp only [FloatCode.sv, e, ite_false]
    unfold scaled; split <;> split <;> omega

theorem fsub_fin {a b : Int} (ha : IsFin a) (hb : IsFin b) :
    fsub a b = ofExact (scaled a - scaled b) := by
  obtain ⟨n1, n2, n3⟩ := hb.negI_parts
  unfold fsub subI addI
  simp only [ha.not_nan, n1, n2, ha.ne.2.2.1, ha.ne.2.2.2.1, ha.sv_eq, n3,
    Bool.or_false, Bool.false_eq_true, ite_false, ← Int.sub_eq_add_neg]
  split
  · rename_i h; rw [canon_zeroOf, h]; exact (ofExactDiv_zero 1).symm
  · exact canon_rnd _ 1

theorem fmul_fin {a b : Int} (ha : IsFin a) (hb : IsFin b) :
    fmul a b = ofExactDiv (scaled a * scaled b) unitK := by
  unfold fmul mulI
  simp only [ha.not_nan, hb.not_nan, ha.not_inf, hb.not_inf, ha.sv_eq, hb.sv_eq,
    Bool.or_false, Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h; rw [canon_zeroOf, h]; exact (ofExactDiv_zero _).symm
  · exact canon_rnd _ _

theorem fdiv_fin {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0) :
    fdiv a b = ofExactDiv ((if scaled b < 0 then -scaled a else scaled a) * unitK)
      (scaled b).natAbs := by
  have hbz : isZeroCode b = false := by
    have h0 : b ≠ 0 := fun e => hb0 (by subst e; rfl)
    simp [isZeroCode, h0, hb.ne.2.2.2.2]
  unfold fdiv divI
  simp only [ha.not_nan, hb.not_nan, ha.not_inf, hb.not_inf, hbz, ha.sv_eq, hb.sv_eq,
    Bool.or_false, Bool.and_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h
    have ha0 : a = 0 := by
      simp only [isZeroCode, Bool.or_eq_true, beq_iff_eq] at h
      exact h.resolve_right ha.ne.2.2.2.2
    subst ha0
    rw [canon_zeroOf]
    simp only [show scaled 0 = 0 from rfl, Int.neg_zero, ite_self, Int.zero_mul]
    exact (ofExactDiv_zero _).symm
  · exact canon_rnd _ _

/-- Rounding moves by at most `2⁻⁵³` of the magnitude, or half a unit of the
grid below `2⁵³`: `2⁵³ · |n · r − v| ≤ max |v| (n · 2⁵²)`. -/
theorem ofExactDiv_err {v : Int} {n : Nat} (hn : 0 < n) (hf : IsFin (ofExactDiv v n)) :
    2 ^ 53 * ((n : Int) * scaled (ofExactDiv v n) - v).natAbs ≤ max v.natAbs (n * 2 ^ 52) := by
  have h1 := ofExactDiv_within hn hf
  have h2 := ulpDiv_le v hn
  generalize ulpDiv v n = u at h1 h2
  generalize ((n : Int) * scaled (ofExactDiv v n) - v).natAbs = E at h1 ⊢
  have h3 := Nat.mul_le_mul_left (2 ^ 52) h1
  rw [Nat.mul_right_comm n] at h2
  rw [show 2 ^ 53 * E = 2 ^ 52 * (2 * E) by rw [← Nat.mul_assoc]]
  rw [Nat.mul_comm (n * u)] at h2
  exact Nat.le_trans h3 h2

/-! ### The bounds the checker trusted before D31 (#582)

A double `+`, `-`, `*` or `/` of finite doubles whose exact result is well
below the largest double is finite, and within a few `u` of the exact
result. Stated on scaled values, so the checker bounds the result with
integer interval arithmetic (`floatArith` in `Contracts.lean`) and rules out
an overflow to `±∞` from the inputs' bounds (`BinFn.mayInf`). Axioms before
D31, theorems of it now. -/

theorem add_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (fadd a b) ∧ (scaled (fadd a b) - (scaled a + scaled b)).natAbs ≤
      ((scaled a).natAbs + (scaled b).natAbs) / 2 ^ 50 + 1 := by
  rw [fadd_fin ha hb]
  have hS := Int.natAbs_add_le (scaled a) (scaled b)
  obtain ⟨hf, hr⟩ := ofExact_rel (S := scaled a + scaled b) (by omega)
  refine ⟨hf, ?_⟩
  generalize (scaled (ofExact (scaled a + scaled b)) - (scaled a + scaled b)).natAbs = E at hr ⊢
  omega

theorem sub_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (fsub a b) ∧ (scaled (fsub a b) - (scaled a - scaled b)).natAbs ≤
      ((scaled a).natAbs + (scaled b).natAbs) / 2 ^ 50 + 1 := by
  rw [fsub_fin ha hb]
  have hS := Int.natAbs_sub_le (scaled a) (scaled b)
  obtain ⟨hf, hr⟩ := ofExact_rel (S := scaled a - scaled b) (by omega)
  refine ⟨hf, ?_⟩
  generalize (scaled (ofExact (scaled a - scaled b)) - (scaled a - scaled b)).natAbs = E at hr ⊢
  omega

theorem mul_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs * (scaled b).natAbs ≤ 2 ^ 3171) :
    IsFin (fmul a b) ∧
      (2 ^ 1074 * scaled (fmul a b) - scaled a * scaled b).natAbs ≤
        (scaled a).natAbs * (scaled b).natAbs / 2 ^ 50 + 2 ^ 1074 := by
  rw [fmul_fin ha hb]
  have hv : (scaled a * scaled b).natAbs = (scaled a).natAbs * (scaled b).natAbs :=
    Int.natAbs_mul _ _
  have hn : 0 < unitK := Nat.two_pow_pos _
  have hf := ofExactDiv_fin (v := scaled a * scaled b) hn (by
    rw [hv]; refine Nat.le_trans h (Nat.le_of_eq ?_); unfold unitK; rw [← Nat.pow_add])
  refine ⟨hf, ?_⟩
  have he := ofExactDiv_err hn hf
  rw [hv] at he
  have hk : ((unitK : Nat) : Int) = 2 ^ 1074 := Int.natCast_pow 2 1074
  rw [hk] at he
  generalize (2 ^ 1074 * scaled (ofExactDiv (scaled a * scaled b) unitK) -
    scaled a * scaled b).natAbs = E at he ⊢
  rw [show unitK = 2 ^ 1074 from rfl] at he
  generalize (scaled a).natAbs * (scaled b).natAbs = P at he ⊢
  generalize (2 : Nat) ^ 1074 = K at he ⊢
  omega

/-- The quotient's sign moved onto the numerator: `|n · r − v|` is
`|r · B − A · 2¹⁰⁷⁴|`. -/
theorem div_err_eq (r A B : Int) :
    (((B.natAbs : Nat) : Int) * r - (if B < 0 then -A else A) * ((unitK : Nat) : Int)).natAbs =
      (r * B - A * 2 ^ 1074).natAbs := by
  have hk : ((unitK : Nat) : Int) = 2 ^ 1074 := Int.natCast_pow 2 1074
  rw [hk]
  generalize (2 : Int) ^ 1074 = K
  split
  · rw [show ((B.natAbs : Nat) : Int) = -B by omega]
    rw [show -B * r - -A * K = -(r * B - A * K) by
      rw [Int.neg_mul, Int.neg_mul, Int.sub_neg, Int.mul_comm B r]; omega]
    exact Int.natAbs_neg _
  · rw [show ((B.natAbs : Nat) : Int) = B by omega, Int.mul_comm B r]

theorem div_parts {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) :
    IsFin (fdiv a b) ∧ 2 ^ 53 * (scaled (fdiv a b) * scaled b - scaled a * 2 ^ 1074).natAbs ≤
      max ((scaled a).natAbs * 2 ^ 1074) ((scaled b).natAbs * 2 ^ 52) := by
  rw [fdiv_fin ha hb hb0]
  have hn : 0 < (scaled b).natAbs := Int.natAbs_pos.2 hb0
  have hv : ((if scaled b < 0 then -scaled a else scaled a) * ((unitK : Nat) : Int)).natAbs =
      (scaled a).natAbs * 2 ^ 1074 := by
    rw [Int.natAbs_mul]
    have : ((unitK : Nat) : Int).natAbs = 2 ^ 1074 := Int.natAbs_natCast _
    rw [this]; split <;> simp only [Int.natAbs_neg]
  have hf := ofExactDiv_fin (v := (if scaled b < 0 then -scaled a else scaled a) * unitK) hn (by
    rw [hv, Nat.mul_comm (scaled b).natAbs]; exact h)
  refine ⟨hf, ?_⟩
  have he := ofExactDiv_err hn hf
  rw [div_err_eq, hv] at he
  exact he

/-- The arithmetic of `div_scaled`, with `K₁ = 2¹⁰⁷⁴` and `K₂ = 2¹⁰²⁴` as
variables so that no power is evaluated. -/
theorem div_bound_arith {R B A E c K₁ K₂ : Nat} (hB : 0 < B) (h1 : K₁ = c * 2 ^ 53)
    (h2 : K₂ = c * 2 ^ 3) (htri : R * B ≤ A * K₁ + E) (he : 2 ^ 53 * E ≤ max (A * K₁) (B * 2 ^ 52)) :
    R ≤ A * (K₁ + K₂) / B + 1 := by
  subst h1 h2
  rw [← Nat.mul_assoc] at htri he
  rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
  generalize A * c = X at htri he ⊢
  have hle : (R - 1) * B ≤ X * 2 ^ 53 + X * 2 ^ 3 := by
    rw [Nat.sub_mul, Nat.one_mul]
    generalize R * B = RB at htri ⊢
    omega
  have := (Nat.le_div_iff_mul_le hB).2 hle
  omega

theorem div_err_arith {E A B : Nat} (he : 2 ^ 53 * E ≤ max A (B * 2 ^ 52)) :
    2 ^ 51 * E ≤ 2 * A + 2 ^ 50 * B := by omega

theorem div_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) :
    IsFin (fdiv a b) ∧
      (scaled (fdiv a b)).natAbs ≤
        (scaled a).natAbs * (2 ^ 1074 + 2 ^ 1024) / (scaled b).natAbs + 1 := by
  obtain ⟨hf, he⟩ := div_parts ha hb hb0 h
  refine ⟨hf, ?_⟩
  have hn : 0 < (scaled b).natAbs := Int.natAbs_pos.2 hb0
  have hrb : (scaled (fdiv a b) * scaled b).natAbs = (scaled (fdiv a b)).natAbs * (scaled b).natAbs :=
    Int.natAbs_mul _ _
  have htri : (scaled (fdiv a b) * scaled b).natAbs ≤
      (scaled (fdiv a b) * scaled b - scaled a * 2 ^ 1074).natAbs + (scaled a * 2 ^ 1074).natAbs := by
    have := Int.natAbs_add_le (scaled (fdiv a b) * scaled b - scaled a * 2 ^ 1074) (scaled a * 2 ^ 1074)
    rwa [Int.sub_add_cancel] at this
  have hak : (scaled a * 2 ^ 1074).natAbs = (scaled a).natAbs * 2 ^ 1074 := by
    rw [Int.natAbs_mul]; rfl
  rw [hrb, hak] at htri
  generalize (scaled (fdiv a b) * scaled b - scaled a * 2 ^ 1074).natAbs = E at he htri
  generalize (scaled (fdiv a b)).natAbs = R at htri ⊢
  generalize hB : (scaled b).natAbs = B at hn htri he ⊢
  generalize (scaled a).natAbs = A at he htri ⊢
  exact div_bound_arith hn (Nat.pow_add 2 1021 53) (Nat.pow_add 2 1021 3)
    (by rw [Nat.add_comm]; exact htri) he

theorem div_scaled_err {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) :
    IsFin (fdiv a b) ∧
      2 ^ 51 * (scaled (fdiv a b) * scaled b - scaled a * 2 ^ 1074).natAbs ≤
        2 * (scaled a).natAbs * 2 ^ 1074 + 2 ^ 50 * (scaled b).natAbs := by
  obtain ⟨hf, he⟩ := div_parts ha hb hb0 h
  refine ⟨hf, ?_⟩
  exact Nat.le_trans (div_err_arith he) (Nat.le_of_eq (by rw [Nat.mul_assoc]))

theorem scaled_nonneg {c : Int} (h : 0 ≤ c) : 0 ≤ scaled c := scaled_mono (c := 0) h

/-- Rounding keeps the sign (#441): a sum or product of non-negative finite
doubles, and a quotient of one by a positive one, is non-negative. -/
theorem add_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (_h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ fadd a b := by
  rw [fadd_fin ha hb]
  exact ofExact_nonneg (Int.add_nonneg (scaled_nonneg ha0) (scaled_nonneg hb0))

theorem mul_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (_h : (scaled a).natAbs * (scaled b).natAbs ≤ 2 ^ 3171) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ fmul a b := by
  rw [fmul_fin ha hb]
  exact ofExactDiv_nonneg _ (Int.mul_nonneg (scaled_nonneg ha0) (scaled_nonneg hb0))

theorem div_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (_h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) (ha0 : 0 ≤ a) (hb0' : 0 ≤ b) :
    0 ≤ fdiv a b := by
  rw [fdiv_fin ha hb hb0]
  have : ¬ scaled b < 0 := by have := scaled_nonneg hb0'; omega
  simp only [this, ite_false]
  exact ofExactDiv_nonneg _ (Int.mul_nonneg (scaled_nonneg ha0) (by unfold unitK; omega))

end Substrait.FloatCode
