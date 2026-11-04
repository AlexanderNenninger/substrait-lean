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
finite magnitude. What is stated here holds for every format: the codes,
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
