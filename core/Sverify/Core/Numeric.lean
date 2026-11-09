import Sverify.Core.Float

/-!
# Elementary functions and bitwise operations

**Elementary functions of doubles** (`sqrt`, `exp`, `ln`, `log10`, `log2`,
`sin`, …, `atan2`, `logb`) mean what Substrait's `functions_arithmetic.yaml`
and `functions_logarithmic.yaml` say. They are computed with native floats,
as `POWER` is: C's `libm`. The contract checker treats each result as "some
double", so nothing is assumed about its rounding.

Outside a function's domain Substrait's `on_domain_error` (and, for
logarithms, `on_log_zero`) decides. A plan that omits it gets **ERROR**, as
for `overflow` and `on_division_by_zero` (epic #185): `sqrt` of a negative,
the logarithm of zero or a negative, `asin` and `acos` outside `[-1, 1]`,
`atan2(0, 0)`, and `logb` to a base that is not positive or is 1. A NaN
argument is in every domain: NaN in, NaN out. An error is `null` here, and
`analysis/Sverify/Analysis/Safety.lean` reports it as `Issue.domain`.

**Bitwise operations** act on 64-bit two's complement, exactly. Substrait's
`shift_left` and `shift_right` fill the vacated bits with zeros (with the
sign, shifting right), so bits shifted out are lost. Substrait leaves shift
counts outside `0`–`63` open; the reference raises on them (DataFusion and
Java take the count modulo 64, DuckDB raises).
-/

namespace Substrait

namespace FloatCode

/-- The code of `1.0`, magnitude `2¹⁰⁷⁴`. -/
def one : Int := 2 * 2 ^ 1074 + 1

/-- The code of `-1.0`. -/
def negOne : Int := -one

#guard one == ofFloat 1.0 && negOne == ofFloat (-1.0)

end FloatCode

/-- Elementary functions of one double. -/
inductive FMath where
  | sqrt | exp | ln | log10 | log2 | sin | cos | tan | asin | acos | atan
  deriving Repr, DecidableEq

/-- The Substrait name. -/
def FMath.name : FMath → String
  | .sqrt => "sqrt" | .exp => "exp" | .ln => "ln" | .log10 => "log10" | .log2 => "log2"
  | .sin => "sin" | .cos => "cos" | .tan => "tan" | .asin => "asin" | .acos => "acos"
  | .atan => "atan"

def FMath.all : List FMath :=
  [.sqrt, .exp, .ln, .log10, .log2, .sin, .cos, .tan, .asin, .acos, .atan]

def FMath.ofName? (n : String) : Option FMath := FMath.all.find? (·.name == n)

def FMath.eval : FMath → Float → Float
  | .sqrt => Float.sqrt | .exp => Float.exp | .ln => Float.log | .log10 => Float.log10
  | .log2 => Float.log2 | .sin => Float.sin | .cos => Float.cos | .tan => Float.tan
  | .asin => Float.asin | .acos => Float.acos | .atan => Float.atan

/-- The smallest code in the function's domain (`none`: no bound). -/
def FMath.lo? : FMath → Option Int
  | .sqrt => some 0
  | .ln | .log10 | .log2 => some 1
  | .asin | .acos => some FloatCode.negOne
  -- `±∞` would give NaN, which no operation creates (#257).
  | .sin | .cos | .tan => some (FloatCode.negInf + 1)
  | _ => none

/-- The largest code other than NaN in the function's domain. -/
def FMath.hi? : FMath → Option Int
  | .asin | .acos => some FloatCode.one
  | .sin | .cos | .tan => some (FloatCode.posInf - 1)
  | _ => none

/-- Is the double with code `c` in the function's domain? NaN always is. -/
def FMath.inDomain (f : FMath) (c : Int) : Bool :=
  f.lo?.all (· ≤ c) && (f.hi?.all (c ≤ ·) || c == FloatCode.nan)

-- One `simp` set serves every function's case, each using part of it.
set_option linter.unusedSimpArgs false in
set_option exponentiation.threshold 2100 in
/-- A double in a domain has its canonical code there too: no domain has a
lower bound below `-0.0`'s, and NaN is in every domain (D31). -/
theorem FMath.inDomain_canon {f : FMath} {c : Int} (h : f.inDomain c = true) :
    f.inDomain (FloatCode.canon c) = true := by
  have h0 : FloatCode.negZero = -(2 * (FloatCode.maxMag : Int) + 6) := fp64.negZero_eq
  have h1 : FloatCode.negNan = -(2 * (FloatCode.maxMag : Int) + 5) := fp64.negNan_eq
  have h2 : FloatCode.nan = 2 * (FloatCode.maxMag : Int) + 5 := fp64.nan_eq
  have h3 : FloatCode.negInf = -(2 * (FloatCode.maxMag : Int) + 3) := fp64.negInf_eq
  have h4 : FloatCode.posInf = 2 * (FloatCode.maxMag : Int) + 3 := fp64.posInf_eq
  have hone : FloatCode.one = 2 * (2 : Int) ^ 1074 + 1 := rfl
  have hnone : FloatCode.negOne = -(2 * (2 : Int) ^ 1074 + 1) := rfl
  have hmm : (2 : Nat) ^ 1100 ≤ FloatCode.maxMag := by
    rw [FloatCode.maxMag_def]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide : 1100 ≤ 2045))
      (Nat.le_mul_of_pos_left _ (by decide))
  have hmm' : ((2 : Nat) ^ 1100 : Int) ≤ (FloatCode.maxMag : Int) := by exact_mod_cast hmm
  by_cases e0 : c = FloatCode.negZero
  · subst e0; rw [show FloatCode.canon FloatCode.negZero = 0 from fp64.canon_negZero]
    cases f <;> simp only [FMath.inDomain, FMath.lo?, FMath.hi?, Option.all_some, Option.all_none,
      Bool.true_and, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.and_eq_true,
      true_or, or_true, and_true, true_and] at h ⊢ <;>
      omega
  by_cases e1 : c = FloatCode.negNan
  · subst e1; rw [show FloatCode.canon FloatCode.negNan = FloatCode.nan from fp64.canon_negNan]
    cases f <;> simp only [FMath.inDomain, FMath.lo?, FMath.hi?, Option.all_some, Option.all_none,
      Bool.true_and, Bool.and_true, beq_self_eq_true, Bool.or_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq, Bool.and_eq_true, true_or, or_true, and_true, true_and] <;>
      omega
  · rw [show FloatCode.canon c = c from fp64.canon_eq_self ⟨e0, e1⟩]; exact h

/-- The function of the double with code `c`; `none` outside its domain. -/
def FMath.apply (f : FMath) (c : Int) : Option Int :=
  -- The domain of `-0.0` is `0.0`'s, of the negative NaN the NaN's (D31);
  -- the value is IEEE's on the raw double (`sqrt(-0.0)` is `-0.0`).
  if f.inDomain (FloatCode.canon c) then some (FloatCode.ofFloat (f.eval (FloatCode.toFloat c))) else none

#guard FMath.apply .sqrt (FloatCode.ofFloat 4.0) == some (FloatCode.ofFloat 2.0)
#guard FMath.apply .sqrt (FloatCode.ofFloat (-1.0)) == none
#guard FMath.apply .sqrt 0 == some 0 && FMath.apply .ln 0 == none
#guard FMath.apply .ln FloatCode.nan == some FloatCode.nan
#guard FMath.apply .asin FloatCode.one == some (FloatCode.ofFloat (Float.asin 1.0))
#guard FMath.apply .acos (FloatCode.ofFloat 1.5) == none
#guard FMath.apply .exp FloatCode.posInf == some FloatCode.posInf

/-- `atan2(y, x)`: a domain error at `(0, 0)`. -/
def atan2? (y x : Int) : Option Int :=
  -- The domain reads one zero (D31); the value is the native one on the raw
  -- doubles (`atan2(-0.0, -1)` is `-π`).
  if FloatCode.canon y = 0 ∧ FloatCode.canon x = 0 then none else some (FloatCode.lift₂ Float.atan2 y x)

/-- `logb(x, b)`, the logarithm of `x` to base `b`, as `ln x / ln b`: a
domain error unless `x` and `b` are positive and `b` is not 1. -/
def logb? (x b : Int) : Option Int :=
  if 0 < FloatCode.canon x ∧ 0 < FloatCode.canon b ∧ FloatCode.canon b ≠ FloatCode.one then
    some (FloatCode.lift₂ (fun x b => Float.log x / Float.log b) x b)
  else none

/-- Whether `atan2?` and `logb?` are defined reads only canonical codes. -/
theorem atan2?_isSome_canon (y x : Int) :
    (atan2? (FloatCode.canon y) (FloatCode.canon x)).isSome = (atan2? y x).isSome := by
  unfold atan2?
  simp only [FloatCode.canon_idem]
  split
  · rfl
  · simp only [Option.isSome_some]

theorem logb?_isSome_canon (x b : Int) :
    (logb? (FloatCode.canon x) (FloatCode.canon b)).isSome = (logb? x b).isSome := by
  unfold logb?
  simp only [FloatCode.canon_idem]
  split
  · simp only [Option.isSome_some]
  · rfl

#guard atan2? 0 0 == none && atan2? 0 FloatCode.negOne == some (FloatCode.ofFloat 3.141592653589793)
#guard logb? (FloatCode.ofFloat 8.0) (FloatCode.ofFloat 2.0) == some (FloatCode.ofFloat 3.0)
#guard logb? 0 (FloatCode.ofFloat 2.0) == none && logb? FloatCode.one FloatCode.one == none

/-- Bitwise operations on 64-bit integers. -/
inductive BitOp where
  | and | or | xor
  /-- Shifts by `0`–`63` bits; right shifts keep the sign. -/
  | shl | shr
  deriving Repr, DecidableEq

/-- The name the writer uses: Substrait's `bitwise_*`, and DataFusion's names
for the shifts (Substrait's `shift_left` and `shift_right` parse too). -/
def BitOp.name : BitOp → String
  | .and => "bitwise_and" | .or => "bitwise_or" | .xor => "bitwise_xor"
  | .shl => "bitwise_shift_left" | .shr => "bitwise_shift_right"

def BitOp.all : List BitOp := [.and, .or, .xor, .shl, .shr]

def BitOp.ofName? : String → Option BitOp
  | "shift_left" => some .shl
  | "shift_right" => some .shr
  | n => BitOp.all.find? (·.name == n)

def BitOp.isShift : BitOp → Bool
  | .shl | .shr => true
  | _ => false

/-- The operation on `a` and `b`; `none` for a shift count outside `0`–`63`. -/
def BitOp.apply (op : BitOp) (a b : Int) : Option Int :=
  let x := BitVec.ofInt 64 a
  match op with
  | .and => some (x &&& BitVec.ofInt 64 b).toInt
  | .or => some (x ||| BitVec.ofInt 64 b).toInt
  | .xor => some (x ^^^ BitVec.ofInt 64 b).toInt
  | .shl => if 0 ≤ b ∧ b < 64 then some (x <<< b.toNat).toInt else none
  | .shr => if 0 ≤ b ∧ b < 64 then some (x.sshiftRight b.toNat).toInt else none

#guard BitOp.apply .and (-3) 70 == some 68 && BitOp.apply .or (-3) 70 == some (-1)
#guard BitOp.apply .xor 7 (-1) == some (-8)
#guard BitOp.apply .shl (-3) 6 == some (-192) && BitOp.apply .shl 1 63 == some (-9223372036854775808)
#guard BitOp.apply .shl 3 63 == some (-9223372036854775808) && BitOp.apply .shl 7 64 == none
#guard BitOp.apply .shr (-3) 6 == some (-1) && BitOp.apply .shr 7 (-1) == none
#guard BitOp.apply .shr (-9223372036854775808) 3 == some (-1152921504606846976)

end Substrait
