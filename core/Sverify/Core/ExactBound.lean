import Lean.Data.Json

/-!
# Exact arithmetic for the reported bounds (#660)

The tolerance analyses (`Epsilon.lean`, `EngineRobust.lean`, `OpenSums.lean`,
the Lipschitz modules) evaluate the formulas of
`float-bounds/FloatBounds/Propagate.lean` and `Epsilon.lean` in `Rat`. Every
`+`, `-`, `*` and `/` is exact, so a computed bound is the formula's value
and no factor covers an evaluation in doubles. Three operations are not
field operations:

* `sqrtUp` and `sqrtDown`, square roots rounded outward to 64 bits
  (`sqrtUp_sq`, `sqrtDown_sq`, both proved here);
* `expUp`, an upper bound on `exp x` from `(1 - x/N)^(-N) ≥ exp x ≥ (1 + x/N)^N`
  with `N = 2⁶⁰`, the powers taken by squaring with outward rounding. The two
  inequalities are facts about the reals, stated beside `NativeLink.exp`
  in `docs/proofs.md` ("What is trusted");
* `toJsonUp`, a bound as JSON: a decimal at least `q · (1 + 2⁻⁵⁰) + 2⁻¹⁰⁷⁴`
  (`upDecimal_ge`, proved), so the double nearest to it, which a JSON reader
  takes, is still at least `q`.
-/

namespace Substrait.ExactBound

open Lean (Json JsonNumber)

/-- `2 ^ k` for an integer `k`, exactly. -/
def pow2 (k : Int) : Rat :=
  if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/-- The unit roundoff of a double, `2⁻⁵³`. -/
def unitRound : Rat := pow2 (-53)

/-- `2⁻¹⁰²²`, the least normal double: the underflow term of a rounding. -/
def tiny : Rat := pow2 (-1022)

/-- `2⁻¹⁰⁷⁴`, the least positive double. -/
def least : Rat := pow2 (-1074)

/-- `n` scaled units (`FloatCode.scaled`: the value times `2¹⁰⁷⁴`), exactly. -/
def unscale (n : Nat) : Rat := (n : Rat) / ((2 ^ 1074 : Nat) : Rat)

/-! ## Lemmas on `Rat` -/

/-- Cross-multiplied, over positive denominators. -/
theorem div_le_div_of_mul_le (a b c d : Rat) (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) : a / b ≤ c / d := by
  have hb' : b ≠ 0 := (Rat.ne_of_gt hb)
  have hd' : d ≠ 0 := (Rat.ne_of_gt hd)
  have e1 : a / b = (a * d) / (b * d) := by
    rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
    have := Rat.mul_inv_cancel d hd'
    grind
  have e2 : c / d = (c * b) / (b * d) := by
    rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
    have := Rat.mul_inv_cancel b hb'
    grind
  rw [e1, e2, Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hb hd)))

/-- A nonnegative rational as a quotient of naturals. -/
theorem eq_natDiv (q : Rat) (h : 0 ≤ q) : q = (q.num.toNat : Rat) / (q.den : Rat) := by
  conv => lhs; rw [← Rat.num_divInt_den q]
  rw [Rat.divInt_eq_div]
  have : ((q.num.toNat : Int) : Rat) = (q.num : Rat) := by rw [Int.toNat_of_nonneg (Rat.num_nonneg.mpr h)]
  rw [← this]; rfl

theorem sq_div (x y : Rat) : (x / y) * (x / y) = (x * x) / (y * y) := by
  simp only [Rat.div_def, Rat.inv_mul_rev]; grind

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  rcases Rat.le_iff_lt_or_eq.mp hb with hb | hb
  · exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))
  · rw [← hb]; simp

/-! ## Rounding to a dyadic, outward -/

/-- `q ≥ 0` rounded up to `p` significant bits (`q` itself at `0`). -/
def roundUp (p : Nat) (q : Rat) : Rat :=
  if q ≤ 0 then q else
  let a := q.num.toNat
  let b := q.den
  let s : Int := (p : Int) - ((a.log2 : Int) - (b.log2 : Int))
  if 0 ≤ s then
    let n := a * 2 ^ s.toNat
    (((n + b - 1) / b : Nat) : Rat) / ((2 ^ s.toNat : Nat) : Rat)
  else
    let d := b * 2 ^ (-s).toNat
    (((a + d - 1) / d : Nat) : Rat) * ((2 ^ (-s).toNat : Nat) : Rat)

/-- `q ≥ 0` rounded down to `p` significant bits. -/
def roundDown (p : Nat) (q : Rat) : Rat :=
  if q ≤ 0 then q else
  let a := q.num.toNat
  let b := q.den
  let s : Int := (p : Int) - ((a.log2 : Int) - (b.log2 : Int))
  if 0 ≤ s then
    ((a * 2 ^ s.toNat / b : Nat) : Rat) / ((2 ^ s.toNat : Nat) : Rat)
  else
    ((a / (b * 2 ^ (-s).toNat) : Nat) : Rat) * ((2 ^ (-s).toNat : Nat) : Rat)

/-! ## Square roots -/

/-- The scaled radicand of `q = a / b`: `√q = √(a · b · 4⁶⁴) / (b · 2⁶⁴)`. -/
def sqrtRad (q : Rat) : Nat := q.num.toNat * q.den * 4 ^ 64

/-- The scale of `sqrtRad`'s root. -/
def sqrtScale (q : Rat) : Nat := q.den * 2 ^ 64

/-- `√q` rounded up, within `2⁻⁶⁴` of it relatively (`0` for `q ≤ 0`). -/
def sqrtUp (q : Rat) : Rat :=
  if q ≤ 0 then 0 else ((sqrtRad q).sqrt + 1 : Nat) / (sqrtScale q : Rat)

/-- `√q` rounded down (`0` for `q ≤ 0`). -/
def sqrtDown (q : Rat) : Rat :=
  if q ≤ 0 then 0 else ((sqrtRad q).sqrt : Nat) / (sqrtScale q : Rat)

/-- **`sqrtUp` is at least the root.** -/
theorem sqrtUp_sq (q : Rat) (h : 0 ≤ q) : q ≤ sqrtUp q * sqrtUp q := by
  unfold sqrtUp
  split
  · next h0 => grind
  · next h0 =>
    have hq : 0 < q := by grind
    have hden : 0 < q.den := Nat.pos_of_ne_zero q.den_nz
    have hr := Nat.lt_succ_sqrt (sqrtRad q)
    conv => lhs; rw [eq_natDiv q h]
    rw [sq_div]
    apply div_le_div_of_mul_le
    · exact Rat.natCast_pos.mpr hden
    · have h1 : 0 < sqrtScale q := Nat.mul_pos hden (Nat.pow_pos (by decide))
      rw [← Rat.natCast_mul]; exact Rat.natCast_pos.mpr (Nat.mul_pos h1 h1)
    · rw [← Rat.natCast_mul, ← Rat.natCast_mul, ← Rat.natCast_mul, ← Rat.natCast_mul, Rat.natCast_le_natCast]
      unfold sqrtRad sqrtScale at *
      have : q.num.toNat * q.den * 4 ^ 64 * q.den ≤ ((q.num.toNat * q.den * 4 ^ 64).sqrt + 1) * ((q.num.toNat * q.den * 4 ^ 64).sqrt + 1) * q.den :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hr)
      have e : q.num.toNat * (q.den * 2 ^ 64 * (q.den * 2 ^ 64)) = q.num.toNat * q.den * 4 ^ 64 * q.den := by
        rw [show (4:Nat) ^ 64 = 2 ^ 64 * 2 ^ 64 by decide]; grind
      rw [e]; exact this

theorem sqrtDown_nonneg (q : Rat) : 0 ≤ sqrtDown q := by
  unfold sqrtDown; split
  · exact Rat.le_refl
  · exact div_nonneg' Rat.natCast_nonneg Rat.natCast_nonneg

/-- **`sqrtDown` is at most the root.** -/
theorem sqrtDown_sq (q : Rat) (h : 0 ≤ q) : sqrtDown q * sqrtDown q ≤ q := by
  unfold sqrtDown
  split
  · simp; exact h
  · next h0 =>
    have hden : 0 < q.den := Nat.pos_of_ne_zero q.den_nz
    have hr := Nat.sqrt_le (sqrtRad q)
    conv => rhs; rw [eq_natDiv q h]
    rw [sq_div]
    apply div_le_div_of_mul_le
    · have h1 : 0 < sqrtScale q := Nat.mul_pos hden (Nat.pow_pos (by decide))
      rw [← Rat.natCast_mul]; exact Rat.natCast_pos.mpr (Nat.mul_pos h1 h1)
    · exact Rat.natCast_pos.mpr hden
    · rw [← Rat.natCast_mul, ← Rat.natCast_mul, ← Rat.natCast_mul, ← Rat.natCast_mul, Rat.natCast_le_natCast]
      unfold sqrtRad sqrtScale at *
      have : (q.num.toNat * q.den * 4 ^ 64).sqrt * (q.num.toNat * q.den * 4 ^ 64).sqrt * q.den ≤ q.num.toNat * q.den * 4 ^ 64 * q.den :=
        Nat.mul_le_mul_right _ hr
      have e : q.num.toNat * (q.den * 2 ^ 64 * (q.den * 2 ^ 64)) = q.num.toNat * q.den * 4 ^ 64 * q.den := by
        rw [show (4:Nat) ^ 64 = 2 ^ 64 * 2 ^ 64 by decide]; grind
      rw [e]; exact this

/-! ## The exponential -/

/-- `x ^ (2 ^ k)` by squaring, each square rounded with `r`. -/
def sqIter (r : Rat → Rat) : Nat → Rat → Rat
  | 0, x => x
  | k + 1, x => sqIter r k (r (x * x))

/-- The bits kept by the exponential's squarings. -/
def expBits : Nat := 128

/-- `(1 + t / 2⁶⁰) ^ (2⁶⁰)`, rounded down: at most `exp t`, for `t ≥ 0`. -/
def expLow (t : Rat) : Rat :=
  sqIter (roundDown expBits) 60 (roundDown expBits (1 + t * pow2 (-60)))

/-- An upper bound on `exp x`: for `x ≥ 0`, `(1 - x / 2⁶⁰) ^ (-2⁶⁰)`, the base
rounded down and the power's reciprocal up; for `x < 0`, `1 / expLow (-x)`,
rounded up. -/
def expUp (x : Rat) : Rat :=
  if x < 0 then roundUp expBits (1 / expLow (-x))
  else
    let base := roundDown expBits (1 - x * pow2 (-60))
    roundUp expBits (1 / sqIter (roundDown expBits) 60 base)

/-! ## Output -/

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The decimal `toJsonUp` writes for `q > 0`: `q · (1 + 2⁻⁵⁰) + 2⁻¹⁰⁷⁴`
rounded up at about 20 significant digits, as a mantissa and a count of
decimals. -/
def upDecimal (q : Rat) : Nat × Nat :=
  let w := q * (1 + pow2 (-50)) + least
  let a := w.num.toNat
  let b := w.den
  let digits (n : Nat) := (toString n).length
  let k : Nat := (20 + digits b) - digits a
  (ceilDiv (a * 10 ^ k) b, k)

theorem pow2_nonneg (k : Int) : 0 ≤ pow2 k := by
  unfold pow2; split
  · exact Rat.natCast_nonneg
  · exact div_nonneg' (by decide) Rat.natCast_nonneg

theorem le_ceilDiv (a b : Nat) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have := Nat.div_add_mod (a + b - 1) b
  have := Nat.mod_lt (a + b - 1) hb
  grind

/-- **The decimal `toJsonUp` writes is at least `q · (1 + 2⁻⁵⁰) + 2⁻¹⁰⁷⁴`.** A
JSON reader takes the double nearest to it, within `2⁻⁵³` of it relatively
or `2⁻¹⁰⁷⁵` absolutely, so at least `q`. -/
theorem upDecimal_ge (q : Rat) (h : 0 ≤ q) :
    q * (1 + pow2 (-50)) + least ≤ ((upDecimal q).1 : Rat) / ((10 ^ (upDecimal q).2 : Nat) : Rat) := by
  have hw : 0 ≤ q * (1 + pow2 (-50)) + least := by
    have := pow2_nonneg (-50); have := pow2_nonneg (-1074); unfold least
    have := Rat.mul_nonneg h (show (0:Rat) ≤ 1 + pow2 (-50) by grind); grind
  generalize hW : q * (1 + pow2 (-50)) + least = w at hw
  simp only [upDecimal, hW]
  generalize (20 + (toString w.den).length) - (toString w.num.toNat).length = k
  conv => lhs; rw [eq_natDiv w hw]
  have hden : 0 < w.den := Nat.pos_of_ne_zero w.den_nz
  apply div_le_div_of_mul_le
  · exact Rat.natCast_pos.mpr hden
  · exact Rat.natCast_pos.mpr (Nat.pow_pos (by decide))
  · rw [← Rat.natCast_mul, ← Rat.natCast_mul, Rat.natCast_le_natCast]
    exact le_ceilDiv _ _ hden

/-- A bound as JSON, rounded up: `0` for zero, and for `q > 0` a decimal the
nearest double of which is at least `q` (`upDecimal_ge`). -/
def toJsonUp (q : Rat) : Json :=
  if q ≤ 0 then Json.num (0 : Nat) else
  let (m, k) := upDecimal q
  .num ⟨m, k⟩

/-- A JSON number, exactly. -/
def ofJsonNumber (n : JsonNumber) : Rat := (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

end Substrait.ExactBound
