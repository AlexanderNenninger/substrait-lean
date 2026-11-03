/-!
# Floats and timestamps as integers

**Floats.** Doubles compare as SQL engines compare them (PostgreSQL, DuckDB,
Spark, Snowflake): `-∞ < negatives < 0.0 < positives < +∞ < NaN`, where
`-0.0` *is* `0.0` and every NaN is the same NaN, equal to itself. The model
has one zero and one NaN, so `-0.0` never appears in a result (`-1 · 0.0` is
`0.0`) and `-0.0 >= 0` holds. (DataFusion's own order, `f64::total_cmp`,
puts `-0.0` below `+0.0` and negative NaNs first; `sverify` canonicalizes
DataFusion's inputs and results instead.)

A double is represented by an integer *code* with exactly that order: for
magnitude `m` (`|x| · 2¹⁰⁷⁴` for finite `x`, which is an exact integer;
`M + 1` for ∞, `M + 2` for NaN) the code is `±(2m + 1)`, and zero is `0`.
Comparing doubles is then comparing codes, so filters such as `v > 0.5` or
`v <> -9999.0` are modelled exactly and reuse all of the integer reasoning,
and negation is code negation (the parser keeps NaN fixed under it).

Float *arithmetic* rounds; it is computed with Lean's native `Float` and
treated as "some double" by the contract checker, so no rounding facts are
assumed. The conversions below go through the IEEE bit pattern and are
trusted code.

**Timestamps** are microseconds since 1970-01-01, dates are days, and
day/second intervals are microseconds.
-/

namespace Substrait.FloatCode

/-- Magnitude of the largest finite double: (2⁵³ − 1) · 2⁹⁷¹ · 2¹⁰⁷⁴. -/
@[irreducible] def maxMag : Nat := (2 ^ 53 - 1) * 2 ^ 2045
def infMag : Nat := maxMag + 1
def nanMag : Nat := maxMag + 2

/-- The code of magnitude `m`: zero has one code, `0`, and NaN is never
negative. -/
def ofMag (negative : Bool) (m : Nat) : Int :=
  let c : Int := 2 * m + 1
  if m = 0 then 0 else if negative ∧ m ≠ nanMag then -c else c

def posInf : Int := ofMag false infMag
def negInf : Int := ofMag true infMag
def nan : Int := ofMag false nanMag

/-- The code of a native double. -/
def ofFloat (f : Float) : Int :=
  let bits : Nat := f.toBits.toNat
  let negative := bits / 2 ^ 63 == 1
  let e : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let m : Nat := bits % 2 ^ 52
  let mag : Nat :=
    if e == 2047 then (if m == 0 then infMag else nanMag)
    else if e == 0 then m else (2 ^ 52 + m) * 2 ^ (e - 1)
  ofMag negative mag

/-- The native double for a code (exact for every code `ofFloat` produces). -/
def toFloat (c : Int) : Float :=
  let sign : Nat := if c < 0 then 1 else 0
  let mag := (c.natAbs - 1) / 2
  let bits :=
    if mag ≥ nanMag then 0x7FF8000000000000
    else if mag == infMag then 0x7FF0000000000000
    else if mag < 2 ^ 52 then mag
    else
      let l := Nat.log2 mag
      let e := l - 51
      (e % 2 ^ 11) * 2 ^ 52 + (mag / 2 ^ (l - 52) - 2 ^ 52)
  Float.ofBits (UInt64.ofNat (sign * 2 ^ 63 + bits))

def lift₂ (op : Float → Float → Float) (a b : Int) : Int := ofFloat (op (toFloat a) (toFloat b))

/-- `ROUND(x, d)`, as DuckDB computes it (#335), halves away from zero: with
`m = 10^|d|` (C's `pow`), `round(x · m) / m` for `d ≥ 0`, or `x` itself where
that is not finite (`m` or `x · m` is `±∞`); `round(x / m) · m` for `d < 0`,
or 0 where that is not finite (`round(42, -1000)` is 0, not `0 · ∞`). `±∞`
and NaN stay. -/
def roundTo (d : Int) (c : Int) : Int :=
  let x := toFloat c
  if x.isNaN || x.isInf then c
  else
    let m := Float.pow 10.0 (Float.ofNat d.natAbs)
    let r := if 0 ≤ d then (x * m).round / m else (x / m).round * m
    if r.isNaN || r.isInf then (if 0 ≤ d then c else 0) else ofFloat r

/-- Negation flips the sign; zero (code `0`) stays zero. Code negation would
turn NaN into a code below `-∞`, so the parser writes `negate` as
`CASE WHEN x = NaN THEN x ELSE -x END`, as SQL engines have one NaN. -/
def neg (c : Int) : Int := -c

/-- A code strictly between `-∞` and `+∞`: other codes become the largest
finite double of their sign. -/
def finite (c : Int) : Int :=
  if posInf ≤ c then ofMag false maxMag else if c ≤ negInf then ofMag true maxMag else c

/-- `n` rounded to a multiple of `2ˢ`, halves to the even multiple (IEEE's
round to nearest). -/
def roundTo2 (s n : Nat) : Nat :=
  if 2 ^ s < 2 * (n % 2 ^ s) ∨ (2 * (n % 2 ^ s) = 2 ^ s ∧ n / 2 ^ s % 2 = 1) then
    (n / 2 ^ s + 1) * 2 ^ s
  else n / 2 ^ s * 2 ^ s

/-- The number of bits of `n`, counting at most `f` (structural, so that the
kernel computes it in `f` steps; `Nat.log2` takes `n` steps). -/
def bitLen : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else bitLen f (n / 2) + 1

/-- `n` rounded to 53 significant bits, as IEEE rounds an integer to a
double (before the exponent's range is applied). From `2¹¹⁰⁰` on, far above
every double, it is `2¹¹⁰⁰`. The fuel `min 1100 n` keeps the kernel from
unrolling `bitLen` on an `n` it does not know. -/
def roundSig (n : Nat) : Nat :=
  if n < 2 ^ 1100 then roundTo2 (bitLen (min 1100 n) n - 53) n else 2 ^ 1100

/-- The code of `i` rounded to 53 significant bits, without a bound on the
exponent. -/
def ofIntRaw (i : Int) : Int :=
  let m : Int := (roundSig i.natAbs * 2 ^ 1074 : Nat)
  if i = 0 then 0 else if i < 0 then -(2 * m + 1) else 2 * m + 1

/-- An integer as a double, computed exactly (#372): its magnitude rounded
to 53 significant bits, halves to even, as IEEE converts it. Magnitudes from
`2¹⁰²⁴` on become the largest finite double (as `finite` makes them); IEEE
rounds them to `±∞`, but no integer the model holds (64 bits at most) gets
there, and it lets the checker know the double is finite, so that no `SUM` or `AVG` of
converted integers can add `+∞` and `-∞` (#257). Exact, so that the checker
can use that the conversion is monotone (`ofIntExact_mono`). -/
def ofIntExact (i : Int) : Int :=
  max (-(2 * (maxMag : Int) + 1)) (min (2 * (maxMag : Int) + 1) (ofIntRaw i))

theorem posInf_eq : posInf = 2 * maxMag + 3 := by
  simp only [posInf, ofMag, infMag, Nat.add_one_ne_zero, ite_false, Bool.false_eq_true,
    false_and]
  omega

theorem negInf_eq : negInf = -(2 * maxMag + 3) := by
  have : maxMag + 1 ≠ nanMag := by simp [nanMag]
  simp only [negInf, ofMag, infMag, Nat.add_one_ne_zero, ite_false, true_and, this, ne_eq,
    not_false_eq_true, ite_true]
  omega

set_option exponentiation.threshold 2048 in
theorem maxMag_pos : 0 < maxMag := by
  unfold maxMag; exact Nat.mul_pos (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by decide)))
    (Nat.two_pow_pos _)

theorem finite_bounds (c : Int) : negInf < finite c ∧ finite c < posInf := by
  have hM := maxMag_pos
  have hn : maxMag ≠ nanMag := by simp [nanMag]
  simp only [finite, ofMag, posInf_eq, negInf_eq, Nat.pos_iff_ne_zero.1 hM, ite_false, hn,
    Bool.false_eq_true, false_and, true_and, ne_eq, not_false_eq_true, ite_true]
  split <;> (try split) <;> omega

theorem ofIntExact_bounds (i : Int) : negInf < ofIntExact i ∧ ofIntExact i < posInf := by
  simp only [ofIntExact, posInf_eq, negInf_eq]; omega

theorem ofIntExact_ne_zero {i : Int} (h : i ≠ 0) : ofIntExact i ≠ 0 := by
  have := maxMag_pos
  simp only [ofIntExact, ofIntRaw, h, ite_false]
  split <;> omega

theorem roundTo2_mono (s : Nat) {n n' : Nat} (h : n ≤ n') : roundTo2 s n ≤ roundTo2 s n' := by
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hq : n / 2 ^ s ≤ n' / 2 ^ s := Nat.div_le_div_right h
  have hd := Nat.div_add_mod n (2 ^ s)
  have hd' := Nat.div_add_mod n' (2 ^ s)
  have hr := Nat.mod_lt n hP
  have hr' := Nat.mod_lt n' hP
  have lo : ∀ m, m / 2 ^ s * 2 ^ s ≤ roundTo2 s m := fun m => by
    unfold roundTo2; split
    · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    · exact Nat.le_refl _
  have hi : ∀ m, roundTo2 s m ≤ (m / 2 ^ s + 1) * 2 ^ s := fun m => by
    unfold roundTo2; split
    · exact Nat.le_refl _
    · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  rcases Nat.lt_or_eq_of_le hq with hlt | heq
  · calc roundTo2 s n ≤ (n / 2 ^ s + 1) * 2 ^ s := hi n
      _ ≤ n' / 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ hlt
      _ ≤ roundTo2 s n' := lo n'
  · have hrr : n % 2 ^ s ≤ n' % 2 ^ s := by
      rw [Nat.mul_comm] at hd hd'
      rw [heq] at hd; omega
    have key := lo n'
    unfold roundTo2 at key ⊢
    rw [heq]
    split
    · split
      · exact Nat.le_refl _
      · omega
    · split
      · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
      · exact Nat.le_refl _

theorem roundTo2_mul (s k : Nat) : roundTo2 s (k * 2 ^ s) = k * 2 ^ s := by
  have hP : 0 < 2 ^ s := Nat.two_pow_pos s
  have hm : k * 2 ^ s % 2 ^ s = 0 := Nat.mul_mod_left _ _
  have hdv : k * 2 ^ s / 2 ^ s = k := Nat.mul_div_cancel _ hP
  unfold roundTo2
  rw [hm, hdv]
  split
  · omega
  · rfl

theorem bitLen_zero : ∀ f, bitLen f 0 = 0
  | 0 => rfl
  | _ + 1 => by simp [bitLen]

theorem bitLen_le_fuel : ∀ f n, bitLen f n ≤ f
  | 0, _ => Nat.le_refl _
  | f + 1, n => by
    unfold bitLen; split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (bitLen_le_fuel f _)

theorem bitLen_mono : ∀ f {n n' : Nat}, n ≤ n' → bitLen f n ≤ bitLen f n'
  | 0, _, _, _ => Nat.le_refl _
  | f + 1, n, n', h => by
    unfold bitLen; split
    · exact Nat.zero_le _
    · simp only [show n' ≠ 0 by omega, ↓reduceIte]
      exact Nat.succ_le_succ (bitLen_mono f (Nat.div_le_div_right h))

theorem lt_two_pow_bitLen : ∀ f n, n < 2 ^ f → n < 2 ^ bitLen f n
  | 0, n, h => by simp at h; subst h; simp [bitLen]
  | f + 1, n, h => by
    unfold bitLen; split
    · rename_i h0; simp [h0]
    · have ih := lt_two_pow_bitLen f (n / 2) (by rw [Nat.pow_succ] at h; omega)
      rw [Nat.pow_succ]; omega

theorem two_pow_bitLen_le : ∀ f n, n ≠ 0 → 2 ^ bitLen f n ≤ 2 * n
  | 0, n, h => by simp [bitLen]; omega
  | f + 1, n, h => by
    unfold bitLen
    simp only [h, ↓reduceIte, Nat.pow_succ]
    by_cases h2 : n / 2 = 0
    · rw [h2, bitLen_zero]; omega
    · have := two_pow_bitLen_le f (n / 2) h2; omega

/-- Enough fuel counts every bit. -/
theorem bitLen_fuel : ∀ f g n, n < 2 ^ f → n < 2 ^ g → bitLen f n = bitLen g n
  | 0, g, n, hf, _ => by simp at hf; subst hf; rw [bitLen_zero, bitLen_zero]
  | f + 1, 0, n, _, hg => by simp at hg; subst hg; rw [bitLen_zero, bitLen_zero]
  | f + 1, g + 1, n, hf, hg => by
    unfold bitLen; split
    · rfl
    · rw [Nat.pow_succ] at hf hg
      rw [bitLen_fuel f g (n / 2) (by omega) (by omega)]

theorem bitLen_min {n : Nat} (h : n < 2 ^ 1100) : bitLen (min 1100 n) n = bitLen 1100 n :=
  bitLen_fuel _ _ n (by
    rcases Nat.le_total 1100 n with hm | hm
    · rw [Nat.min_eq_left hm]; exact h
    · rw [Nat.min_eq_right hm]; exact Nat.lt_two_pow_self) h

set_option exponentiation.threshold 2100 in
theorem roundSig_mono {n n' : Nat} (h : n ≤ n') : roundSig n ≤ roundSig n' := by
  unfold roundSig
  have hl := bitLen_mono 1100 h
  have hle := bitLen_le_fuel 1100 n
  by_cases hn : n < 2 ^ 1100
  · rw [bitLen_min hn]
    have h1 : n < 2 ^ 53 * 2 ^ (bitLen 1100 n - 53) := by
      rw [← Nat.pow_add]
      exact Nat.lt_of_lt_of_le (lt_two_pow_bitLen _ _ hn) (Nat.pow_le_pow_right (by decide) (by omega))
    have top : roundTo2 (bitLen 1100 n - 53) n ≤ 2 ^ 53 * 2 ^ (bitLen 1100 n - 53) :=
      Nat.le_trans (roundTo2_mono _ (Nat.le_of_lt h1)) (Nat.le_of_eq (roundTo2_mul _ _))
    simp only [hn, ↓reduceIte]
    by_cases hn' : n' < 2 ^ 1100
    · simp only [hn', ↓reduceIte]
      rw [bitLen_min hn']
      by_cases hs : bitLen 1100 n - 53 = bitLen 1100 n' - 53
      · rw [hs]; exact roundTo2_mono _ h
      · -- `n` rounds to at most `2^(s+53)`, `n'` to at least `2^(s'+52)`, and `s < s'`.
        have hn0 : n' ≠ 0 := by
          intro h0; subst h0; rw [bitLen_zero] at hs hl; omega
        have h2 : 2 ^ 52 * 2 ^ (bitLen 1100 n' - 53) ≤ n' := by
          have := two_pow_bitLen_le 1100 n' hn0
          have e : bitLen 1100 n' = 53 + (bitLen 1100 n' - 53) := by omega
          rw [e, Nat.pow_add, show (2 : Nat) ^ 53 = 2 * 2 ^ 52 by decide] at this
          rw [Nat.mul_assoc] at this; omega
        have h3 : 2 ^ 53 * 2 ^ (bitLen 1100 n - 53) ≤ 2 ^ 52 * 2 ^ (bitLen 1100 n' - 53) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        calc roundTo2 (bitLen 1100 n - 53) n
            ≤ 2 ^ 53 * 2 ^ (bitLen 1100 n - 53) := top
          _ ≤ 2 ^ 52 * 2 ^ (bitLen 1100 n' - 53) := h3
          _ = roundTo2 (bitLen 1100 n' - 53) (2 ^ 52 * 2 ^ (bitLen 1100 n' - 53)) :=
            (roundTo2_mul _ _).symm
          _ ≤ roundTo2 (bitLen 1100 n' - 53) n' := roundTo2_mono _ h2
    · simp only [hn', ↓reduceIte]
      refine Nat.le_trans top ?_
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
  · simp only [hn, show ¬n' < 2 ^ 1100 by omega, ↓reduceIte, Nat.le_refl]

theorem ofIntRaw_mono {i j : Int} (h : i ≤ j) : ofIntRaw i ≤ ofIntRaw j := by
  simp only [ofIntRaw]
  have hm : ∀ {a b : Nat}, a ≤ b →
      ((roundSig a * 2 ^ 1074 : Nat) : Int) ≤ ((roundSig b * 2 ^ 1074 : Nat) : Int) :=
    fun hab => Int.ofNat_le.2 (Nat.mul_le_mul_right _ (roundSig_mono hab))
  have h0 : ∀ a : Nat, (0 : Int) ≤ ((roundSig a * 2 ^ 1074 : Nat) : Int) := fun _ => Int.natCast_nonneg _
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0 <;> simp only [hi0, hj0, ite_true, ite_false] <;>
    (try split) <;> (try split) <;> (try omega)
  all_goals first
    | (have := hm (a := j.natAbs) (b := i.natAbs) (by omega); have := h0 j.natAbs; omega)
    | (have := hm (a := i.natAbs) (b := j.natAbs) (by omega); have := h0 i.natAbs; omega)
    | (have := h0 i.natAbs; have := h0 j.natAbs; omega)

theorem ofIntExact_mono {i j : Int} (h : i ≤ j) : ofIntExact i ≤ ofIntExact j := by
  have := ofIntRaw_mono h
  simp only [ofIntExact]; omega

/-- A conversion of integers to doubles, with what the checker knows of it. -/
structure IntToDouble where
  conv : Int → Int
  bounds : ∀ i, negInf < conv i ∧ conv i < posInf
  ne_zero : ∀ {i}, i ≠ 0 → conv i ≠ 0
  mono : ∀ {i j}, i ≤ j → conv i ≤ conv j

/-- `ofIntExact`, behind a constant the kernel does not unfold: proofs about
plans use only the properties above, as they did of the native conversion
before, and type-checking them never computes a rounding. -/
opaque intToDouble : IntToDouble :=
  ⟨ofIntExact, ofIntExact_bounds, ofIntExact_ne_zero, ofIntExact_mono⟩

/-- An integer as a double (`ofIntExact`). -/
def ofInt (i : Int) : Int := intToDouble.conv i

theorem ofInt_bounds (i : Int) : negInf < ofInt i ∧ ofInt i < posInf := intToDouble.bounds i

theorem ofInt_ne_zero {i : Int} (h : i ≠ 0) : ofInt i ≠ 0 := intToDouble.ne_zero h

/-- The conversion of integers to doubles is monotone. -/
theorem ofInt_mono {i j : Int} (h : i ≤ j) : ofInt i ≤ ofInt j := intToDouble.mono h

-- The native conversion agrees, also where it rounds (`2⁵³ + 1` is a tie).
#guard [0, 1, -1, 7, -12345, 2 ^ 53, 2 ^ 53 + 1, 2 ^ 53 + 3, -(2 ^ 53 + 1), 2 ^ 63 - 1,
  -(2 ^ 63), 2 ^ 62 + 2 ^ 9, 2 ^ 62 + 2 ^ 9 + 1, 2 ^ 1100, -(2 ^ 1100)].all fun i =>
    ofInt i == finite (ofFloat (Float.ofInt i))
#guard ofInt (2 ^ 1100) == ofMag false maxMag

def isNan (c : Int) : Bool := c == nan

-- One zero and one NaN: `-0.0` and a negative NaN (as x86 computes `0/0`)
-- have the codes of `0.0` and NaN, and negation keeps zero.
#guard ofFloat (Float.ofBits 0x8000000000000000) == 0 && ofFloat 0.0 == 0
#guard ofFloat (Float.ofBits 0xFFF8000000000000) == nan && ofFloat (0.0 / 0.0) == nan
#guard neg (ofFloat 0.0) == 0 && neg (ofFloat 1.5) == ofFloat (-1.5)
-- `ROUND(x, d)` as DuckDB gives it (#335), at ordinary and extreme digits.
#guard roundTo (-1) (ofFloat 42.0) == ofFloat 40.0 && roundTo (-2) (ofFloat 42.0) == 0
#guard roundTo (-1000) (ofFloat 42.0) == 0 && roundTo (-2147483648) (ofFloat 1.0) == 0
#guard roundTo (-5) (ofFloat 521924.88982515107) == ofFloat 500000.0
#guard roundTo 2 (ofFloat 42.123) == ofFloat 42.12 && roundTo 0 (ofFloat 2.5) == ofFloat 3.0
#guard roundTo 400 (ofFloat 5e-324) == ofFloat 5e-324 && roundTo 308 (ofFloat 5e-324) == 0
#guard roundTo (-309) (ofFloat 1e308) == 0 && roundTo (-308) (ofFloat 1e308) == ofFloat 1e308
#guard roundTo (-3) posInf == posInf && roundTo 3 nan == nan
#guard ofFloat (-1.0 * 0.0) == 0 && negInf < ofFloat (-1.0) && ofFloat 5e-324 > 0 && posInf < nan

/-- `(-1)^s · m · 2⁻¹⁰⁷⁴` for a finite code, as `(negative, m)`. -/
def finiteParts (c : Int) : Bool × Nat := (c < 0, (c.natAbs - 1) / 2)

/-- `fmod(a, b)`, the remainder of doubles in C and IEEE 754, which DuckDB,
DataFusion and Spark compute for `%`: `a - b · trunc(a / b)`, with the sign of
`a`. It is exact, so the codes give it without rounding: the magnitude of a
finite double is an integer (`|x| · 2¹⁰⁷⁴`), and the remainder of the
magnitudes is the magnitude of the remainder. NaN or an infinite `a` give
NaN, and an infinite `b` gives `a`. A zero `b` gives NaN here, but the model
reports it as a division by zero (`BinFn.issue`), as for integers (#203). -/
def fmod (a b : Int) : Int :=
  let (negative, ma) := finiteParts a
  let mb := (finiteParts b).2
  if infMag ≤ ma ∨ nanMag ≤ mb ∨ mb = 0 then nan
  else if mb = infMag then a
  else ofMag negative (ma % mb)

#guard fmod (ofFloat 7.5) (ofFloat 2.0) == ofFloat 1.5
#guard fmod (ofFloat (-7.5)) (ofFloat 2.0) == ofFloat (-1.5)
#guard fmod (ofFloat 7.5) (ofFloat (-2.0)) == ofFloat 1.5
-- `-0.0` in IEEE; the model's one zero.
#guard fmod (ofFloat (-4.0)) (ofFloat 2.0) == 0 && fmod 0 (ofFloat 2.0) == 0
#guard fmod (ofFloat 7.5) 0 == nan && fmod 0 0 == nan && fmod nan (ofFloat 2.0) == nan
#guard fmod posInf (ofFloat 2.0) == nan && fmod negInf (ofFloat 2.0) == nan
#guard fmod (ofFloat 7.5) posInf == ofFloat 7.5 && fmod (ofFloat (-7.5)) negInf == ofFloat (-7.5)
#guard fmod (ofFloat 7.5) nan == nan && fmod posInf posInf == nan
-- Exact where `a - b · trunc(a / b)` in doubles is not (it gives `0.0` for
-- the first and third), across exponents and for subnormals.
#guard fmod (ofFloat 1e308) (ofFloat 3.0) == ofFloat 2.0
#guard fmod (ofFloat 1e308) (ofFloat 1e-300) == ofFloat 3.0195000970293847e-301
#guard fmod (ofFloat 1152921504606846977.0) (ofFloat 7.0) == ofFloat 1.0
#guard fmod (ofFloat 0.3) (ofFloat 0.1) == ofFloat 0.09999999999999998
#guard fmod (ofFloat 5e-324) (ofFloat 2.0) == ofFloat 5e-324

/-- `CAST(x AS DECIMAL(_, s))` of a double, as the decimal's unscaled integer:
`round(x · 10ˢ)` computed in doubles, halves away from zero, as DuckDB and
DataFusion cast (#27). NaN and ±∞ have none. -/
def toDecimal? (c : Int) (s : Nat) : Option Int :=
  let (negative, m) := finiteParts (ofFloat (toFloat c * Float.ofNat (10 ^ s)).round)
  -- A whole double's magnitude is a multiple of 2¹⁰⁷⁴.
  if infMag ≤ m then none else
    let q : Int := (m / 2 ^ 1074 : Nat)
    some (if negative then -q else q)

/-- A decimal's unscaled integer `n` at scale `s` as a double's code,
correctly rounded (#27). A decimal has at most 38 digits, far below `2¹⁰²⁴`,
so `finite` changes nothing and tells the checker the double is finite
(#257). -/
def ofDecimal (n : Int) (s : Nat) : Int :=
  let f := Float.ofScientific n.natAbs true s
  finite (ofFloat (if n < 0 then -f else f))

-- The backends' cases: the product rounds in doubles (`-2.675 · 100` is
-- `-267.5`), and `0.145 · 100` is just below `14.5`.
#guard toDecimal? (ofFloat 0.125) 2 == some 13 && toDecimal? (ofFloat (-2.675)) 2 == some (-268)
#guard toDecimal? (ofFloat 0.135) 2 == some 14 && toDecimal? (ofFloat 0.145) 2 == some 14
#guard toDecimal? (ofFloat 2.5) 0 == some 3 && toDecimal? (ofFloat (-2.5)) 0 == some (-3)
#guard toDecimal? (ofFloat 1e20) 2 == some (10 ^ 22) && toDecimal? nan 2 == none
#guard toDecimal? posInf 0 == none && toDecimal? 0 3 == some 0
#guard ofDecimal 1234 2 == ofFloat 12.34 && ofDecimal (-5) 2 == ofFloat (-0.05)
#guard ofDecimal 145 3 == ofFloat 0.145 && ofDecimal 0 5 == 0
-- Correctly rounded where `n` itself is not a double: 2⁵³ + 1 is a tie.
#guard ofDecimal 9007199254740993 0 == ofFloat 9007199254740992.0
#guard ofDecimal 99999999999999999999 2 == ofFloat 999999999999999999.99

end Substrait.FloatCode

namespace Substrait.Time

/-- Days since 1970-01-01 for a proleptic Gregorian date (Howard Hinnant's
`days_from_civil`). -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def parseNat? (s : String) : Option Nat := if s.isEmpty then none else s.toNat?

/-- `YYYY-MM-DD` → days since the epoch. -/
def parseDate? (s : String) : Option Int := do
  let [y, m, d] := s.splitOn "-" | none
  return daysFromCivil (← parseNat? y) (← parseNat? m) (← parseNat? d)

/-- `YYYY-MM-DD[ HH:MM:SS[.ffffff]]` → microseconds since the epoch. -/
def parseTimestamp? (s : String) : Option Int := do
  let (datePart, timePart) := match s.splitOn " " with
    | [d] => (d, "00:00:00")
    | [d, t] => (d, t)
    | _ => ("", "")
  let days ← parseDate? datePart
  let (hms, fracPart) := match timePart.splitOn "." with
    | [t] => (t, "")
    | [t, f] => (t, f)
    | _ => ("", "")
  let [h, mi, sec] := hms.splitOn ":" | none
  let frac := (fracPart ++ "000000").take 6
  let micros ← if fracPart.isEmpty then pure 0 else parseNat? frac.toString
  return ((days * 24 + (← parseNat? h)) * 60 + (← parseNat? mi)) * 60_000_000 +
    (← parseNat? sec) * 1_000_000 + micros

end Substrait.Time

namespace Substrait.Base64

def decodeChar (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- Decode standard base64 into bytes. -/
def decode (s : String) : Option (List Nat) := do
  let vals ← (s.toList.filter (· ≠ '=')).mapM decodeChar
  let bits := vals.flatMap fun v => (List.range 6).reverse.map fun i => (v / 2 ^ i) % 2
  let nbytes := bits.length / 8
  return (List.range nbytes).map fun b =>
    ((List.range 8).map fun i => bits[b * 8 + i]! * 2 ^ (7 - i)).sum

/-- A little-endian two's-complement integer (Substrait's decimal encoding). -/
def leSigned (bytes : List Nat) : Int :=
  let n : Nat := (bytes.zipIdx.map fun (b, i) => b * 256 ^ i).sum
  if bytes.length > 0 && bytes.getLast! ≥ 128 then (n : Int) - 256 ^ bytes.length else n

def encodeChar (v : Nat) : Char :=
  if v < 26 then Char.ofNat ('A'.toNat + v)
  else if v < 52 then Char.ofNat ('a'.toNat + v - 26)
  else if v < 62 then Char.ofNat ('0'.toNat + v - 52)
  else if v = 62 then '+' else '/'

/-- Encode bytes as standard base64, padded with `=`. -/
def encode (bytes : List Nat) : String :=
  let bits := bytes.flatMap fun b => (List.range 8).reverse.map fun i => (b / 2 ^ i) % 2
  let groups := (bits.length + 5) / 6
  let chars := (List.range groups).map fun g =>
    encodeChar ((List.range 6).map fun i => bits.getD (g * 6 + i) 0 * 2 ^ (5 - i)).sum
  (String.ofList chars).pushn '=' ((4 - groups % 4) % 4)

/-- `m` as 16 little-endian bytes of two's complement (Substrait's decimal
encoding, for `-2¹²⁷ ≤ m < 2¹²⁷`). -/
def leBytes16 (m : Int) : List Nat :=
  let u : Nat := (if m < 0 then m + 2 ^ 128 else m).toNat
  (List.range 16).map fun i => u / 256 ^ i % 256

#guard [0, 1, -1, 1235, -1235, 10 ^ 37, -(10 ^ 37)].all fun m =>
  (decode (encode (leBytes16 m))).map leSigned == some m
#guard encode (leBytes16 1235) == "0wQAAAAAAAAAAAAAAAAAAA=="

end Substrait.Base64
