import SubstraitLean.FloatFormat

/-!
# Floats and timestamps as integers

**Floats.** Doubles compare as SQL engines compare them (PostgreSQL, DuckDB,
Spark, Snowflake): `-∞ < negatives < 0.0 < positives < +∞ < NaN`, where
`-0.0` *is* `0.0` and every NaN is the same NaN, equal to itself. The model
has one zero and one NaN, so `-0.0` never appears in a result (`-1 · 0.0` is
`0.0`) and `-0.0 >= 0` holds. (DataFusion's own order, `f64::total_cmp`,
puts `-0.0` below `+0.0` and negative NaNs first; `sverify` canonicalizes
DataFusion's inputs and results instead.)

A double is represented by an integer *code* with exactly that order
(`SubstraitLean/FloatFormat.lean` states the codes for every format; doubles
are its instance `fp64`): for
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
abbrev maxMag : Nat := fp64.maxMag
abbrev infMag : Nat := fp64.infMag
abbrev nanMag : Nat := fp64.nanMag

/-- The code of magnitude `m` (`FloatFormat.ofMag`). -/
abbrev ofMag : Bool → Nat → Int := fp64.ofMag

abbrev posInf : Int := fp64.posInf
abbrev negInf : Int := fp64.negInf
abbrev nan : Int := fp64.nan

theorem maxMag_def : maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := fp64_maxMag

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

/-- `ROUND(x, d)`, as DuckDB 2.0 computes it (#335, `duckdb-round-digits-2`), halves
away from zero: with `m = 10^|d|` (C's `pow`), `round(x · m) / m` for
`d ≥ 0` and `round(x / m) · m` for `d < 0`, or `x` itself where that is not
finite (`round(1.5e308, -308)` is `1.5e308`, not `2e308`); 0 for `d < 0`
when `m` is `±∞` (`round(42, -1000)` is 0). `±∞` and NaN stay. -/
def roundTo (d : Int) (c : Int) : Int :=
  let x := toFloat c
  if x.isNaN || x.isInf then c
  else
    let m := Float.pow 10.0 (Float.ofNat d.natAbs)
    if d < 0 && m.isInf then 0
    else
      let r := if 0 ≤ d then (x * m).round / m else (x / m).round * m
      if r.isNaN || r.isInf then c else ofFloat r

/-- Negation flips the sign; zero (code `0`) stays zero. Code negation would
turn NaN into a code below `-∞`, so the parser writes `negate` as
`CASE WHEN x = NaN THEN x ELSE -x END`, as SQL engines have one NaN. -/
def neg (c : Int) : Int := -c

/-- A code strictly between `-∞` and `+∞` (`FloatFormat.finite`). -/
abbrev finite : Int → Int := fp64.finite

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

theorem posInf_eq : posInf = 2 * maxMag + 3 := fp64.posInf_eq

theorem negInf_eq : negInf = -(2 * maxMag + 3) := fp64.negInf_eq

theorem maxMag_pos : 0 < maxMag := fp64.maxMag_pos (by decide)

theorem finite_bounds (c : Int) : negInf < finite c ∧ finite c < posInf := fp64.finite_bounds (by decide) c

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

/-- The code of an integer that is a double exactly (`|i| ≤ 2⁵³`). -/
abbrev exactCode : Int → Int := fp64.exactCode

set_option exponentiation.threshold 2100 in
theorem roundSig_exact {n : Nat} (h : n ≤ 2 ^ 53) : roundSig n = n := by
  have hC : n < 2 ^ 1100 := Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) (by decide))
  unfold roundSig
  simp only [hC, ↓reduceIte]
  rw [bitLen_min hC]
  by_cases hn : n = 0
  · subst hn; rw [bitLen_zero]; simpa using roundTo2_mul 0 0
  have hb := two_pow_bitLen_le 1100 n hn
  have hb54 : bitLen 1100 n ≤ 54 := by
    apply Nat.le_of_not_lt; intro hlt
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hlt
    have : 2 ^ 55 ≤ 2 * n := Nat.le_trans this hb
    have : (2 : Nat) ^ 55 = 2 * 2 ^ 54 := by decide
    have : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by decide
    omega
  by_cases h53 : bitLen 1100 n ≤ 53
  · rw [show bitLen 1100 n - 53 = 0 by omega]
    simpa using roundTo2_mul 0 n
  · have hb' : bitLen 1100 n = 54 := by omega
    rw [hb'] at hb
    have e1 : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by decide
    have hn' : n = 2 ^ 52 * 2 ^ 1 := by
      have : (2 : Nat) ^ 53 = 2 ^ 52 * 2 ^ 1 := by decide
      omega
    rw [hb', show 54 - 53 = 1 by rfl, hn']
    exact roundTo2_mul _ _

set_option exponentiation.threshold 2100 in
theorem ofIntExact_exact {i : Int} (h : i.natAbs ≤ 2 ^ 53) : ofIntExact i = exactCode i := by
  have hr := roundSig_exact h
  have hM : ((i.natAbs * 2 ^ 1074 : Nat) : Int) ≤ maxMag := by
    have : i.natAbs * 2 ^ 1074 ≤ maxMag := by
      have hm : maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := maxMag_def
      rw [hm]
      exact Nat.le_trans (Nat.mul_le_mul_right _ h) (by decide)
    exact_mod_cast this
  have h0 : (0 : Int) ≤ ((i.natAbs * 2 ^ 1074 : Nat) : Int) := Int.natCast_nonneg _
  simp only [ofIntExact, ofIntRaw, exactCode, FloatFormat.exactCode, fp64_scale, hr]
  split <;> (try split) <;> omega

/-- The code of magnitude `m` (`|x| · 2¹⁰⁷⁴`), negative if `neg`. -/
abbrev signedCode : Bool → Nat → Int := FloatFormat.signedCode

/-- Rounding to a multiple of `2ˢ` moves by at most half of it. -/
theorem roundTo2_err (s n : Nat) (hs : 1 ≤ s) :
    roundTo2 s n ≤ n + 2 ^ (s - 1) ∧ n ≤ roundTo2 s n + 2 ^ (s - 1) := by
  have hP : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hd := Nat.div_add_mod n (2 ^ s)
  have hrl := Nat.mod_lt n (Nat.two_pow_pos s)
  unfold roundTo2
  rw [hP] at hd hrl ⊢
  generalize 2 ^ (s - 1) = G at hd hrl ⊢
  generalize n / (2 * G) = q at hd ⊢
  generalize n % (2 * G) = r at hd hrl ⊢
  have e1 : (q + 1) * (2 * G) = q * (2 * G) + 2 * G := by rw [Nat.add_mul, Nat.one_mul]
  have e2 : 2 * G * q = q * (2 * G) := Nat.mul_comm _ _
  rw [e1]
  split <;> constructor <;> omega

set_option exponentiation.threshold 2100 in
/-- `roundSig` is within half a unit in the last place: `2⁻⁵³`, relatively. -/
theorem roundSig_rel {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 1100) :
    2 ^ 53 * roundSig n ≤ (2 ^ 53 + 1) * n ∧ (2 ^ 53 - 1) * n ≤ 2 ^ 53 * roundSig n := by
  unfold roundSig
  simp only [h, ↓reduceIte]
  rw [bitLen_min h]
  have p53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
  by_cases hs : bitLen 1100 n - 53 = 0
  · rw [hs, show roundTo2 0 n = n by simpa using roundTo2_mul 0 n, p53]
    constructor <;> omega
  · have hb := two_pow_bitLen_le 1100 n (by omega)
    have e : bitLen 1100 n = (bitLen 1100 n - 53 - 1) + 54 := by omega
    rw [e, Nat.pow_add] at hb
    obtain ⟨h1, h2⟩ := roundTo2_err (bitLen 1100 n - 53) n (by omega)
    have e2 : 2 ^ (bitLen 1100 n - 53 - 1) * 2 ^ 54 = 2 * (2 ^ (bitLen 1100 n - 53 - 1) * 2 ^ 53) := by
      rw [show (2 : Nat) ^ 54 = 2 * 2 ^ 53 by decide]; ac_rfl
    rw [show bitLen 1100 n - 53 - 1 = bitLen 1100 n - 53 - 1 from rfl] at h1 h2
    generalize 2 ^ (bitLen 1100 n - 53 - 1) = E at hb h1 h2 e2
    generalize roundTo2 (bitLen 1100 n - 53) n = R at h1 h2 ⊢
    rw [p53] at e2 ⊢
    constructor <;> omega

set_option exponentiation.threshold 2100 in
theorem bitLen_pow {k : Nat} (hk : k < 1100) : bitLen 1100 (2 ^ k) = k + 1 := by
  have h1 := lt_two_pow_bitLen 1100 (2 ^ k) (Nat.pow_lt_pow_right (by decide) hk)
  have h2 := two_pow_bitLen_le 1100 (2 ^ k) (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos k))
  rw [← Nat.pow_succ'] at h2
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h1
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 h2
  omega

set_option exponentiation.threshold 2100 in
theorem roundSig_pow {k : Nat} (hk : k < 1100) : roundSig (2 ^ k) = 2 ^ k := by
  have hC : 2 ^ k < 2 ^ 1100 := Nat.pow_lt_pow_right (by decide) hk
  unfold roundSig
  simp only [hC, ↓reduceIte]
  rw [bitLen_min hC, bitLen_pow hk]
  have e : 2 ^ k = 2 ^ (k - (k + 1 - 53)) * 2 ^ (k + 1 - 53) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e]; exact roundTo2_mul _ _

set_option exponentiation.threshold 2100 in
theorem ofIntExact_rel {i : Int} (h0 : i ≠ 0) (h : i.natAbs ≤ 2 ^ 1023) :
    ∃ M, ofIntExact i = signedCode (decide (i < 0)) M ∧
      2 ^ 53 * M ≤ (2 ^ 53 + 1) * (i.natAbs * 2 ^ 1074) ∧
      (2 ^ 53 - 1) * (i.natAbs * 2 ^ 1074) ≤ 2 ^ 53 * M := by
  have hpos : 0 < i.natAbs := by omega
  have hC : i.natAbs < 2 ^ 1100 := Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) (by decide))
  obtain ⟨r1, r2⟩ := roundSig_rel hpos hC
  -- `2¹⁰²³` is a double: rounding stays at or below it, far from overflow.
  have htop : roundSig i.natAbs ≤ 2 ^ 1023 := by
    have := roundSig_mono h; rwa [roundSig_pow (by decide)] at this
  have hM : roundSig i.natAbs * 2 ^ 1074 ≤ maxMag := by
    have hm : maxMag = (2 ^ 53 - 1) * 2 ^ 2045 := maxMag_def
    have e : (2 : Nat) ^ 1023 * 2 ^ 1074 = 2 ^ 52 * 2 ^ 2045 := by
      simp only [← Nat.pow_add]
    rw [hm]
    refine Nat.le_trans (Nat.mul_le_mul_right _ htop) ?_
    rw [e]; exact Nat.mul_le_mul_right _ (by decide)
  have hMi : ((roundSig i.natAbs * 2 ^ 1074 : Nat) : Int) ≤ maxMag := by exact_mod_cast hM
  have hpos' : 0 < roundSig i.natAbs := by
    have p53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
    rw [p53] at r2; omega
  have hne : roundSig i.natAbs * 2 ^ 1074 ≠ 0 := Nat.mul_ne_zero (by omega) (by
    exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
  refine ⟨roundSig i.natAbs * 2 ^ 1074, ?_, ?_, ?_⟩
  · unfold ofIntExact ofIntRaw signedCode FloatFormat.signedCode
    generalize roundSig i.natAbs * 2 ^ 1074 = M at hMi hne ⊢
    generalize (maxMag : Int) = X at hMi ⊢
    simp only [h0, hne, ↓reduceIte]
    by_cases hn : i < 0 <;> simp only [hn, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true] <;> omega
  · rw [← Nat.mul_assoc, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ r1
  · rw [← Nat.mul_assoc, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ r2

/-- A monotone conversion to finite doubles (`FloatFormat.FiniteMonoConv`). -/
abbrev FiniteMonoConv := fp64.FiniteMonoConv

/-- A conversion of integers to doubles, with what the checker knows of it
(`FloatFormat.IntConv`): exact up to `2⁵³`, within `2⁻⁵³` relatively up to
`2¹⁰²³`. -/
abbrev IntToDouble := fp64.IntConv

set_option exponentiation.threshold 1100 in
/-- `ofIntExact`, behind a constant the kernel does not unfold: proofs about
plans use only the properties above, as they did of the native conversion
before, and type-checking them never computes a rounding. -/
opaque intToDouble : IntToDouble :=
  ⟨⟨ofIntExact, ofIntExact_bounds, ofIntExact_mono⟩, ofIntExact_ne_zero, ofIntExact_exact,
    ofIntExact_rel⟩

/-- An integer as a double (`ofIntExact`). -/
def ofInt (i : Int) : Int := intToDouble.conv i

/-- `CAST(i AS DOUBLE)` as a `FiniteMonoConv`. -/
def intConv : FiniteMonoConv := intToDouble.toFiniteMonoConv

theorem ofInt_bounds (i : Int) : negInf < ofInt i ∧ ofInt i < posInf := intToDouble.bounds i

theorem ofInt_ne_zero {i : Int} (h : i ≠ 0) : ofInt i ≠ 0 := intToDouble.ne_zero h

/-- The conversion of integers to doubles is monotone. -/
theorem ofInt_mono {i j : Int} (h : i ≤ j) : ofInt i ≤ ofInt j := intToDouble.mono h

/-- Integers up to `2⁵³` in magnitude convert exactly. -/
theorem ofInt_exact {i : Int} (h : i.natAbs ≤ 2 ^ 53) : ofInt i = exactCode i := intToDouble.exact h

set_option exponentiation.threshold 1100 in
/-- Integers up to `2¹⁰²³` in magnitude convert within half a unit in the last
place, `|fl(n) − n| ≤ 2⁻⁵³ · |n|` (as magnitudes `· 2¹⁰⁷⁴`). -/
theorem ofInt_rel {i : Int} (h0 : i ≠ 0) (h : i.natAbs ≤ 2 ^ 1023) :
    ∃ M, ofInt i = signedCode (decide (i < 0)) M ∧
      2 ^ 53 * M ≤ (2 ^ 53 + 1) * (i.natAbs * 2 ^ 1074) ∧
      (2 ^ 53 - 1) * (i.natAbs * 2 ^ 1074) ≤ 2 ^ 53 * M := intToDouble.rel h0 h

-- The native conversion agrees, also where it rounds (`2⁵³ + 1` is a tie).
#guard [0, 1, -1, 7, -12345, 2 ^ 53, 2 ^ 53 + 1, 2 ^ 53 + 3, -(2 ^ 53 + 1), 2 ^ 63 - 1,
  -(2 ^ 63), 2 ^ 62 + 2 ^ 9, 2 ^ 62 + 2 ^ 9 + 1, 2 ^ 1100, -(2 ^ 1100)].all fun i =>
    ofInt i == finite (ofFloat (Float.ofInt i))
#guard ofInt (2 ^ 1100) == ofMag false maxMag

/-! ### Scaled values, for the error bounds of #85

`scaled c` is the value of the double with code `c`, times `2¹⁰⁷⁴`: its
magnitude, with its sign. It is monotone in the code, and a code bound
follows from a scaled one (`le_codeHi`, `codeLo_le`), so the checker can do
its interval arithmetic for `SUM` and `AVG` of doubles on integers. -/

def scaled (c : Int) : Int :=
  if c < 0 then -(((c.natAbs - 1) / 2 : Nat) : Int) else (((c.natAbs - 1) / 2 : Nat) : Int)

theorem scaled_mono {c d : Int} (h : c ≤ d) : scaled c ≤ scaled d := by
  unfold scaled
  split <;> split <;> omega

/-- A code with scaled value at most `s` is at most `codeHi s`. -/
def codeHi (s : Int) : Int := 2 * s + 2

/-- A code with scaled value at least `s` is at least `codeLo s`. -/
def codeLo (s : Int) : Int := 2 * s - 2

theorem le_codeHi {c s : Int} (h : scaled c ≤ s) : c ≤ codeHi s := by
  unfold scaled at h; unfold codeHi
  split at h <;> omega

theorem codeLo_le {c s : Int} (h : s ≤ scaled c) : codeLo s ≤ c := by
  unfold scaled at h; unfold codeLo
  split at h <;> omega

/-! ### Trusted: one double operation (#582)

A double `+`, `-`, `*` or `/` of finite doubles whose exact result is well
below the largest double is finite, and within a few `u` of the exact result
of the codes' values. Stated on scaled values, so the checker bounds the
result with integer interval arithmetic (`floatArith` in `Contracts.lean`)
and rules out an overflow to `±∞` from the inputs' bounds (`BinFn.mayInf`).
Proved for IEEE 754 rounding to nearest in `float-bounds/` as `core_add`,
`core_sub`, `core_mul` and `core_div` (`FloatBounds/Arith.lean`), given its
`NativeLink` and the code conversions above (`Decoded`), with `u · tiny`
scaled to `1/2`. Axioms here so that the core needs no Mathlib. -/

/-- A finite double's code. -/
def IsFin (c : Int) : Prop := negInf < c ∧ c < posInf

axiom add_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (lift₂ (· + ·) a b) ∧ (scaled (lift₂ (· + ·) a b) - (scaled a + scaled b)).natAbs ≤
      ((scaled a).natAbs + (scaled b).natAbs) / 2 ^ 50 + 1

axiom sub_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (lift₂ (· - ·) a b) ∧ (scaled (lift₂ (· - ·) a b) - (scaled a - scaled b)).natAbs ≤
      ((scaled a).natAbs + (scaled b).natAbs) / 2 ^ 50 + 1

axiom mul_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs * (scaled b).natAbs ≤ 2 ^ 3171) :
    IsFin (lift₂ (· * ·) a b) ∧
      (2 ^ 1074 * scaled (lift₂ (· * ·) a b) - scaled a * scaled b).natAbs ≤
        (scaled a).natAbs * (scaled b).natAbs / 2 ^ 50 + 2 ^ 1074

axiom div_scaled {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) :
    IsFin (lift₂ (· / ·) a b) ∧
      (scaled (lift₂ (· / ·) a b)).natAbs ≤
        (scaled a).natAbs * (2 ^ 1074 + 2 ^ 1024) / (scaled b).natAbs + 1

/-- Rounding keeps the sign (#441): a sum or product of non-negative finite
doubles, and a quotient of one by a positive one, is non-negative, under the
guards of `add_scaled`, `mul_scaled` and `div_scaled`. Code `0` is `+0.0`, and
`ofFloat` gives it for `-0.0` too, so a code is at least `0` exactly where its
double is. IEEE 754's rounding to nearest is monotone and rounds `0` to `0`
(`StdModel.nonneg`); proved as `core_add_nonneg`, `core_mul_nonneg` and
`core_div_nonneg` in `float-bounds/FloatBounds/Arith.lean`. -/
axiom add_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs + (scaled b).natAbs ≤ 2 ^ 2097) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ lift₂ (· + ·) a b

axiom mul_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs * (scaled b).natAbs ≤ 2 ^ 3171) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    0 ≤ lift₂ (· * ·) a b

axiom div_nonneg {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : scaled b ≠ 0)
    (h : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (scaled b).natAbs) (ha0 : 0 ≤ a) (hb0' : 0 ≤ b) :
    0 ≤ lift₂ (· / ·) a b

/-- `2⁵²`. -/
def tolK : Nat := 2 ^ 52

/-- `⌈a / b⌉`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The error bound of a `SUM` of at most `n` doubles, each at most `Bs`
scaled, scaled and rounded up: `γ n · n · ((1 + 2u) B + 2⁻¹⁰²²) + 2 n u B`
with `u = 2⁻⁵³`, `γ n = n u / (1 − n u)`. Proved as `sumTol_le` in
`float-bounds/FloatBounds/Core.lean` (`docs/float-bounds.md`). -/
def sumTolScaled (n Bs : Nat) : Nat :=
  ceilDiv (n ^ 2 * ((tolK + 1) * Bs + tolK ^ 2)) (tolK * (2 * tolK - n)) + ceilDiv (n * Bs) tolK

/-- The error bound of an `AVG`: `γ (n + 2) · ((1 + 2u) B + 2⁻¹⁰²²) + 2 u B`
(`avgTol_le`). -/
def avgTolScaled (n Bs : Nat) : Nat :=
  ceilDiv ((n + 2) * ((tolK + 1) * Bs + tolK ^ 2)) (tolK * (2 * tolK - (n + 2))) +
    ceilDiv Bs tolK

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
#guard roundTo (-308) (ofFloat 1.5e308) == ofFloat 1.5e308 && roundTo (-308) (ofFloat 5e307) == ofFloat 1e308
#guard roundTo (-308) (ofFloat (-1.5e308)) == ofFloat (-1.5e308) && roundTo (-309) (ofFloat 1.5e308) == 0
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

/-! ### One zero and one NaN: `canon` (#444 step 1b)

`-0.0` and the negative NaN have codes outside `[-∞, NaN]`
(`FloatFormat.negZero`, `negNan`), which the reference never produces. Every
operation here commutes with `canon` on the reference's codes: their results
are reference codes, which `canon` fixes. Operations elsewhere build their
results from `ofFloat`, `ofMag`, `ofInt` or their inputs, so the same holds
of them (`canon_ofFloat`). Negation is the exception the parser already
handles: code negation sends NaN to the negative NaN, and `canon` of it is
the parser's `CASE WHEN x = NaN THEN x ELSE -x END` (`canon_neg`). -/

abbrev negZero : Int := fp64.negZero
abbrev negNan : Int := fp64.negNan
abbrev IsRef : Int → Prop := fp64.IsRef
abbrev canon : Int → Int := fp64.canon

theorem canon_of_isRef {c : Int} (h : IsRef c) : canon c = c := fp64.canon_of_isRef h

theorem canon_idem (c : Int) : canon (canon c) = canon c := fp64.canon_idem c

theorem canon_mono {a b : Int} (h : fp64.key a ≤ fp64.key b) : canon a ≤ canon b := fp64.canon_mono h

theorem isRef_of_bounds {c : Int} (h : negInf < c ∧ c < posInf) : IsRef c :=
  have := fp64.posInf_lt_nan
  ⟨Int.le_of_lt h.1, Int.le_of_lt (Int.lt_trans h.2 this)⟩

theorem isRef_nan : IsRef nan :=
  have := fp64.posInf_lt_nan; have := fp64.negInf_lt_zero; have := fp64.zero_lt_posInf
  ⟨by show fp64.negInf ≤ fp64.nan; omega, Int.le_refl _⟩

/-- A result built from a native double is a reference code. -/
theorem canon_ofFloat (f : Float) : canon (ofFloat f) = ofFloat f := fp64.canon_ofMag _ _

theorem canon_finite (c : Int) : canon (finite c) = finite c := fp64.canon_finite c

theorem canon_of_bounds {c : Int} (h : negInf < c ∧ c < posInf) : canon c = c :=
  canon_of_isRef (isRef_of_bounds h)

theorem lift₂_canon (op : Float → Float → Float) {a b : Int} (ha : IsRef a) (hb : IsRef b) :
    lift₂ op (canon a) (canon b) = canon (lift₂ op a b) := by
  rw [canon_of_isRef ha, canon_of_isRef hb]; exact (canon_ofFloat _).symm

theorem canon_zero : canon 0 = 0 :=
  canon_of_bounds ⟨fp64.negInf_lt_zero, fp64.zero_lt_posInf⟩

theorem roundTo_canon (d : Int) {c : Int} (h : IsRef c) : roundTo d (canon c) = canon (roundTo d c) := by
  rw [canon_of_isRef h]
  unfold roundTo; dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first
    | exact (canon_of_isRef h).symm
    | exact canon_zero.symm
    | exact (canon_ofFloat _).symm

theorem finite_canon {c : Int} (h : IsRef c) : finite (canon c) = canon (finite c) := by
  rw [canon_of_isRef h, canon_finite]

theorem ofIntExact_canon (i : Int) : canon (ofIntExact i) = ofIntExact i :=
  canon_of_bounds (ofIntExact_bounds i)

/-- Code negation commutes with `canon` except at NaN, where `canon` gives
the parser's negation. -/
theorem canon_neg {c : Int} (h : IsRef c) : canon (neg c) = if c = nan then nan else neg c := by
  split
  · rename_i e; subst e; exact fp64.canon_negNan
  · rename_i e
    apply fp64.canon_eq_self
    have := fp64.nan_eq; have := fp64.negNan_eq; have := fp64.negZero_eq
    have h2 : c ≤ fp64.nan := h.2
    have e' : c ≠ fp64.nan := e
    show -c ≠ fp64.negZero ∧ -c ≠ fp64.negNan
    omega

theorem neg_canon {c : Int} (h : IsRef c) : neg (canon c) = neg c := by rw [canon_of_isRef h]

theorem fmod_canon {a b : Int} (ha : IsRef a) (hb : IsRef b) :
    fmod (canon a) (canon b) = canon (fmod a b) := by
  rw [canon_of_isRef ha, canon_of_isRef hb]
  unfold fmod; dsimp only
  split
  · exact (canon_of_isRef isRef_nan).symm
  · split
    · exact (canon_of_isRef ha).symm
    · exact (fp64.canon_ofMag _ _).symm

/-- `CAST(x AS DECIMAL(_, s))` of a double with native floats (the model's is
`toDecimal?`, `SubstraitLean/Conversions.lean`), as the decimal's unscaled integer:
`round(x · 10ˢ)` computed in doubles, halves away from zero, as DuckDB and
DataFusion cast (#27). NaN and ±∞ have none. -/
def toDecimalNative? (c : Int) (s : Nat) : Option Int :=
  let (negative, m) := finiteParts (ofFloat (toFloat c * Float.ofNat (10 ^ s)).round)
  -- A whole double's magnitude is a multiple of 2¹⁰⁷⁴.
  if infMag ≤ m then none else
    let q : Int := (m / 2 ^ 1074 : Nat)
    some (if negative then -q else q)

/-- A decimal's unscaled integer `n` at scale `s` as a double's code with
native floats (the model's is `ofDecimal`, `SubstraitLean/Conversions.lean`),
correctly rounded (#27). A decimal has at most 38 digits, far below `2¹⁰²⁴`,
so `finite` changes nothing and tells the checker the double is finite
(#257). -/
def ofDecimalNative (n : Int) (s : Nat) : Int :=
  let f := Float.ofScientific n.natAbs true s
  finite (ofFloat (if n < 0 then -f else f))

-- The backends' cases: the product rounds in doubles (`-2.675 · 100` is
-- `-267.5`), and `0.145 · 100` is just below `14.5`.
#guard toDecimalNative? (ofFloat 0.125) 2 == some 13 && toDecimalNative? (ofFloat (-2.675)) 2 == some (-268)
#guard toDecimalNative? (ofFloat 0.135) 2 == some 14 && toDecimalNative? (ofFloat 0.145) 2 == some 14
#guard toDecimalNative? (ofFloat 2.5) 0 == some 3 && toDecimalNative? (ofFloat (-2.5)) 0 == some (-3)
#guard toDecimalNative? (ofFloat 1e20) 2 == some (10 ^ 22) && toDecimalNative? nan 2 == none
#guard toDecimalNative? posInf 0 == none && toDecimalNative? 0 3 == some 0
#guard ofDecimalNative 1234 2 == ofFloat 12.34 && ofDecimalNative (-5) 2 == ofFloat (-0.05)
#guard ofDecimalNative 145 3 == ofFloat 0.145 && ofDecimalNative 0 5 == 0
-- Correctly rounded where `n` itself is not a double: 2⁵³ + 1 is a tie.
#guard ofDecimalNative 9007199254740993 0 == ofFloat 9007199254740992.0
#guard ofDecimalNative 99999999999999999999 2 == ofFloat 999999999999999999.99

theorem canon_ofInt (i : Int) : canon (ofInt i) = ofInt i := canon_of_bounds (ofInt_bounds i)

theorem canon_ofDecimalNative (n : Int) (s : Nat) : canon (ofDecimalNative n s) = ofDecimalNative n s :=
  canon_finite _

#guard canon negZero == 0 && canon negNan == nan && canon (neg nan) == nan
#guard canon posInf == posInf && canon negInf == negInf && canon (ofFloat (-1.5)) == ofFloat (-1.5)
#guard fp64.key negZero < fp64.key 0 && fp64.key (ofFloat (-5e-324)) < fp64.key negZero
#guard fp64.key posInf < fp64.key negNan && fp64.key negNan < fp64.key nan

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
