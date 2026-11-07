import SubstraitLean.Float
import SubstraitLean.Value

/-!
# Correctly rounded sums of doubles (D25, #914)

Every finite double is an integer multiple of `2⁻¹⁰⁷⁴`: its code's scaled
value (`FloatCode.scaled`, here `FloatCode.exact`) is that integer. So the
sum of any list of doubles is an exact integer in the same unit, in any
order. `floatSumCR` rounds that exact sum once, to the nearest double with
ties to even (`FloatCode.ofExact`), and `floatAvgCR` rounds the exact sum
divided by the count once (`FloatCode.ofExactDiv`). NaN and the infinities
follow IEEE 754: a NaN, or `+∞` with `-∞`, gives NaN, and one kind of
infinity gives it.

The value depends on the multiset of values only (`floatSumCR_perm`), and
everything here is integer arithmetic, with no native `Float` and no axiom.
The bounds the contract checker assumes of the sequential sum
(`floatSum_mem`, `floatAvg_mem` and `floatSum_sign` in `Aggregate.lean`)
are theorems of it (`floatSumCR_mem`, `floatAvgCR_mem`, `floatSumCR_sign`).
How far an engine's own order of additions may be from it is
`epsilon_sum_cr` in `float-bounds/`.

A double's magnitude in units of `2⁻¹⁰⁷⁴` has at most 53 significant bits:
`k · 2ᵍ` with `k < 2⁵³`. Below `2⁵³` every integer is one (the subnormals and
the smallest binade), so the grid is `1` there and `2ᵍ` in the binade
`[2⁵²⁺ᵍ, 2⁵³⁺ᵍ)`. A magnitude above the largest double after rounding is
`±∞`, as IEEE 754 rounds an overflow to nearest.
-/

namespace Substrait.FloatCode

/-- The exact value of a finite double's code, in units of `2⁻¹⁰⁷⁴`: `0` for
`0`, `±m` for `±(2m + 1)`. It is `scaled`. -/
abbrev exact (c : Int) : Int := scaled c

/-- `a / d` rounded to the nearest integer, ties to even. -/
def rndDiv (a d : Nat) : Nat :=
  if d < 2 * (a % d) ∨ (2 * (a % d) = d ∧ a / d % 2 = 1) then a / d + 1 else a / d

/-- The exponent of the grid of doubles at the magnitude `a / n`: the bits of
`⌊a / n⌋` past 53, or `0` below `2⁵³`. -/
def gridExp (a n : Nat) : Nat := (a / n).log2 - 52

/-- The magnitude `a / n` rounded to the nearest multiple of its grid, ties
to even: to 53 significant bits, with no bound on the exponent. -/
def roundMagDiv (a n : Nat) : Nat := rndDiv a (n * 2 ^ gridExp a n) * 2 ^ gridExp a n

/-- The non-negative code of a rounded magnitude: `+∞` past the largest
double. -/
def posCode (m : Nat) : Int := if maxMag < m then posInf else if m = 0 then 0 else 2 * m + 1

/-- The code of the double nearest to `v / n · 2⁻¹⁰⁷⁴`, ties to even, `±∞`
past the largest double. -/
def ofExactDiv (v : Int) (n : Nat) : Int :=
  if v < 0 then -posCode (roundMagDiv v.natAbs n) else posCode (roundMagDiv v.natAbs n)

/-- The code of the double nearest to `v · 2⁻¹⁰⁷⁴`, ties to even, `±∞` past
the largest double. -/
def ofExact (v : Int) : Int := ofExactDiv v 1

/-- The unit in the last place at `v / n`, in units of `2⁻¹⁰⁷⁴`: rounding
moves by at most half of it (`ofExactDiv_within`). -/
def ulpDiv (v : Int) (n : Nat) : Nat := 2 ^ gridExp v.natAbs n

theorem ofExactDiv_one (v : Int) : ofExactDiv v 1 = ofExact v := rfl

/-! ### Rounding a quotient to an integer -/

theorem rndDiv_ge (a d : Nat) : a / d ≤ rndDiv a d := by
  unfold rndDiv; split <;> omega

theorem rndDiv_le (a d : Nat) : rndDiv a d ≤ a / d + 1 := by
  unfold rndDiv; split <;> omega

theorem rndDiv_zero (d : Nat) : rndDiv 0 d = 0 := by
  simp [rndDiv]

theorem rndDiv_mul (k : Nat) {d : Nat} (hd : 0 < d) : rndDiv (k * d) d = k := by
  have h1 : k * d % d = 0 := Nat.mul_mod_left _ _
  have h2 : k * d / d = k := Nat.mul_div_cancel _ hd
  unfold rndDiv; rw [h1, h2]; split <;> omega

theorem rndDiv_mono {a a' d : Nat} (_hd : 0 < d) (h : a ≤ a') : rndDiv a d ≤ rndDiv a' d := by
  have hq : a / d ≤ a' / d := Nat.div_le_div_right h
  rcases Nat.lt_or_eq_of_le hq with hlt | heq
  · have := rndDiv_le a d; have := rndDiv_ge a' d; omega
  · have hd1 := Nat.div_add_mod a d
    have hd2 := Nat.div_add_mod a' d
    have hr : a % d ≤ a' % d := by
      rw [heq] at hd1
      omega
    unfold rndDiv; rw [heq]
    split <;> split <;> omega

/-- Rounding stays at or below a multiple of `d` that `a` does not pass. -/
theorem rndDiv_le_of {a d K : Nat} (hd : 0 < d) (h : a ≤ K * d) : rndDiv a d ≤ K := by
  have hq : a / d ≤ K := by
    have := Nat.div_le_div_right (c := d) h
    rwa [Nat.mul_div_cancel _ hd] at this
  rcases Nat.lt_or_eq_of_le hq with hlt | heq
  · have := rndDiv_le a d; omega
  · have hd1 := Nat.div_add_mod a d
    rw [heq] at hd1
    have hm : a % d = 0 := by
      have : K * d = d * K := Nat.mul_comm _ _
      omega
    unfold rndDiv; rw [hm, heq]; split <;> omega

/-- Rounding to the nearest multiple of `d` moves by at most `d / 2`. -/
theorem rndDiv_err (a : Nat) {d : Nat} (hd : 0 < d) :
    2 * (((rndDiv a d * d : Nat) : Int) - (a : Int)).natAbs ≤ d := by
  have hd1 := Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  have hm : d * (a / d) = a / d * d := Nat.mul_comm _ _
  unfold rndDiv; split
  · have : (a / d + 1) * d = a / d * d + d := Nat.succ_mul _ _
    rw [this]; omega
  · omega

/-! ### The grid -/

theorem log2_mono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · subst ha; simp [Nat.log2_zero]
  · exact (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le ha) h)

theorem gridExp_mono {a a' : Nat} (n : Nat) (h : a ≤ a') : gridExp a n ≤ gridExp a' n := by
  have := log2_mono (Nat.div_le_div_right (c := n) h)
  unfold gridExp; omega

/-- A positive grid exponent `g` puts the magnitude at `2⁵²⁺ᵍ` or above. -/
theorem le_of_gridExp {a n : Nat} (hg : 0 < gridExp a n) :
    2 ^ (gridExp a n + 52) ≤ a / n := by
  unfold gridExp at hg ⊢
  have h0 : a / n ≠ 0 := by intro h; rw [h, Nat.log2_zero] at hg; omega
  have := Nat.log2_self_le h0
  rwa [show (a / n).log2 - 52 + 52 = (a / n).log2 by omega]

/-- The magnitude is below `2⁵³⁺ᵍ`. -/
theorem lt_of_gridExp (a n : Nat) : a / n < 2 ^ (gridExp a n + 53) := by
  have h := @Nat.lt_log2_self (a / n)
  unfold gridExp
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))

theorem roundMagDiv_mono {a a' n : Nat} (hn : 0 < n) (h : a ≤ a') :
    roundMagDiv a n ≤ roundMagDiv a' n := by
  have hs := gridExp_mono n h
  have hlo0 := lt_of_gridExp a n
  unfold roundMagDiv
  generalize hg : gridExp a n = g at hs hlo0 ⊢
  generalize hg' : gridExp a' n = g' at hs ⊢
  rcases Nat.lt_or_eq_of_le hs with hlt | heq
  · -- `a` lies below `2⁵²⁺ᵍ'`, a multiple of both grids, and `a'` at or above it.
    have hP : 0 < 2 ^ g := Nat.two_pow_pos g
    have hP' : 0 < 2 ^ g' := Nat.two_pow_pos g'
    have hlo : a / n < 2 ^ (g' + 52) :=
      Nat.lt_of_lt_of_le hlo0 (Nat.pow_le_pow_right (by omega) (by omega))
    have hhi : 2 ^ (g' + 52) ≤ a' / n := by
      have := le_of_gridExp (a := a') (n := n) (by omega)
      rwa [hg'] at this
    have hpow : 2 ^ (g' + 52) = 2 ^ (g' + 52 - g) * 2 ^ g := by
      rw [← Nat.pow_add]; congr 1; omega
    have left : rndDiv a (n * 2 ^ g) * 2 ^ g ≤ 2 ^ (g' + 52) := by
      have ha : a ≤ 2 ^ (g' + 52 - g) * (n * 2 ^ g) := by
        have := (Nat.div_lt_iff_lt_mul hn).1 hlo
        rw [hpow] at this
        have e : 2 ^ (g' + 52 - g) * 2 ^ g * n = 2 ^ (g' + 52 - g) * (n * 2 ^ g) := by
          rw [Nat.mul_assoc, Nat.mul_comm (2 ^ g) n]
        omega
      have := rndDiv_le_of (Nat.mul_pos hn hP) ha
      rw [hpow]; exact Nat.mul_le_mul_right _ this
    have right : 2 ^ (g' + 52) ≤ rndDiv a' (n * 2 ^ g') * 2 ^ g' := by
      have hq : 2 ^ 52 ≤ a' / (n * 2 ^ g') := by
        rw [← Nat.div_div_eq_div_mul]
        apply (Nat.le_div_iff_mul_le hP').2
        rw [← Nat.pow_add, Nat.add_comm]; exact hhi
      have := Nat.le_trans hq (rndDiv_ge a' (n * 2 ^ g'))
      rw [Nat.pow_add, Nat.mul_comm (2 ^ g')]
      exact Nat.mul_le_mul_right _ this
    omega
  · subst heq
    exact Nat.mul_le_mul_right _ (rndDiv_mono (Nat.mul_pos hn (Nat.two_pow_pos _)) h)

theorem roundMagDiv_zero (n : Nat) : roundMagDiv 0 n = 0 := by
  simp [roundMagDiv, rndDiv_zero]

/-- A magnitude of at most 53 significant bits is its own rounding. -/
theorem roundMagDiv_exact {k s : Nat} (hk : k < 2 ^ 53) : roundMagDiv (k * 2 ^ s) 1 = k * 2 ^ s := by
  unfold roundMagDiv
  rw [Nat.one_mul]
  by_cases hg : gridExp (k * 2 ^ s) 1 ≤ s
  · generalize gridExp (k * 2 ^ s) 1 = g at hg ⊢
    have e : k * 2 ^ s = k * 2 ^ (s - g) * 2 ^ g := by
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [e, rndDiv_mul _ (Nat.two_pow_pos g)]
  · -- A grid coarser than `2ˢ` would put the magnitude at `2⁵³⁺ˢ` or above.
    exfalso
    have h1 := le_of_gridExp (a := k * 2 ^ s) (n := 1) (by omega)
    rw [Nat.div_one] at h1
    have h2 : k * 2 ^ s < 2 ^ 53 * 2 ^ s := Nat.mul_lt_mul_of_pos_right hk (Nat.two_pow_pos s)
    rw [← Nat.pow_add] at h2
    have h3 : 2 ^ (53 + s) ≤ 2 ^ (gridExp (k * 2 ^ s) 1 + 52) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-! ### Codes -/

theorem posCode_mono {m m' : Nat} (h : m ≤ m') : posCode m ≤ posCode m' := by
  have := posInf_eq
  unfold posCode; split <;> split <;> (try split) <;> (try split) <;> omega

theorem posCode_nonneg (m : Nat) : 0 ≤ posCode m := by
  have := posInf_eq
  unfold posCode; split
  · omega
  · split <;> omega

theorem ofExactDiv_mono {v w : Int} {n : Nat} (hn : 0 < n) (h : v ≤ w) :
    ofExactDiv v n ≤ ofExactDiv w n := by
  unfold ofExactDiv
  have h1 := posCode_nonneg (roundMagDiv v.natAbs n)
  have h2 := posCode_nonneg (roundMagDiv w.natAbs n)
  split <;> split
  · have := posCode_mono (roundMagDiv_mono hn (show w.natAbs ≤ v.natAbs by omega)); omega
  · omega
  · omega
  · exact posCode_mono (roundMagDiv_mono hn (by omega))

theorem ofExactDiv_nonneg {v : Int} (n : Nat) (h : 0 ≤ v) : 0 ≤ ofExactDiv v n := by
  unfold ofExactDiv; simp only [show ¬ v < 0 by omega, ↓reduceIte]; exact posCode_nonneg _

theorem ofExactDiv_nonpos {v : Int} (n : Nat) (h : v ≤ 0) : ofExactDiv v n ≤ 0 := by
  unfold ofExactDiv; split
  · have := posCode_nonneg (roundMagDiv v.natAbs n); omega
  · have hv : v = 0 := by omega
    subst hv; simp [roundMagDiv_zero, posCode]

theorem ofExactDiv_neg (v : Int) (n : Nat) : ofExactDiv (-v) n = -ofExactDiv v n := by
  unfold ofExactDiv
  rw [Int.natAbs_neg]
  by_cases hv : v = 0
  · subst hv; simp [roundMagDiv_zero, posCode]
  · split <;> split <;> omega

theorem ofExact_mono {v w : Int} (h : v ≤ w) : ofExact v ≤ ofExact w := ofExactDiv_mono (by omega) h

theorem ofExact_nonneg {v : Int} (h : 0 ≤ v) : 0 ≤ ofExact v := ofExactDiv_nonneg 1 h

theorem ofExact_neg (v : Int) : ofExact (-v) = -ofExact v := ofExactDiv_neg v 1

theorem posCode_of_le {m : Nat} (h : m ≤ maxMag) :
    posCode m = if m = 0 then (0 : Int) else 2 * (m : Int) + 1 := by
  simp only [posCode, Nat.not_lt.2 h, ↓reduceIte]

theorem scaled_posCode {m : Nat} (h : m ≤ maxMag) : scaled (posCode m) = m := by
  rw [posCode_of_le h]
  by_cases h0 : m = 0
  · subst h0; rfl
  · simp only [h0, ite_false]; unfold scaled; split <;> omega

theorem scaled_neg_posCode {m : Nat} (h : m ≤ maxMag) : scaled (-posCode m) = -(m : Int) := by
  rw [posCode_of_le h]
  by_cases h0 : m = 0
  · subst h0; rfl
  · simp only [h0, ite_false]; unfold scaled; split <;> omega

set_option exponentiation.threshold 2100 in
/-- `2ᵏ` is at most the largest double's magnitude for `k ≤ 2097`. -/
theorem pow_le_maxMag {k : Nat} (hk : k ≤ 2097) : 2 ^ k ≤ maxMag := by
  rw [maxMag_def]
  calc 2 ^ k ≤ 2 ^ 2097 := Nat.pow_le_pow_right (by omega) hk
    _ = 2 ^ 52 * 2 ^ 2045 := by rw [← Nat.pow_add]
    _ ≤ (2 ^ 53 - 1) * 2 ^ 2045 := Nat.mul_le_mul_right _ (by omega)

/-- Below `+∞`, a magnitude's code is `posCode`'s, with its sign. -/
theorem ofMag_eq (neg : Bool) {m : Nat} (hm : m ≤ maxMag) :
    ofMag neg m = if neg then -posCode m else posCode m := by
  have hn : nanMag = maxMag + 2 := rfl
  have hne : m ≠ nanMag := by omega
  simp only [ofMag, FloatFormat.ofMag, posCode, show ¬ maxMag < m by omega, ↓reduceIte]
  cases neg <;> by_cases h0 : m = 0 <;> simp_all

/-- A double rounds to itself (`ofExact_exact`): every finite double's
magnitude is `k · 2ˢ` with `k < 2⁵³`. -/
theorem ofExact_exact (neg : Bool) {k s : Nat} (hk : k < 2 ^ 53) (hm : k * 2 ^ s ≤ maxMag) :
    ofExact (exact (ofMag neg (k * 2 ^ s))) = ofMag neg (k * 2 ^ s) := by
  have hpos : ofExact ((k * 2 ^ s : Nat) : Int) = posCode (k * 2 ^ s) := by
    simp only [ofExact, ofExactDiv, Int.natAbs_natCast, roundMagDiv_exact hk,
      show ¬ ((k * 2 ^ s : Nat) : Int) < 0 by omega, ↓reduceIte]
  rw [ofMag_eq neg hm]
  cases neg
  · simp only [Bool.false_eq_true, ite_false, exact, scaled_posCode hm, hpos]
  · simp only [ite_true, exact, scaled_neg_posCode hm, ofExact_neg, hpos]

/-- A finite result is within half an ulp: `|v / n − r| ≤ ulp / 2`, times `2n`. -/
theorem ofExactDiv_within {v : Int} {n : Nat} (hn : 0 < n) (hf : IsFin (ofExactDiv v n)) :
    2 * ((n : Int) * scaled (ofExactDiv v n) - v).natAbs ≤ n * ulpDiv v n := by
  have hm : roundMagDiv v.natAbs n ≤ maxMag := by
    have := posInf_eq; have := negInf_eq
    apply Classical.byContradiction; intro hlt
    unfold IsFin ofExactDiv posCode at hf
    simp only [show maxMag < roundMagDiv v.natAbs n by omega, ↓reduceIte] at hf
    split at hf <;> omega
  have herr := rndDiv_err v.natAbs (Nat.mul_pos hn (Nat.two_pow_pos (gridExp v.natAbs n)))
  unfold ofExactDiv ulpDiv
  unfold roundMagDiv at hm ⊢
  generalize rndDiv v.natAbs (n * 2 ^ gridExp v.natAbs n) = r at hm herr ⊢
  generalize 2 ^ gridExp v.natAbs n = P at hm herr ⊢
  have key : ((r * (n * P) : Nat) : Int) = (n : Int) * ((r * P : Nat) : Int) := by
    push_cast; exact Int.mul_left_comm _ _ _
  rw [key] at herr
  split
  · rw [scaled_neg_posCode hm, Int.mul_neg]; omega
  · rw [scaled_posCode hm]; omega

/-- The ulp is at most `2⁻⁵²` of the magnitude, or `1` below `2⁵³`. -/
theorem ulpDiv_le (v : Int) {n : Nat} (_hn : 0 < n) :
    n * 2 ^ 52 * ulpDiv v n ≤ max v.natAbs (n * 2 ^ 52) := by
  unfold ulpDiv
  by_cases hg : gridExp v.natAbs n = 0
  · rw [hg]; omega
  · have h := le_of_gridExp (a := v.natAbs) (n := n) (by omega)
    have h2 : n * (v.natAbs / n) ≤ v.natAbs := Nat.mul_div_le _ _
    have h3 := Nat.mul_le_mul_left n h
    rw [Nat.pow_add] at h3
    have : n * 2 ^ 52 * 2 ^ gridExp v.natAbs n = n * (2 ^ gridExp v.natAbs n * 2 ^ 52) := by
      rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 52)]
    omega

theorem ulpDiv_pos (v : Int) (n : Nat) : 0 < ulpDiv v n := Nat.two_pow_pos _

set_option exponentiation.threshold 2100 in
/-- A quotient up to `2²⁰⁹⁷` rounds to a finite double. -/
theorem ofExactDiv_fin {v : Int} {n : Nat} (hn : 0 < n) (h : v.natAbs ≤ n * 2 ^ 2097) :
    IsFin (ofExactDiv v n) := by
  have hmax : 2 ^ 2097 ≤ maxMag := pow_le_maxMag (Nat.le_refl _)
  have hq : v.natAbs / n ≤ 2 ^ 2097 := by
    have := Nat.div_le_div_right (c := n) h
    rwa [Nat.mul_comm, Nat.mul_div_cancel _ hn] at this
  have hg : gridExp v.natAbs n ≤ 2045 := by
    unfold gridExp
    by_cases h0 : v.natAbs / n = 0
    · rw [h0, Nat.log2_zero]; omega
    · have hlt : v.natAbs / n < 2 ^ 2098 :=
        Nat.lt_of_le_of_lt hq (Nat.pow_lt_pow_right (by decide) (by decide))
      have := (Nat.log2_lt (k := 2098) h0).2 hlt
      omega
  have hr : roundMagDiv v.natAbs n ≤ 2 ^ 2097 := by
    unfold roundMagDiv
    generalize gridExp v.natAbs n = g at hg ⊢
    have hpow : 2 ^ 2097 = 2 ^ (2097 - g) * 2 ^ g := by rw [← Nat.pow_add]; congr 1; omega
    have ha : v.natAbs ≤ 2 ^ (2097 - g) * (n * 2 ^ g) := by
      have e : 2 ^ (2097 - g) * (n * 2 ^ g) = n * 2 ^ 2097 := by
        rw [hpow, Nat.mul_left_comm]
      rw [e]; exact h
    have := rndDiv_le_of (Nat.mul_pos hn (Nat.two_pow_pos g)) ha
    rw [hpow]; exact Nat.mul_le_mul_right _ this
  have := posInf_eq; have := negInf_eq
  unfold IsFin ofExactDiv posCode
  simp only [show ¬ maxMag < roundMagDiv v.natAbs n by omega, ↓reduceIte]
  split <;> split <;> omega

set_option exponentiation.threshold 2100 in
/-- The correctly rounded sum is within `u = 2⁻⁵³` of the exact sum,
relatively: the standard model's bound (`StdModel` in `float-bounds/`) with
no underflow term, since below `2⁵³` the sum is exact. `epsilon_sum_cr`
(`float-bounds/FloatBounds/Epsilon.lean`) takes this as its hypothesis on the
reference's value. -/
theorem ofExact_rel {S : Int} (h : S.natAbs ≤ 2 ^ 2097) :
    IsFin (ofExact S) ∧ 2 ^ 53 * (scaled (ofExact S) - S).natAbs ≤ S.natAbs := by
  have hfin := ofExactDiv_fin (v := S) (n := 1) (by omega) (by omega)
  have hw := ofExactDiv_within (v := S) (n := 1) (by omega) hfin
  have hu := ulpDiv_le S (n := 1) (by omega)
  rw [ofExactDiv_one] at hw hfin
  simp only [Int.natCast_one, Int.one_mul, Nat.one_mul] at hw hu
  exact ⟨hfin, by omega⟩

end Substrait.FloatCode

namespace Substrait

open FloatCode

/-! ### Sums of values -/

/-- The exact sum of the doubles among `vs`, in units of `2⁻¹⁰⁷⁴`. -/
def exactSum : List Value → Int
  | [] => 0
  | .float c :: vs => exact c + exactSum vs
  | _ :: vs => exactSum vs

/-- Does a code among `vs` satisfy `p`? -/
def anyCode (p : Int → Bool) (vs : List Value) : Bool :=
  vs.any fun | .float c => p c | _ => false

/-- NaN, `+∞` or `-∞` for a list with a non-finite double, as IEEE 754 adds
them: a NaN, or both infinities, give NaN. A code below `-∞` (no value of the
reference has one) counts as `-∞`. -/
def nonFinite (vs : List Value) : Option Int :=
  if anyCode (fun c => decide (nan ≤ c)) vs ||
      (anyCode (fun c => decide (posInf ≤ c ∧ c < nan)) vs && anyCode (fun c => decide (c ≤ negInf)) vs)
    then some nan
  else if anyCode (fun c => decide (posInf ≤ c ∧ c < nan)) vs then some posInf
  else if anyCode (fun c => decide (c ≤ negInf)) vs then some negInf
  else none

/-- `SUM` of the doubles among `vs` (D25): the exact sum, rounded once. -/
def floatSumCR (vs : List Value) : Int := (nonFinite vs).getD (ofExact (exactSum vs))

/-- `AVG` of the doubles `vs` (D25): the exact sum divided by the count,
rounded once. -/
def floatAvgCR (vs : List Value) : Int := (nonFinite vs).getD (ofExactDiv (exactSum vs) vs.length)

theorem exactSum_perm {vs ws : List Value} (h : vs.Perm ws) : exactSum vs = exactSum ws := by
  induction h with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [exactSum, ih]
  | swap x y l => cases x <;> cases y <;> simp [exactSum] <;> omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem nonFinite_perm {vs ws : List Value} (h : vs.Perm ws) : nonFinite vs = nonFinite ws := by
  have e : ∀ p, anyCode p vs = anyCode p ws := fun _ => h.any_eq
  simp only [nonFinite, e]

/-- The point of D25: a `SUM` of doubles is a function of the multiset of
values. -/
theorem floatSumCR_perm {vs ws : List Value} (h : vs.Perm ws) : floatSumCR vs = floatSumCR ws := by
  simp only [floatSumCR, nonFinite_perm h, exactSum_perm h]

theorem floatAvgCR_perm {vs ws : List Value} (h : vs.Perm ws) : floatAvgCR vs = floatAvgCR ws := by
  simp only [floatAvgCR, nonFinite_perm h, exactSum_perm h, h.length_eq]

theorem nan_eq : nan = 2 * maxMag + 5 := fp64.nan_eq

theorem anyCode_map_false {cs : List Int} {p : Int → Bool} (h : ∀ c ∈ cs, p c = false) :
    anyCode p (cs.map .float) = false := by
  simp only [anyCode, List.any_map, List.any_eq_false]
  intro c hc; simp [h c hc]

/-- What `nonFinite` gives, and what it needs: `-∞` a code at or below `-∞`,
NaN or `+∞` a code at or above `+∞`. -/
theorem nonFinite_cases (vs : List Value) :
    nonFinite vs = none ∨
      (nonFinite vs = some negInf ∧ anyCode (fun c => decide (c ≤ negInf)) vs = true) ∨
      ((nonFinite vs = some nan ∨ nonFinite vs = some posInf) ∧
        anyCode (fun c => decide (posInf ≤ c)) vs = true) := by
  have hmono : ∀ p : Int → Bool, (∀ c, p c = true → posInf ≤ c) → anyCode p vs = true →
      anyCode (fun c => decide (posInf ≤ c)) vs = true := fun p hp h => by
    simp only [anyCode, List.any_eq_true] at h ⊢
    obtain ⟨x, hx, hpx⟩ := h
    refine ⟨x, hx, ?_⟩
    cases x <;> simp_all
  have h1 := hmono (fun c => decide (nan ≤ c)) (fun c h => by
    simp at h; have := nan_eq; have := posInf_eq; omega)
  have h2 := hmono (fun c => decide (posInf ≤ c ∧ c < nan)) (fun c h => by simp at h; omega)
  unfold nonFinite
  revert h1 h2
  generalize anyCode (fun c => decide (nan ≤ c)) vs = a
  generalize anyCode (fun c => decide (posInf ≤ c ∧ c < nan)) vs = b
  generalize anyCode (fun c => decide (c ≤ negInf)) vs = d
  cases a <;> cases b <;> cases d <;> simp <;> intro h <;> simp [h]

theorem nonFinite_of_fin {cs : List Int} (h : ∀ c ∈ cs, IsFin c) : nonFinite (cs.map .float) = none := by
  have := nan_eq; have := posInf_eq; have := negInf_eq
  simp only [nonFinite]
  rw [anyCode_map_false (fun c hc => by have := h c hc; unfold IsFin at this; simp; omega),
    anyCode_map_false (fun c hc => by have := h c hc; unfold IsFin at this; simp; omega),
    anyCode_map_false (fun c hc => by have := h c hc; unfold IsFin at this; simp; omega)]
  rfl

/-- `k · lo ≤ Σ ≤ k · hi` for `k` values in `[lo, hi]`. -/
theorem exactSum_bounds {cs : List Int} {lo hi : Int}
    (hb : ∀ c ∈ cs, lo ≤ scaled c ∧ scaled c ≤ hi) :
    cs.length * lo ≤ exactSum (cs.map .float) ∧ exactSum (cs.map .float) ≤ cs.length * hi := by
  induction cs with
  | nil => simp [exactSum]
  | cons c cs ih =>
    have ⟨h1, h2⟩ := hb c (List.mem_cons_self ..)
    have ⟨i1, i2⟩ := ih fun x hx => hb x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, exactSum, List.length_cons, exact]
    push_cast
    rw [Int.add_mul, Int.add_mul]
    omega

theorem exactSum_nonneg {cs : List Int} (h : ∀ c ∈ cs, 0 ≤ c) : 0 ≤ exactSum (cs.map .float) := by
  induction cs with
  | nil => simp [exactSum]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, exactSum, exact, scaled]
    split <;> omega

theorem exactSum_nonpos {cs : List Int} (h : ∀ c ∈ cs, c ≤ 0) : exactSum (cs.map .float) ≤ 0 := by
  induction cs with
  | nil => simp [exactSum]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, exactSum, exact, scaled]
    split <;> omega

/-- `⌈a / 2⁵²⌉` is at least `⌊a / 2⁵²⌋`. -/
theorem ceilDiv_ge (a : Nat) (_ : Unit) : a / 2 ^ 52 ≤ ceilDiv a tolK :=
  Nat.div_le_div_right (show a ≤ a + 2 ^ 52 - 1 by omega)

set_option exponentiation.threshold 2100 in
/-- A value with scaled magnitude at most `2¹⁴⁷⁴` is finite. -/
theorem isFin_of_scaled {c : Int} (h : (scaled c).natAbs ≤ 2 ^ 1474) : IsFin c := by
  have hm : 2 ^ 1474 < maxMag :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) (by omega : 1474 < 1475)) (pow_le_maxMag (by omega))
  have := posInf_eq; have := negInf_eq
  unfold scaled at h; unfold IsFin
  split at h <;> omega

set_option exponentiation.threshold 2100 in
/-- The bounds of a `SUM` of doubles that the contract checker uses, as
`floatSum_mem` (`Aggregate.lean`) states them of the sequential sum, with
half an ulp in place of the order's error. -/
theorem floatSumCR_mem {cs : List Int} {N : Nat} {lo hi : Int} (hne : cs ≠ []) (hN : cs.length ≤ N)
    (h32 : N ≤ 2 ^ 32) (hlo : lo.natAbs ≤ 2 ^ 1474) (hhi : hi.natAbs ≤ 2 ^ 1474)
    (hb : ∀ c ∈ cs, lo ≤ scaled c ∧ scaled c ≤ hi) :
    min lo (N * lo) - sumTolScaled N (max lo.natAbs hi.natAbs)
        ≤ scaled (floatSumCR (cs.map .float)) ∧
      scaled (floatSumCR (cs.map .float))
        ≤ max hi (N * hi) + sumTolScaled N (max lo.natAbs hi.natAbs) := by
  have hfin : ∀ c ∈ cs, IsFin c := fun c hc => isFin_of_scaled (by have := hb c hc; omega)
  have hk : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  simp only [floatSumCR, nonFinite_of_fin hfin, Option.getD_none]
  have ⟨s1, s2⟩ := exactSum_bounds hb
  generalize exactSum (cs.map .float) = S at s1 s2 ⊢
  generalize hB : max lo.natAbs hi.natAbs = B
  generalize cs.length = k at hk hN s1 s2
  have hcast : ((N * B : Nat) : Int) = (N : Int) * (B : Int) := Int.natCast_mul _ _
  have hkB : (k : Int) * hi ≤ N * B ∧ -((N : Int) * B) ≤ k * lo := by
    have m1 := Int.mul_le_mul_of_nonneg_left (show hi ≤ (B : Int) by omega) (Int.natCast_nonneg k)
    have m2 := Int.mul_le_mul_of_nonneg_left (show -(B : Int) ≤ lo by omega) (Int.natCast_nonneg k)
    have m3 := Int.mul_le_mul_of_nonneg_right (show (k : Int) ≤ N by omega) (Int.natCast_nonneg B)
    rw [Int.mul_neg] at m2
    omega
  have hmin : min lo (N * lo) ≤ k * lo := by
    by_cases h0 : 0 ≤ lo
    · have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ k by omega) h0; omega
    · have := Int.mul_le_mul_of_nonpos_right (show (k : Int) ≤ N by omega) (by omega : lo ≤ 0); omega
  have hmax : k * hi ≤ max hi (N * hi) := by
    by_cases h0 : 0 ≤ hi
    · have := Int.mul_le_mul_of_nonneg_right (show (k : Int) ≤ N by omega) h0; omega
    · have := Int.mul_le_mul_of_nonpos_right (show (1 : Int) ≤ k by omega) (by omega : hi ≤ 0); omega
  have hNB : N * B ≤ 2 ^ 2097 := by
    have : N * B ≤ 2 ^ 32 * 2 ^ 1474 := Nat.mul_le_mul h32 (by omega)
    rw [← Nat.pow_add] at this
    exact Nat.le_trans this (Nat.pow_le_pow_right (by omega) (by omega))
  have hfin' := ofExactDiv_fin (v := S) (n := 1) (by omega) (by omega)
  have hw := ofExactDiv_within (v := S) (n := 1) (by omega) hfin'
  have hu := ulpDiv_le S (n := 1) (by omega)
  rw [ofExactDiv_one] at hw
  have htol : (N * B) / 2 ^ 52 ≤ sumTolScaled N B :=
    Nat.le_trans (ceilDiv_ge _ ()) (Nat.le_add_left _ _)
  simp only [Int.natCast_one, Int.one_mul, Nat.one_mul] at hw hu
  constructor <;> omega

set_option exponentiation.threshold 2100 in
/-- The bounds of an `AVG` of doubles, as `floatAvg_mem` states them. -/
theorem floatAvgCR_mem {cs : List Int} {N : Nat} {lo hi : Int} (hne : cs ≠ []) (hN : cs.length ≤ N)
    (_h32 : N ≤ 2 ^ 32) (hlo : lo.natAbs ≤ 2 ^ 1474) (hhi : hi.natAbs ≤ 2 ^ 1474)
    (hb : ∀ c ∈ cs, lo ≤ scaled c ∧ scaled c ≤ hi) :
    lo - avgTolScaled N (max lo.natAbs hi.natAbs) ≤ scaled (floatAvgCR (cs.map .float)) ∧
      scaled (floatAvgCR (cs.map .float)) ≤ hi + avgTolScaled N (max lo.natAbs hi.natAbs) := by
  have hfin : ∀ c ∈ cs, IsFin c := fun c hc => isFin_of_scaled (by have := hb c hc; omega)
  have hk : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  simp only [floatAvgCR, nonFinite_of_fin hfin, Option.getD_none, List.length_map]
  have ⟨s1, s2⟩ := exactSum_bounds hb
  generalize exactSum (cs.map .float) = S at s1 s2 ⊢
  generalize hB : max lo.natAbs hi.natAbs = B
  generalize cs.length = k at hk hN s1 s2 ⊢
  have hcast : ((k * B : Nat) : Int) = (k : Int) * (B : Int) := Int.natCast_mul _ _
  have hkB : (k : Int) * hi ≤ k * B ∧ -((k : Int) * B) ≤ k * lo := by
    have m1 := Int.mul_le_mul_of_nonneg_left (show hi ≤ (B : Int) by omega) (Int.natCast_nonneg k)
    have m2 := Int.mul_le_mul_of_nonneg_left (show -(B : Int) ≤ lo by omega) (Int.natCast_nonneg k)
    rw [Int.mul_neg] at m2
    omega
  have hB2 : B ≤ 2 ^ 2097 :=
    Nat.le_trans (show B ≤ 2 ^ 1474 by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hkB2 : k * B ≤ k * 2 ^ 2097 := Nat.mul_le_mul_left k hB2
  have hfin' : IsFin (ofExactDiv S k) := ofExactDiv_fin (by omega) (by omega)
  have hw := ofExactDiv_within (by omega) hfin'
  have hu := ulpDiv_le S (n := k) (by omega)
  have hU0 := ulpDiv_pos S k
  generalize scaled (ofExactDiv S k) = R at hw ⊢
  generalize ulpDiv S k = U at hw hu hU0
  have hkU : ((k * U : Nat) : Int) = (k : Int) * (U : Int) := Int.natCast_mul _ _
  have hkpos : (0 : Int) < k := by omega
  -- The ulp is `1`, or at most `2⁻⁵²` of the bound.
  have hU : 2 ^ 52 * U ≤ B ∨ U = 1 := by
    by_cases hS : S.natAbs ≤ k * 2 ^ 52
    · right
      have : k * 2 ^ 52 * U ≤ k * 2 ^ 52 * 1 := by rw [Nat.mul_one]; omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
    · left
      have h1 : k * 2 ^ 52 * U ≤ S.natAbs := by omega
      have h2 : S.natAbs ≤ k * B := by omega
      have : k * (2 ^ 52 * U) ≤ k * B := by rw [← Nat.mul_assoc]; omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
  -- Divide `2k · R` against `2S ± k · U` by `k`.
  have lower : lo * 2 - U ≤ R * 2 := by
    apply Int.le_of_mul_le_mul_left _ hkpos
    rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc]
    omega
  have upper : R * 2 ≤ hi * 2 + U := by
    apply Int.le_of_mul_le_mul_left _ hkpos
    rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc]
    omega
  have htol : B / 2 ^ 52 ≤ avgTolScaled N B :=
    Nat.le_trans (ceilDiv_ge _ ()) (Nat.le_add_left _ _)
  constructor <;> omega

/-- Doubles all at least `0` (at most `0`) have a `SUM` and an `AVG` at least
`0` (at most `0`), as `floatSum_sign` states of the sequential sum. -/
theorem floatSumCR_sign {cs : List Int} (_hne : cs ≠ []) :
    ((∀ c ∈ cs, 0 ≤ c) → 0 ≤ floatSumCR (cs.map .float) ∧ 0 ≤ floatAvgCR (cs.map .float)) ∧
      ((∀ c ∈ cs, c ≤ 0) → floatSumCR (cs.map .float) ≤ 0 ∧ floatAvgCR (cs.map .float) ≤ 0) := by
  have := nan_eq; have := posInf_eq; have := negInf_eq; have := maxMag_pos
  constructor
  · intro h
    have hs := exactSum_nonneg h
    have hf : anyCode (fun c => decide (c ≤ negInf)) (cs.map .float) = false :=
      anyCode_map_false fun c hc => by have := h c hc; simp; omega
    unfold floatSumCR floatAvgCR
    rcases nonFinite_cases (cs.map .float) with e | ⟨_, e2⟩ | ⟨e | e, _⟩
    · rw [e]; exact ⟨ofExact_nonneg hs, ofExactDiv_nonneg _ hs⟩
    · rw [hf] at e2; contradiction
    · rw [e]; simp only [Option.getD_some]; omega
    · rw [e]; simp only [Option.getD_some]; omega
  · intro h
    have hs := exactSum_nonpos h
    have hf : anyCode (fun c => decide (posInf ≤ c)) (cs.map .float) = false :=
      anyCode_map_false fun c hc => by have := h c hc; simp; omega
    unfold floatSumCR floatAvgCR
    rcases nonFinite_cases (cs.map .float) with e | ⟨e, _⟩ | ⟨_, e2⟩
    · rw [e]; exact ⟨ofExactDiv_nonpos _ hs, ofExactDiv_nonpos _ hs⟩
    · rw [e]; simp only [Option.getD_some]; omega
    · rw [hf] at e2; contradiction

/-! ### Examples

The expected sums are Python's `math.fsum`, which is correctly rounded. Added
in list order, `0.1 + 0.2 + 0.3` is `0.6000000000000001`; the mean of three
`0.1` is `0.10000000000000002`. -/

private def sumOf (xs : List Float) : Int := floatSumCR (xs.map fun x => .float (ofFloat x))
private def avgOf (xs : List Float) : Int := floatAvgCR (xs.map fun x => .float (ofFloat x))

#guard [([0.1, 0.2, 0.3], 0.6),
  ([0.3, 0.2, 0.1], 0.6),
  ([9007199254740992.0, 1.0], 9007199254740992.0),
  ([9007199254740992.0, 1.0, 1.0], 9007199254740994.0),
  ([5e-324, 5e-324], 1e-323),
  ([1e16, 1.0, -1e16, 1.0], 2.0),
  ([1e308, -1e308, 1e-300], 1e-300),
  ([-0.1, -0.2, -0.3], -0.6),
  ([-3.994418859044304e-17], -3.994418859044304e-17),
  ([0.3598847355321706, 31.896761328605482, -3.3427601926044994e-19], 32.256646064137655),
  ([0.5811445413014543, 0.2578270248986406, 8796809655.830156, 0.08589431412576826,
    0.7822492105972978], 8796809657.537271),
  ([0.100852056089906, 0.5886988141697911, 0.6082233213753983, 0.3334931455689619,
    0.5549395044629044, -4.989390879648303e16], -4.989390879648303e16),
  ([0.8896667171443167, -6969000881700933.0, 0.03707554737230212], -6969000881700932.0),
  ([0.9411975165731968, 5.887537376915839e-15, 0.9339476456037524], 1.8751451621769553)
  ].all fun (xs, s) => sumOf xs == ofFloat s
-- Overflow, and the IEEE rules for NaN and the infinities.
#guard sumOf [1e308, 1e308] == posInf && sumOf [-1e308, -1e308] == negInf
#guard sumOf [1.0 / 0.0, 1.0] == posInf && sumOf [1.0 / 0.0, -1.0 / 0.0] == nan
#guard sumOf [0.0 / 0.0, 1.0] == nan && sumOf [-1.0 / 0.0, 2.0] == negInf
#guard sumOf [] == 0 && sumOf [0.0] == 0
-- One rounding for the mean.
#guard avgOf [0.1, 0.1, 0.1] == ofFloat 0.1 && avgOf [1e308, 1e308] == ofFloat 1e308
#guard avgOf [1.0, 2.0] == ofFloat 1.5 && avgOf [1.0, 1.0, 2.0] == ofFloat (4.0 / 3.0)

end Substrait
