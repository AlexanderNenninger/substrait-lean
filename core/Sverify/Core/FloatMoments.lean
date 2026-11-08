import Sverify.Core.FloatExact

/-!
# Exact moments and correctly rounded square roots (#918, preparation)

The pieces a correctly rounded `VAR`, `STDDEV`, `COVAR` and `CORR` need, on
integers, before any of them is used (the reference's statistical aggregates
are still `varOf`, `covOf`, `corrOf` with their generic properties,
`StatProps`; a decision would change that).

* `isqrt n`: `⌊√n⌋`, with `isqrt_spec`.
* `sqrtMag a b`: the magnitude, in units of `2⁻¹⁰⁷⁴`, of `√(a / b)` rounded to
  the grid of doubles, ties to even, from the integer square root of
  `a · 2¹²⁰ / b` and a sticky bit. `sqrtMag_near`: within one grid step of
  `√(a / b)`, stated on squares.
* `momentsOf cs`: the count, `Σx` and `Σx²` of the doubles `cs` as exact
  integers (scaled by `2¹⁰⁷⁴` and `2²¹⁴⁸`), and the co-moment numerator
  `comomentNum cs = n · Σx² − (Σx)²`, which is `n²` times the population
  variance's numerator. `comomentNum_nonneg` (Lagrange's identity, one step
  at a time) and the perm lemmas: the moments are functions of the multiset.
-/

namespace Substrait.FloatCode

/-! ### Integer square root -/

/-- `⌊√n⌋`, from `⌊√(n / 4)⌋` (`isqrt_spec`). -/
def isqrt (n : Nat) : Nat :=
  if h : n < 4 then (if n = 0 then 0 else 1)
  else
    let r := 2 * isqrt (n / 4)
    if (r + 1) * (r + 1) ≤ n then r + 1 else r
termination_by n
decreasing_by omega

theorem isqrt_spec : ∀ n : Nat, isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [isqrt]
    by_cases h : n < 4
    · simp only [h, ↓reduceDIte]
      by_cases h0 : n = 0
      · subst h0; simp
      · simp only [h0, ↓reduceIte]; omega
    · simp only [h, ↓reduceDIte]
      have ⟨l, u⟩ := ih (n / 4) (by omega)
      generalize isqrt (n / 4) = s at l u
      have hm := Nat.div_add_mod n 4
      have hr := Nat.mod_lt n (show 0 < 4 by omega)
      split
      · constructor
        · assumption
        · -- `n < 4 (s + 1)² = (2s + 2)²`
          have : n < 4 * ((s + 1) * (s + 1)) := by omega
          grind
      · constructor
        · -- `(2s)² = 4 s² ≤ 4 (n / 4) ≤ n`
          have : 4 * (s * s) ≤ n := by omega
          grind
        · omega

/-- Squares are monotone. -/
theorem sq_le_sq {a b : Nat} (h : a ≤ b) : a * a ≤ b * b := Nat.mul_le_mul h h

/-- `isqrt` is the largest `r` with `r² ≤ n`. -/
theorem le_isqrt {r n : Nat} (h : r * r ≤ n) : r ≤ isqrt n := by
  have ⟨_, u⟩ := isqrt_spec n
  apply Classical.byContradiction; intro hlt
  have := sq_le_sq (show isqrt n + 1 ≤ r by omega)
  omega

theorem isqrt_mono {m n : Nat} (h : m ≤ n) : isqrt m ≤ isqrt n :=
  le_isqrt (Nat.le_trans (isqrt_spec m).1 h)

/-! ### `√(a / b)` rounded to the grid of doubles -/

/-- `t / 2⁶⁰` rounded to a multiple of `2ᵉ`, ties to even, where `exact`
says whether the value is `t / 2⁶⁰` itself or a little above it (the
sticky bit). -/
def roundGrid (t e : Nat) (exact : Bool) : Nat :=
  if 2 * (t % 2 ^ (e + 60)) < 2 ^ (e + 60) then t / 2 ^ (e + 60) * 2 ^ e
  else if 2 ^ (e + 60) < 2 * (t % 2 ^ (e + 60)) then (t / 2 ^ (e + 60) + 1) * 2 ^ e
  else if exact then
    (if t / 2 ^ (e + 60) % 2 = 0 then t / 2 ^ (e + 60) else t / 2 ^ (e + 60) + 1) * 2 ^ e
  else (t / 2 ^ (e + 60) + 1) * 2 ^ e

/-- The magnitude, in units of `2⁻¹⁰⁷⁴`, of `√(a / b)` rounded to the grid of
doubles with ties to even, with no bound on the exponent. `t = ⌊√(a / b) · 2⁶⁰⌋`
(the integer square root of `⌊a · 2¹²⁰ / b⌋`), `e` the grid's exponent at
`⌊t / 2⁶⁰⌋` (`gridExp`), and a sticky bit: whether `√(a / b) · 2⁶⁰` is `t`
exactly. -/
def sqrtMag (a b : Nat) : Nat :=
  roundGrid (isqrt (a * 2 ^ 120 / b)) (gridExp (isqrt (a * 2 ^ 120 / b)) (2 ^ 60))
    (decide ((a * 2 ^ 120) % b = 0 ∧
      isqrt (a * 2 ^ 120 / b) * isqrt (a * 2 ^ 120 / b) = a * 2 ^ 120 / b))

/-- The grid step of `sqrtMag a b`. -/
def sqrtGrid (a b : Nat) : Nat := 2 ^ gridExp (isqrt (a * 2 ^ 120 / b)) (2 ^ 60)

/-- The rounding gives one of the two grid points around `t / 2⁶⁰`. -/
theorem roundGrid_cases (t e : Nat) (exact : Bool) :
    roundGrid t e exact = t / 2 ^ (e + 60) * 2 ^ e ∨
      roundGrid t e exact = (t / 2 ^ (e + 60) + 1) * 2 ^ e := by
  unfold roundGrid
  split
  · exact .inl rfl
  · split
    · exact .inr rfl
    · split
      · split
        · exact .inl rfl
        · exact .inr rfl
      · exact .inr rfl

/-- `t = ⌊√(a / b) · 2⁶⁰⌋`, on squares: `t² · b ≤ a · 2¹²⁰ < (t + 1)² · b`. -/
theorem isqrt_ratio {a b : Nat} (hb : 0 < b) :
    isqrt (a * 2 ^ 120 / b) * isqrt (a * 2 ^ 120 / b) * b ≤ a * 2 ^ 120 ∧
      a * 2 ^ 120 < (isqrt (a * 2 ^ 120 / b) + 1) * (isqrt (a * 2 ^ 120 / b) + 1) * b := by
  have ⟨l, u⟩ := isqrt_spec (a * 2 ^ 120 / b)
  generalize isqrt (a * 2 ^ 120 / b) = t at l u
  generalize a * 2 ^ 120 = A at l u ⊢
  exact ⟨Nat.le_trans (Nat.mul_le_mul_right b l) (Nat.div_mul_le_self A b),
    (Nat.div_lt_iff_lt_mul hb).1 u⟩

/-- **Within one grid step**: with `g` the grid step, `s = √(a / b)` and `M`
the rounded magnitude, `(M − g)² · b ≤ a` and `a ≤ (M + g)² · b` (`M − g`
read as `0` below). -/
theorem sqrtMag_near {a b : Nat} (hb : 0 < b) :
    (sqrtMag a b - sqrtGrid a b) * (sqrtMag a b - sqrtGrid a b) * b ≤ a ∧
      a ≤ (sqrtMag a b + sqrtGrid a b) * (sqrtMag a b + sqrtGrid a b) * b := by
  have ⟨l, u⟩ := isqrt_ratio (a := a) hb
  have hcases := roundGrid_cases (isqrt (a * 2 ^ 120 / b)) (gridExp (isqrt (a * 2 ^ 120 / b)) (2 ^ 60))
    (decide ((a * 2 ^ 120) % b = 0 ∧
      isqrt (a * 2 ^ 120 / b) * isqrt (a * 2 ^ 120 / b) = a * 2 ^ 120 / b))
  unfold sqrtMag sqrtGrid
  generalize roundGrid _ _ _ = M at hcases ⊢
  generalize isqrt (a * 2 ^ 120 / b) = t at l u hcases ⊢
  generalize gridExp t (2 ^ 60) = e at hcases ⊢
  -- `t = q · G + r` with `G = g · 2⁶⁰`: `q g ≤ s < (q + 1) g`.
  have hG : 2 ^ (e + 60) = 2 ^ e * 2 ^ 60 := Nat.pow_add 2 e 60
  rw [hG] at hcases
  generalize hg : 2 ^ e = g at hcases ⊢
  have hg0 : 0 < g := hg ▸ Nat.two_pow_pos e
  have hdm := Nat.div_add_mod t (g * 2 ^ 60)
  have hrl := Nat.mod_lt t (Nat.mul_pos hg0 (Nat.two_pow_pos 60))
  generalize t / (g * 2 ^ 60) = q at hcases hdm
  generalize t % (g * 2 ^ 60) = r at hdm hrl
  have h120 : (2 : Nat) ^ 120 = 2 ^ 60 * 2 ^ 60 := by rw [← Nat.pow_add]
  -- Below: `(q g · 2⁶⁰)² b ≤ t² b ≤ a 2¹²⁰`.
  have lo : (q * g) * (q * g) * b ≤ a := by
    have h1 : q * g * 2 ^ 60 ≤ t := by
      have : g * 2 ^ 60 * q = q * g * 2 ^ 60 := by grind
      omega
    have h2 := Nat.le_trans (Nat.mul_le_mul_right b (sq_le_sq h1)) l
    have e1 : q * g * 2 ^ 60 * (q * g * 2 ^ 60) * b = q * g * (q * g) * b * 2 ^ 120 := by
      rw [h120]; grind
    rw [e1] at h2
    exact Nat.le_of_mul_le_mul_right h2 (Nat.two_pow_pos 120)
  -- Above: `a 2¹²⁰ < (t + 1)² b ≤ ((q + 1) g · 2⁶⁰)² b`.
  have hi : a ≤ ((q + 1) * g) * ((q + 1) * g) * b := by
    have h1 : t + 1 ≤ (q + 1) * g * 2 ^ 60 := by
      have : g * 2 ^ 60 * q = q * g * 2 ^ 60 := by grind
      have : (q + 1) * g * 2 ^ 60 = q * g * 2 ^ 60 + g * 2 ^ 60 := by grind
      omega
    have h2 := Nat.lt_of_lt_of_le u (Nat.mul_le_mul_right b (sq_le_sq h1))
    have e1 : (q + 1) * g * 2 ^ 60 * ((q + 1) * g * 2 ^ 60) * b =
        (q + 1) * g * ((q + 1) * g) * b * 2 ^ 120 := by
      rw [h120]; grind
    rw [e1] at h2
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right h2)
  rcases hcases with rfl | rfl
  · exact ⟨Nat.le_trans (Nat.mul_le_mul_right b (sq_le_sq (Nat.sub_le _ _))) lo,
      Nat.le_trans hi (Nat.mul_le_mul_right b (sq_le_sq (by grind)))⟩
  · exact ⟨Nat.le_trans (Nat.mul_le_mul_right b (sq_le_sq (by grind))) lo,
      Nat.le_trans hi (Nat.mul_le_mul_right b (sq_le_sq (by omega)))⟩

-- A square of a grid point rounds to it; a halfway case ties to even.
#guard sqrtMag 0 1 == 0 && sqrtMag 1 1 == 1 && sqrtMag 4 1 == 2 && sqrtMag (2 ^ 200) 1 == 2 ^ 100
#guard sqrtMag 9 4 == 2 -- `√(9/4) = 1.5` lies halfway between 1 and 2: ties to even
#guard sqrtMag (3 ^ 2 * 2 ^ 120) 1 == 3 * 2 ^ 60
-- `√2` in units of `2⁻¹⁰⁷⁴`, scaled up past the subnormals: `√(2 · 4^k)` is
-- `√2 · 2^k`, rounded to 53 bits.
#guard sqrtMag (2 * 4 ^ 60) 1 == 6369051672525773 * 2 ^ 8

end Substrait.FloatCode

namespace Substrait

open FloatCode

/-! ### Exact moments -/

/-- `Σx` of the codes `cs`, in units of `2⁻¹⁰⁷⁴` (`exactSum`'s). -/
def scaledSum (cs : List Int) : Int := (cs.map scaled).foldr (· + ·) 0

/-- `Σx²` of the codes `cs`, in units of `2⁻²¹⁴⁸`. -/
def sqSumOf (cs : List Int) : Int := (cs.map fun c => scaled c * scaled c).foldr (· + ·) 0

/-- `Σxy` of the pairs `ps`, in units of `2⁻²¹⁴⁸`. -/
def prodSumOf (ps : List (Int × Int)) : Int :=
  (ps.map fun p => scaled p.1 * scaled p.2).foldr (· + ·) 0

/-- `n · Σx² − (Σx)²`: `n²` times the population variance's numerator, in
units of `2⁻²¹⁴⁸`; exact. -/
def comomentNum (cs : List Int) : Int := cs.length * sqSumOf cs - scaledSum cs * scaledSum cs

/-- `n · Σxy − Σx · Σy` of the pairs. -/
def coComomentNum (ps : List (Int × Int)) : Int :=
  ps.length * prodSumOf ps - scaledSum (ps.map (·.1)) * scaledSum (ps.map (·.2))

theorem scaledSum_cons (c : Int) (cs : List Int) : scaledSum (c :: cs) = scaled c + scaledSum cs := rfl

theorem sqSumOf_cons (c : Int) (cs : List Int) :
    sqSumOf (c :: cs) = scaled c * scaled c + sqSumOf cs := rfl

theorem prodSumOf_cons (p : Int × Int) (ps : List (Int × Int)) :
    prodSumOf (p :: ps) = scaled p.1 * scaled p.2 + prodSumOf ps := rfl

/-- `Σ (x − c)²` over `cs`, for one more value `c`. -/
def devSq (c : Int) (cs : List Int) : Int :=
  (cs.map fun x => (scaled x - scaled c) * (scaled x - scaled c)).foldr (· + ·) 0

theorem devSq_nonneg (c : Int) : ∀ cs : List Int, 0 ≤ devSq c cs
  | [] => by simp [devSq]
  | x :: cs => by
    have := devSq_nonneg c cs
    have : 0 ≤ (scaled x - scaled c) * (scaled x - scaled c) := by
      rcases Int.le_total 0 (scaled x - scaled c) with h | h
      · exact Int.mul_nonneg h h
      · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (by omega) (by omega)
    simp only [devSq, List.map_cons, List.foldr_cons] at this ⊢
    unfold devSq at *
    omega

theorem devSq_eq (c : Int) : ∀ cs : List Int,
    devSq c cs = sqSumOf cs - 2 * scaled c * scaledSum cs + cs.length * (scaled c * scaled c)
  | [] => by simp [devSq, sqSumOf, scaledSum]
  | x :: cs => by
    have ih := devSq_eq c cs
    simp only [devSq, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, sqSumOf_cons, scaledSum_cons, List.length_cons]
    push_cast
    grind

/-- One step of Lagrange's identity: a value `c` adds `Σ (x − c)²` to the
numerator. -/
theorem comomentNum_cons (c : Int) (cs : List Int) :
    comomentNum (c :: cs) = comomentNum cs + devSq c cs := by
  rw [devSq_eq]
  simp only [comomentNum, sqSumOf_cons, scaledSum_cons, List.length_cons]
  push_cast
  grind

/-- **A variance's numerator is not negative.** -/
theorem comomentNum_nonneg : ∀ cs : List Int, 0 ≤ comomentNum cs
  | [] => by simp [comomentNum, sqSumOf, scaledSum]
  | c :: cs => by
    rw [comomentNum_cons]
    have := comomentNum_nonneg cs
    have := devSq_nonneg c cs
    omega

theorem scaledSum_perm {cs ds : List Int} (h : cs.Perm ds) : scaledSum cs = scaledSum ds := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [scaledSum_cons, ih]
  | swap x y l => simp only [scaledSum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sqSumOf_perm {cs ds : List Int} (h : cs.Perm ds) : sqSumOf cs = sqSumOf ds := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sqSumOf_cons, ih]
  | swap x y l => simp only [sqSumOf_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem prodSumOf_perm {ps qs : List (Int × Int)} (h : ps.Perm qs) : prodSumOf ps = prodSumOf qs := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [prodSumOf_cons, ih]
  | swap x y l => simp only [prodSumOf_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The moments are functions of the multiset.** -/
theorem comomentNum_perm {cs ds : List Int} (h : cs.Perm ds) : comomentNum cs = comomentNum ds := by
  simp only [comomentNum, scaledSum_perm h, sqSumOf_perm h, h.length_eq]

theorem coComomentNum_perm {ps qs : List (Int × Int)} (h : ps.Perm qs) :
    coComomentNum ps = coComomentNum qs := by
  simp only [coComomentNum, prodSumOf_perm h, scaledSum_perm (h.map _), h.length_eq]

/-- The variance's numerator of a pair list's first side is the co-moment
of the pairs `(x, x)`. -/
theorem coComomentNum_diag (cs : List Int) :
    coComomentNum (cs.map fun c => (c, c)) = comomentNum cs := by
  have h1 : prodSumOf (cs.map fun c => (c, c)) = sqSumOf cs := by
    induction cs with
    | nil => rfl
    | cons c cs ih => simp only [List.map_cons, prodSumOf_cons, sqSumOf_cons, ih]
  simp only [coComomentNum, comomentNum, h1, List.map_map, List.length_map, Function.comp_def,
    List.map_id']

-- `n Σx² − (Σx)²` of `1, 2, 3, 4` (scaled) is `4 · 30 − 100 = 20` times the
-- squared unit: `(2⁻¹⁰⁷⁴)²`'s count of `Σ (x − 2.5)² · 4 = 5 · 4`.
#guard comomentNum ([1.0, 2.0, 3.0, 4.0].map ofFloat) == 20 * 2 ^ 2148

/-- **The clamp shims of D30 are sound**: clamping an engine's value `x` to an
interval `[lo, hi]` that holds the exact value `e` never moves it further
from `e`. The writers clamp a variance or deviation at `0` and a correlation
to `[-1, 1]` (`Dialect.clamp_stat`); codes are ordered as their doubles, so
this holds of codes and of scaled values alike. -/
theorem Stat.clamp_near {lo hi e x : Int} (hl : lo ≤ e) (hh : e ≤ hi) :
    (max lo (min hi x) - e).natAbs ≤ (x - e).natAbs := by
  omega

/-- `n · Σv² − (Σv)²` of the values `vs` themselves: `comomentNum` of codes
is this of their scaled values (`comomentNum_eq`). -/
def momentNum (vs : List Int) : Int :=
  vs.length * (vs.map fun v => v * v).foldr (· + ·) 0 - vs.foldr (· + ·) 0 * vs.foldr (· + ·) 0

theorem comomentNum_eq (cs : List Int) : comomentNum cs = momentNum (cs.map scaled) := by
  simp only [comomentNum, momentNum, sqSumOf, scaledSum, List.length_map, List.map_map,
    Function.comp_def]

theorem shift_sum (c : Int) : ∀ vs : List Int,
    (vs.map (· - c)).foldr (· + ·) 0 = vs.foldr (· + ·) 0 - vs.length * c
  | [] => by simp
  | v :: vs => by
    simp only [List.map_cons, List.foldr_cons, List.length_cons, shift_sum c vs]
    push_cast; grind

theorem shift_sqSum (c : Int) : ∀ vs : List Int,
    ((vs.map (· - c)).map fun v => v * v).foldr (· + ·) 0 =
      (vs.map fun v => v * v).foldr (· + ·) 0 - 2 * c * vs.foldr (· + ·) 0 + vs.length * (c * c)
  | [] => by simp
  | v :: vs => by
    simp only [List.map_cons, List.foldr_cons, List.length_cons, shift_sqSum c vs]
    push_cast; grind

/-- **The Snowflake mean-shift shim keeps the reference's value** (#1023):
the exact co-moment `n · Σv² − (Σv)²`, which `varOf` rounds once (D30), is
the same for the values shifted by any constant `c`, so the reference value
of `VAR_*(x − c)` over a group is that of `VAR_*(x)`. The writer shifts each
value by its group's `AVG`; the engine's error on the shifted doubles is
Snowflake's profile bound (recorded privately). -/
theorem momentNum_shift (vs : List Int) (c : Int) : momentNum (vs.map (· - c)) = momentNum vs := by
  simp only [momentNum, shift_sqSum, shift_sum, List.length_map]
  grind

end Substrait
