module

public import FloatBounds.Moments

/-!
# The facts the core trusts (#85)

The contract checker in `SubstraitLean` has no Mathlib and no real numbers.
It works with *scaled* values: a double `x` is `x · 2¹⁰⁷⁴`, an integer, the
magnitude part of `FloatCode`. `core/Sverify/Core/Float.lean` states two trusted
facts in that form (`FloatCode.fsum_mem`, `FloatCode.avg_mem`), with the
tolerances `sumTolScaled` and `avgTolScaled` below, defined the same way
there. This file proves them for the standard model, over the reals:

* `core_sum`: a rounded sum of `n ≤ N` values in `[lo, hi]` lies in
  `[min(lo, N·lo) − τ, max(hi, N·hi) + τ]`, `τ = sumTolScaled N Bs / 2¹⁰⁷⁴`;
* `core_avg`: their rounded mean lies in `[lo − τ', hi + τ']`,
  `τ' = avgTolScaled N Bs / 2¹⁰⁷⁴`,

for `N ≤ 2³²` and values at most `Bs / 2¹⁰⁷⁴ ≤ 2⁴⁰⁰` in magnitude. The
values the model adds are the doubles `FloatCode.toFloat` decodes, which may
be within `2u` of the codes' values, relatively (`Decoded`): a code with
more than 53 significant bits is truncated.

What remains trusted is `NativeLink` (`FloatBounds/Link.lean`, IEEE rounding
of Lean's `Float`) and the code conversions of `core/Sverify/Core/Float.lean`.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- `2⁵²`: `tiny · 2¹⁰⁷⁴`, and `1 / (2u)`. -/
def K : ℕ := 2 ^ 52

/-- `⌈a / b⌉`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `sumTol n B · 2¹⁰⁷⁴`, rounded up, for `Bs = B · 2¹⁰⁷⁴`: with
`γ n = n / (2K − n)`, it is `γ n · n · ((1 + 2u)·Bs + K) + 2 n u Bs`. -/
def sumTolScaled (n Bs : ℕ) : ℕ :=
  ceilDiv (n ^ 2 * ((K + 1) * Bs + K ^ 2)) (K * (2 * K - n)) + ceilDiv (n * Bs) K

/-- `avgTol n B · 2¹⁰⁷⁴`, rounded up: `γ (n + 2) · ((1 + 2u)·Bs + K) + 2 u Bs`. -/
def avgTolScaled (n Bs : ℕ) : ℕ :=
  ceilDiv ((n + 2) * ((K + 1) * Bs + K ^ 2)) (K * (2 * K - (n + 2))) + ceilDiv Bs K

theorem ceilDiv_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ceilDiv a b := by
  unfold ceilDiv
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have h := Nat.lt_div_mul_add (a := a + b - 1) hb
  have : a ≤ (a + b - 1) / b * b := by
    have := Nat.div_add_mod (a + b - 1) b
    have := Nat.mod_lt (a + b - 1) hb
    rw [mul_comm] at *
    omega
  exact_mod_cast this

/-- The values `(x', x)`: `x'` the double the model adds, `x` the code's
value, within `2u|x|`. -/
def Decoded (ps : List (ℝ × ℝ)) : Prop := ∀ p ∈ ps, |p.1 - p.2| ≤ 2 * u * |p.2|

theorem u_eq : u = 1 / (2 * K) := by rw [u_val]; unfold K; norm_num

theorem tiny_eq : tiny * 2 ^ 1074 = K := by unfold tiny K; norm_num

variable (M : StdModel)

/-- The rounded sum of the doubles, against the exact sum of the values:
within `γ n · n ((1 + 2u) B + tiny) + 2 n u B`. -/
theorem StdModel.decoded_sum_error {ps : List (ℝ × ℝ)} (hd : Decoded ps) {B : ℝ}
    (hB : ∀ p ∈ ps, |p.2| ≤ B) (hn : (ps.length : ℝ) * u < 1)
    (hov : (1 + gamma ps.length) * (ps.length * ((1 + 2 * u) * B + tiny)) ≤ maxFinite) :
    |M.sum (ps.map Prod.fst) - (ps.map Prod.snd).sum|
      ≤ gamma ps.length * (ps.length * ((1 + 2 * u) * B + tiny)) + 2 * ps.length * u * B := by
  have hu := u_pos
  have hB' : ∀ x ∈ ps.map Prod.fst, |x| ≤ (1 + 2 * u) * B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hd p hp
    have := abs_sub_abs_le_abs_sub p.1 p.2
    have := hB p hp
    nlinarith [abs_nonneg p.2]
  have h1 := M.sum_error_of_bound hB' (by simpa using hn) (by simpa using hov)
  simp only [List.length_map] at h1
  have h2 := abs_sum_map_sub_le Prod.fst Prod.snd (fun _ => (1 : ℝ)) (2 * u * B) ps (by
    intro p hp
    have h1 := hd p hp
    have h2 := hB p hp
    have : 2 * u * |p.2| ≤ 2 * u * B := by gcongr
    simpa using le_trans h1 this)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at h2
  calc _ = |(M.sum (ps.map Prod.fst) - (ps.map Prod.fst).sum)
        + ((ps.map Prod.fst).sum - (ps.map Prod.snd).sum)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

theorem sum_mem_of_bounds {xs : List ℝ} {lo hi : ℝ} (h : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) :
    xs.length * lo ≤ xs.sum ∧ xs.sum ≤ xs.length * hi := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    simp only [List.sum_cons, List.length_cons]; push_cast
    constructor <;> linarith [hx.1, hx.2]

/-- The tolerance `γ n · n ((1 + 2u) B + tiny) + 2 n u B`, for `n ≤ N`, is at
most `sumTolScaled N Bs / 2¹⁰⁷⁴` when `B = Bs / 2¹⁰⁷⁴`. -/
theorem sumTol_le {n N Bs : ℕ} (hnN : n ≤ N) (hN : N ≤ 2 ^ 32) :
    gamma n * (n * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny)) + 2 * n * u * (Bs / 2 ^ 1074)
      ≤ sumTolScaled N Bs / 2 ^ 1074 := by
  have hu := u_pos
  have hK : (K : ℝ) = 2 ^ 52 := by unfold K; norm_num
  have hNr : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hBs : (0 : ℝ) ≤ Bs := Nat.cast_nonneg Bs
  have huK : u = 1 / (2 * K) := u_eq
  have hNu : (N : ℝ) * u < 1 := by rw [huK, hK]; rw [mul_one_div, div_lt_one (by norm_num)]; linarith
  have hgn := gamma_mono hnN hNu
  have hgN0 := gamma_nonneg hNu
  have hg0 := gamma_nonneg (n := n) (lt_of_le_of_lt (by gcongr) hNu)
  -- monotone in `n`
  have h1 : gamma n * (n * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny)) + 2 * n * u * (Bs / 2 ^ 1074)
      ≤ gamma N * (N * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny)) + 2 * N * u * (Bs / 2 ^ 1074) := by
    have : 0 ≤ (1 + 2 * u) * (Bs / 2 ^ 1074) + tiny := by have := tiny_pos; positivity
    gcongr
  refine le_trans h1 ?_
  -- the closed form
  have hden : (0 : ℝ) < 2 * K - N := by rw [hK]; linarith
  have hgN : gamma N = N / (2 * K - N) := by
    unfold gamma; rw [huK]; field_simp
  have hpos : 0 < K * (2 * K - N) := by
    have : N < 2 * K := by unfold K; omega
    exact Nat.mul_pos (by unfold K; positivity) (by omega)
  have c1 := ceilDiv_ge (N ^ 2 * ((K + 1) * Bs + K ^ 2)) (K * (2 * K - N)) hpos
  have c2 := ceilDiv_ge (N * Bs) K (by unfold K; positivity)
  have hcast : ((K * (2 * K - N) : ℕ) : ℝ) = K * (2 * K - N) := by
    have : N ≤ 2 * K := by unfold K; omega
    push_cast [Nat.cast_sub this]; ring
  rw [hcast] at c1
  unfold sumTolScaled
  push_cast
  rw [hgN, add_div]
  have ht : tiny = K / 2 ^ 1074 := by rw [← tiny_eq]; field_simp
  rw [ht, huK]
  have hK0 : (0 : ℝ) < K := by rw [hK]; norm_num
  have e : (N : ℝ) / (2 * K - N) * (N * ((1 + 2 * (1 / (2 * K))) * (Bs / 2 ^ 1074) + K / 2 ^ 1074))
        + 2 * N * (1 / (2 * K)) * (Bs / 2 ^ 1074)
      = (N ^ 2 * ((K + 1) * Bs + K ^ 2) / (K * (2 * K - N))) / 2 ^ 1074
        + (N * Bs / K) / 2 ^ 1074 := by
    field_simp
  rw [e]
  push_cast at c1 c2
  gcongr

/-- **The `SUM` the core trusts** (`FloatCode.fsum_mem`). -/
theorem StdModel.core_sum {ps : List (ℝ × ℝ)} (hd : Decoded ps) (hne : ps ≠ [])
    {lo hi : ℝ} (hx : ∀ p ∈ ps, lo ≤ p.2 ∧ p.2 ≤ hi) {N Bs : ℕ} (hN : ps.length ≤ N)
    (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474) (hlo : |lo| * 2 ^ 1074 ≤ Bs)
    (hhi : |hi| * 2 ^ 1074 ≤ Bs) :
    min lo (N * lo) - sumTolScaled N Bs / 2 ^ 1074 ≤ M.sum (ps.map Prod.fst) ∧
      M.sum (ps.map Prod.fst) ≤ max hi (N * hi) + sumTolScaled N Bs / 2 ^ 1074 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  set B : ℝ := Bs / 2 ^ 1074 with hBdef
  have hB : ∀ p ∈ ps, |p.2| ≤ B := by
    intro p hp
    obtain ⟨h1, h2⟩ := hx p hp
    rw [hBdef, le_div_iff₀ (by positivity)]
    have : |p.2| ≤ max |lo| |hi| := by
      rw [abs_le]; constructor
      · have := neg_abs_le lo; have := le_max_left |lo| |hi|; linarith
      · have := le_abs_self hi; have := le_max_right |lo| |hi|; linarith
    rcases le_total |lo| |hi| with h | h
    · rw [max_eq_right h] at this; nlinarith
    · rw [max_eq_left h] at this; nlinarith
  have hB0 : 0 ≤ B := by positivity
  have hB400 : B ≤ 2 ^ 400 := by
    rw [hBdef, div_le_iff₀ (by positivity)]; linarith [show (2 : ℝ) ^ 400 * 2 ^ 1074 = 2 ^ 1474 by norm_num]
  have hl1 : (1 : ℝ) ≤ ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hlN : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN32
  have hu' := u_val
  have hnu : (ps.length : ℝ) * u < 1 := by rw [hu']; rw [mul_one_div, div_lt_one (by norm_num)]; linarith
  have hg := gamma_nonneg hnu
  have hg2 : 1 + gamma ps.length ≤ 2 := by
    unfold gamma
    rw [hu']
    have : (ps.length : ℝ) / 2 ^ 53 ≤ 1 / 2 := by rw [div_le_iff₀ (by norm_num)]; linarith
    have : (ps.length : ℝ) * (1 / 2 ^ 53) / (1 - ps.length * (1 / 2 ^ 53)) ≤ 1 := by
      rw [div_le_one (by rw [mul_one_div]; linarith)]; rw [mul_one_div]; linarith
    linarith
  have hov : (1 + gamma ps.length) * (ps.length * ((1 + 2 * u) * B + tiny)) ≤ maxFinite := by
    have h1 : (1 + 2 * u) * B + tiny ≤ 2 ^ 402 := by
      have : tiny ≤ 1 := by unfold tiny; norm_num
      have : 2 * u ≤ 1 := by rw [hu']; norm_num
      nlinarith
    have h2 : (ps.length : ℝ) * ((1 + 2 * u) * B + tiny) ≤ 2 ^ 32 * 2 ^ 402 :=
      mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
    have := mul_le_mul hg2 h2 (by positivity) (by norm_num)
    linarith [two_pow_le_maxFinite]
  have herr := M.decoded_sum_error hd hB hnu hov
  have htol := sumTol_le (n := ps.length) (Bs := Bs) hN hN32
  rw [← hBdef] at htol
  have hsum := sum_mem_of_bounds (xs := ps.map Prod.snd) (lo := lo) (hi := hi) (by
    intro x hx'; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'; exact hx p hp)
  simp only [List.length_map] at hsum
  have hlo' : min lo (N * lo) ≤ ps.length * lo := by
    rcases le_total 0 lo with h | h
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (min_le_right _ _) (by nlinarith)
  have hhi' : ps.length * hi ≤ max hi (N * hi) := by
    rcases le_total 0 hi with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  have := abs_le.mp (le_trans herr htol)
  constructor <;> linarith [this.1, this.2]

/-- The tolerance `γ (n + 2) ((1 + 2u) B + tiny) + 2 u B`, for `n ≤ N`, is at
most `avgTolScaled N Bs / 2¹⁰⁷⁴` when `B = Bs / 2¹⁰⁷⁴`. -/
theorem avgTol_le {n N Bs : ℕ} (hnN : n ≤ N) (hN : N ≤ 2 ^ 32) :
    gamma (n + 2) * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) + 2 * u * (Bs / 2 ^ 1074)
      ≤ avgTolScaled N Bs / 2 ^ 1074 := by
  have hu := u_pos
  have hK : (K : ℝ) = 2 ^ 52 := by unfold K; norm_num
  have hNr : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have huK : u = 1 / (2 * K) := u_eq
  have hNu : ((N + 2 : ℕ) : ℝ) * u < 1 := by
    rw [huK, hK]; push_cast; rw [mul_one_div, div_lt_one (by norm_num)]; linarith
  have hgn := gamma_mono (show n + 2 ≤ N + 2 by omega) hNu
  have hgN0 := gamma_nonneg hNu
  have h1 : gamma (n + 2) * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) + 2 * u * (Bs / 2 ^ 1074)
      ≤ gamma (N + 2) * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) + 2 * u * (Bs / 2 ^ 1074) := by
    have : 0 ≤ (1 + 2 * u) * (Bs / 2 ^ 1074) + tiny := by have := tiny_pos; positivity
    gcongr
  refine le_trans h1 ?_
  have hden : (0 : ℝ) < 2 * K - (N + 2) := by rw [hK]; linarith
  have hgN : gamma (N + 2) = (N + 2) / (2 * K - (N + 2)) := by
    unfold gamma; rw [huK]; push_cast; field_simp
  have hpos : 0 < K * (2 * K - (N + 2)) := by
    have : N + 2 < 2 * K := by unfold K; omega
    exact Nat.mul_pos (by unfold K; positivity) (by omega)
  have c1 := ceilDiv_ge ((N + 2) * ((K + 1) * Bs + K ^ 2)) (K * (2 * K - (N + 2))) hpos
  have c2 := ceilDiv_ge Bs K (by unfold K; positivity)
  have hcast : ((K * (2 * K - (N + 2)) : ℕ) : ℝ) = K * (2 * K - (N + 2)) := by
    have : N + 2 ≤ 2 * K := by unfold K; omega
    push_cast [Nat.cast_sub this]; ring
  rw [hcast] at c1
  unfold avgTolScaled
  push_cast
  rw [hgN]
  have ht : tiny = K / 2 ^ 1074 := by rw [← tiny_eq]; field_simp
  rw [ht, huK]
  have hK0 : (0 : ℝ) < K := by rw [hK]; norm_num
  have e : ((N : ℝ) + 2) / (2 * K - (N + 2)) * ((1 + 2 * (1 / (2 * K))) * (Bs / 2 ^ 1074)
        + K / 2 ^ 1074) + 2 * (1 / (2 * K)) * (Bs / 2 ^ 1074)
      = ((N + 2) * ((K + 1) * Bs + K ^ 2) / (K * (2 * K - (N + 2)))) / 2 ^ 1074
        + (Bs / K) / 2 ^ 1074 := by
    field_simp
  rw [e, ← add_div]
  push_cast at c1 c2
  gcongr

/-- **The `AVG` the core trusts** (`FloatCode.avg_mem`). -/
theorem StdModel.core_avg {ps : List (ℝ × ℝ)} (hd : Decoded ps) (hne : ps ≠ [])
    {lo hi : ℝ} (hx : ∀ p ∈ ps, lo ≤ p.2 ∧ p.2 ≤ hi) {N Bs : ℕ} (hN : ps.length ≤ N)
    (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474) (hlo : |lo| * 2 ^ 1074 ≤ Bs)
    (hhi : |hi| * 2 ^ 1074 ≤ Bs) :
    lo - avgTolScaled N Bs / 2 ^ 1074 ≤ M.fl (M.sum (ps.map Prod.fst) / ps.length) ∧
      M.fl (M.sum (ps.map Prod.fst) / ps.length) ≤ hi + avgTolScaled N Bs / 2 ^ 1074 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  set B : ℝ := Bs / 2 ^ 1074 with hBdef
  have hB : ∀ p ∈ ps, |p.2| ≤ B := by
    intro p hp
    obtain ⟨h1, h2⟩ := hx p hp
    rw [hBdef, le_div_iff₀ (by positivity)]
    have : |p.2| ≤ max |lo| |hi| := by
      rw [abs_le]; constructor
      · have := neg_abs_le lo; have := le_max_left |lo| |hi|; linarith
      · have := le_abs_self hi; have := le_max_right |lo| |hi|; linarith
    rcases le_total |lo| |hi| with h | h
    · rw [max_eq_right h] at this; nlinarith
    · rw [max_eq_left h] at this; nlinarith
  have hB0 : 0 ≤ B := by positivity
  have hB400 : B ≤ 2 ^ 400 := by
    rw [hBdef, div_le_iff₀ (by positivity)]; linarith [show (2 : ℝ) ^ 400 * 2 ^ 1074 = 2 ^ 1474 by norm_num]
  have hl0 : (0 : ℝ) < ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hlN : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN32
  have hu' := u_val
  have hn2u : ((ps.length + 2 : ℕ) : ℝ) * u < 1 := by
    rw [hu']; push_cast; rw [mul_one_div, div_lt_one (by norm_num)]; linarith
  have hnu : (ps.length : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn2u
  have hg := gamma_nonneg hnu
  have hg2 : 1 + gamma ps.length ≤ 2 := by
    unfold gamma
    rw [hu']
    have : (ps.length : ℝ) * (1 / 2 ^ 53) / (1 - ps.length * (1 / 2 ^ 53)) ≤ 1 := by
      rw [div_le_one (by rw [mul_one_div]; linarith)]; rw [mul_one_div]; linarith
    linarith
  -- the doubles the model adds
  have hB' : ∀ x ∈ ps.map Prod.fst, |x| ≤ (1 + 2 * u) * B := by
    intro x hx'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
    have := hd p hp
    have := abs_sub_abs_le_abs_sub p.1 p.2
    have := hB p hp
    nlinarith [abs_nonneg p.2]
  have hmag := mag_le_of_bound hB'
  simp only [List.length_map] at hmag
  have hov : (1 + gamma ps.length) * mag (ps.map Prod.fst) ≤ maxFinite := by
    have h1 : (1 + 2 * u) * B + tiny ≤ 2 ^ 402 := by
      have : tiny ≤ 1 := by unfold tiny; norm_num
      have : 2 * u ≤ 1 := by rw [hu']; norm_num
      nlinarith
    have h2 : mag (ps.map Prod.fst) ≤ 2 ^ 32 * 2 ^ 402 :=
      le_trans hmag (mul_le_mul (by linarith) h1 (by positivity) (by norm_num))
    have := mul_le_mul hg2 h2 (mag_nonneg _) (by norm_num)
    linarith [two_pow_le_maxFinite]
  have havg := M.avg_error (xs := ps.map Prod.fst) (by simpa using hne) (by simpa using hn2u)
    (by simpa using hov)
  simp only [List.length_map] at havg
  have hg2' := gamma_nonneg hn2u
  have e1 : gamma (ps.length + 2) * mag (ps.map Prod.fst) / ps.length
      ≤ gamma (ps.length + 2) * ((1 + 2 * u) * B + tiny) := by
    rw [div_le_iff₀ hl0]
    have := mul_le_mul_of_nonneg_left hmag hg2'
    linarith [show gamma (ps.length + 2) * (ps.length * ((1 + 2 * u) * B + tiny))
      = gamma (ps.length + 2) * ((1 + 2 * u) * B + tiny) * ps.length by ring]
  -- the decoded values against the codes' values
  have h2 := abs_sum_map_sub_le Prod.fst Prod.snd (fun _ => (1 : ℝ)) (2 * u * B) ps (by
    intro p hp
    have h1 := hd p hp
    have h2 := hB p hp
    have : 2 * u * |p.2| ≤ 2 * u * B := by gcongr
    simpa using le_trans h1 this)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at h2
  have e2 : |(ps.map Prod.fst).sum / ps.length - (ps.map Prod.snd).sum / ps.length| ≤ 2 * u * B := by
    rw [← sub_div, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; linarith
  have htol := avgTol_le (n := ps.length) (Bs := Bs) hN hN32
  rw [← hBdef] at htol
  have hsum := sum_mem_of_bounds (xs := ps.map Prod.snd) (lo := lo) (hi := hi) (by
    intro x hx'; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'; exact hx p hp)
  simp only [List.length_map] at hsum
  have hm1 : lo ≤ (ps.map Prod.snd).sum / ps.length := by
    rw [le_div_iff₀ hl0]; linarith [hsum.1]
  have hm2 : (ps.map Prod.snd).sum / ps.length ≤ hi := by
    rw [div_le_iff₀ hl0]; linarith [hsum.2]
  have a1 := abs_le.mp havg
  have a2 := abs_le.mp e2
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-! ## Signs -/

theorem StdModel.sumFrom_nonneg {a : ℝ} (ha : 0 ≤ a) :
    ∀ {xs : List ℝ}, (∀ x ∈ xs, 0 ≤ x) → 0 ≤ M.sumFrom a xs
  | [], _ => ha
  | x :: xs, h => by
    simp only [StdModel.sumFrom, List.foldl_cons]
    exact StdModel.sumFrom_nonneg (M.nonneg _ (add_nonneg ha (h x (by simp))))
      (fun y hy => h y (by simp [hy]))

theorem StdModel.sumFrom_nonpos {a : ℝ} (ha : a ≤ 0) :
    ∀ {xs : List ℝ}, (∀ x ∈ xs, x ≤ 0) → M.sumFrom a xs ≤ 0
  | [], _ => ha
  | x :: xs, h => by
    simp only [StdModel.sumFrom, List.foldl_cons]
    exact StdModel.sumFrom_nonpos (M.nonpos _ (add_nonpos ha (h x (by simp))))
      (fun y hy => h y (by simp [hy]))

/-- A decoded value has its code's sign. -/
theorem Decoded.sign {ps : List (ℝ × ℝ)} (hd : Decoded ps) {p : ℝ × ℝ} (hp : p ∈ ps) :
    (0 ≤ p.2 → 0 ≤ p.1) ∧ (p.2 ≤ 0 → p.1 ≤ 0) := by
  have h := abs_le.mp (hd p hp)
  have hu : 2 * u ≤ 1 := by rw [u_val]; norm_num
  constructor
  · intro h0; rw [abs_of_nonneg h0] at h; nlinarith [h.1]
  · intro h0; rw [abs_of_nonpos h0] at h; nlinarith [h.2]

/-- **Signs the core trusts**: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`, and
of values `≤ 0` is `≤ 0`. -/
theorem StdModel.core_sign {ps : List (ℝ × ℝ)} (hd : Decoded ps) :
    ((∀ p ∈ ps, 0 ≤ p.2) → 0 ≤ M.sum (ps.map Prod.fst) ∧
        0 ≤ M.fl (M.sum (ps.map Prod.fst) / ps.length)) ∧
      ((∀ p ∈ ps, p.2 ≤ 0) → M.sum (ps.map Prod.fst) ≤ 0 ∧
        M.fl (M.sum (ps.map Prod.fst) / ps.length) ≤ 0) := by
  constructor
  · intro h
    have hs : 0 ≤ M.sum (ps.map Prod.fst) := M.sumFrom_nonneg le_rfl (by
      intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hd.sign hp).1 (h p hp))
    exact ⟨hs, M.nonneg _ (div_nonneg hs (Nat.cast_nonneg _))⟩
  · intro h
    have hs : M.sum (ps.map Prod.fst) ≤ 0 := M.sumFrom_nonpos le_rfl (by
      intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hd.sign hp).2 (h p hp))
    exact ⟨hs, M.nonpos _ (div_nonpos_of_nonpos_of_nonneg hs (Nat.cast_nonneg _))⟩

end FloatBounds

end
