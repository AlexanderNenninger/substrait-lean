module

public import FloatBounds.TwoPassRel

/-!
# Welford's algorithm, to first order in the spread (#85)

`Welford.lean` bounds Welford's update by `64 n² u B²`, which is useless when
the values sit far from zero relative to their spread. This file proves the
first-order behaviour (Chan, Golub and LeVeque, 1983): for `n ≤ 2³²` doubles
at most `2³⁹⁹`,

  `|Ŝ − S| ≤ 36 n u √(S Q') + 111 n² u² Q' + 4 n u · tiny`,

with `Q' = Σ (|xᵢ| + tiny)²` (`welfordVar_rel`). The invariant carries the
error of the mean, at most `6 u A` with `A = Σ (|xᵢ| + tiny)`, and of the
co-moment, which grows by `14 u A |D| + 7 u S` per value (`D = x − x̄`, the
deviation from the mean before it). At the end `Σ |D| ≤ √(2 n S)` and
`A ≤ √(n Q')`.

The update is DuckDB's (`welfordStep` with `y = x`): `d = x − x̄`,
`x̄' = x̄ + d / k`, `S' = S + d · (x − x̄')`. The first value is exact
(`StdModel.idem`, `StdModel.zero`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- The arithmetic of `wmean_step`, with `a = u A`, `b = u |x|`, `c = u·tiny`. -/
theorem wmean_arith {a b c z d w P Su R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hz0 : 0 ≤ z) (_hd0 : 0 ≤ d) (hP0 : 0 ≤ P)
    (hw1 : 1 / 2 ^ 32 ≤ w) (hw2 : w ≤ 1 / 2)
    (hz : z ≤ b + a + 6 * u * a) (hd : d ≤ (1 + u) * z + u * c)
    (hP : P ≤ 6 * a * (1 - w) + (z + c) * w + (d * w + c))
    (hS : Su ≤ (a + b) * w + u * P) (hR : R ≤ Su + c) :
    R + P ≤ 6 * a + 6 * b + 6 * c := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hw0 : 0 ≤ w := by linarith
  have e1 : z * w ≤ (b + a + 6 * u * a) * w := mul_le_mul_of_nonneg_right hz hw0
  have e2 : d * w ≤ ((1 + u) * z + u * c) * w := mul_le_mul_of_nonneg_right hd hw0
  have e3 : u * z * w ≤ (1 / 2 ^ 53) * (z * w) := by
    have := mul_le_mul_of_nonneg_right hu' (by positivity : 0 ≤ z * w); linarith
  have e4 : u * a * w ≤ (1 / 2 ^ 53) * (a * w) := by
    have := mul_le_mul_of_nonneg_right hu' (by positivity : 0 ≤ a * w); linarith
  have e5 : u * c * w ≤ c * w := by
    have := mul_le_mul_of_nonneg_right (le_trans hu' (by norm_num) : u ≤ 1) (by positivity : 0 ≤ c * w); linarith
  have e6 : b * w ≤ b / 2 := by have := mul_le_mul_of_nonneg_left hw2 hb; linarith
  have e7 : c * w ≤ c / 2 := by have := mul_le_mul_of_nonneg_left hw2 hc; linarith
  have e8 : a / 2 ^ 32 ≤ a * w := by have := mul_le_mul_of_nonneg_left hw1 ha; linarith
  have e9 : u * P ≤ P / 2 ^ 53 := by have := mul_le_mul_of_nonneg_right hu' hP0; linarith
  have e10 : z * w ≤ z / 2 := by have := mul_le_mul_of_nonneg_left hw2 hz0; linarith
  have e11 : a * w ≤ a / 2 := by have := mul_le_mul_of_nonneg_left hw2 ha; linarith
  have e12 : u * a ≤ a / 2 ^ 53 := by have := mul_le_mul_of_nonneg_right hu' ha; linarith
  nlinarith

/-- **The mean in Welford's update**, against `A = Σ (|xᵢ| + tiny)`: from a
mean within `6 u A` of the exact one, the next is within `6 u A'`,
`A' = A + |x| + tiny`; and `d = fl(x − x̄)` is within `7 u A' + u |x − m|` of
`x − m`. -/
theorem StdModel.wmean_step {K : ℕ} (hK1 : 1 ≤ K) (hK : K + 1 ≤ 2 ^ 32) {m mh x A : ℝ}
    (hm : |m| * K ≤ A) (hAt : K * tiny ≤ A) (hAb : A ≤ 2 ^ 432) (hx : |x| ≤ 2 ^ 399)
    (hε : |mh - m| ≤ 6 * u * A) :
    |M.fl (x - mh) - (x - m)| ≤ 7 * u * (A + |x| + tiny) + u * |x - m| ∧
      |M.fl (mh + M.fl (M.fl (x - mh) / ((K : ℝ) + 1))) - (m + (x - m) / ((K : ℝ) + 1))|
        ≤ 6 * u * (A + |x| + tiny) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hkr : ((K : ℝ) + 1) ≤ 2 ^ 32 := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K + 1 := by linarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hAt
  have hmA : |m| ≤ A := by
    have := mul_le_mul_of_nonneg_left hK1r (abs_nonneg m); linarith
  have hx0 := abs_nonneg x
  have huA : u * A ≤ A / 2 ^ 53 := by have := mul_le_mul_of_nonneg_right hu' hA0; linarith
  have p1 : 0 ≤ u * A := by positivity
  have p2 : 0 ≤ u * |x| := by positivity
  have p3 : 0 ≤ u * tiny := by positivity
  have p4 : 0 ≤ u * |x - m| := by positivity
  -- `z1 = x − mh`, rounded to `d`
  have hεA : |mh - m| ≤ A := by linarith
  have hz2 : |x - mh| ≤ |x - m| + |mh - m| := by
    have : x - mh = (x - m) - (mh - m) := by ring
    rw [this]; exact abs_sub _ _
  have hxm : |x - m| ≤ |x| + A := by have := abs_sub x m; linarith
  have hz1 : |x - mh| ≤ |x| + A + 6 * u * A := by linarith
  have hz1b : |x - mh| ≤ 2 ^ 434 := by linarith
  have r1 := M.err (x - mh) (by linarith)
  have hr1u : u * |x - mh| ≤ u * |x - m| + u * |mh - m| := by
    have := mul_le_mul_of_nonneg_left hz2 hu.le; linarith
  have hr1A : u * |mh - m| ≤ u * A := mul_le_mul_of_nonneg_left hεA hu.le
  have hd1 : |M.fl (x - mh) - (x - m)| ≤ 7 * u * (A + |x| + tiny) + u * |x - m| := by
    have e : M.fl (x - mh) - (x - m) = (M.fl (x - mh) - (x - mh)) - (mh - m) := by ring
    rw [e]
    have h1 := abs_sub (M.fl (x - mh) - (x - mh)) (mh - m)
    linarith
  refine ⟨hd1, ?_⟩
  have hd : |M.fl (x - mh)| ≤ |x - mh| + u * |x - mh| + u * tiny := by
    have := abs_sub_abs_le_abs_sub (M.fl (x - mh)) (x - mh); linarith
  have hdb : |M.fl (x - mh)| ≤ 2 ^ 435 := by
    have : u * |x - mh| ≤ 2 ^ 434 / 2 ^ 53 := by
      have := mul_le_mul hu' hz1b (abs_nonneg _) (by norm_num); linarith
    have : u * tiny ≤ 1 := le_trans (mul_le_mul hu' ht1 ht.le (by norm_num)) (by norm_num)
    linarith
  -- `q = d / k`, rounded
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / ((K : ℝ) + 1) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ≤ 1 / 2 := by rw [hw, div_le_div_iff₀ hk0 (by norm_num)]; linarith
  have hwk : w * ((K : ℝ) + 1) = 1 := by rw [hw]; field_simp
  have hdk : M.fl (x - mh) / ((K : ℝ) + 1) = M.fl (x - mh) * w := by rw [hw]; ring
  have hdkx : (x - m) / ((K : ℝ) + 1) = (x - m) * w := by rw [hw]; ring
  rw [hdk, hdkx]
  have hdw : |M.fl (x - mh) * w| ≤ |M.fl (x - mh)| * w := by rw [abs_mul, abs_of_pos hw0]
  have hdwb : |M.fl (x - mh) * w| ≤ 2 ^ 435 := by
    have := mul_le_mul_of_nonneg_left hw2 (abs_nonneg (M.fl (x - mh))); linarith
  have r2 := M.err (M.fl (x - mh) * w) (by linarith)
  -- the decomposition of the new mean's error
  have hdec : mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)
      = (mh - m) * (1 - w) + (M.fl (x - mh) - (x - mh)) * w
        + (M.fl (M.fl (x - mh) * w) - M.fl (x - mh) * w) := by ring
  have hM'e : m + (x - m) * w = m * K * w + x * w := by linear_combination (-m) * hwk
  have h1w : 0 ≤ 1 - w := by linarith
  have hM' : |m + (x - m) * w| ≤ (A + |x|) * w := by
    rw [hM'e]
    have := abs_add_le (m * K * w) (x * w)
    rw [abs_mul (m * K), abs_mul m, abs_mul x, abs_of_pos hw0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ K)] at this
    have h1 := mul_le_mul_of_nonneg_right hm hw0.le
    linarith
  have b1 : |(mh - m) * (1 - w)| ≤ 6 * u * A * (1 - w) := by
    rw [abs_mul, abs_of_nonneg h1w]; exact mul_le_mul_of_nonneg_right hε h1w
  have b2 : |(M.fl (x - mh) - (x - mh)) * w| ≤ u * (|x - mh| + tiny) * w := by
    rw [abs_mul, abs_of_pos hw0]; exact mul_le_mul_of_nonneg_right r1 hw0.le
  have hpre : |mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)|
      ≤ 6 * u * A * (1 - w) + u * (|x - mh| + tiny) * w
        + u * (|M.fl (x - mh)| * w + tiny) := by
    rw [hdec]
    have a1 := abs_add_le ((mh - m) * (1 - w) + (M.fl (x - mh) - (x - mh)) * w)
      (M.fl (M.fl (x - mh) * w) - M.fl (x - mh) * w)
    have a2 := abs_add_le ((mh - m) * (1 - w)) ((M.fl (x - mh) - (x - mh)) * w)
    have a3 : u * (|M.fl (x - mh) * w| + tiny) ≤ u * (|M.fl (x - mh)| * w + tiny) := by
      gcongr
    linarith
  -- `|mh + q|` is far from overflow
  have hw1 : w ≤ 1 := by linarith
  have hwlo : 1 / 2 ^ 32 ≤ w := by
    rw [hw]; exact one_div_le_one_div_of_le (by positivity) hkr
  have hPb : |mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)| ≤ 2 ^ 437 := by
    have c1 : 6 * u * A * (1 - w) ≤ 2 ^ 433 := by
      have := mul_le_mul_of_nonneg_left (by linarith : 1 - w ≤ 1) (by positivity : 0 ≤ 6 * u * A)
      linarith
    have c2 : u * (|x - mh| + tiny) * w ≤ 2 ^ 435 := by
      have h1 : u * (|x - mh| + tiny) ≤ 2 ^ 435 := by
        have := mul_le_mul hu' (by linarith : |x - mh| + tiny ≤ 2 ^ 435) (by positivity) (by norm_num)
        linarith
      have := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ u * (|x - mh| + tiny)); linarith
    have c3 : u * (|M.fl (x - mh)| * w + tiny) ≤ 2 ^ 436 := by
      have h1 : |M.fl (x - mh)| * w ≤ 2 ^ 435 := by
        have := mul_le_mul_of_nonneg_left hw1 (abs_nonneg (M.fl (x - mh))); linarith
      have := mul_le_mul hu' (by linarith : |M.fl (x - mh)| * w + tiny ≤ 2 ^ 436) (by positivity)
        (by norm_num)
      linarith
    linarith
  have hM'b : |m + (x - m) * w| ≤ 2 ^ 433 := by
    have := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ A + |x|); linarith
  have hsumb : |mh + M.fl (M.fl (x - mh) * w)| ≤ 2 ^ 1000 := by
    have := abs_sub_abs_le_abs_sub (mh + M.fl (M.fl (x - mh) * w)) (m + (x - m) * w)
    linarith
  have r3 := M.err (mh + M.fl (M.fl (x - mh) * w)) (by linarith)
  have hmq : |mh + M.fl (M.fl (x - mh) * w)| ≤ (A + |x|) * w
      + |mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)| := by
    have := abs_sub_abs_le_abs_sub (mh + M.fl (M.fl (x - mh) * w)) (m + (x - m) * w); linarith
  have e : M.fl (mh + M.fl (M.fl (x - mh) * w)) - (m + (x - m) * w)
      = (M.fl (mh + M.fl (M.fl (x - mh) * w)) - (mh + M.fl (M.fl (x - mh) * w)))
        + (mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)) := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  have key := wmean_arith (a := u * A) (b := u * |x|) (c := u * tiny) (z := u * |x - mh|)
    (d := u * |M.fl (x - mh)|) (w := w)
    (P := |mh + M.fl (M.fl (x - mh) * w) - (m + (x - m) * w)|)
    (Su := u * |mh + M.fl (M.fl (x - mh) * w)|)
    (R := |M.fl (mh + M.fl (M.fl (x - mh) * w)) - (mh + M.fl (M.fl (x - mh) * w))|)
    p1 p2 p3 (by positivity) (by positivity) (abs_nonneg _) hwlo hw2
    (by have := mul_le_mul_of_nonneg_left hz1 hu.le; linarith)
    (by have := mul_le_mul_of_nonneg_left hd hu.le; linarith)
    (by linarith)
    (by have := mul_le_mul_of_nonneg_left hmq hu.le; linarith)
    (by linarith)
  linarith

/-- The product of two deviations, each perturbed by at most `8 u A' + u |D|`. -/
theorem prod_dev {D E α β A' : ℝ} (hE : |E| ≤ |D|) (hD : |D| ≤ A')
    (hα : |α| ≤ 8 * u * A' + u * |D|) (hβ : |β| ≤ 8 * u * A' + u * |D|) :
    |(D + α) * (E + β) - D * E| ≤ 16 * u * A' * |D| + 2 * u * D ^ 2 + 81 * u ^ 2 * A' ^ 2 := by
  have hu := u_pos
  have hA' : 0 ≤ A' := le_trans (abs_nonneg _) hD
  have e : (D + α) * (E + β) - D * E = D * β + E * α + α * β := by ring
  rw [e]
  have h1 : |D * β| ≤ |D| * (8 * u * A' + u * |D|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hβ (abs_nonneg _)
  have h2 : |E * α| ≤ |D| * (8 * u * A' + u * |D|) := by
    rw [abs_mul]; exact mul_le_mul hE hα (abs_nonneg _) (abs_nonneg _)
  have hb : 8 * u * A' + u * |D| ≤ 9 * u * A' := by
    have := mul_le_mul_of_nonneg_left hD hu.le; linarith
  have h3 : |α * β| ≤ (9 * u * A') ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (le_trans hα hb) (le_trans hβ hb) (abs_nonneg _) (by positivity)
  have h4 := abs_add_le (D * β + E * α) (α * β)
  have h5 := abs_add_le (D * β) (E * α)
  have e2 : |D| * (8 * u * A' + u * |D|) = 8 * u * A' * |D| + u * D ^ 2 := by
    rw [mul_add, ← sq_abs D]; ring
  nlinarith

/-- `ΔS = D · D (1 − w)` with `0 < w ≤ 1/2`: `0 ≤ ΔS`, `D² ≤ 2 ΔS ≤ 2 D²`. -/
theorem dsq_facts (D : ℝ) {w : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 1 / 2) :
    0 ≤ D * (D * (1 - w)) ∧ D ^ 2 ≤ 2 * (D * (D * (1 - w))) ∧ D * (D * (1 - w)) ≤ D ^ 2 := by
  have e : D * (D * (1 - w)) = D ^ 2 * (1 - w) := by ring
  rw [e]
  have h := sq_nonneg D
  refine ⟨mul_nonneg h (by linarith), ?_, ?_⟩
  · nlinarith
  · have := mul_le_mul_of_nonneg_left (by linarith : 1 - w ≤ 1) h; linarith

/-- Rounding the product `q ≈ ΔS` and adding it to `Ch ≈ S`. -/
theorem StdModel.wvar_tail {q ΔS A' Dabs S Ch G : ℝ}
    (hq : |q - ΔS| ≤ 16 * u * A' * Dabs + 4 * u * ΔS + 81 * u ^ 2 * A' ^ 2)
    (hΔ0 : 0 ≤ ΔS) (hΔA : ΔS ≤ A' ^ 2) (hD0 : 0 ≤ Dabs) (hDA : Dabs ≤ A') (hA'b : A' ≤ 2 ^ 433)
    (htA : tiny ≤ A') (hS : 0 ≤ S) (hSb : S ≤ 2 ^ 900) (hC : |Ch - S| ≤ G) (hGb : G ≤ 2 ^ 900) :
    |M.fl (Ch + M.fl q) - (S + ΔS)|
      ≤ (1 + u) * G + 17 * u * A' * Dabs + 7 * u * (S + ΔS) + 103 * u ^ 2 * A' ^ 2
        + 3 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hA'0 : 0 ≤ A' := le_trans ht.le htA
  have hA2 : A' ^ 2 ≤ 2 ^ 866 := by
    calc A' ^ 2 ≤ (2 ^ 433) ^ 2 := by gcongr
      _ = 2 ^ 866 := by norm_num
  have hAD : A' * Dabs ≤ A' ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hDA hA'0
  -- size of the products, for the overflow conditions and the second-order terms
  have s1 : u * A' * Dabs ≤ A' ^ 2 / 2 ^ 53 := by
    have := mul_le_mul_of_nonneg_left hAD hu.le
    have := mul_le_mul_of_nonneg_right hu' (sq_nonneg A'); linarith
  have s2 : u * ΔS ≤ A' ^ 2 / 2 ^ 53 := by
    have := mul_le_mul hu' hΔA hΔ0 (by norm_num); linarith
  have s3 : u ^ 2 * A' ^ 2 ≤ A' ^ 2 / 2 ^ 106 := by
    have : u ^ 2 ≤ 1 / 2 ^ 106 := by
      calc u ^ 2 ≤ (1 / 2 ^ 53) ^ 2 := by gcongr
        _ = 1 / 2 ^ 106 := by norm_num
    have := mul_le_mul_of_nonneg_right this (sq_nonneg A'); linarith
  have hqa : |q| ≤ ΔS + 16 * u * A' * Dabs + 4 * u * ΔS + 81 * u ^ 2 * A' ^ 2 := by
    have := abs_sub_abs_le_abs_sub q ΔS; rw [abs_of_nonneg hΔ0] at this; linarith
  have hqb : |q| ≤ 2 ^ 1000 := by linarith
  have r5 := M.err q (by linarith)
  -- `u |q| ≤ u ΔS + 21 u² A'²`
  have t1 : u * (u * A' * Dabs) ≤ u ^ 2 * A' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hAD (by positivity : 0 ≤ u * u); linarith
  have t2 : u * (u * ΔS) ≤ u ^ 2 * A' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΔA (by positivity : 0 ≤ u * u); linarith
  have t3 : u * (81 * u ^ 2 * A' ^ 2) ≤ u ^ 2 * A' ^ 2 := by
    have := mul_le_mul_of_nonneg_right (by linarith : 81 * u ≤ 1)
      (by positivity : 0 ≤ u ^ 2 * A' ^ 2); linarith
  have hqu : u * |q| ≤ u * ΔS + 21 * u ^ 2 * A' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hqa hu.le; linarith
  have hPe : |M.fl q - ΔS| ≤ 16 * u * A' * Dabs + 5 * u * ΔS + 102 * u ^ 2 * A' ^ 2 + u * tiny := by
    have e : M.fl q - ΔS = (M.fl q - q) + (q - ΔS) := by ring
    rw [e]; have := abs_add_le (M.fl q - q) (q - ΔS); linarith
  -- the sum, rounded
  have hσ2 : |Ch + M.fl q| ≤ S + ΔS + G + |M.fl q - ΔS| := by
    have e : Ch + M.fl q = (S + ΔS) + ((Ch - S) + (M.fl q - ΔS)) := by ring
    rw [e]
    have := abs_add_le (S + ΔS) ((Ch - S) + (M.fl q - ΔS))
    have := abs_add_le (Ch - S) (M.fl q - ΔS)
    rw [abs_of_nonneg (by positivity : 0 ≤ S + ΔS)] at *; linarith
  have hPb : |M.fl q - ΔS| ≤ 2 ^ 900 := by
    have : u * tiny ≤ 1 := le_trans (mul_le_mul hu' ht1 ht.le (by norm_num)) (by norm_num)
    linarith
  have hσ : |Ch + M.fl q| ≤ 2 ^ 1000 := by linarith
  have r6 := M.err (Ch + M.fl q) (by linarith)
  have e : M.fl (Ch + M.fl q) - (S + ΔS) = (M.fl (Ch + M.fl q) - (Ch + M.fl q))
      + ((Ch - S) + (M.fl q - ΔS)) := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  have a1 := abs_add_le (Ch - S) (M.fl q - ΔS)
  have g1 : u * |Ch + M.fl q| ≤ u * (S + ΔS) + u * G + u * |M.fl q - ΔS| := by
    have := mul_le_mul_of_nonneg_left hσ2 hu.le; linarith
  have g2 : u * |M.fl q - ΔS| ≤ u * A' * Dabs + u * ΔS + u ^ 2 * A' ^ 2 + u * tiny := by
    have := mul_le_mul_of_nonneg_left hPe hu.le
    have b1 : u * (16 * u * A' * Dabs) ≤ u * A' * Dabs := by
      have := mul_le_mul_of_nonneg_right (by linarith : 16 * u ≤ 1) (by positivity : 0 ≤ u * A' * Dabs)
      linarith
    have b2 : u * (5 * u * ΔS) ≤ u * ΔS := by
      have := mul_le_mul_of_nonneg_right (by linarith : 5 * u ≤ 1) (by positivity : 0 ≤ u * ΔS)
      linarith
    have b3 : u * (102 * u ^ 2 * A' ^ 2) ≤ u ^ 2 * A' ^ 2 := by
      have := mul_le_mul_of_nonneg_right (by linarith : 102 * u ≤ 1) (by positivity : 0 ≤ u ^ 2 * A' ^ 2)
      linarith
    have b4 : u * (u * tiny) ≤ u * tiny := by
      have := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) (by positivity : 0 ≤ u * tiny)
      linarith
    linarith
  have hS7 : 0 ≤ u * S := by positivity
  have hD7 : 0 ≤ u * A' * Dabs := by positivity
  have hG7 : 0 ≤ u * G := mul_nonneg hu.le (le_trans (abs_nonneg _) hC)
  linarith

/-- **Welford's update of the co-moment** (`y = x`): from a co-moment within
`G` of `S`, the next is within
`(1 + u) G + 17 u A' |D| + 7 u S' + 103 u² A'² + 3 u·tiny` of `S'`, with
`D = x − m` and `S' = S + D (x − m')`, `m'` the new mean. -/
theorem StdModel.wvar_step {K : ℕ} (hK1 : 1 ≤ K) (hK : K + 1 ≤ 2 ^ 32) {m mh x A S Ch G : ℝ}
    (hm : |m| * K ≤ A) (hAt : K * tiny ≤ A) (hAb : A ≤ 2 ^ 432) (hx : |x| ≤ 2 ^ 399)
    (hε : |mh - m| ≤ 6 * u * A) (hS : 0 ≤ S) (hSb : S ≤ 2 ^ 900) (hC : |Ch - S| ≤ G)
    (hGb : G ≤ 2 ^ 900) :
    |M.fl (Ch + M.fl (M.fl (x - mh) * M.fl (x - M.fl (mh + M.fl (M.fl (x - mh) / ((K : ℝ) + 1))))))
        - (S + (x - m) * (x - (m + (x - m) / ((K : ℝ) + 1))))|
      ≤ (1 + u) * G + 17 * u * (A + |x| + tiny) * |x - m|
        + 7 * u * (S + (x - m) * (x - (m + (x - m) / ((K : ℝ) + 1))))
        + 103 * u ^ 2 * (A + |x| + tiny) ^ 2 + 3 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hk0 : (0 : ℝ) < K + 1 := by linarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hAt
  have hmA : |m| ≤ A := by
    have := mul_le_mul_of_nonneg_left hK1r (abs_nonneg m); linarith
  obtain ⟨h1, h2⟩ := M.wmean_step hK1 hK hm hAt hAb hx hε
  -- names for the reals involved
  obtain ⟨A', hA'⟩ : ∃ A', A' = A + |x| + tiny := ⟨_, rfl⟩
  rw [← hA'] at h1 h2 ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = x - m := ⟨_, rfl⟩
  rw [← hD] at h1 ⊢
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / ((K : ℝ) + 1) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ≤ 1 / 2 := by rw [hw, div_le_div_iff₀ hk0 (by norm_num)]; linarith
  have hDk : D / ((K : ℝ) + 1) = D * w := by rw [hw]; ring
  have hxD : (x - m) / ((K : ℝ) + 1) = D * w := by rw [hD, hw]; ring
  rw [hxD] at h2
  rw [hDk]
  set mh' := M.fl (mh + M.fl (M.fl (x - mh) / ((K : ℝ) + 1)))
  set d := M.fl (x - mh)
  -- `E = x − m' = D (1 − w)`
  have hE : x - (m + D * w) = D * (1 - w) := by rw [hD]; ring
  rw [hE]
  have h1w : 0 ≤ 1 - w := by linarith
  have hEabs : |D * (1 - w)| ≤ |D| := by
    rw [abs_mul, abs_of_nonneg h1w]; exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have hDA : |D| ≤ A' := by
    rw [hD, hA']; have := abs_sub x m; linarith
  have hA'0 : 0 ≤ A' := le_trans (abs_nonneg _) hDA
  have htA : tiny ≤ A' := by rw [hA']; linarith [abs_nonneg x]
  have hA'b : A' ≤ 2 ^ 433 := by rw [hA']; linarith
  -- `ê = fl(x − mh')`
  have hxmh' : |x - mh'| ≤ |D * (1 - w)| + 6 * u * A' := by
    have : x - mh' = D * (1 - w) - (mh' - (m + D * w)) := by rw [hD]; ring
    rw [this]; have := abs_sub (D * (1 - w)) (mh' - (m + D * w)); linarith
  have r4 := M.err (x - mh') (by nlinarith)
  have hβ : |M.fl (x - mh') - D * (1 - w)| ≤ 8 * u * A' + u * |D| := by
    have e : M.fl (x - mh') - D * (1 - w) = (M.fl (x - mh') - (x - mh')) - (mh' - (m + D * w)) := by
      rw [hD]; ring
    rw [e]
    have := abs_sub (M.fl (x - mh') - (x - mh')) (mh' - (m + D * w))
    have a1 : u * |x - mh'| ≤ u * |D| + u * (6 * u * A') := by
      have := mul_le_mul_of_nonneg_left (le_trans hxmh' (by linarith : |D * (1 - w)| + 6 * u * A'
        ≤ |D| + 6 * u * A')) hu.le
      linarith
    have a2 : u * (6 * u * A') ≤ u * A' := by
      have : 6 * u * A' ≤ A' := by nlinarith
      exact mul_le_mul_of_nonneg_left this hu.le
    have a3 : u * tiny ≤ u * A' := mul_le_mul_of_nonneg_left htA hu.le
    linarith
  have hα : |d - D| ≤ 8 * u * A' + u * |D| := by
    have : 0 ≤ u * A' := by positivity
    linarith
  -- the product
  have hprod := prod_dev hEabs hDA (α := d - D) (β := M.fl (x - mh') - D * (1 - w)) hα hβ
  have e1 : (D + (d - D)) * (D * (1 - w) + (M.fl (x - mh') - D * (1 - w))) = d * M.fl (x - mh') := by
    ring
  rw [e1] at hprod
  have hdsq := dsq_facts D hw0 hw2
  have hDA2 : D ^ 2 ≤ A' ^ 2 := by rw [← sq_abs D]; exact pow_le_pow_left₀ (abs_nonneg _) hDA 2
  have hpe : |d * M.fl (x - mh') - D * (D * (1 - w))|
      ≤ 16 * u * A' * |D| + 4 * u * (D * (D * (1 - w))) + 81 * u ^ 2 * A' ^ 2 := by
    have := mul_le_mul_of_nonneg_left hdsq.2.1 (by positivity : (0 : ℝ) ≤ 2 * u); linarith
  exact M.wvar_tail hpe hdsq.1 (le_trans hdsq.2.2 hDA2) (abs_nonneg D) hDA hA'b htA hS hSb hC hGb

end FloatBounds

end
