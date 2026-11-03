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

end FloatBounds

end
