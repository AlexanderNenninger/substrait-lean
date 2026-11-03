module

public import FloatBounds.CovRel

/-!
# Two-pass covariance, to first order in the spread (#85)

The reference's own algorithm for `COVAR_*`: the means, then the products of
the deviations from them, added in order (`twoPass`). With the computed means
`x̄ + ε_x` and `ȳ + ε_y`, the exact sum of those products is `C + n ε_x ε_y`
(`sum_dev_shift`), and each product's rounding is relative to `|d_x| |d_y|`
(`prod_step`), whose sum is at most `√(S_xx S_yy)` to first order. So

  `|Ĉ − C| ≤ 6 n u √(S_xx S_yy) + 1.1 u (√(Q'_y S_xx) + √(Q'_x S_yy)) + 120 n² u² √(Q'_x Q'_y) + 4 n² u · tiny`

(`twoPass_cov_rel`), with `Q'_x = Σ (|x| + tiny)²`.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- `Σ (xᵢ − a)(yᵢ − b) = C + n (a − x̄)(b − ȳ)`. -/
theorem sum_dev_shift {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (a b : ℝ) :
    (ps.map fun p => (p.1 - a) * (p.2 - b)).sum = comoment ps + ps.length * (a - mx ps) * (b - my ps) := by
  have h : (ps.length : ℝ) ≠ 0 := by simp [hne]
  rw [sum_dev_mul, comoment_eq]
  simp only [mx, my]
  field_simp
  ring

/-- A rounded product of two rounded values. -/
theorem StdModel.prod_step {a b : ℝ} (ha : |a| ≤ 2 ^ 450) (hb : |b| ≤ 2 ^ 450) :
    |M.fl (M.fl a * M.fl b) - a * b|
      ≤ 3.01 * u * (|a| * |b|) + 1.01 * u * (tiny * |a| + tiny * |b|) + 1.01 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have ea := M.err a (by linarith)
  have eb := M.err b (by linarith)
  generalize hα : M.fl a - a = α at ea
  generalize hβ : M.fl b - b = β at eb
  have hfa : M.fl a = a + α := by linarith
  have hfb : M.fl b = b + β := by linarith
  rw [hfa, hfb]
  have hA := abs_nonneg a
  have hB := abs_nonneg b
  have e1 : (a + α) * (b + β) - a * b = a * β + b * α + α * β := by ring
  have k1 : |a * β| ≤ u * (|a| * |b|) + u * (tiny * |a|) := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left eb hA
    linarith
  have k2 : |b * α| ≤ u * (|a| * |b|) + u * (tiny * |b|) := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left ea hB
    linarith
  have k3 : |α * β| ≤ u * (|a| + tiny) * (u * (|b| + tiny)) := by
    rw [abs_mul]; exact mul_le_mul ea eb (abs_nonneg _) (by positivity)
  have hE : |(a + α) * (b + β) - a * b| ≤ u * (|a| * |b|) + u * (tiny * |a|)
      + (u * (|a| * |b|) + u * (tiny * |b|)) + u * (|a| + tiny) * (u * (|b| + tiny)) := by
    rw [e1]
    have := abs_add_le (a * β + b * α) (α * β)
    have := abs_add_le (a * β) (b * α)
    linarith
  -- the second-order term
  have q : u * (|a| + tiny) * (u * (|b| + tiny)) ≤ 0.001 * (u * (|a| * |b|))
      + 0.001 * (u * (tiny * |a|)) + 0.001 * (u * (tiny * |b|)) + 0.001 * (u * tiny) := by
    have e : u * (|a| + tiny) * (u * (|b| + tiny)) = u * (u * (|a| * |b|)) + u * (u * (tiny * |a|))
        + u * (u * (tiny * |b|)) + u * (u * tiny) * tiny := by ring
    rw [e]
    have c1 := mul_le_mul_of_nonneg_right (by linarith : u ≤ 0.001) (by positivity : 0 ≤ u * (|a| * |b|))
    have c2 := mul_le_mul_of_nonneg_right (by linarith : u ≤ 0.001) (by positivity : 0 ≤ u * (tiny * |a|))
    have c3 := mul_le_mul_of_nonneg_right (by linarith : u ≤ 0.001) (by positivity : 0 ≤ u * (tiny * |b|))
    have c4 := mul_le_mul_of_nonneg_right (by linarith : u ≤ 0.001) (by positivity : 0 ≤ u * tiny)
    have c5 : u * (u * tiny) * tiny ≤ u * (u * tiny) := mul_le_of_le_one_right (by positivity) ht1
    linarith
  have hab : |a| * |b| ≤ 2 ^ 900 := by
    have := mul_le_mul ha hb hB (by norm_num)
    have : (2 : ℝ) ^ 450 * 2 ^ 450 = 2 ^ 900 := by norm_num
    linarith
  have hsmall : u * (|a| * |b|) + u * (tiny * |a|) + (u * (|a| * |b|) + u * (tiny * |b|))
      + u * (|a| + tiny) * (u * (|b| + tiny)) ≤ 2 ^ 900 := by
    have s1 : u * (|a| * |b|) ≤ 2 ^ 900 / 8 := by
      have := mul_le_mul hu' hab (by positivity) (by norm_num); linarith
    have s2 : u * (tiny * |a|) ≤ 2 ^ 900 / 8 := by
      have h1 : tiny * |a| ≤ 1 * 2 ^ 450 := mul_le_mul ht1 ha hA (by norm_num)
      have := mul_le_mul hu' h1 (by positivity) (by norm_num); linarith
    have s3 : u * (tiny * |b|) ≤ 2 ^ 900 / 8 := by
      have h1 : tiny * |b| ≤ 1 * 2 ^ 450 := mul_le_mul ht1 hb hB (by norm_num)
      have := mul_le_mul hu' h1 (by positivity) (by norm_num); linarith
    have s4 : u * tiny ≤ 1 := by have := mul_le_mul hu' ht1 ht.le (by norm_num); linarith
    linarith
  have hp : |(a + α) * (b + β)| ≤ 2 ^ 902 := by
    have := abs_sub_abs_le_abs_sub ((a + α) * (b + β)) (a * b)
    rw [abs_mul a b] at this
    linarith
  have ep := M.err ((a + α) * (b + β)) (by linarith)
  have hpa : |(a + α) * (b + β)| ≤ |a| * |b| + (u * (|a| * |b|) + u * (tiny * |a|)
      + (u * (|a| * |b|) + u * (tiny * |b|)) + u * (|a| + tiny) * (u * (|b| + tiny))) := by
    have := abs_sub_abs_le_abs_sub ((a + α) * (b + β)) (a * b)
    rw [abs_mul a b] at this
    linarith
  have e2 : M.fl ((a + α) * (b + β)) - a * b
      = (M.fl ((a + α) * (b + β)) - (a + α) * (b + β)) + ((a + α) * (b + β) - a * b) := by ring
  rw [e2]
  have k4 := abs_add_le (M.fl ((a + α) * (b + β)) - (a + α) * (b + β)) ((a + α) * (b + β) - a * b)
  have k5 := mul_le_mul_of_nonneg_left hpa hu.le
  -- `u` times the first-order error
  have p1 : 0 ≤ u * (|a| * |b|) := by positivity
  have p2 : 0 ≤ u * (tiny * |a|) := by positivity
  have p3 : 0 ≤ u * (tiny * |b|) := by positivity
  have p4 : 0 ≤ u * tiny := by positivity
  have k6 : u * (u * (|a| * |b|) + u * (tiny * |a|) + (u * (|a| * |b|) + u * (tiny * |b|))
      + u * (|a| + tiny) * (u * (|b| + tiny))) ≤ 0.003 * (u * (|a| * |b|))
        + 0.003 * (u * (tiny * |a|)) + 0.003 * (u * (tiny * |b|)) + 0.003 * (u * tiny) := by
    have h0 : 0 ≤ u * (|a| * |b|) + u * (tiny * |a|) + (u * (|a| * |b|) + u * (tiny * |b|))
        + u * (|a| + tiny) * (u * (|b| + tiny)) := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : u ≤ 0.001) h0
    linarith
  have e3 : u * (|(a + α) * (b + β)| + tiny) = u * |(a + α) * (b + β)| + u * tiny := by ring
  have e4 : 3.01 * u * (|a| * |b|) + 1.01 * u * (tiny * |a| + tiny * |b|) + 1.01 * u * tiny
      = 3.01 * (u * (|a| * |b|)) + 1.01 * (u * (tiny * |a|)) + 1.01 * (u * (tiny * |b|))
        + 1.01 * (u * tiny) := by ring
  have e5 : u * (|a| * |b| + (u * (|a| * |b|) + u * (tiny * |a|)
      + (u * (|a| * |b|) + u * (tiny * |b|)) + u * (|a| + tiny) * (u * (|b| + tiny))))
      = u * (|a| * |b|) + u * (u * (|a| * |b|) + u * (tiny * |a|)
      + (u * (|a| * |b|) + u * (tiny * |b|)) + u * (|a| + tiny) * (u * (|b| + tiny))) := by ring
  linarith
