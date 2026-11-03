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

/-- A rounded product of rounded values at most `2⁴⁵⁰`. -/
theorem StdModel.prod_abs_le {a b : ℝ} (ha : |a| ≤ 2 ^ 450) (hb : |b| ≤ 2 ^ 450) :
    |M.fl (M.fl a * M.fl b)| ≤ 2 ^ 901 := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have h1 := M.prod_step ha hb
  have h2 := abs_sub_abs_le_abs_sub (M.fl (M.fl a * M.fl b)) (a * b)
  rw [abs_mul] at h2
  have hab : |a| * |b| ≤ 2 ^ 900 := by
    have := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    have : (2 : ℝ) ^ 450 * 2 ^ 450 = 2 ^ 900 := by norm_num
    linarith
  have s1 : 3.01 * u * (|a| * |b|) ≤ 2 ^ 898 := by
    have k := mul_le_mul (by linarith : 3.01 * u ≤ 1 / 2 ^ 51) hab (by positivity) (by norm_num)
    have : (1 : ℝ) / 2 ^ 51 * 2 ^ 900 ≤ 2 ^ 898 := by norm_num
    linarith
  have s2 : 1.01 * u * (tiny * |a| + tiny * |b|) ≤ 2 ^ 898 := by
    have k1 : tiny * |a| ≤ 1 * 2 ^ 450 := mul_le_mul ht1 ha (abs_nonneg _) (by norm_num)
    have k2 : tiny * |b| ≤ 1 * 2 ^ 450 := mul_le_mul ht1 hb (abs_nonneg _) (by norm_num)
    have k := mul_le_mul (by linarith : 1.01 * u ≤ 1) (add_le_add k1 k2) (by positivity) (by norm_num)
    have : (1 : ℝ) * (1 * 2 ^ 450 + 1 * 2 ^ 450) ≤ 2 ^ 898 := by norm_num
    linarith
  have s3 : 1.01 * u * tiny ≤ 1 := by
    have := mul_le_mul (by linarith : 1.01 * u ≤ 1) ht1 ht.le (by norm_num); linarith
  have : (2 : ℝ) ^ 900 + 2 ^ 898 + 2 ^ 898 + 1 ≤ 2 ^ 901 := by norm_num
  linarith

/-- The computed mean is within `6 u Σ (|x| + tiny)` of the exact one. -/
theorem StdModel.mean6 {xs : List ℝ} (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32)
    (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) :
    |M.mean xs - xs.sum / xs.length| ≤ 6 * u * mag xs := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hn1 : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn0 : (0 : ℝ) < xs.length := by linarith
  have hN' : (xs.length : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hn2u : ((xs.length + 2 : ℕ) : ℝ) * u ≤ 1 / 2 := by push_cast; nlinarith
  have hg := gamma_le_two hn2u
  have hgn := gamma_le_two (k := xs.length) (by nlinarith)
  have hmagb : mag xs ≤ 2 ^ 32 * (2 ^ 399 + 1) := by
    have := mag_le_of_bound hB
    have : (xs.length : ℝ) * (2 ^ 399 + tiny) ≤ 2 ^ 32 * (2 ^ 399 + 1) :=
      mul_le_mul hN' (by linarith) (by positivity) (by norm_num)
    linarith
  have hov : (1 + gamma xs.length) * mag xs ≤ maxFinite := by
    have : 1 + gamma xs.length ≤ 2 := by nlinarith
    have h0 := mag_nonneg xs
    have := mul_le_mul this hmagb h0 (by norm_num)
    have : (2 : ℝ) * (2 ^ 32 * (2 ^ 399 + 1)) ≤ 2 ^ 1023 := by norm_num
    linarith
  have havg := M.avg_error hne (by push_cast; nlinarith) hov
  unfold StdModel.mean
  calc _ ≤ gamma (xs.length + 2) * mag xs / xs.length := havg
    _ ≤ 2 * ((xs.length + 2 : ℕ) : ℝ) * u * mag xs / xs.length := by
        gcongr; exact mag_nonneg xs
    _ ≤ 6 * u * mag xs := by
        rw [div_le_iff₀ hn0]; push_cast
        have : 0 ≤ u * mag xs := mul_nonneg hu.le (mag_nonneg xs)
        nlinarith

/-- The arithmetic at the end of `twoPass_cov_rel`, with `v = n u`. -/
theorem tpc_arith {n K H G X P0 P1 W tT exy : ℝ} (hn1 : 1 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21)
    (hP0 : 0 ≤ P0) (hP1 : 0 ≤ P1) (hW : 0 ≤ W) (hK0 : 0 ≤ K) (htT0 : 0 ≤ tT)
    (hK : K ≤ P0 + 12 * (n * u) * W + 36 * (n * u) ^ 2 * W)
    (htT : tT ≤ P1 + 12 * (n * u) * W)
    (hH : H = 3.01 * u * K + 1.01 * u * tT + 1.01 * n * u * tiny)
    (hG : G ≤ 2 * n * u * (K + H + n * tiny))
    (hexy : exy ≤ 36 * (n * u) ^ 2 * W) (hX : X ≤ G + H + exy) :
    X ≤ 6 * n * u * P0 + 1.1 * u * P1 + 120 * n ^ 2 * u ^ 2 * W + 4 * n ^ 2 * u * tiny := by
  have hu := u_pos
  have ht := tiny_pos
  obtain ⟨v, hv⟩ : ∃ v, v = n * u := ⟨_, rfl⟩
  rw [← hv] at hnu hK htT hexy
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have huv : u ≤ v := by rw [hv]; nlinarith
  have hn0 : 0 ≤ n := by linarith
  -- `H`
  have a1 : u * (v * W) ≤ v * (v * W) := mul_le_mul_of_nonneg_right huv (by positivity)
  have a2 : u * (v ^ 2 * W) ≤ 0.001 * (v * (v * W)) := by
    have : u * (v ^ 2 * W) = u * (v * (v * W)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hK' := mul_le_mul_of_nonneg_left hK hu.le
  have htT' := mul_le_mul_of_nonneg_left htT hu.le
  have hvt : n * u * tiny = v * tiny := by rw [hv]
  have hH' : H ≤ 3.01 * (u * P0) + 1.01 * (u * P1) + 49 * (v * (v * W)) + 1.01 * (v * tiny) := by
    rw [hH]
    have e1 : u * (P0 + 12 * v * W + 36 * v ^ 2 * W) = u * P0 + 12 * (u * (v * W)) + 36 * (u * (v ^ 2 * W)) := by
      ring
    have e2 : u * (P1 + 12 * v * W) = u * P1 + 12 * (u * (v * W)) := by ring
    rw [e1] at hK'; rw [e2] at htT'
    have e3 : 1.01 * n * u * tiny = 1.01 * (v * tiny) := by rw [hv]; ring
    have p : 0 ≤ v * (v * W) := by positivity
    nlinarith
  -- `G`
  have hG' : G ≤ 2 * (v * P0) + 0.001 * (u * P0) + 0.001 * (u * P1) + 26 * (v * (v * W))
      + 0.001 * (v * tiny) + 2 * (n * (v * tiny)) := by
    have e : 2 * n * u * (K + H + n * tiny) = 2 * (v * K) + 2 * (v * H) + 2 * (n * (v * tiny)) := by
      rw [hv]; ring
    rw [e] at hG
    have b1 : v * K ≤ v * P0 + 12 * (v * (v * W)) + 36 * (v * (v ^ 2 * W)) := by
      have := mul_le_mul_of_nonneg_left hK hv0
      have e2 : v * (P0 + 12 * v * W + 36 * v ^ 2 * W) = v * P0 + 12 * (v * (v * W))
          + 36 * (v * (v ^ 2 * W)) := by ring
      linarith
    have b2 : v * (v ^ 2 * W) ≤ 0.001 * (v * (v * W)) := by
      have : v * (v ^ 2 * W) = v * (v * (v * W)) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hH0 : 0 ≤ H := by rw [hH]; positivity
    have b3 : v * H ≤ v * (3.01 * (u * P0) + 1.01 * (u * P1) + 49 * (v * (v * W)) + 1.01 * (v * tiny)) :=
      mul_le_mul_of_nonneg_left hH' hv0
    have b4 : v * (3.01 * (u * P0) + 1.01 * (u * P1) + 49 * (v * (v * W)) + 1.01 * (v * tiny))
        ≤ 0.0004 * (u * P0) + 0.0004 * (u * P1) + 0.0004 * (v * (v * W)) + 0.0004 * (v * tiny) := by
      have h0 : 0 ≤ 3.01 * (u * P0) + 1.01 * (u * P1) + 49 * (v * (v * W)) + 1.01 * (v * tiny) := by
        positivity
      have := mul_le_mul_of_nonneg_right (by linarith : v ≤ 1 / 2 ^ 21) h0
      have : 0 ≤ u * P0 := by positivity
      have : 0 ≤ u * P1 := by positivity
      have : 0 ≤ v * (v * W) := by positivity
      have : 0 ≤ v * tiny := by positivity
      linarith
    have : 0 ≤ u * P0 := by positivity
    have : 0 ≤ u * P1 := by positivity
    have : 0 ≤ v * (v * W) := by positivity
    have : 0 ≤ v * tiny := by positivity
    have : 0 ≤ v * P0 := by positivity
    linarith
  -- assemble
  have c1 : u * P0 ≤ v * P0 := mul_le_mul_of_nonneg_right huv hP0
  have c2 : v * tiny ≤ n * (v * tiny) := le_mul_of_one_le_left (by positivity) hn1
  have c3 : exy ≤ 36 * (v * (v * W)) := by
    have : 36 * v ^ 2 * W = 36 * (v * (v * W)) := by ring
    linarith
  have e1 : 6 * n * u * P0 = 6 * (v * P0) := by rw [hv]; ring
  have e2 : 120 * n ^ 2 * u ^ 2 * W = 120 * (v * (v * W)) := by rw [hv]; ring
  have e3 : 4 * n ^ 2 * u * tiny = 4 * (n * (v * tiny)) := by rw [hv]; ring
  have e4 : 1.1 * u * P1 = 1.1 * (u * P1) := by ring
  rw [e1, e2, e3, e4]
  have : 0 ≤ u * P1 := by positivity
  have : 0 ≤ v * (v * W) := by positivity
  have : 0 ≤ v * P0 := by positivity
  have : 0 ≤ n * (v * tiny) := by positivity
  have : 0 ≤ v * tiny := by positivity
  linarith

theorem sum_lin {α : Type*} (l : List α) (f g : α → ℝ) (c1 c2 c3 : ℝ) :
    (l.map fun x => c1 * f x + c2 * g x + c3).sum
      = c1 * (l.map f).sum + c2 * (l.map g).sum + l.length * c3 := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- `n tiny² ≤ Σ (|x| + tiny)²`. -/
theorem len_tiny_sq_le {α : Type*} (l : List α) (f : α → ℝ) :
    l.length * tiny ^ 2 ≤ (l.map fun x => (|f x| + tiny) ^ 2).sum := by
  have ht := tiny_pos
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]; push_cast
    have : tiny ^ 2 ≤ (|f x| + tiny) ^ 2 := by
      have := abs_nonneg (f x); gcongr; linarith
    linarith

/-- `Σ (xᵢ − m)² = S_xx + n (m − x̄)²`. -/
theorem sum_sq_dev_fst {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (m : ℝ) :
    (ps.map fun p => (p.1 - m) * (p.1 - m)).sum
      = comoment (dupL (ps.map Prod.fst)) + ps.length * (m - mx ps) ^ 2 := by
  have h := sum_dev_shift (ps := dupL (ps.map Prod.fst)) (by simpa [dupL] using hne) m m
  rw [my_dupL, mx_dupL_fst, dupL_length, List.length_map] at h
  have e : comoment (dupL (ps.map Prod.fst)) + ps.length * (m - mx ps) ^ 2
      = comoment (dupL (ps.map Prod.fst)) + ps.length * (m - mx ps) * (m - mx ps) := by ring
  rw [e, ← h]
  simp [dupL, List.map_map, Function.comp_def]

theorem sum_sq_dev_snd {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (m : ℝ) :
    (ps.map fun p => (p.2 - m) * (p.2 - m)).sum
      = comoment (dupL (ps.map Prod.snd)) + ps.length * (m - my ps) ^ 2 := by
  have h := sum_dev_shift (ps := dupL (ps.map Prod.snd)) (by simpa [dupL] using hne) m m
  rw [my_dupL, mx_dupL_snd, dupL_length, List.length_map] at h
  have e : comoment (dupL (ps.map Prod.snd)) + ps.length * (m - my ps) ^ 2
      = comoment (dupL (ps.map Prod.snd)) + ps.length * (m - my ps) * (m - my ps) := by ring
  rw [e, ← h]
  simp [dupL, List.map_map, Function.comp_def]

theorem sum_two {α : Type*} (l : List α) (f g : α → ℝ) (c : ℝ) :
    (l.map fun x => c * f x + c * g x).sum = c * (l.map f).sum + c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem mag_eq (xs : List ℝ) : mag xs = (xs.map abs).sum + xs.length * tiny := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [mag_cons, ih, List.map_cons, List.sum_cons, List.length_cons]; push_cast; ring

/-- `√(n ε²) ≤ 6 n u √Q` from `|ε| ≤ 6 u A` and `A² ≤ n Q`. -/
theorem ex_le {n ε A Q : ℝ} (hn : 0 ≤ n) (hQ : 0 ≤ Q) (hA : A ^ 2 ≤ n * Q)
    (hε : |ε| ≤ 6 * u * A) : √(n * ε ^ 2) ≤ 6 * (n * u) * √Q := by
  have hu := u_pos
  rw [Real.sqrt_le_left (by positivity)]
  have a : ε ^ 2 ≤ (6 * u * A) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hε 2
  have b := mul_le_mul_of_nonneg_left a hn
  have e1 : n * (6 * u * A) ^ 2 = 36 * u ^ 2 * (n * A ^ 2) := by ring
  have e2 : (6 * (n * u) * √Q) ^ 2 = 36 * u ^ 2 * (n * (n * Q)) := by
    rw [mul_pow, Real.sq_sqrt hQ]; ring
  rw [e2]
  have c := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hn) (by positivity : (0 : ℝ) ≤ 36 * u ^ 2)
  linarith

/-- `tiny · T ≤ √Q' (√S + √(n ε²))` from `T² ≤ n (S + n ε²)` and `n tiny² ≤ Q'`. -/
theorem tT_le {n T S ε Q : ℝ} (hn : 0 ≤ n) (_hT0 : 0 ≤ T) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hT : T ^ 2 ≤ n * (S + n * ε ^ 2)) (htQ : n * tiny ^ 2 ≤ Q) :
    tiny * T ≤ √Q * (√S + √(n * ε ^ 2)) := by
  have ht := tiny_pos
  have hZ : 0 ≤ S + n * ε ^ 2 := by positivity
  have h1 : (tiny * T) ^ 2 ≤ (√Q * (√S + √(n * ε ^ 2))) ^ 2 := by
    have a : (tiny * T) ^ 2 ≤ (n * tiny ^ 2) * (S + n * ε ^ 2) := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ tiny ^ 2)
      have e : (tiny * T) ^ 2 = tiny ^ 2 * T ^ 2 := by ring
      have e2 : tiny ^ 2 * (n * (S + n * ε ^ 2)) = (n * tiny ^ 2) * (S + n * ε ^ 2) := by ring
      linarith
    have b : (n * tiny ^ 2) * (S + n * ε ^ 2) ≤ Q * (S + n * ε ^ 2) := mul_le_mul_of_nonneg_right htQ hZ
    have c : Q * (S + n * ε ^ 2) ≤ (√Q * (√S + √(n * ε ^ 2))) ^ 2 := by
      have hs := Real.sq_sqrt hS
      have he := Real.sq_sqrt (by positivity : 0 ≤ n * ε ^ 2)
      have p : 0 ≤ √S * √(n * ε ^ 2) := by positivity
      rw [mul_pow, Real.sq_sqrt hQ]
      apply mul_le_mul_of_nonneg_left _ hQ
      nlinarith
    linarith
  exact (abs_le_of_sq_le_sq' h1 (by positivity)).2

/-- `K ≤ (√S_x + √(n ε_x²))(√S_y + √(n ε_y²))` from `K² ≤ (S_x + n ε_x²)(S_y + n ε_y²)`. -/
theorem K_le {K Sx Sy ax ay : ℝ} (_hK0 : 0 ≤ K) (hSx : 0 ≤ Sx) (hSy : 0 ≤ Sy) (hax : 0 ≤ ax)
    (hay : 0 ≤ ay) (hK : K ^ 2 ≤ (Sx + ax) * (Sy + ay)) :
    K ≤ (√Sx + √ax) * (√Sy + √ay) := by
  have h1 : (Sx + ax) * (Sy + ay) ≤ ((√Sx + √ax) * (√Sy + √ay)) ^ 2 := by
    have a : Sx + ax ≤ (√Sx + √ax) ^ 2 := by
      have := Real.sq_sqrt hSx; have := Real.sq_sqrt hax
      have : 0 ≤ √Sx * √ax := by positivity
      nlinarith
    have b : Sy + ay ≤ (√Sy + √ay) ^ 2 := by
      have := Real.sq_sqrt hSy; have := Real.sq_sqrt hay
      have : 0 ≤ √Sy * √ay := by positivity
      nlinarith
    calc (Sx + ax) * (Sy + ay) ≤ (√Sx + √ax) ^ 2 * (√Sy + √ay) ^ 2 :=
          mul_le_mul a b (by positivity) (by positivity)
      _ = _ := by ring
  exact (abs_le_of_sq_le_sq' (le_trans hK h1) (by positivity)).2

set_option maxHeartbeats 2000000 in
/-- The second pass, from any means within `6 u A` of the exact ones. -/
theorem StdModel.tpc_core {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32)
    (hB : Bounded (2 ^ 399) ps) {mhx mhy : ℝ}
    (hεx : |mhx - mx ps| ≤ 6 * u * mag (ps.map Prod.fst))
    (hεy : |mhy - my ps| ≤ 6 * u * mag (ps.map Prod.snd)) :
    |M.sum (ps.map fun p => M.fl (M.fl (p.1 - mhx) * M.fl (p.2 - mhy))) - comoment ps|
      ≤ 6 * ps.length * u * (√(comoment (dupL (ps.map Prod.fst))) * √(comoment (dupL (ps.map Prod.snd))))
        + 1.1 * u * (√((ps.map fun p => (|p.2| + tiny) ^ 2).sum) * √(comoment (dupL (ps.map Prod.fst)))
          + √((ps.map fun p => (|p.1| + tiny) ^ 2).sum) * √(comoment (dupL (ps.map Prod.snd))))
        + 120 * ps.length ^ 2 * u ^ 2 * (√((ps.map fun p => (|p.1| + tiny) ^ 2).sum)
          * √((ps.map fun p => (|p.2| + tiny) ^ 2).sum))
        + 4 * ps.length ^ 2 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  obtain ⟨⟨hAx0, hAxb, -, -, hmxb, hSx0, -⟩, ⟨hAy0, hAyb, -, -, hmyb, hSy0, -⟩⟩ :=
    pair_facts hne hN hB
  -- names
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ps.length := ⟨_, rfl⟩
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast List.length_pos_iff.mpr hne
  have hN' : n ≤ 2 ^ 32 := by rw [hn]; exact_mod_cast hN
  have hnu : n * u ≤ 1 / 2 ^ 21 := by
    calc n * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  obtain ⟨Ax, hAx⟩ : ∃ A, A = mag (ps.map Prod.fst) := ⟨_, rfl⟩
  obtain ⟨Ay, hAy⟩ : ∃ A, A = mag (ps.map Prod.snd) := ⟨_, rfl⟩
  obtain ⟨Sx, hSx⟩ : ∃ S, S = comoment (dupL (ps.map Prod.fst)) := ⟨_, rfl⟩
  obtain ⟨Sy, hSy⟩ : ∃ S, S = comoment (dupL (ps.map Prod.snd)) := ⟨_, rfl⟩
  obtain ⟨Qx, hQx⟩ : ∃ Q, Q = (ps.map fun p => (|p.1| + tiny) ^ 2).sum := ⟨_, rfl⟩
  obtain ⟨Qy, hQy⟩ : ∃ Q, Q = (ps.map fun p => (|p.2| + tiny) ^ 2).sum := ⟨_, rfl⟩
  have hAQx : Ax ^ 2 ≤ n * Qx := by
    have := mag_sq_le (ps.map Prod.fst)
    simpa [hAx, hn, hQx, List.map_map, Function.comp_def] using this
  have hAQy : Ay ^ 2 ≤ n * Qy := by
    have := mag_sq_le (ps.map Prod.snd)
    simpa [hAy, hn, hQy, List.map_map, Function.comp_def] using this
  have hQx0 : 0 ≤ Qx := by
    rw [hQx]; exact List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hQy0 : 0 ≤ Qy := by
    rw [hQy]; exact List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hSQx : Sx ≤ Qx := by
    rw [hSx, hQx]
    refine le_trans (comoment_dupL_le _) ?_
    simp only [List.map_map, Function.comp_def]
    apply List.sum_le_sum; intro p _
    have := abs_nonneg p.1
    calc p.1 ^ 2 = |p.1| ^ 2 := (sq_abs _).symm
      _ ≤ (|p.1| + tiny) ^ 2 := by gcongr; linarith
  have hSQy : Sy ≤ Qy := by
    rw [hSy, hQy]
    refine le_trans (comoment_dupL_le _) ?_
    simp only [List.map_map, Function.comp_def]
    apply List.sum_le_sum; intro p _
    have := abs_nonneg p.2
    calc p.2 ^ 2 = |p.2| ^ 2 := (sq_abs _).symm
      _ ≤ (|p.2| + tiny) ^ 2 := by gcongr; linarith
  have htQx : n * tiny ^ 2 ≤ Qx := by rw [hn, hQx]; exact len_tiny_sq_le ps Prod.fst
  have htQy : n * tiny ^ 2 ≤ Qy := by rw [hn, hQy]; exact len_tiny_sq_le ps Prod.snd
  rw [← hAx] at hεx hAx0 hAxb
  rw [← hAy] at hεy hAy0 hAyb
  rw [← hSx] at hSx0
  rw [← hSy] at hSy0
  -- the deviations
  obtain ⟨εx, hεx'⟩ : ∃ e, e = mhx - mx ps := ⟨_, rfl⟩
  obtain ⟨εy, hεy'⟩ : ∃ e, e = mhy - my ps := ⟨_, rfl⟩
  rw [← hεx'] at hεx
  rw [← hεy'] at hεy
  have hmhx : |mhx| ≤ 2 ^ 401 := by
    have h1 : u * Ax ≤ 1 / 2 ^ 53 * 2 ^ 432 := mul_le_mul hu' hAxb hAx0 (by norm_num)
    have h2 : (6 : ℝ) * (1 / 2 ^ 53 * 2 ^ 432) + 2 ^ 400 ≤ 2 ^ 401 := by norm_num
    have : mhx = mx ps + εx := by rw [hεx']; ring
    rw [this]; have := abs_add_le (mx ps) εx; linarith
  have hmhy : |mhy| ≤ 2 ^ 401 := by
    have h1 : u * Ay ≤ 1 / 2 ^ 53 * 2 ^ 432 := mul_le_mul hu' hAyb hAy0 (by norm_num)
    have h2 : (6 : ℝ) * (1 / 2 ^ 53 * 2 ^ 432) + 2 ^ 400 ≤ 2 ^ 401 := by norm_num
    have : mhy = my ps + εy := by rw [hεy']; ring
    rw [this]; have := abs_add_le (my ps) εy; linarith
  have hdx : ∀ p ∈ ps, |p.1 - mhx| ≤ 2 ^ 450 := by
    intro p hp; have := abs_sub p.1 mhx; have := (hB p hp).1; linarith
  have hdy : ∀ p ∈ ps, |p.2 - mhy| ≤ 2 ^ 450 := by
    intro p hp; have := abs_sub p.2 mhy; have := (hB p hp).2; linarith
  -- the exact sums
  have hsg : (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum = comoment ps + n * εx * εy := by
    rw [sum_dev_shift hne, hn, hεx', hεy']
  have hZx : (ps.map fun p => (p.1 - mhx) * (p.1 - mhx)).sum = Sx + n * εx ^ 2 := by
    rw [sum_sq_dev_fst hne, hSx, hn, hεx']
  have hZy : (ps.map fun p => (p.2 - mhy) * (p.2 - mhy)).sum = Sy + n * εy ^ 2 := by
    rw [sum_sq_dev_snd hne, hSy, hn, hεy']
  -- `K = Σ |d_x| |d_y|`, `T_x = Σ |d_x|`
  obtain ⟨K, hK⟩ : ∃ K, K = (ps.map fun p => |p.1 - mhx| * |p.2 - mhy|).sum := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hK2 : K ^ 2 ≤ (Sx + n * εx ^ 2) * (Sy + n * εy ^ 2) := by
    have h := list_cs (ps.map fun p => (|p.1 - mhx|, |p.2 - mhy|))
    simp only [List.map_map, Function.comp_def, abs_mul_abs_self] at h
    rw [hK, ← hZx, ← hZy]; exact h
  obtain ⟨Tx, hTx⟩ : ∃ T, T = (ps.map fun p => |p.1 - mhx|).sum := ⟨_, rfl⟩
  obtain ⟨Ty, hTy⟩ : ∃ T, T = (ps.map fun p => |p.2 - mhy|).sum := ⟨_, rfl⟩
  have hTx2 : Tx ^ 2 ≤ n * (Sx + n * εx ^ 2) := by
    have h := sq_abs_sum_le (ps.map fun p => p.1 - mhx)
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [← hn] at h
    rw [hTx, ← hZx]
    have e : (ps.map fun p => (p.1 - mhx) * (p.1 - mhx)) = ps.map fun p => (p.1 - mhx) ^ 2 := by
      congr 1; funext p; ring
    rw [e]; exact h
  have hTy2 : Ty ^ 2 ≤ n * (Sy + n * εy ^ 2) := by
    have h := sq_abs_sum_le (ps.map fun p => p.2 - mhy)
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [← hn] at h
    rw [hTy, ← hZy]
    have e : (ps.map fun p => (p.2 - mhy) * (p.2 - mhy)) = ps.map fun p => (p.2 - mhy) ^ 2 := by
      congr 1; funext p; ring
    rw [e]; exact h
  have hTx0 : 0 ≤ Tx := by
    rw [hTx]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hTy0 : 0 ≤ Ty := by
    rw [hTy]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hexb := ex_le (by linarith) hQx0 hAQx hεx
  have heyb := ex_le (by linarith) hQy0 hAQy hεy
  have hTxb := tT_le (by linarith) hTx0 hSx0 hQy0 hTx2 htQy
  have hTyb := tT_le (by linarith) hTy0 hSy0 hQx0 hTy2 htQx
  have hKb := K_le hK0 hSx0 hSy0 (by positivity) (by positivity) hK2
  have hsq : √Sx ≤ √Qx := Real.sqrt_le_sqrt hSQx
  have hsqy : √Sy ≤ √Qy := Real.sqrt_le_sqrt hSQy
  -- the rounding of each product
  have hstep : ∀ p ∈ ps, |M.fl (M.fl (p.1 - mhx) * M.fl (p.2 - mhy)) - (p.1 - mhx) * (p.2 - mhy)|
      ≤ 1 * (3.01 * u * (|p.1 - mhx| * |p.2 - mhy|)
        + 1.01 * u * (tiny * |p.1 - mhx| + tiny * |p.2 - mhy|) + 1.01 * u * tiny) := by
    intro p hp; rw [one_mul]; exact M.prod_step (hdx p hp) (hdy p hp)
  have hH := abs_sum_map_sub_le (fun p : ℝ × ℝ => M.fl (M.fl (p.1 - mhx) * M.fl (p.2 - mhy)))
    (fun p => (p.1 - mhx) * (p.2 - mhy))
    (fun p => 3.01 * u * (|p.1 - mhx| * |p.2 - mhy|)
      + 1.01 * u * (tiny * |p.1 - mhx| + tiny * |p.2 - mhy|) + 1.01 * u * tiny) 1 ps hstep
  rw [one_mul] at hH
  have hl := sum_lin ps (fun p => |p.1 - mhx| * |p.2 - mhy|)
    (fun p => tiny * |p.1 - mhx| + tiny * |p.2 - mhy|) (3.01 * u) (1.01 * u) (1.01 * u * tiny)
  have h2 := sum_two ps (fun p => |p.1 - mhx|) (fun p => |p.2 - mhy|) tiny
  rw [← hK] at hl
  rw [← hTx, ← hTy] at h2
  rw [h2, ← hn] at hl
  obtain ⟨H, hHd⟩ : ∃ H, H = 3.01 * u * K + 1.01 * u * (tiny * Tx + tiny * Ty) + 1.01 * n * u * tiny :=
    ⟨_, rfl⟩
  have hsh : (ps.map fun p => 3.01 * u * (|p.1 - mhx| * |p.2 - mhy|)
      + 1.01 * u * (tiny * |p.1 - mhx| + tiny * |p.2 - mhy|) + 1.01 * u * tiny).sum = H := by
    rw [hl, hHd]; ring
  rw [hsh] at hH
  -- the magnitudes of the rounded products
  obtain ⟨P, hP⟩ : ∃ P, P = ps.map fun p => M.fl (M.fl (p.1 - mhx) * M.fl (p.2 - mhy)) := ⟨_, rfl⟩
  rw [← hP] at hH ⊢
  have hPa : (P.map abs).sum ≤ K + H := by
    rw [hP, List.map_map, ← hsh, hK, ← List.sum_map_add]
    apply List.sum_le_sum
    intro p hp
    simp only [Function.comp_apply]
    have := M.prod_step (hdx p hp) (hdy p hp)
    have := abs_sub_abs_le_abs_sub (M.fl (M.fl (p.1 - mhx) * M.fl (p.2 - mhy))) ((p.1 - mhx) * (p.2 - mhy))
    rw [abs_mul ((p.1 - mhx))] at this
    linarith
  have hPlen : P.length = ps.length := by rw [hP, List.length_map]
  have hmagP : mag P ≤ K + H + n * tiny := by
    rw [mag_eq, hPlen, ← hn]; linarith
  have hPb : ∀ y ∈ P, |y| ≤ 2 ^ 901 := by
    intro y hy
    rw [hP] at hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact M.prod_abs_le (hdx p hp) (hdy p hp)
  -- the sum, rounded
  have hgn := gamma_le_two (k := ps.length) (by rw [← hn]; linarith)
  have hγ0 := gamma_nonneg (n := ps.length) (by rw [← hn]; linarith)
  have hmagPb : mag P ≤ 2 ^ 32 * (2 ^ 901 + 1) := by
    have := mag_le_of_bound hPb
    rw [hPlen, ← hn] at this
    have : n * (2 ^ 901 + tiny) ≤ 2 ^ 32 * (2 ^ 901 + 1) := mul_le_mul hN' (by linarith) (by positivity) (by norm_num)
    linarith
  have hsum := M.sum_error (xs := P) (by rw [hPlen, ← hn]; linarith) (by
    rw [hPlen]
    have : 1 + gamma ps.length ≤ 2 := by rw [← hn] at hgn; nlinarith
    have := mul_le_mul this hmagPb (mag_nonneg P) (by norm_num)
    have : (2 : ℝ) * (2 ^ 32 * (2 ^ 901 + 1)) ≤ 2 ^ 1023 := by norm_num
    linarith)
  rw [hPlen] at hsum
  rw [← hn] at hgn
  have hG : |M.sum P - P.sum| ≤ 2 * n * u * (K + H + n * tiny) := by
    refine le_trans hsum ?_
    exact mul_le_mul hgn hmagP (mag_nonneg P) (by positivity)
  -- assemble
  have hX : |M.sum P - comoment ps| ≤ |M.sum P - P.sum| + H + n * |εx| * |εy| := by
    have e : M.sum P - comoment ps = (M.sum P - P.sum) + (P.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum)
        + ((ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps) := by ring
    rw [e]
    have k1 := abs_add_le ((M.sum P - P.sum) + (P.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum))
      ((ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps)
    have k2 := abs_add_le (M.sum P - P.sum) (P.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum)
    have k3 : |(ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps| = n * |εx| * |εy| := by
      rw [hsg, show comoment ps + n * εx * εy - comoment ps = n * εx * εy by ring, abs_mul, abs_mul,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
    linarith only [k1, k2, k3, hH]
  have hexy : n * |εx| * |εy| ≤ 36 * (n * u) ^ 2 * (√Qx * √Qy) := by
    have a := mul_le_mul hεx hεy (abs_nonneg _) (by positivity)
    have b := aa_le (by linarith) hQx0 hQy0 hAx0 hAy0 hAQx hAQy
    rw [Real.sqrt_mul hQx0] at b
    have c : n * (|εx| * |εy|) ≤ n * (6 * u * Ax * (6 * u * Ay)) := mul_le_mul_of_nonneg_left a (by linarith)
    have d : n * (6 * u * Ax * (6 * u * Ay)) = 36 * u ^ 2 * n * (Ax * Ay) := by ring
    have e := mul_le_mul_of_nonneg_left b (by positivity : (0 : ℝ) ≤ 36 * u ^ 2 * n)
    have f : 36 * u ^ 2 * n * (n * (√Qx * √Qy)) = 36 * (n * u) ^ 2 * (√Qx * √Qy) := by ring
    have g : n * |εx| * |εy| = n * (|εx| * |εy|) := by ring
    linarith
  -- the terms of `tpc_arith`
  have hv0 : 0 ≤ n * u := by positivity
  have hW0 : 0 ≤ √Qx * √Qy := by positivity
  have hKt : K ≤ √Sx * √Sy + 12 * (n * u) * (√Qx * √Qy) + 36 * (n * u) ^ 2 * (√Qx * √Qy) := by
    have a1 : √Sx * √(n * εy ^ 2) ≤ √Qx * (6 * (n * u) * √Qy) :=
      mul_le_mul hsq heyb (by positivity) (by positivity)
    have a2 : √(n * εx ^ 2) * √Sy ≤ 6 * (n * u) * √Qx * √Qy :=
      mul_le_mul hexb hsqy (by positivity) (by positivity)
    have a3 : √(n * εx ^ 2) * √(n * εy ^ 2) ≤ 6 * (n * u) * √Qx * (6 * (n * u) * √Qy) :=
      mul_le_mul hexb heyb (by positivity) (by positivity)
    have e : (√Sx + √(n * εx ^ 2)) * (√Sy + √(n * εy ^ 2)) = √Sx * √Sy + √Sx * √(n * εy ^ 2)
        + √(n * εx ^ 2) * √Sy + √(n * εx ^ 2) * √(n * εy ^ 2) := by ring
    linarith only [hKb, e, a1, a2, a3]
  have htT : tiny * Tx + tiny * Ty ≤ (√Qy * √Sx + √Qx * √Sy) + 12 * (n * u) * (√Qx * √Qy) := by
    have a1 : √Qy * √(n * εx ^ 2) ≤ √Qy * (6 * (n * u) * √Qx) := mul_le_mul_of_nonneg_left hexb (by positivity)
    have a2 : √Qx * √(n * εy ^ 2) ≤ √Qx * (6 * (n * u) * √Qy) := mul_le_mul_of_nonneg_left heyb (by positivity)
    linarith only [hTxb, hTyb, a1, a2]
  have := tpc_arith hn1 hnu (by positivity) (by positivity) hW0 hK0 (by positivity) hKt htT hHd hG hexy hX
  rw [← hSx, ← hSy, ← hQx, ← hQy, ← hn]
  exact this
