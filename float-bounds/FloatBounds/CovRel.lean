module

public import FloatBounds.MergeRel
public import FloatBounds.Welford

/-!
# The covariance, to first order in the spread (#85)

The analogue of `WelfordRel.lean` and `MergeRel.lean` for pairs: DuckDB's
`COVAR_*` (`welfordStep` and `chan` of `Welford.lean`), in any plan of
updates and merges.

The bounds are in `R = √(S_xx S_yy)`: by Cauchy–Schwarz the co-moment of
any part satisfies `|C| ≤ R`, and so does every increment of an update or a
merge.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- Rounding the increment `q ≈ ΔC` and adding it to `Ĉ ≈ C`, when `|ΔC|` and
`|C + ΔC|` are at most `R`. -/
theorem StdModel.ctail {q ΔC C Ch G P R AA : ℝ} (hP : 0 ≤ P) (hR : 0 ≤ R) (hAA : 0 ≤ AA)
    (hq : |q - ΔC| ≤ 8 * u * P + 4 * u * R + 81 * u ^ 2 * AA) (hΔ : |ΔC| ≤ R)
    (hC' : |C + ΔC| ≤ R) (hRb : R ≤ 2 ^ 900) (hPb : P ≤ 2 ^ 900) (hAAb : AA ≤ 2 ^ 900)
    (hC : |Ch - C| ≤ G) (hGb : G ≤ 2 ^ 900) :
    |M.fl (Ch + M.fl q) - (C + ΔC)|
      ≤ (1 + u) * G + 8.5 * u * P + 7 * u * R + 103 * u ^ 2 * AA + 3 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) hC
  obtain ⟨E, hE⟩ : ∃ E, E = 8 * u * P + 4 * u * R + 81 * u ^ 2 * AA := ⟨_, rfl⟩
  rw [← hE] at hq
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hEb : E ≤ 2 ^ 900 := by
    have h1 : 8 * u * P ≤ 8 * u * 2 ^ 900 := by gcongr
    have h2 : 4 * u * R ≤ 4 * u * 2 ^ 900 := by gcongr
    have h3 : 81 * u ^ 2 * AA ≤ 81 * u ^ 2 * 2 ^ 900 := by gcongr
    have h4 : u ^ 2 ≤ u := by nlinarith
    have h5 : 93 * u * 2 ^ 900 ≤ (2 : ℝ) ^ 900 := by nlinarith
    nlinarith
  have hqa : |q| ≤ R + E := by have := abs_sub_abs_le_abs_sub q ΔC; linarith
  have r5 := M.err q (by linarith)
  have hE2 : |M.fl q - ΔC| ≤ E + u * (R + E + tiny) := by
    have e : M.fl q - ΔC = (M.fl q - q) + (q - ΔC) := by ring
    rw [e]
    have := abs_add_le (M.fl q - q) (q - ΔC)
    have := mul_le_mul_of_nonneg_left (by linarith : |q| + tiny ≤ R + E + tiny) hu.le
    linarith
  have huR : u * (R + E + tiny) ≤ 2 ^ 902 := by
    have := mul_le_mul hu' (by linarith : R + E + tiny ≤ 2 ^ 902) (by positivity) (by norm_num)
    linarith
  have hs : |Ch + M.fl q| ≤ R + G + (E + u * (R + E + tiny)) := by
    have e : Ch + M.fl q = (C + ΔC) + ((Ch - C) + (M.fl q - ΔC)) := by ring
    rw [e]
    have := abs_add_le (C + ΔC) ((Ch - C) + (M.fl q - ΔC))
    have := abs_add_le (Ch - C) (M.fl q - ΔC)
    linarith
  have r6 := M.err (Ch + M.fl q) (by linarith)
  have e : M.fl (Ch + M.fl q) - (C + ΔC)
      = (M.fl (Ch + M.fl q) - (Ch + M.fl q)) + ((Ch - C) + (M.fl q - ΔC)) := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  have a1 := abs_add_le (Ch - C) (M.fl q - ΔC)
  have g1 : u * |Ch + M.fl q| ≤ u * (R + G + (E + u * (R + E + tiny))) :=
    mul_le_mul_of_nonneg_left hs hu.le
  -- the second-order terms
  have p1 : u * E ≤ 0.001 * E := mul_le_mul_of_nonneg_right (by linarith) hE0
  have p2 : u * (u * R) ≤ 0.001 * (u * R) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p3 : u * (u * E) ≤ 0.001 * E := by
    have : u * E ≤ E := by nlinarith
    nlinarith
  have p4 : u * (u * tiny) ≤ 0.001 * (u * tiny) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p5 : 0 ≤ u * P := by positivity
  have p6 : 0 ≤ u ^ 2 * AA := by positivity
  have hE' : 1.003 * E ≤ 8.5 * u * P + 4.1 * u * R + 103 * u ^ 2 * AA := by
    rw [hE]
    have : 0 ≤ u * R := by positivity
    nlinarith
  nlinarith

/-- `fl(y − m̂')` against `E = y − m' = D (1 − w)`, from the new mean's error. -/
theorem StdModel.ydev_err {y m mh' D w A' : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 1 / 2)
    (hE : y - (m + D * w) = D * (1 - w)) (hm' : |mh' - (m + D * w)| ≤ 6 * u * A')
    (hDA : |D| ≤ A') (htA : tiny ≤ A') (hA'b : A' ≤ 2 ^ 433) :
    |M.fl (y - mh') - D * (1 - w)| ≤ 8 * u * A' + u * |D| := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hA'0 : 0 ≤ A' := le_trans (abs_nonneg _) hDA
  have h1w : 0 ≤ 1 - w := by linarith
  have hEabs : |D * (1 - w)| ≤ |D| := by
    rw [abs_mul, abs_of_nonneg h1w]; exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have hxmh' : |y - mh'| ≤ |D * (1 - w)| + 6 * u * A' := by
    have : y - mh' = D * (1 - w) - (mh' - (m + D * w)) := by linarith
    rw [this]; have := abs_sub (D * (1 - w)) (mh' - (m + D * w)); linarith
  have h6 : 6 * u * A' ≤ A' := by nlinarith
  have r4 := M.err (y - mh') (by linarith)
  have e : M.fl (y - mh') - D * (1 - w) = (M.fl (y - mh') - (y - mh')) - (mh' - (m + D * w)) := by
    linarith
  rw [e]
  have := abs_sub (M.fl (y - mh') - (y - mh')) (mh' - (m + D * w))
  have a1 : u * |y - mh'| ≤ u * |D| + u * (6 * u * A') := by
    have := mul_le_mul_of_nonneg_left (le_trans hxmh' (by linarith : |D * (1 - w)| + 6 * u * A'
      ≤ |D| + 6 * u * A')) hu.le
    linarith
  have a2 : u * (6 * u * A') ≤ u * A' := mul_le_mul_of_nonneg_left h6 hu.le
  have a3 : u * tiny ≤ u * A' := mul_le_mul_of_nonneg_left htA hu.le
  linarith

/-- The product of two deviations, each perturbed: `|(Dx + α)(Ey + β) − Dx Ey|`. -/
theorem prod_dev2 {Dx Dy Ey α β Ax Ay : ℝ} (hE : |Ey| ≤ |Dy|) (hDx : |Dx| ≤ Ax) (hDy : |Dy| ≤ Ay)
    (hα : |α| ≤ 8 * u * Ax + u * |Dx|) (hβ : |β| ≤ 8 * u * Ay + u * |Dy|) :
    |(Dx + α) * (Ey + β) - Dx * Ey|
      ≤ 8 * u * (Ax * |Dy| + Ay * |Dx|) + 2 * u * (|Dx| * |Dy|) + 81 * u ^ 2 * (Ax * Ay) := by
  have hu := u_pos
  have hAx : 0 ≤ Ax := le_trans (abs_nonneg _) hDx
  have hAy : 0 ≤ Ay := le_trans (abs_nonneg _) hDy
  have e : (Dx + α) * (Ey + β) - Dx * Ey = Dx * β + Ey * α + α * β := by ring
  rw [e]
  have h1 : |Dx * β| ≤ |Dx| * (8 * u * Ay + u * |Dy|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hβ (abs_nonneg _)
  have h2 : |Ey * α| ≤ |Dy| * (8 * u * Ax + u * |Dx|) := by
    rw [abs_mul]; exact mul_le_mul hE hα (abs_nonneg _) (abs_nonneg _)
  have hbx : 8 * u * Ax + u * |Dx| ≤ 9 * u * Ax := by
    have := mul_le_mul_of_nonneg_left hDx hu.le; linarith
  have hby : 8 * u * Ay + u * |Dy| ≤ 9 * u * Ay := by
    have := mul_le_mul_of_nonneg_left hDy hu.le; linarith
  have h3 : |α * β| ≤ (9 * u * Ax) * (9 * u * Ay) := by
    rw [abs_mul]
    exact mul_le_mul (le_trans hα hbx) (le_trans hβ hby) (abs_nonneg _) (by positivity)
  have h4 := abs_add_le (Dx * β + Ey * α) (α * β)
  have h5 := abs_add_le (Dx * β) (Ey * α)
  have e1 : |Dx| * (8 * u * Ay + u * |Dy|) + |Dy| * (8 * u * Ax + u * |Dx|) + (9 * u * Ax) * (9 * u * Ay)
      = 8 * u * (Ax * |Dy| + Ay * |Dx|) + 2 * u * (|Dx| * |Dy|) + 81 * u ^ 2 * (Ax * Ay) := by ring
  linarith

/-- **DuckDB's update of the co-moment of pairs**: from a co-moment within `G`
of `C`, the next is within
`(1 + u) G + 8.5 u (A'_x |D_y| + A'_y |D_x|) + 7 u R' + 103 u² A'_x A'_y + 3 u·tiny`
of `C' = C + D_x (y − m'_y)`, for any `R'` at least `|C'|` and `|D_x (y − m'_y)|`. -/
theorem StdModel.cov_step {K : ℕ} (hK1 : 1 ≤ K) (hK : K + 1 ≤ 2 ^ 32)
    {mx mxh x Ax my myh y Ay C Ch G R : ℝ}
    (hmx : |mx| * K ≤ Ax) (hAxt : K * tiny ≤ Ax) (hAxb : Ax ≤ 2 ^ 432) (hx : |x| ≤ 2 ^ 399)
    (hεx : |mxh - mx| ≤ 6 * u * Ax)
    (hmy : |my| * K ≤ Ay) (hAyt : K * tiny ≤ Ay) (hAyb : Ay ≤ 2 ^ 432) (hy : |y| ≤ 2 ^ 399)
    (hεy : |myh - my| ≤ 6 * u * Ay)
    (hR0 : 0 ≤ R) (hRb : R ≤ 2 ^ 900)
    (hCR : |C + (x - mx) * (y - (my + (y - my) / ((K : ℝ) + 1)))| ≤ R)
    (hΔR : |(x - mx) * (y - (my + (y - my) / ((K : ℝ) + 1)))| ≤ R)
    (hC : |Ch - C| ≤ G) (hGb : G ≤ 2 ^ 900) :
    |M.fl (Ch + M.fl (M.fl (x - mxh) * M.fl (y - M.fl (myh + M.fl (M.fl (y - myh) / ((K : ℝ) + 1))))))
        - (C + (x - mx) * (y - (my + (y - my) / ((K : ℝ) + 1))))|
      ≤ (1 + u) * G + 8.5 * u * ((Ax + |x| + tiny) * |y - my| + (Ay + |y| + tiny) * |x - mx|)
        + 7 * u * R + 103 * u ^ 2 * ((Ax + |x| + tiny) * (Ay + |y| + tiny)) + 3 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hk0 : (0 : ℝ) < K + 1 := by linarith
  have hAx0 : 0 ≤ Ax := le_trans (by positivity) hAxt
  have hAy0 : 0 ≤ Ay := le_trans (by positivity) hAyt
  have hmxA : |mx| ≤ Ax := by
    have := mul_le_mul_of_nonneg_left hK1r (abs_nonneg mx); linarith
  have hmyA : |my| ≤ Ay := by
    have := mul_le_mul_of_nonneg_left hK1r (abs_nonneg my); linarith
  obtain ⟨hdx, -⟩ := M.wmean_step hK1 hK hmx hAxt hAxb hx hεx
  obtain ⟨-, hmy'⟩ := M.wmean_step hK1 hK hmy hAyt hAyb hy hεy
  obtain ⟨Ax', hAx'⟩ : ∃ A', A' = Ax + |x| + tiny := ⟨_, rfl⟩
  obtain ⟨Ay', hAy'⟩ : ∃ A', A' = Ay + |y| + tiny := ⟨_, rfl⟩
  rw [← hAx'] at hdx ⊢
  rw [← hAy'] at hmy' ⊢
  obtain ⟨Dx, hDx⟩ : ∃ D, D = x - mx := ⟨_, rfl⟩
  obtain ⟨Dy, hDy⟩ : ∃ D, D = y - my := ⟨_, rfl⟩
  rw [← hDx] at hdx hCR hΔR ⊢
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / ((K : ℝ) + 1) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ≤ 1 / 2 := by rw [hw, div_le_div_iff₀ hk0 (by norm_num)]; linarith
  have hyD : (y - my) / ((K : ℝ) + 1) = Dy * w := by rw [hDy, hw]; ring
  rw [hyD] at hmy' hCR hΔR ⊢
  rw [← hDy]
  have hE : y - (my + Dy * w) = Dy * (1 - w) := by rw [hDy]; ring
  rw [hE] at hCR hΔR ⊢
  have hDxA : |Dx| ≤ Ax' := by rw [hDx, hAx']; have := abs_sub x mx; linarith
  have hDyA : |Dy| ≤ Ay' := by rw [hDy, hAy']; have := abs_sub y my; linarith
  have htAy : tiny ≤ Ay' := by rw [hAy']; linarith [abs_nonneg y]
  have hAy'b : Ay' ≤ 2 ^ 433 := by rw [hAy']; linarith
  have hAx'b : Ax' ≤ 2 ^ 433 := by rw [hAx']; linarith
  generalize M.fl (myh + M.fl (M.fl (y - myh) / ((K : ℝ) + 1))) = mh' at hmy' ⊢
  have hβ := M.ydev_err hw0 hw2 hE hmy' hDyA htAy hAy'b
  have h1w : 0 ≤ 1 - w := by linarith
  have hEabs : |Dy * (1 - w)| ≤ |Dy| := by
    rw [abs_mul, abs_of_nonneg h1w]; exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have hα : |M.fl (x - mxh) - Dx| ≤ 8 * u * Ax' + u * |Dx| := by
    have : 0 ≤ u * Ax' := by rw [hAx']; positivity
    linarith
  have hprod := prod_dev2 hEabs hDxA hDyA hα hβ
  have e1 : (Dx + (M.fl (x - mxh) - Dx)) * (Dy * (1 - w) + (M.fl (y - mh') - Dy * (1 - w)))
      = M.fl (x - mxh) * M.fl (y - mh') := by ring
  rw [e1] at hprod
  -- `|D_x| |D_y| ≤ 2 R`
  have hDD : |Dx| * |Dy| ≤ 2 * R := by
    have e : |Dx * (Dy * (1 - w))| = |Dx| * |Dy| * (1 - w) := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1w]; ring
    rw [e] at hΔR
    have : 0 ≤ |Dx| * |Dy| := by positivity
    nlinarith
  have hpe : |M.fl (x - mxh) * M.fl (y - mh') - Dx * (Dy * (1 - w))|
      ≤ 8 * u * (Ax' * |Dy| + Ay' * |Dx|) + 4 * u * R + 81 * u ^ 2 * (Ax' * Ay') := by
    have := mul_le_mul_of_nonneg_left hDD (by positivity : (0 : ℝ) ≤ 2 * u); linarith
  have hAx'0 : 0 ≤ Ax' := le_trans (abs_nonneg _) hDxA
  have hAy'0 : 0 ≤ Ay' := le_trans (abs_nonneg _) hDyA
  have hP : Ax' * |Dy| + Ay' * |Dx| ≤ 2 ^ 900 := by
    have h1 := mul_le_mul hAx'b (le_trans hDyA hAy'b) (abs_nonneg _) (by norm_num)
    have h2 := mul_le_mul hAy'b (le_trans hDxA hAx'b) (abs_nonneg _) (by norm_num)
    have : (2 : ℝ) ^ 433 * 2 ^ 433 + 2 ^ 433 * 2 ^ 433 ≤ 2 ^ 900 := by norm_num
    linarith
  have hAA : Ax' * Ay' ≤ 2 ^ 900 := by
    have := mul_le_mul hAx'b hAy'b hAy'0 (by norm_num)
    have : (2 : ℝ) ^ 433 * 2 ^ 433 ≤ 2 ^ 900 := by norm_num
    linarith
  exact M.ctail (by positivity) hR0 (by positivity) hpe hΔR hCR hRb hP hAA hC hGb
