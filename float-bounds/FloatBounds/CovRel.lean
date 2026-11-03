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

/-! ## The invariant over pairs -/

/-- Cauchy–Schwarz over a list of pairs. -/
theorem list_cs : ∀ l : List (ℝ × ℝ),
    (l.map fun p => p.1 * p.2).sum ^ 2
      ≤ (l.map fun p => p.1 * p.1).sum * (l.map fun p => p.2 * p.2).sum
  | [] => by simp
  | (a, b) :: l => by
    simp only [List.map_cons, List.sum_cons]
    have ih := list_cs l
    obtain ⟨s, hs⟩ : ∃ s, s = (l.map fun p => p.1 * p.2).sum := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ s, s = (l.map fun p => p.1 * p.1).sum := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ s, s = (l.map fun p => p.2 * p.2).sum := ⟨_, rfl⟩
    rw [← hs, ← hA, ← hB] at ih ⊢
    have hA0 : 0 ≤ A := by
      rw [hA]; exact List.sum_nonneg (fun y hy => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; exact mul_self_nonneg _)
    have hB0 : 0 ≤ B := by
      rw [hB]; exact List.sum_nonneg (fun y hy => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; exact mul_self_nonneg _)
    have h0 : 4 * (a * b) ^ 2 * s ^ 2 ≤ 4 * (a * b) ^ 2 * (A * B) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h1 : (2 * (a * b * s)) ^ 2 ≤ (a * a * B + b * b * A) ^ 2 := by
      nlinarith [sq_nonneg (a * a * B - b * b * A)]
    have h3 : 0 ≤ a * a * B + b * b * A := by
      have := mul_nonneg (mul_self_nonneg a) hB0
      have := mul_nonneg (mul_self_nonneg b) hA0
      linarith
    have h2 : 2 * (a * b * s) ≤ a * a * B + b * b * A := (abs_le_of_sq_le_sq' h1 h3).2
    nlinarith

theorem mx_dupL_fst (ps : List (ℝ × ℝ)) : mx (dupL (ps.map Prod.fst)) = mx ps := by
  simp [mx, sx, dupL, List.map_map, Function.comp_def]

theorem mx_dupL_snd (ps : List (ℝ × ℝ)) : mx (dupL (ps.map Prod.snd)) = my ps := by
  simp [mx, my, sx, sy, dupL, List.map_map, Function.comp_def]

/-- `S_xx = Σ (xᵢ − x̄)²`, `S_yy` likewise. -/
theorem comoment_fst (ps : List (ℝ × ℝ)) :
    comoment (dupL (ps.map Prod.fst)) = (ps.map fun p => (p.1 - mx ps) * (p.1 - mx ps)).sum := by
  unfold comoment
  rw [my_dupL, mx_dupL_fst]
  simp [dupL, List.map_map, Function.comp_def]

theorem comoment_snd (ps : List (ℝ × ℝ)) :
    comoment (dupL (ps.map Prod.snd)) = (ps.map fun p => (p.2 - my ps) * (p.2 - my ps)).sum := by
  unfold comoment
  rw [my_dupL, mx_dupL_snd]
  simp [dupL, List.map_map, Function.comp_def]

/-- **`C² ≤ S_xx S_yy`**. -/
theorem comoment_sq_le (ps : List (ℝ × ℝ)) :
    comoment ps ^ 2 ≤ comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd)) := by
  have h := list_cs (ps.map fun p => (p.1 - mx ps, p.2 - my ps))
  simp only [List.map_map, Function.comp_def] at h
  rw [comoment_fst, comoment_snd]
  exact h

/-- `|C| ≤ √(S_xx S_yy)`. -/
theorem abs_comoment_le_sqrt (ps : List (ℝ × ℝ)) :
    |comoment ps| ≤ √(comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd))) :=
  Real.abs_le_sqrt (comoment_sq_le ps)

/-- The bound of the invariant over pairs,
`(1 + 3nu)(8.5 u (A_x D_y + A_y D_x) + 10 u n R + 60 u² L A_x A_y + 12 u L·tiny)`. -/
noncomputable def cBound (n Ax Ay Dx Dy R L : ℝ) : ℝ :=
  (1 + 3 * n * u) * (8.5 * u * (Ax * Dy + Ay * Dx) + 10 * u * n * R + 60 * u ^ 2 * L * (Ax * Ay)
    + 12 * u * tiny * L)

theorem cBound_le {K Ax Ay Dx Dy R L : ℝ} (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ 32) (hAx0 : 0 ≤ Ax)
    (hAx : Ax ≤ 2 ^ 432) (hAy0 : 0 ≤ Ay) (hAy : Ay ≤ 2 ^ 432) (hDx0 : 0 ≤ Dx)
    (hDx : Dx ≤ 2 ^ 436) (hDy0 : 0 ≤ Dy) (hDy : Dy ≤ 2 ^ 436) (hR0 : 0 ≤ R) (hR : R ≤ 2 ^ 830)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 ^ 39) : cBound K Ax Ay Dx Dy R L ≤ 2 ^ 900 := by
  unfold cBound
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hKu : K * u ≤ 1 / 2 ^ 21 := by
    calc K * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  have hLu : L * u ≤ 1 / 2 ^ 14 := by
    calc L * u ≤ 2 ^ 39 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 14 := by norm_num
  have c0 : 1 + 3 * K * u ≤ 2 := by linarith
  have hAD : Ax * Dy + Ay * Dx ≤ 2 ^ 869 := by
    have h1 := mul_le_mul hAx hDy hDy0 (by norm_num)
    have h2 := mul_le_mul hAy hDx hDx0 (by norm_num)
    have : (2 : ℝ) ^ 432 * 2 ^ 436 + 2 ^ 432 * 2 ^ 436 ≤ 2 ^ 869 := by norm_num
    linarith
  have c1 : 8.5 * u * (Ax * Dy + Ay * Dx) ≤ 2 ^ 869 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : 8.5 * u ≤ 1)
      (by positivity : 0 ≤ Ax * Dy + Ay * Dx)
    linarith
  have c2 : 10 * u * K * R ≤ 2 ^ 830 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : 10 * (K * u) ≤ 1) hR0; linarith
  have hA2 : Ax * Ay ≤ 2 ^ 864 := by
    have := mul_le_mul hAx hAy hAy0 (by norm_num)
    have : (2 : ℝ) ^ 432 * 2 ^ 432 = 2 ^ 864 := by norm_num
    linarith
  have c3 : 60 * u ^ 2 * L * (Ax * Ay) ≤ 2 ^ 864 := by
    have h1 : 60 * u ^ 2 * L ≤ 1 := by
      have : u * (L * u) ≤ 1 / 2 ^ 53 * (1 / 2 ^ 14) := mul_le_mul hu' hLu (by positivity) (by norm_num)
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ Ax * Ay); linarith
  have c4 : 12 * u * tiny * L ≤ 1 := by
    have := mul_le_mul hLu ht1 ht.le (by norm_num); nlinarith
  have hsum : 8.5 * u * (Ax * Dy + Ay * Dx) + 10 * u * K * R + 60 * u ^ 2 * L * (Ax * Ay)
      + 12 * u * tiny * L ≤ 2 ^ 870 := by linarith
  have h0 : 0 ≤ 8.5 * u * (Ax * Dy + Ay * Dx) + 10 * u * K * R + 60 * u ^ 2 * L * (Ax * Ay)
      + 12 * u * tiny * L := by positivity
  have := mul_le_mul c0 hsum h0 (by norm_num)
  linarith

/-- A step keeps the bound of the invariant. -/
theorem carith {n Ax Ay Ax' Ay' Dx Dy dx dy R R' L L' G : ℝ} (hn : 0 ≤ n)
    (hnu : (n + 1) * u ≤ 1 / 2 ^ 21) (hAx0 : 0 ≤ Ax) (hAx : Ax ≤ Ax') (hAy0 : 0 ≤ Ay)
    (hAy : Ay ≤ Ay') (hDx : 0 ≤ Dx) (hDy : 0 ≤ Dy) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) (hR0 : 0 ≤ R)
    (hR : R ≤ R') (hL0 : 0 ≤ L) (hL : L + 2 ≤ L') (hG : G ≤ cBound n Ax Ay Dx Dy R L) :
    (1 + u) * G + 8.5 * u * (Ax' * dy + Ay' * dx) + 7 * u * R' + 103 * u ^ 2 * (Ax' * Ay')
        + 3 * u * tiny
      ≤ cBound (n + 1) Ax' Ay' (Dx + dx) (Dy + dy) R' L' := by
  unfold cBound at hG ⊢
  have hu := u_pos
  have ht := tiny_pos
  have hAx'0 : 0 ≤ Ax' := le_trans hAx0 hAx
  have hAy'0 : 0 ≤ Ay' := le_trans hAy0 hAy
  have hR'0 : 0 ≤ R' := le_trans hR0 hR
  obtain ⟨T', hT'⟩ : ∃ T, T = 8.5 * u * (Ax' * Dy + Ay' * Dx) + 10 * u * n * R'
      + 60 * u ^ 2 * L * (Ax' * Ay') + 12 * u * tiny * L := ⟨_, rfl⟩
  have hTT : 8.5 * u * (Ax * Dy + Ay * Dx) + 10 * u * n * R + 60 * u ^ 2 * L * (Ax * Ay)
      + 12 * u * tiny * L ≤ T' := by
    have h1 : Ax * Dy + Ay * Dx ≤ Ax' * Dy + Ay' * Dx := by
      have := mul_le_mul_of_nonneg_right hAx hDy
      have := mul_le_mul_of_nonneg_right hAy hDx
      linarith
    have h2 : Ax * Ay ≤ Ax' * Ay' := mul_le_mul hAx hAy hAy0 hAx'0
    have h3 : 8.5 * u * (Ax * Dy + Ay * Dx) ≤ 8.5 * u * (Ax' * Dy + Ay' * Dx) := by gcongr
    have h4 : 10 * u * n * R ≤ 10 * u * n * R' := by gcongr
    have h5 : 60 * u ^ 2 * L * (Ax * Ay) ≤ 60 * u ^ 2 * L * (Ax' * Ay') := by gcongr
    rw [hT']; linarith
  have hT0 : 0 ≤ T' := by rw [hT']; positivity
  have hfac : (1 + u) * (1 + 3 * n * u) ≤ 1 + 3 * (n + 1) * u := by
    have h1 : 3 * n * u ≤ 1 := by nlinarith
    have : 3 * n * u * u ≤ 2 * u := by nlinarith
    nlinarith
  have hG' : (1 + u) * G ≤ (1 + 3 * (n + 1) * u) * T' := by
    calc (1 + u) * G ≤ (1 + u) * ((1 + 3 * n * u) * T') := by
          gcongr; exact le_trans hG (by gcongr)
      _ = ((1 + u) * (1 + 3 * n * u)) * T' := by ring
      _ ≤ _ := by gcongr
  obtain ⟨I, hI⟩ : ∃ I, I = 8.5 * u * (Ax' * dy + Ay' * dx) + 7 * u * R'
      + 103 * u ^ 2 * (Ax' * Ay') + 3 * u * tiny := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [hI]; positivity
  have hinc : I ≤ (1 + 3 * (n + 1) * u) * I := le_mul_of_one_le_left hI0 (by nlinarith)
  have hnew : T' + I ≤ 8.5 * u * (Ax' * (Dy + dy) + Ay' * (Dx + dx)) + 10 * u * (n + 1) * R'
      + 60 * u ^ 2 * L' * (Ax' * Ay') + 12 * u * tiny * L' := by
    have p1 : 0 ≤ u * R' := by positivity
    have p2 : 2 * (u ^ 2 * (Ax' * Ay')) ≤ (L' - L) * (u ^ 2 * (Ax' * Ay')) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have p3 : 2 * (u * tiny) ≤ (L' - L) * (u * tiny) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have p4 : 0 ≤ u ^ 2 * (Ax' * Ay') := by positivity
    have p5 : 0 ≤ u * tiny := by positivity
    rw [hT', hI]
    linarith
  have := mul_le_mul_of_nonneg_left hnew (by positivity : (0 : ℝ) ≤ 1 + 3 * (n + 1) * u)
  have e : (1 + 3 * (n + 1) * u) * (T' + I) = (1 + 3 * (n + 1) * u) * T' + (1 + 3 * (n + 1) * u) * I := by
    ring
  linarith

/-- The invariant of DuckDB's plans over pairs `ps`: the means within `6 u A`,
and the co-moment within `cBound`, where `D_x² ≤ L(n) S_xx`, `D_y² ≤ L(n) S_yy`
and `R = √(S_xx S_yy)`. -/
def CInv (ps : List (ℝ × ℝ)) (s : WState) : Prop :=
  s.n = ps.length ∧ |s.mx - mx ps| ≤ 6 * u * mag (ps.map Prod.fst) ∧
    |s.my - my ps| ≤ 6 * u * mag (ps.map Prod.snd) ∧
    ∃ Dx Dy : ℝ, 0 ≤ Dx ∧ 0 ≤ Dy ∧
      Dx ^ 2 ≤ Lw ps.length * comoment (dupL (ps.map Prod.fst)) ∧
      Dy ^ 2 ≤ Lw ps.length * comoment (dupL (ps.map Prod.snd)) ∧
      |s.c - comoment ps| ≤ cBound ps.length (mag (ps.map Prod.fst)) (mag (ps.map Prod.snd)) Dx Dy
        (√(comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd)))) (Lw ps.length)

theorem cBound_nonneg {n Ax Ay Dx Dy R L : ℝ} (hn : 0 ≤ n) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hDx : 0 ≤ Dx) (hDy : 0 ≤ Dy) (hR : 0 ≤ R) (hL : 0 ≤ L) : 0 ≤ cBound n Ax Ay Dx Dy R L := by
  have hu := u_pos
  have ht := tiny_pos
  unfold cBound; positivity

/-- The facts about the pairs a bound needs. -/
theorem pair_facts {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32)
    (hB : Bounded (2 ^ 399) ps) :
    (0 ≤ mag (ps.map Prod.fst) ∧ mag (ps.map Prod.fst) ≤ 2 ^ 432 ∧
      ps.length * tiny ≤ mag (ps.map Prod.fst) ∧ |mx ps| * ps.length ≤ mag (ps.map Prod.fst) ∧
      |mx ps| ≤ 2 ^ 400 ∧ 0 ≤ comoment (dupL (ps.map Prod.fst)) ∧
      comoment (dupL (ps.map Prod.fst)) ≤ 2 ^ 830) ∧
    (0 ≤ mag (ps.map Prod.snd) ∧ mag (ps.map Prod.snd) ≤ 2 ^ 432 ∧
      ps.length * tiny ≤ mag (ps.map Prod.snd) ∧ |my ps| * ps.length ≤ mag (ps.map Prod.snd) ∧
      |my ps| ≤ 2 ^ 400 ∧ 0 ≤ comoment (dupL (ps.map Prod.snd)) ∧
      comoment (dupL (ps.map Prod.snd)) ≤ 2 ^ 830) := by
  have h1 := list_facts (xs := ps.map Prod.fst) (by simpa using hne) (by simpa using hN)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).1)
  have h2 := list_facts (xs := ps.map Prod.snd) (by simpa using hne) (by simpa using hN)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).2)
  simp only [List.length_map, mx_dupL_fst, mx_dupL_snd] at h1 h2
  exact ⟨h1, h2⟩

/-- `√(S_xx S_yy) ≤ 2⁸³⁰`. -/
theorem sqrt_le_830 {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ 2 ^ 830) (hb' : b ≤ 2 ^ 830) :
    √(a * b) ≤ 2 ^ 830 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := mul_le_mul ha' hb' hb (by positivity)
  have e : ((2 : ℝ) ^ 830) ^ 2 = 2 ^ 830 * 2 ^ 830 := by ring
  rw [e]; exact this

theorem StdModel.welfordStep_first {x y : ℝ} (hx : M.fl x = x) (hy : M.fl y = y) :
    M.welfordStep .empty (x, y) = ⟨1, x, y, 0⟩ := by
  simp only [StdModel.welfordStep, WState.empty, Nat.cast_zero, zero_add, sub_zero, div_one, hx,
    hy, sub_self, M.zero, mul_zero]

theorem StdModel.cInv_one {x y : ℝ} (hx : M.fl x = x) (hy : M.fl y = y) :
    CInv [(x, y)] (M.welfordStep .empty (x, y)) := by
  have ht := tiny_pos
  rw [M.welfordStep_first hx hy]
  have hmx : mx [(x, y)] = x := by simp [mx, sx]
  have hmy : my [(x, y)] = y := by simp [my, sy]
  have hc : comoment [(x, y)] = 0 := by simp [comoment, mx, my, sx, sy]
  have hcx : comoment (dupL ([(x, y)].map Prod.fst)) = 0 := by
    simp [comoment, dupL, mx, my, sx, sy]
  have hcy : comoment (dupL ([(x, y)].map Prod.snd)) = 0 := by
    simp [comoment, dupL, mx, my, sx, sy]
  refine ⟨rfl, ?_, ?_, 0, 0, le_rfl, le_rfl, ?_, ?_, ?_⟩
  · simp only [hmx, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) u_pos.le) (mag_nonneg _)
  · simp only [hmy, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) u_pos.le) (mag_nonneg _)
  · rw [hcx]; simp
  · rw [hcy]; simp
  · rw [hc, sub_self, abs_zero]
    exact cBound_nonneg (by positivity) (mag_nonneg _) (mag_nonneg _) le_rfl le_rfl
      (Real.sqrt_nonneg _) (Lw_nonneg _)

/-- The exact update of the co-moment of the `x`s alone. -/
theorem comoment_fst_snoc (ps : List (ℝ × ℝ)) (x y : ℝ) :
    comoment (dupL ((ps ++ [(x, y)]).map Prod.fst))
      = comoment (dupL (ps.map Prod.fst))
        + (x - mx ps) * (x - (mx ps + (x - mx ps) / ((ps.length : ℝ) + 1))) := by
  have hsnd : mx (dupL (ps.map Prod.fst ++ [x]))
      = mx ps + (x - mx ps) / ((ps.length : ℝ) + 1) := by
    rw [dupL_append, show dupL [x] = [(x, x)] from rfl, mx_snoc, dupL_length, mx_dupL_fst,
      List.length_map]
  rw [List.map_append, show [(x, y)].map Prod.fst = [x] from rfl, dupL_append,
    show dupL [x] = [(x, x)] from rfl, comoment_snoc,
    show dupL (ps.map Prod.fst) ++ [(x, x)] = dupL (ps.map Prod.fst ++ [x]) by simp [dupL],
    my_dupL, hsnd, mx_dupL_fst]

theorem comoment_snd_snoc (ps : List (ℝ × ℝ)) (x y : ℝ) :
    comoment (dupL ((ps ++ [(x, y)]).map Prod.snd))
      = comoment (dupL (ps.map Prod.snd))
        + (y - my ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1))) := by
  have hsnd : mx (dupL (ps.map Prod.snd ++ [y]))
      = my ps + (y - my ps) / ((ps.length : ℝ) + 1) := by
    rw [dupL_append, show dupL [y] = [(y, y)] from rfl, mx_snoc, dupL_length, mx_dupL_snd,
      List.length_map]
  rw [List.map_append, show [(x, y)].map Prod.snd = [y] from rfl, dupL_append,
    show dupL [y] = [(y, y)] from rfl, comoment_snoc,
    show dupL (ps.map Prod.snd) ++ [(y, y)] = dupL (ps.map Prod.snd ++ [y]) by simp [dupL],
    my_dupL, hsnd, mx_dupL_snd]

set_option maxHeartbeats 1000000 in
theorem StdModel.cInv_snoc {ps : List (ℝ × ℝ)} {x y : ℝ} (hne : ps ≠ [])
    (hN : ps.length + 1 ≤ 2 ^ 32) (hB : Bounded (2 ^ 399) (ps ++ [(x, y)])) {s : WState}
    (hs : CInv ps s) : CInv (ps ++ [(x, y)]) (M.welfordStep s (x, y)) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  obtain ⟨K', mxh, myh, Ch⟩ := s
  obtain ⟨hn, hεx, hεy, Dx, Dy, hDx0, hDy0, hDx, hDy, hC⟩ := hs
  simp only at hn hεx hεy hC
  subst hn
  unfold CInv
  have hBp : Bounded (2 ^ 399) ps := (Bounded.append.mp hB).1
  have hxy := (Bounded.append.mp hB).2 (x, y) (by simp)
  simp only at hxy
  obtain ⟨⟨hAx0, hAxb, hAxt, hmx, hmxb, hSx0, hSxb⟩, ⟨hAy0, hAyb, hAyt, hmy, hmyb, hSy0, hSyb⟩⟩ :=
    pair_facts hne (by omega) hBp
  obtain ⟨⟨-, -, -, -, -, hSx0', hSxb'⟩, ⟨-, -, -, -, -, hSy0', hSyb'⟩⟩ :=
    pair_facts (ps := ps ++ [(x, y)]) (by simp) (by simp; omega) hB
  have hK1 : 1 ≤ ps.length := List.length_pos_iff.mpr hne
  have hK1r : (1 : ℝ) ≤ ps.length := by exact_mod_cast hK1
  have hKr : (ps.length : ℝ) + 1 ≤ 2 ^ 32 := by exact_mod_cast hN
  -- the exact update
  have hmxs := mx_snoc ps (x, y)
  have hmys := my_snoc ps (x, y)
  have hcs : comoment (ps ++ [(x, y)])
      = comoment ps + (x - mx ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1))) := by
    rw [comoment_snoc, hmys]
  have hsx := comoment_fst_snoc ps x y
  have hsy := comoment_snd_snoc ps x y
  have hmagx : mag ((ps ++ [(x, y)]).map Prod.fst) = mag (ps.map Prod.fst) + |x| + tiny := by
    simp [mag_append]; ring
  have hmagy : mag ((ps ++ [(x, y)]).map Prod.snd) = mag (ps.map Prod.snd) + |y| + tiny := by
    simp [mag_append]; ring
  have hlen : (ps ++ [(x, y)]).length = ps.length + 1 := by simp
  have hRle := abs_comoment_le_sqrt (ps ++ [(x, y)])
  -- names
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / ((ps.length : ℝ) + 1) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ≤ 1 / 2 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have ex : (x - mx ps) * (x - (mx ps + (x - mx ps) / ((ps.length : ℝ) + 1)))
      = (x - mx ps) * ((x - mx ps) * (1 - w)) := by rw [hw]; ring
  have ey : (y - my ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))
      = (y - my ps) * ((y - my ps) * (1 - w)) := by rw [hw]; ring
  have exy : (x - mx ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))
      = (x - mx ps) * ((y - my ps) * (1 - w)) := by rw [hw]; ring
  have hfx := dsq_facts (x - mx ps) hw0 hw2
  have hfy := dsq_facts (y - my ps) hw0 hw2
  rw [← ex] at hfx
  rw [← ey] at hfy
  obtain ⟨Sx', hSx'⟩ : ∃ S, S = comoment (dupL ((ps ++ [(x, y)]).map Prod.fst)) := ⟨_, rfl⟩
  obtain ⟨Sy', hSy'⟩ : ∃ S, S = comoment (dupL ((ps ++ [(x, y)]).map Prod.snd)) := ⟨_, rfl⟩
  rw [← hSx'] at hsx hSx0' hSxb' hRle ⊢
  rw [← hSy'] at hsy hSy0' hSyb' hRle ⊢
  -- `|ΔC| ≤ R'`, `R ≤ R'`
  have hΔR : |(x - mx ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))| ≤ √(Sx' * Sy') := by
    apply Real.abs_le_sqrt
    have e : ((x - mx ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))) ^ 2
        = ((x - mx ps) * (x - (mx ps + (x - mx ps) / ((ps.length : ℝ) + 1))))
          * ((y - my ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))) := by
      rw [ex, ey, exy]; ring
    rw [e]
    exact mul_le_mul (by linarith) (by linarith) hfy.1 hSx0'
  have hRR : √(comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd)))
      ≤ √(Sx' * Sy') :=
    Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) hSy0 hSx0')
  rw [hcs] at hRle ⊢
  -- the bounds against overflow
  have hLK := Lw_le (n := ps.length) (by omega)
  have hL39 : Lw ps.length ≤ 2 ^ 39 := by
    have : (ps.length : ℝ) ≤ 2 ^ 32 := by linarith
    linarith
  have hDxb := Ds_le hDx0 hSx0 hL39 hSxb hDx
  have hDyb := Ds_le hDy0 hSy0 hL39 hSyb hDy
  have hGb := cBound_le hK1r (by linarith) hAx0 hAxb hAy0 hAyb hDx0 hDxb hDy0 hDyb
    (Real.sqrt_nonneg _) (sqrt_le_830 hSx0 hSy0 hSxb hSyb) (Lw_nonneg _) hL39
  have hst := M.cov_step hK1 hN hmx hAxt hAxb hxy.1 hεx hmy hAyt hAyb hxy.2 hεy
    (Real.sqrt_nonneg _) (by have := sqrt_le_830 hSx0' hSy0' hSxb' hSyb'; linarith) hRle hΔR hC
    (by linarith)
  obtain ⟨-, hmx'⟩ := M.wmean_step hK1 hN hmx hAxt hAxb hxy.1 hεx
  obtain ⟨-, hmy'⟩ := M.wmean_step hK1 hN hmy hAyt hAyb hxy.2 hεy
  have hnu : ((ps.length : ℝ) + 1) * u ≤ 1 / 2 ^ 21 := by
    calc ((ps.length : ℝ) + 1) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  have ar := carith (n := (ps.length : ℝ)) (Ax' := mag (ps.map Prod.fst) + |x| + tiny)
    (Ay' := mag (ps.map Prod.snd) + |y| + tiny) (dx := |x - mx ps|) (dy := |y - my ps|)
    (L := Lw ps.length) (L' := Lw (ps.length + 1)) (by positivity) hnu hAx0 (by linarith [abs_nonneg x]) hAy0
    (by linarith [abs_nonneg y]) hDx0 hDy0 (abs_nonneg _) (abs_nonneg _) (Real.sqrt_nonneg _)
    hRR (Lw_nonneg _) (by have := Lw_succ ps.length; linarith) le_rfl
  refine ⟨by simp [StdModel.welfordStep], ?_, ?_, Dx + |x - mx ps|, Dy + |y - my ps|,
    by positivity, by positivity, ?_, ?_, ?_⟩
  · simp only [StdModel.welfordStep, hmxs, hmagx]; exact hmx'
  · simp only [StdModel.welfordStep, hmys, hmagy]; exact hmy'
  · rw [hlen, hsx]
    have h2 : |x - mx ps| ^ 2 ≤ 2 * ((x - mx ps) * (x - (mx ps + (x - mx ps) / ((ps.length : ℝ) + 1)))) := by
      rw [sq_abs]; exact hfx.2.1
    have := cs3 hDx0 (abs_nonneg _) le_rfl (Lw_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) le_rfl hSx0
      hfx.1 le_rfl hDx h2 (by simp)
    simp only [add_zero] at this
    have h3 := mul_le_mul_of_nonneg_right (by have := Lw_succ ps.length; linarith :
      Lw ps.length + 2 ≤ Lw (ps.length + 1)) (by linarith : 0 ≤ comoment (dupL (ps.map Prod.fst))
        + (x - mx ps) * (x - (mx ps + (x - mx ps) / ((ps.length : ℝ) + 1))))
    linarith
  · rw [hlen, hsy]
    have h2 : |y - my ps| ^ 2 ≤ 2 * ((y - my ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1)))) := by
      rw [sq_abs]; exact hfy.2.1
    have := cs3 hDy0 (abs_nonneg _) le_rfl (Lw_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) le_rfl hSy0
      hfy.1 le_rfl hDy h2 (by simp)
    simp only [add_zero] at this
    have h3 := mul_le_mul_of_nonneg_right (by have := Lw_succ ps.length; linarith :
      Lw ps.length + 2 ≤ Lw (ps.length + 1)) (by linarith : 0 ≤ comoment (dupL (ps.map Prod.snd))
        + (y - my ps) * (y - (my ps + (y - my ps) / ((ps.length : ℝ) + 1))))
    linarith
  · simp only [StdModel.welfordStep]
    rw [hlen, hmagx, hmagy]
    push_cast
    exact le_trans hst ar
