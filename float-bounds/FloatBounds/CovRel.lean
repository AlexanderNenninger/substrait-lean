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

theorem StdModel.cInv_all {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32)
    (hB : Bounded (2 ^ 399) ps) (hrep : ∀ p ∈ ps, M.fl p.1 = p.1 ∧ M.fl p.2 = p.2) :
    CInv ps (ps.foldl M.welfordStep .empty) := by
  induction ps using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton qs q ih =>
    obtain ⟨x, y⟩ := q
    simp only [List.length_append, List.length_singleton] at hN
    rcases eq_or_ne qs [] with rfl | hqs
    · have h := hrep (x, y) (by simp)
      simpa using M.cInv_one h.1 h.2
    · have hs := ih hqs (by omega) (Bounded.append.mp hB).1
        (fun p hp => hrep p (by simp [hp]))
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact M.cInv_snoc hqs hN hB hs

/-! ## Chan's merge of pairs -/

/-- One rounding of a scaled approximation: `|fl(e c) − E c|`. -/
theorem StdModel.rnd_scale {e E ε c : ℝ} (he : |e - E| ≤ ε) (hc : 0 ≤ c)
    (hb : |e * c| ≤ maxFinite) :
    |M.fl (e * c) - E * c| ≤ (1 + u) * (c * ε) + u * (c * |E|) + u * tiny := by
  have hu := u_pos
  have h1 := M.err (e * c) hb
  have h2 : |e * c - E * c| ≤ c * ε := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hc, mul_comm]; exact mul_le_mul_of_nonneg_left he hc
  have h3 : |e * c| ≤ c * |E| + c * ε := by
    have := abs_sub_abs_le_abs_sub (e * c) (E * c)
    rw [abs_mul E, abs_of_nonneg hc] at this; linarith
  have hsplit : M.fl (e * c) - E * c = (M.fl (e * c) - e * c) + (e * c - E * c) := by ring
  rw [hsplit]
  have := abs_add_le (M.fl (e * c) - e * c) (e * c - E * c)
  have := mul_le_mul_of_nonneg_left h3 hu.le
  linarith

set_option maxHeartbeats 800000 in
/-- DuckDB's `T = Δx · Δy · n_s · n_t / n`, from the rounded product `P`, each
operation rounded: within `5 u (|P| h + (1 + h) tiny)` of `P h`. -/
theorem StdModel.T_chain2 {P : ℝ} {ns nt : ℕ} (hs : 1 ≤ ns) (ht1 : 1 ≤ nt)
    (hn : ns + nt ≤ 2 ^ 32) (hP : |P| ≤ 2 ^ 840) :
    |M.fl (M.fl (M.fl (M.fl P * ns) * nt) / ((nt : ℝ) + ns))
        - P * ((ns : ℝ) * nt / ((nt : ℝ) + ns))|
      ≤ 5 * u * (|P| * ((ns : ℝ) * nt / ((nt : ℝ) + ns))
        + (1 + (ns : ℝ) * nt / ((nt : ℝ) + ns)) * tiny) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have htn1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hsr : (1 : ℝ) ≤ ns := by exact_mod_cast hs
  have htr : (1 : ℝ) ≤ nt := by exact_mod_cast ht1
  have hnr : (ns : ℝ) + nt ≤ 2 ^ 32 := by exact_mod_cast hn
  obtain ⟨n, hn'⟩ : ∃ n : ℝ, n = (nt : ℝ) + ns := ⟨_, rfl⟩
  rw [← hn']
  have hn0 : 0 < n := by linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 1 / n := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hb1 : b ≤ 1 := by rw [hbdef, div_le_one hn0]; linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (ns : ℝ) * nt / n := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have eh : (ns : ℝ) * nt * b = h := by rw [hbdef, hh]; ring
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (nt : ℝ) * b := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have ha1 : a ≤ 1 := by
    rw [hadef, hbdef, mul_one_div, div_le_one hn0]; linarith
  have hu1 : u ≤ 1 / 2 := by linarith
  have hpa : 0 ≤ |P| := abs_nonneg P
  -- the four roundings
  have hq1 := M.err P (by linarith)
  have hq1b : |M.fl P| ≤ 2 ^ 841 := by
    have := abs_sub_abs_le_abs_sub (M.fl P) P
    have : u * (|P| + tiny) ≤ 2 ^ 841 - 2 ^ 840 := by
      have := mul_le_mul hu' (by linarith : |P| + tiny ≤ 2 ^ 841) (by positivity) (by norm_num)
      norm_num at this ⊢; linarith
    linarith
  have hq1' : |M.fl P - P| ≤ u * |P| + u * tiny := by linarith
  have hb2 : |M.fl P * ns| ≤ maxFinite := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul hq1b (by linarith : (ns : ℝ) ≤ 2 ^ 32) (by positivity) (by norm_num)
    norm_num at this ⊢; linarith
  have e1 := M.rnd_scale hq1' (by positivity : (0 : ℝ) ≤ ns) hb2
  obtain ⟨ε1, hε1⟩ : ∃ ε, ε = (1 + u) * (ns * (u * |P| + u * tiny)) + u * (ns * |P|) + u * tiny :=
    ⟨_, rfl⟩
  rw [← hε1] at e1
  have hε1b : ε1 ≤ 2 ^ 875 := by
    have hX : (ns : ℝ) * |P| ≤ 2 ^ 32 * 2 ^ 840 := mul_le_mul (by linarith) hP hpa (by norm_num)
    have hY : (ns : ℝ) * tiny ≤ 2 ^ 32 * 1 := mul_le_mul (by linarith) htn1 ht.le (by norm_num)
    have hc : (1 + u) * u ≤ 1 := by nlinarith
    have e : ε1 = (1 + u) * u * ((ns : ℝ) * |P|) + (1 + u) * u * ((ns : ℝ) * tiny)
        + u * ((ns : ℝ) * |P|) + u * tiny := by rw [hε1]; ring
    have k1 := mul_le_mul hc hX (by positivity) (by norm_num)
    have k2 := mul_le_mul hc hY (by positivity) (by norm_num)
    have k3 := mul_le_mul (by linarith : u ≤ 1) hX (by positivity) (by norm_num)
    have k4 := mul_le_mul (by linarith : u ≤ 1) htn1 ht.le (by norm_num)
    have : (1 : ℝ) * (2 ^ 32 * 2 ^ 840) + 1 * (2 ^ 32 * 1) + 1 * (2 ^ 32 * 2 ^ 840) + 1 * 1
        ≤ 2 ^ 875 := by norm_num
    linarith
  have hq2b : |M.fl (M.fl P * ns)| ≤ 2 ^ 876 := by
    have := abs_sub_abs_le_abs_sub (M.fl (M.fl P * ns)) (P * ns)
    rw [abs_mul P, Nat.abs_cast] at this
    have : |P| * ns ≤ 2 ^ 840 * 2 ^ 32 := mul_le_mul hP (by linarith) (by positivity) (by norm_num)
    linarith
  have hb3 : |M.fl (M.fl P * ns) * nt| ≤ maxFinite := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul hq2b (by linarith : (nt : ℝ) ≤ 2 ^ 32) (by positivity) (by norm_num)
    norm_num at this ⊢; linarith
  have e2 := M.rnd_scale e1 (by positivity : (0 : ℝ) ≤ nt) hb3
  obtain ⟨ε2, hε2⟩ : ∃ ε, ε = (1 + u) * (nt * ε1) + u * (nt * |P * ns|) + u * tiny := ⟨_, rfl⟩
  rw [← hε2] at e2
  have hε2b : ε2 ≤ 2 ^ 910 := by
    rw [hε2]
    have : (nt : ℝ) * ε1 ≤ 2 ^ 32 * 2 ^ 875 := mul_le_mul (by linarith) hε1b (by
      have := abs_nonneg (M.fl (M.fl P * ns) - P * ns); linarith) (by norm_num)
    have : (nt : ℝ) * |P * ns| ≤ 2 ^ 32 * (2 ^ 840 * 2 ^ 32) := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul (by linarith) (mul_le_mul hP (by linarith) (by positivity) (by norm_num))
        (by positivity) (by norm_num)
    nlinarith
  have hq3b : |M.fl (M.fl (M.fl P * ns) * nt)| ≤ 2 ^ 911 := by
    have h0 := abs_sub_abs_le_abs_sub (M.fl (M.fl (M.fl P * ns) * nt)) (P * ns * nt)
    have h1 : |P * ns * nt| ≤ 2 ^ 840 * 2 ^ 32 * 2 ^ 32 := by
      rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      exact mul_le_mul (mul_le_mul hP (by linarith) (by positivity) (by norm_num)) (by linarith)
        (by positivity) (by norm_num)
    have h2 : (2 : ℝ) ^ 840 * 2 ^ 32 * 2 ^ 32 + 2 ^ 910 ≤ 2 ^ 911 := by norm_num
    linarith
  have e3q : M.fl (M.fl (M.fl P * ns) * nt) / n = M.fl (M.fl (M.fl P * ns) * nt) * b := by
    rw [hbdef]; ring
  have hb4 : |M.fl (M.fl (M.fl P * ns) * nt) * b| ≤ maxFinite := by
    rw [abs_mul, abs_of_nonneg hb0]
    have := mul_le_mul hq3b hb1 hb0 (by norm_num)
    norm_num at this ⊢; linarith
  have e3 := M.rnd_scale e2 hb0 hb4
  rw [← e3q] at e3
  have eP : P * ns * nt * b = P * h := by rw [← eh]; ring
  rw [eP] at e3
  refine le_trans e3 ?_
  -- the arithmetic
  rw [hε2, hε1]
  have hPns : |P * ns| = |P| * ns := by rw [abs_mul, Nat.abs_cast]
  have hPnn : |P * ns * nt| = |P| * ns * nt := by rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
  rw [hPns, hPnn]
  obtain ⟨f4, -, f3, f2⟩ := u_pows
  have e : (1 + u) * (b * ((1 + u) * (nt * ((1 + u) * (ns * (u * |P| + u * tiny)) + u * (ns * |P|)
      + u * tiny)) + u * (nt * (|P| * ns)) + u * tiny)) + u * (b * (|P| * ns * nt)) + u * tiny
      = u * (|P| * (ns * nt * b)) * ((1 + u) ^ 3 + (1 + u) ^ 2 + (1 + u) + 1)
        + u * tiny * ((1 + u) ^ 3 * (ns * nt * b) + (1 + u) ^ 2 * (nt * b) + (1 + u) * b + 1) := by
    ring
  rw [e, eh, ← hadef]
  have hPh : 0 ≤ u * (|P| * h) := by positivity
  have k1 : u * (|P| * h) * ((1 + u) ^ 3 + (1 + u) ^ 2 + (1 + u) + 1) ≤ u * (|P| * h) * 4.04 := by
    apply mul_le_mul_of_nonneg_left _ hPh
    have : 1 + u ≤ 1.01 := by linarith
    linarith
  have k2 : u * tiny * ((1 + u) ^ 3 * h + (1 + u) ^ 2 * a + (1 + u) * b + 1)
      ≤ u * tiny * (1.01 * h + 3.02) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_right f3 hh0
    have := mul_le_mul f2 ha1 ha0 (by norm_num)
    have := mul_le_mul (by linarith : 1 + u ≤ 1.01) hb1 hb0 (by norm_num)
    linarith
  have k3 : u * tiny * (1.01 * h + 3.02) ≤ 5 * u * ((1 + h) * tiny) := by
    have : 0 ≤ u * tiny := by positivity
    have := mul_le_mul_of_nonneg_left (by linarith : 1.01 * h + 3.02 ≤ 5 * (1 + h)) this
    linarith
  have e5 : 5 * u * (|P| * h + (1 + h) * tiny) = 5 * (u * (|P| * h)) + 5 * u * ((1 + h) * tiny) := by
    ring
  linarith

/-- The arithmetic at the end of `wmean_spec`. -/
theorem wmerge_arith {ns nt n a b E ms mt As At : ℝ} (hsr : 1 ≤ ns) (htr : 1 ≤ nt)
    (hn' : n = nt + ns) (ha : a = ns * |ms|) (hb : b = nt * |mt|)
    (k1 : E ≤ 3.02 * u * (a + b) + 3.02 * u * tiny + u * (n * tiny))
    (hms : ns * |ms| ≤ 1.01 * As) (hmt : nt * |mt| ≤ 1.01 * At)
    (hAs : ns * tiny ≤ As) (hAt : nt * tiny ≤ At) :
    E ≤ 6 * u * (ns * At + nt * As) := by
  have hu := u_pos
  have ht := tiny_pos
  have hAs0 : 0 ≤ As := le_trans (by positivity) hAs
  have hAt0 : 0 ≤ At := le_trans (by positivity) hAt
  have m2 : As ≤ nt * As := le_mul_of_one_le_left hAs0 htr
  have m3 : At ≤ ns * At := le_mul_of_one_le_left hAt0 hsr
  have m4 : n * tiny ≤ As + At := by rw [hn']; linarith
  have m5 : tiny ≤ As := by have := mul_le_mul_of_nonneg_right hsr ht.le; linarith
  have m6 : tiny ≤ At := by have := mul_le_mul_of_nonneg_right htr ht.le; linarith
  have q1 := mul_le_mul_of_nonneg_left hms hu.le
  have q2 := mul_le_mul_of_nonneg_left hmt hu.le
  have q3 := mul_le_mul_of_nonneg_left m4 hu.le
  have q5 := mul_le_mul_of_nonneg_left m5 hu.le
  have q6 := mul_le_mul_of_nonneg_left m6 hu.le
  have q7 := mul_le_mul_of_nonneg_left m2 hu.le
  have q8 := mul_le_mul_of_nonneg_left m3 hu.le
  rw [ha, hb] at k1
  have p1 : 0 ≤ u * (ns * At) := by positivity
  have p2 : 0 ≤ u * (nt * As) := by positivity
  linarith

/-- DuckDB's merged mean of pairs, `fl(fl(fl(n_s m_s) + fl(n_t m_t)) / n)`: within
`6 u (n_s A_t + n_t A_s) / n` of the children's weighted mean, when
`n_x |m_x| ≤ 1.01 A_x` and `n_x tiny ≤ A_x`. -/
theorem StdModel.wmean_spec {ns nt : ℕ} (hs : 1 ≤ ns) (ht1 : 1 ≤ nt) (hn : ns + nt ≤ 2 ^ 32)
    {ms mt As At : ℝ} (hms : ns * |ms| ≤ 1.01 * As) (hmt : nt * |mt| ≤ 1.01 * At)
    (hAs : ns * tiny ≤ As) (hAt : nt * tiny ≤ At) (hbs : |ms| ≤ 2 ^ 401) (hbt : |mt| ≤ 2 ^ 401) :
    |M.fl (M.fl (M.fl ((ns : ℝ) * ms) + M.fl ((nt : ℝ) * mt)) / ((nt : ℝ) + ns))
        - ((nt : ℝ) * mt + ns * ms) / ((nt : ℝ) + ns)|
      ≤ 6 * u * ((ns : ℝ) * At + nt * As) / ((nt : ℝ) + ns) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have htn1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hsr : (1 : ℝ) ≤ ns := by exact_mod_cast hs
  have htr : (1 : ℝ) ≤ nt := by exact_mod_cast ht1
  have hnr : (ns : ℝ) + nt ≤ 2 ^ 32 := by exact_mod_cast hn
  obtain ⟨n, hn'⟩ : ∃ n : ℝ, n = (nt : ℝ) + ns := ⟨_, rfl⟩
  rw [← hn']
  have hn0 : 0 < n := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ns * |ms| := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = nt * |mt| := ⟨_, rfl⟩
  have ha' : |(ns : ℝ) * ms| = a := by rw [ha, abs_mul, Nat.abs_cast]
  have hb' : |(nt : ℝ) * mt| = b := by rw [hb, abs_mul, Nat.abs_cast]
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hab : a ≤ 2 ^ 433 := by
    rw [ha]; have := mul_le_mul (by linarith : (ns : ℝ) ≤ 2 ^ 32) hbs (abs_nonneg _) (by norm_num)
    norm_num at this ⊢; linarith
  have hbb : b ≤ 2 ^ 433 := by
    rw [hb]; have := mul_le_mul (by linarith : (nt : ℝ) ≤ 2 ^ 32) hbt (abs_nonneg _) (by norm_num)
    norm_num at this ⊢; linarith
  have r1 := M.err ((ns : ℝ) * ms) (by rw [ha']; linarith)
  have r2 := M.err ((nt : ℝ) * mt) (by rw [hb']; linarith)
  rw [ha'] at r1
  rw [hb'] at r2
  generalize M.fl ((ns : ℝ) * ms) = p1 at r1 ⊢
  generalize M.fl ((nt : ℝ) * mt) = p2 at r2 ⊢
  have hsum : |p1 + p2| ≤ a + b + u * (a + tiny) + u * (b + tiny) := by
    have h1 := abs_add_le p1 p2
    have h2 := abs_sub_abs_le_abs_sub p1 ((ns : ℝ) * ms)
    have h3 := abs_sub_abs_le_abs_sub p2 ((nt : ℝ) * mt)
    rw [ha'] at h2; rw [hb'] at h3
    linarith
  have hsb : |p1 + p2| ≤ 2 ^ 435 := by
    have : u * (a + tiny) + u * (b + tiny) ≤ 2 ^ 434 := by
      have := mul_le_mul hu' (by linarith : a + tiny ≤ 2 ^ 434) (by positivity) (by norm_num)
      have := mul_le_mul hu' (by linarith : b + tiny ≤ 2 ^ 434) (by positivity) (by norm_num)
      norm_num at *; linarith
    have : (2 : ℝ) ^ 433 + 2 ^ 433 + 2 ^ 434 ≤ 2 ^ 435 := by norm_num
    linarith
  have r3 := M.err (p1 + p2) (by linarith)
  generalize M.fl (p1 + p2) = q at r3 ⊢
  -- `E = |q − (b' + a')|`
  have hE : |q - ((nt : ℝ) * mt + ns * ms)| ≤ 2.01 * u * (a + b) + 3.01 * u * tiny := by
    have e : q - ((nt : ℝ) * mt + ns * ms)
        = (q - (p1 + p2)) + (p1 - (ns : ℝ) * ms) + (p2 - (nt : ℝ) * mt) := by ring
    rw [e]
    have k1 := abs_add_le ((q - (p1 + p2)) + (p1 - (ns : ℝ) * ms)) (p2 - (nt : ℝ) * mt)
    have k2 := abs_add_le (q - (p1 + p2)) (p1 - (ns : ℝ) * ms)
    have k3 : u * |p1 + p2| ≤ u * (a + b + u * (a + tiny) + u * (b + tiny)) :=
      mul_le_mul_of_nonneg_left hsum hu.le
    have k4 : u * (u * (a + tiny)) ≤ 0.001 * (u * (a + tiny)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have k5 : u * (u * (b + tiny)) ≤ 0.001 * (u * (b + tiny)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have p1 : 0 ≤ u * a := by positivity
    have p2 : 0 ≤ u * b := by positivity
    have p3 : 0 ≤ u * tiny := by positivity
    linarith
  have hqb : |q / n| ≤ 2 ^ 436 := by
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    have := abs_sub_abs_le_abs_sub q ((nt : ℝ) * mt + ns * ms)
    have := abs_add_le ((nt : ℝ) * mt) (ns * ms)
    rw [hb', ha'] at this
    have : 2.01 * u * (a + b) + 3.01 * u * tiny ≤ 2 ^ 434 := by
      have k1 : u * (a + b) ≤ 1 / 2 ^ 53 * 2 ^ 434 :=
        mul_le_mul hu' (by linarith : a + b ≤ 2 ^ 434) (by positivity) (by norm_num)
      have k2 : u * tiny ≤ 1 / 2 ^ 53 * 1 := mul_le_mul hu' htn1 ht.le (by norm_num)
      have k3 : (2.01 : ℝ) * (1 / 2 ^ 53 * 2 ^ 434) + 3.01 * (1 / 2 ^ 53 * 1) ≤ 2 ^ 434 := by
        norm_num
      linarith
    have : (2 : ℝ) ^ 436 ≤ 2 ^ 436 * n := le_mul_of_one_le_right (by norm_num) (by linarith)
    have : (2 : ℝ) ^ 433 + 2 ^ 433 + 2 ^ 434 ≤ 2 ^ 436 := by norm_num
    linarith
  have r4 := M.err (q / n) (by linarith)
  rw [le_div_iff₀ hn0]
  have k1 : n * |M.fl (q / n) - ((nt : ℝ) * mt + ns * ms) / n|
      ≤ 3.02 * u * (a + b) + 3.02 * u * tiny + u * (n * tiny) := by
    have e : M.fl (q / n) - ((nt : ℝ) * mt + ns * ms) / n
        = (M.fl (q / n) - q / n) + (q - ((nt : ℝ) * mt + ns * ms)) / n := by
      field_simp; ring
    rw [e]
    have h1 := abs_add_le (M.fl (q / n) - q / n) ((q - ((nt : ℝ) * mt + ns * ms)) / n)
    have h2 : n * |(q - ((nt : ℝ) * mt + ns * ms)) / n| = |q - ((nt : ℝ) * mt + ns * ms)| := by
      rw [abs_div, abs_of_pos hn0]; field_simp
    have h3 : n * |q / n| ≤ a + b + |q - ((nt : ℝ) * mt + ns * ms)| := by
      rw [abs_div, abs_of_pos hn0, mul_div_cancel₀ _ hn0.ne']
      have := abs_sub_abs_le_abs_sub q ((nt : ℝ) * mt + ns * ms)
      have := abs_add_le ((nt : ℝ) * mt) (ns * ms)
      rw [hb', ha'] at this
      linarith
    have h4 := mul_le_mul_of_nonneg_left h1 hn0.le
    have h5 := mul_le_mul_of_nonneg_left r4 hn0.le
    have h5' : n * (u * (|q / n| + tiny)) = u * (n * |q / n|) + u * (n * tiny) := by ring
    have h6 := mul_le_mul_of_nonneg_left h3 hu.le
    have h7 := mul_le_mul_of_nonneg_left hE hu.le
    have h8 : u * (2.01 * u * (a + b) + 3.01 * u * tiny)
        ≤ 0.01 * (u * (a + b)) + 0.01 * (u * tiny) := by
      have c1 : u * (2.01 * u * (a + b)) ≤ 0.01 * (u * (a + b)) := by
        have := mul_le_mul_of_nonneg_right (by linarith : 2.01 * u ≤ 0.01)
          (by positivity : 0 ≤ u * (a + b))
        linarith
      have c2 : u * (3.01 * u * tiny) ≤ 0.01 * (u * tiny) := by
        have := mul_le_mul_of_nonneg_right (by linarith : 3.01 * u ≤ 0.01)
          (by positivity : 0 ≤ u * tiny)
        linarith
      linarith
    have h9 : n * (|M.fl (q / n) - q / n| + |(q - ((nt : ℝ) * mt + ns * ms)) / n|)
        = n * |M.fl (q / n) - q / n| + n * |(q - ((nt : ℝ) * mt + ns * ms)) / n| := by ring
    have h10 : u * (a + b + |q - ((nt : ℝ) * mt + ns * ms)|)
        = u * (a + b) + u * |q - ((nt : ℝ) * mt + ns * ms)| := by ring
    linarith
  rw [mul_comm]
  exact wmerge_arith hsr htr hn' ha hb k1 hms hmt hAs hAt

/-- `√(a b) + √(c d) ≤ √((a + c)(b + d))`. -/
theorem sqrt_add_sqrt_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    √(a * b) + √(c * d) ≤ √((a + c) * (b + d)) := by
  have p := Real.sqrt_nonneg (a * b)
  have q := Real.sqrt_nonneg (c * d)
  have hp : √(a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have hq : √(c * d) ^ 2 = c * d := Real.sq_sqrt (by positivity)
  have h1 : (2 * (√(a * b) * √(c * d))) ^ 2 ≤ (a * d + b * c) ^ 2 := by
    have e : (2 * (√(a * b) * √(c * d))) ^ 2 = 4 * (a * b) * (c * d) := by
      rw [mul_pow, mul_pow, hp, hq]; ring
    rw [e]; nlinarith [sq_nonneg (a * d - b * c)]
  have h2 : 2 * (√(a * b) * √(c * d)) ≤ a * d + b * c :=
    (abs_le_of_sq_le_sq' h1 (by positivity)).2
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- The error of `Δ̂x Δ̂y` in a merge, times `h`. -/
theorem cprod_err {Δx Δy Δhx Δhy Ax Ay h : ℝ} (hh : 0 ≤ h) (hΔx : |Δx| ≤ Ax) (hΔy : |Δy| ≤ Ay)
    (hex : |Δhx - Δx| ≤ 7.1 * u * Ax + u * |Δx|) (hey : |Δhy - Δy| ≤ 7.1 * u * Ay + u * |Δy|) :
    h * |Δhx * Δhy - Δx * Δy| ≤ 7.1 * u * (Ax * (h * |Δy|) + Ay * (h * |Δx|))
      + 2 * u * (h * (|Δx| * |Δy|)) + 103 * u ^ 2 * h * (Ax * Ay) := by
  have hu := u_pos
  have hAx : 0 ≤ Ax := le_trans (abs_nonneg _) hΔx
  have hAy : 0 ≤ Ay := le_trans (abs_nonneg _) hΔy
  have e : Δhx * Δhy - Δx * Δy = Δx * (Δhy - Δy) + Δy * (Δhx - Δx) + (Δhx - Δx) * (Δhy - Δy) := by
    ring
  have h1 : |Δx * (Δhy - Δy)| ≤ |Δx| * (7.1 * u * Ay + u * |Δy|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hey (abs_nonneg _)
  have h2 : |Δy * (Δhx - Δx)| ≤ |Δy| * (7.1 * u * Ax + u * |Δx|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hex (abs_nonneg _)
  have bx : 7.1 * u * Ax + u * |Δx| ≤ 8.1 * u * Ax := by
    have := mul_le_mul_of_nonneg_left hΔx hu.le; linarith
  have by' : 7.1 * u * Ay + u * |Δy| ≤ 8.1 * u * Ay := by
    have := mul_le_mul_of_nonneg_left hΔy hu.le; linarith
  have h3 : |(Δhx - Δx) * (Δhy - Δy)| ≤ (8.1 * u * Ax) * (8.1 * u * Ay) := by
    rw [abs_mul]; exact mul_le_mul (le_trans hex bx) (le_trans hey by') (abs_nonneg _) (by positivity)
  have h4 : |Δhx * Δhy - Δx * Δy| ≤ |Δx| * (7.1 * u * Ay + u * |Δy|)
      + |Δy| * (7.1 * u * Ax + u * |Δx|) + (8.1 * u * Ax) * (8.1 * u * Ay) := by
    rw [e]
    have := abs_add_le (Δx * (Δhy - Δy) + Δy * (Δhx - Δx)) ((Δhx - Δx) * (Δhy - Δy))
    have := abs_add_le (Δx * (Δhy - Δy)) (Δy * (Δhx - Δx))
    linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hh
  have p : 0 ≤ u ^ 2 * h * (Ax * Ay) := by positivity
  have e2 : h * (|Δx| * (7.1 * u * Ay + u * |Δy|) + |Δy| * (7.1 * u * Ax + u * |Δx|)
      + (8.1 * u * Ax) * (8.1 * u * Ay)) = 7.1 * u * (Ax * (h * |Δy|) + Ay * (h * |Δx|))
        + 2 * u * (h * (|Δx| * |Δy|)) + 65.61 * (u ^ 2 * h * (Ax * Ay)) := by ring
  have e3 : 103 * u ^ 2 * h * (Ax * Ay) = 103 * (u ^ 2 * h * (Ax * Ay)) := by ring
  linarith

/-- The merge's term `T̂ ≈ Δ̂x Δ̂y h`, against `ΔC = Δx Δy h`, with `Y = |ΔC|`. -/
theorem cT_err {T Q ΔC P Y A h : ℝ} (hP : 0 ≤ P) (hY : |ΔC| ≤ Y) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hQ : |Q - ΔC| ≤ 7.1 * u * P + 2 * u * Y + 103 * u ^ 2 * h * A)
    (hT : |T - Q| ≤ 5 * u * (|Q| + (1 + h) * tiny)) :
    |T - ΔC| ≤ 7.2 * u * P + 7.1 * u * Y + 104 * u ^ 2 * h * A + 5 * u * (1 + h) * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hY
  have hQa : |Q| ≤ Y + (7.1 * u * P + 2 * u * Y + 103 * u ^ 2 * h * A) := by
    have := abs_sub_abs_le_abs_sub Q ΔC; linarith
  have p1 : 0 ≤ u * P := by positivity
  have p2 : 0 ≤ u ^ 2 * h * A := by positivity
  have p3 : 0 ≤ u * Y := by positivity
  have h1 : 5 * u * |Q| ≤ 5 * (u * Y) + 0.1 * (u * P) + 0.01 * (u * Y) + 1 * (u ^ 2 * h * A) := by
    have := mul_le_mul_of_nonneg_left hQa (by positivity : (0 : ℝ) ≤ 5 * u)
    have q1 : 5 * u * (7.1 * u * P) ≤ 0.1 * (u * P) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 35.5 * u ≤ 0.1) p1; nlinarith
    have q2 : 5 * u * (2 * u * Y) ≤ 0.01 * (u * Y) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 10 * u ≤ 0.01) p3; nlinarith
    have q3 : 5 * u * (103 * u ^ 2 * h * A) ≤ 1 * (u ^ 2 * h * A) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 515 * u ≤ 1) p2; nlinarith
    have e : 5 * u * (Y + (7.1 * u * P + 2 * u * Y + 103 * u ^ 2 * h * A))
        = 5 * (u * Y) + 5 * u * (7.1 * u * P) + 5 * u * (2 * u * Y)
          + 5 * u * (103 * u ^ 2 * h * A) := by ring
    linarith
  have e : T - ΔC = (T - Q) + (Q - ΔC) := by ring
  rw [e]
  have h3 := abs_add_le (T - Q) (Q - ΔC)
  have h4 : 5 * u * (|Q| + (1 + h) * tiny) = 5 * u * |Q| + 5 * u * (1 + h) * tiny := by ring
  have e1 : 7.2 * u * P = 7.2 * (u * P) := by ring
  have e2 : 7.1 * u * P = 7.1 * (u * P) := by ring
  have e3 : 104 * u ^ 2 * h * A = 104 * (u ^ 2 * h * A) := by ring
  have e4 : 103 * u ^ 2 * h * A = 103 * (u ^ 2 * h * A) := by ring
  have e5 : 7.1 * u * Y = 7.1 * (u * Y) := by ring
  have e6 : 2 * u * Y = 2 * (u * Y) := by ring
  linarith
