module

public import FloatBounds.Welford

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-!
# Two-pass: Lean's own algorithm

The means, then the products of the deviations from them, added in order
(`meanOf`, then `coDevSum` in `SubstraitLean/Aggregate.lean`).
-/

/-- `γ k ≤ 2 k u` while `k u ≤ 1/2`. -/
theorem gamma_le_two {k : ℕ} (h : (k : ℝ) * u ≤ 1 / 2) : gamma k ≤ 2 * k * u := by
  have hu := u_pos
  unfold gamma
  rw [div_le_iff₀ (by linarith)]
  have : (0 : ℝ) ≤ k * u := by positivity
  nlinarith

/-- The rounded mean of a list. -/
noncomputable def StdModel.mean (xs : List ℝ) : ℝ := M.fl (M.sum xs / xs.length)

section
variable {N : ℕ} {B : ℝ} (S : Scale N B)
include S

/-- `n · u ≤ 2⁻²¹` for a list of at most `N` values. -/
theorem Scale.len_u {xs : List α} (hn : xs.length ≤ N) : (xs.length : ℝ) * u ≤ 1 / 2 ^ 21 := by
  have := S.nu_le
  have : (xs.length : ℝ) * u ≤ N * u := by have := u_pos; gcongr
  norm_num at *; linarith

/-- The rounded sum of `n ≤ N` values within `Y` (with `tiny ≤ Y`): within
`2 n² u (Y + tiny)` of the exact sum, and at most `2 n Y` in magnitude. -/
theorem StdModel.sum_bound {xs : List ℝ} (hn : xs.length ≤ N) {Y : ℝ} (hY : ∀ x ∈ xs, |x| ≤ Y)
    (htY : tiny ≤ Y) (hbig : (xs.length : ℝ) * Y ≤ 2 ^ 998) :
    |M.sum xs - xs.sum| ≤ 2 * xs.length ^ 2 * u * (Y + tiny) ∧
      |M.sum xs| ≤ 2 * xs.length * Y := by
  have hu := u_pos
  have hY0 : 0 ≤ Y := le_trans tiny_pos.le htY
  set n : ℝ := (xs.length : ℝ)
  have hn0 : 0 ≤ n := by positivity
  have hnu : n * u ≤ 1 / 2 ^ 21 := S.len_u hn
  have hg := gamma_le_two (k := xs.length) (by linarith)
  have hg0 := gamma_nonneg (n := xs.length) (by linarith)
  have hnY : n * (Y + tiny) ≤ 2 * (n * Y) := by
    have := mul_le_mul_of_nonneg_left htY hn0; linarith
  have h1g : 1 + gamma xs.length ≤ 2 := by
    have : 2 * n * u ≤ 1 := by linarith
    linarith
  have hov : (1 + gamma xs.length) * (n * (Y + tiny)) ≤ maxFinite := by
    have h0 : 0 ≤ n * (Y + tiny) := mul_nonneg hn0 (by linarith [tiny_pos])
    have := mul_le_mul h1g hnY h0 (by norm_num)
    have := two_pow_le_maxFinite
    linarith
  have h := M.sum_error_of_bound hY (by linarith) hov
  have h2 : gamma xs.length * (n * (Y + tiny)) ≤ 2 * n * u * (n * (Y + tiny)) :=
    mul_le_mul hg le_rfl (mul_nonneg hn0 (by linarith [tiny_pos])) (by nlinarith)
  have e1 : |M.sum xs - xs.sum| ≤ 2 * n ^ 2 * u * (Y + tiny) := by
    have : 2 * n * u * (n * (Y + tiny)) = 2 * n ^ 2 * u * (Y + tiny) := by ring
    linarith
  refine ⟨e1, ?_⟩
  have := abs_sub_abs_le_abs_sub (M.sum xs) xs.sum
  have := abs_sum_le_of_bound hY
  have : 2 * n ^ 2 * u * (Y + tiny) ≤ n * Y := by
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnu hn0)
      (by linarith [tiny_pos] : (0 : ℝ) ≤ Y + tiny)
    have : 2 * n ^ 2 * u * (Y + tiny) = 2 * (n * (n * u) * (Y + tiny)) := by ring
    have : n * (Y + tiny) ≤ 2 * (n * Y) := hnY
    nlinarith
  linarith

/-- The rounded mean of `n ≤ N` values within `B`: within `8 n u B`. -/
theorem StdModel.mean_error {xs : List ℝ} (hne : xs ≠ []) (hn : xs.length ≤ N)
    (hB : ∀ x ∈ xs, |x| ≤ B) :
    |M.mean xs - xs.sum / xs.length| ≤ 8 * xs.length * u * B := by
  have hu := u_pos
  have hBp := S.B_pos
  have htB := S.tiny_le_B
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hl : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn32 : (xs.length : ℝ) ≤ 2 ^ 32 := le_trans (by exact_mod_cast hn) S.n_le'
  set n : ℝ := (xs.length : ℝ)
  have hn0 : 0 ≤ n := by linarith
  have hnu : n * u ≤ 1 / 2 ^ 21 := S.len_u hn
  have hn2u : ((xs.length + 2 : ℕ) : ℝ) * u ≤ 1 / 2 := by push_cast; linarith
  have hg := gamma_le_two hn2u
  have hov : (1 + gamma xs.length) * (n * (B + tiny)) ≤ maxFinite := by
    have : 1 + gamma xs.length ≤ 2 := by
      have := gamma_le_two (k := xs.length) (by linarith); linarith
    have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
    have : n * (B + tiny) ≤ 2 ^ 32 * (2 ^ 400 + 1) :=
      mul_le_mul hn32 (by linarith [S.B_le]) (by linarith [tiny_pos]) (by norm_num)
    have : (1 + gamma xs.length) * (n * (B + tiny)) ≤ 2 * (2 ^ 32 * (2 ^ 400 + 1)) :=
      mul_le_mul (by assumption) this (mul_nonneg hn0 (by linarith [tiny_pos])) (by norm_num)
    linarith [two_pow_le_maxFinite]
  have h := M.avg_error_of_bound hne hB (by linarith) hov
  unfold StdModel.mean
  refine le_trans h ?_
  push_cast at hg
  have htB' : tiny ≤ B / 2 ^ 64 := by
    have : (2 : ℝ)⁻¹ ^ 500 * B ≤ B / 2 ^ 64 := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ)⁻¹ ^ 500 * 2 ^ 64 ≤ 1 := by norm_num
      nlinarith
    linarith
  have h1 : gamma (xs.length + 2) * (B + tiny) ≤ 2 * (n + 2) * u * (B + B / 2 ^ 64) :=
    mul_le_mul hg (by linarith) (by linarith [tiny_pos]) (by nlinarith)
  have h2 : 2 * (n + 2) * u * (B + B / 2 ^ 64) ≤ 8 * n * u * B := by
    have : (n + 2) ≤ 3 * n := by linarith
    have huB : 0 ≤ u * B := by positivity
    have := mul_le_mul_of_nonneg_right this huB
    nlinarith
  linarith

/-! ## Two-pass -/

/-- **Two-pass**: the means, then the products of the deviations from them,
added in order (Lean's `coDevSum` after `meanOf`). -/
noncomputable def StdModel.twoPass (ps : List (ℝ × ℝ)) : ℝ :=
  M.sum (ps.map fun p => M.fl (M.fl (p.1 - M.mean (ps.map Prod.fst))
    * M.fl (p.2 - M.mean (ps.map Prod.snd))))

theorem StdModel.twoPass_error {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ N)
    (hb : Bounded B ps) :
    |M.twoPass ps - comoment ps| ≤ 64 * ps.length ^ 2 * u * B ^ 2 := by
  obtain ⟨hu, hBp, F1, -, F4, htB, F3, htB2, hk32, hB4, hB2⟩ := S.facts hN
  have hB0 := hBp.le
  set n := ps.length with hnl
  have hl : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hmx := M.mean_error S (xs := ps.map Prod.fst) (by simpa using hne) (by simpa using hN)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hb p hp).1)
  have hmy := M.mean_error S (xs := ps.map Prod.snd) (by simpa using hne) (by simpa using hN)
    (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hb p hp).2)
  simp only [List.length_map] at hmx hmy
  change |_ - mx ps| ≤ _ at hmx
  change |_ - my ps| ≤ _ at hmy
  set a := M.mean (ps.map Prod.fst)
  set b := M.mean (ps.map Prod.snd)
  have bx := abs_mx_le hb hB0
  have bY := abs_my_le hb hB0
  -- each product of deviations
  have hP : ∀ p ∈ ps, |M.fl (M.fl (p.1 - a) * M.fl (p.2 - b)) - (p.1 - mx ps) * (p.2 - my ps)|
      ≤ (33 * n + 18) * (u * B ^ 2) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hb p hp
    have dx := M.diff_error S hN h1 bx (by
      have : (p.1 - a) - (p.1 - mx ps) = -(a - mx ps) := by ring
      rw [this, abs_neg]; exact hmx)
    have dy := M.diff_error S hN h2 bY (by
      have : (p.2 - b) - (p.2 - my ps) = -(b - my ps) := by ring
      rw [this, abs_neg]; exact hmy)
    exact M.prod_error S hN (by have := abs_sub p.1 (mx ps); linarith)
      (by have := abs_sub p.2 (my ps); linarith) dx dy
  have hw : 0 ≤ u * B ^ 2 := by positivity
  have hnw : (33 * (n : ℝ) + 18) * (u * B ^ 2) ≤ B ^ 2 := by
    have := mul_le_mul_of_nonneg_right F1 hB0
    have := mul_le_mul_of_nonneg_right F4 hB0
    nlinarith
  -- their sum
  have hsm : (33 * (n : ℝ) + 18) * (u * B ^ 2) ≤ B ^ 2 / 2 ^ 15 := by
    have := mul_le_mul_of_nonneg_right F1 hB0
    have := mul_le_mul_of_nonneg_right F4 hB0
    nlinarith
  have hY : ∀ x ∈ ps.map (fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b))),
      |x| ≤ (4 + 1 / 2 ^ 15) * B ^ 2 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hP p hp
    have := abs_sub_abs_le_abs_sub (M.fl (M.fl (p.1 - a) * M.fl (p.2 - b)))
      ((p.1 - mx ps) * (p.2 - my ps))
    obtain ⟨h1, h2⟩ := hb p hp
    have : |(p.1 - mx ps) * (p.2 - my ps)| ≤ 4 * B ^ 2 := by
      rw [abs_mul]
      have := mul_le_mul (show |p.1 - mx ps| ≤ 2 * B by have := abs_sub p.1 (mx ps); linarith)
        (show |p.2 - my ps| ≤ 2 * B by have := abs_sub p.2 (my ps); linarith)
        (abs_nonneg _) (by positivity)
      linarith
    linarith
  have hB2' := sq_nonneg B
  have hsum := M.sum_bound S (by simpa using hN) hY (by nlinarith [htB2])
    (by simp only [List.length_map]; nlinarith)
  simp only [List.length_map] at hsum
  have hdiff := abs_sum_map_sub_le (fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b)))
    (fun p => (p.1 - mx ps) * (p.2 - my ps)) (fun _ => (1 : ℝ)) ((33 * n + 18) * (u * B ^ 2)) ps
    (fun p hp => by simpa using hP p hp)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at hdiff
  rw [← hnl] at hsum hdiff
  unfold StdModel.twoPass comoment
  have : M.sum (ps.map fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b)))
        - (ps.map fun p => (p.1 - mx ps) * (p.2 - my ps)).sum
      = (M.sum (ps.map fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b)))
          - (ps.map fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b))).sum)
        + ((ps.map fun p => M.fl (M.fl (p.1 - a) * M.fl (p.2 - b))).sum
          - (ps.map fun p => (p.1 - mx ps) * (p.2 - my ps)).sum) := by ring
  rw [this]
  refine le_trans (abs_add_le _ _) ?_
  have hn2 : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have e1 : 2 * (n : ℝ) ^ 2 * u * ((4 + 1 / 2 ^ 15) * B ^ 2 + tiny) ≤ 9 * n ^ 2 * (u * B ^ 2) := by
    have : (4 + 1 / 2 ^ 15) * B ^ 2 + tiny ≤ (9 / 2) * B ^ 2 := by nlinarith [htB2]
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * n ^ 2 * u)
    nlinarith
  have e2 : (n : ℝ) * (33 * n + 18) * (u * B ^ 2) ≤ 51 * n ^ 2 * (u * B ^ 2) := by
    have := mul_le_mul_of_nonneg_right hn2 hw
    nlinarith
  have : (33 * (n : ℝ) + 18) * (u * B ^ 2) * n = n * (33 * n + 18) * (u * B ^ 2) := by ring
  have : 64 * (n : ℝ) ^ 2 * u * B ^ 2 = 64 * n ^ 2 * (u * B ^ 2) := by ring
  have : 0 ≤ (n : ℝ) ^ 2 * (u * B ^ 2) := by positivity
  linarith [hsum.1]

end

end FloatBounds

end
