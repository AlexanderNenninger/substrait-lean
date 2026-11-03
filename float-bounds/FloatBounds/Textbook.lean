module

public import FloatBounds.TwoPass

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

section
variable {N : ℕ} {B : ℝ} (S : Scale N B)
include S

/-!
# Textbook: `Σxy − Σx · Σy / n`

The weakest of the common algorithms: its absolute error is `O(n · u · Σx²)`.
-/

/-- **Textbook**: `Σxy − Σx · Σy / n`, each operation rounded. -/
noncomputable def StdModel.textbook (ps : List (ℝ × ℝ)) : ℝ :=
  M.fl (M.sum (ps.map fun p => M.fl (p.1 * p.2))
    - M.fl (M.fl (M.sum (ps.map Prod.fst) * M.sum (ps.map Prod.snd)) / ps.length))

theorem StdModel.textbook_error {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ N)
    (hb : Bounded B ps) :
    |M.textbook ps - comoment ps| ≤ 64 * ps.length ^ 2 * u * B ^ 2 := by
  obtain ⟨hu, hBp, F1, -, F4, htB, F3, htB2, hk32, hB4, hB2⟩ := S.facts hN
  have hB0 := hBp.le
  have hl : (1 : ℝ) ≤ ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  set n : ℝ := (ps.length : ℝ) with hnl
  clear_value n
  have hn0 : 0 ≤ n := by linarith
  have hw : 0 ≤ u * B ^ 2 := by positivity
  have hB2' := sq_nonneg B
  have htB2' : tiny ≤ B ^ 2 := by linarith
  have hnB2 : n * B ^ 2 ≤ 2 ^ 32 * 2 ^ 800 := mul_le_mul hk32 hB2 hB2' (by norm_num)
  have hnB : n * B ≤ 2 ^ 32 * 2 ^ 400 := mul_le_mul hk32 hB4 hB0 (by norm_num)
  have hn2B2 : n ^ 2 * B ^ 2 ≤ 2 ^ 32 * (2 ^ 32 * 2 ^ 800) := by
    have : n ^ 2 * B ^ 2 = n * (n * B ^ 2) := by ring
    rw [this]; exact mul_le_mul hk32 hnB2 (mul_nonneg hn0 hB2') (by norm_num)
  have hnu : n * u ≤ 1 / 2 ^ 21 := by rw [hnl]; exact S.len_u hN
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hnw : 0 ≤ n * (u * B ^ 2) := mul_nonneg hn0 hw
  have hn2w : n * (u * B ^ 2) ≤ n ^ 2 * (u * B ^ 2) := mul_le_mul_of_nonneg_right hnn hw
  have hn3w : n ^ 2 * (u * B ^ 2) ≤ n ^ 3 * (u * B ^ 2) := by
    have : n ^ 2 ≤ n ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hw
  have huB2 : u * B ^ 2 ≤ B ^ 2 / 2 ^ 53 := by
    have := mul_le_mul_of_nonneg_right F4 hB0; linarith
  -- `Σxy`
  have hxy : ∀ p ∈ ps, |M.fl (p.1 * p.2) - p.1 * p.2| ≤ 3 * u * B ^ 2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hb p hp
    have hz : |p.1 * p.2| ≤ B ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hB0
    have := M.round_count (c := 1) (P := p.1 * p.2) (D := p.1 * p.2) (e := 0) (Dm := B ^ 2)
      (by simp) hz (by positivity) htB2' le_rfl (by linarith)
    simp only [mul_one, mul_zero, zero_add, one_mul] at this
    linarith
  have hYxy : ∀ x ∈ ps.map (fun p => M.fl (p.1 * p.2)), |x| ≤ 2 * B ^ 2 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hxy p hp
    have := abs_sub_abs_le_abs_sub (M.fl (p.1 * p.2)) (p.1 * p.2)
    obtain ⟨h1, h2⟩ := hb p hp
    have : |p.1 * p.2| ≤ B ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hB0
    linarith
  have sxy' := M.sum_bound S (by simpa using hN) hYxy (by linarith)
    (by simp only [List.length_map]; rw [← hnl]; linarith)
  simp only [List.length_map] at sxy'
  rw [← hnl] at sxy'
  have dxy := abs_sum_map_sub_le (fun p => M.fl (p.1 * p.2)) (fun p => p.1 * p.2)
    (fun _ => (1 : ℝ)) (3 * u * B ^ 2) ps (fun p hp => by simpa using hxy p hp)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at dxy
  rw [← hnl] at dxy
  set Sxy := M.sum (ps.map fun p => M.fl (p.1 * p.2))
  have hSxy : |Sxy - sxy ps| ≤ 8 * n ^ 2 * (u * B ^ 2) := by
    have : Sxy - sxy ps = (Sxy - (ps.map fun p => M.fl (p.1 * p.2)).sum)
        + ((ps.map fun p => M.fl (p.1 * p.2)).sum - sxy ps) := by ring
    rw [this]
    refine le_trans (abs_add_le _ _) ?_
    have e1 : 2 * n ^ 2 * u * (2 * B ^ 2 + tiny) ≤ 5 * n ^ 2 * (u * B ^ 2) := by
      have : 2 * B ^ 2 + tiny ≤ 5 / 2 * B ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * n ^ 2 * u)
      linarith
    have e2 : 3 * u * B ^ 2 * n = 3 * (n * (u * B ^ 2)) := by ring
    unfold sxy
    linarith [sxy'.1]
  -- `Σx` and `Σy`
  have hX : ∀ x ∈ ps.map Prod.fst, |x| ≤ B := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hb p hp).1
  have hYy : ∀ x ∈ ps.map Prod.snd, |x| ≤ B := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hb p hp).2
  have tB : tiny ≤ B := by linarith
  have sx' := M.sum_bound S (by simpa using hN) hX tB (by simp only [List.length_map]; rw [← hnl]; linarith)
  have sy' := M.sum_bound S (by simpa using hN) hYy tB (by simp only [List.length_map]; rw [← hnl]; linarith)
  simp only [List.length_map] at sx' sy'
  rw [← hnl] at sx' sy'
  have bsx : |sx ps| ≤ n * B := by
    have := abs_sum_le_of_bound hX; simpa [hnl, sx] using this
  have bsy : |sy ps| ≤ n * B := by
    have := abs_sum_le_of_bound hYy; simpa [hnl, sy] using this
  have hex : 2 * n ^ 2 * u * (B + tiny) ≤ 3 * n * (n * u * B) := by
    have : B + tiny ≤ 3 / 2 * B := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * n ^ 2 * u)
    linarith
  have ex : |M.sum (ps.map Prod.fst) - sx ps| ≤ 3 * n * (n * u * B) := le_trans sx'.1 hex
  have ey : |M.sum (ps.map Prod.snd) - sy ps| ≤ 3 * n * (n * u * B) := le_trans sy'.1 hex
  set X := M.sum (ps.map Prod.fst)
  set Y := M.sum (ps.map Prod.snd)
  -- `Σx · Σy`, rounded
  have hXY := abs_mul_sub_le ex ey bsx bsy
  have hexs : 3 * n * (n * u * B) ≤ n * B / 2 ^ 19 := by
    have := mul_le_mul_of_nonneg_left F1 (by linarith : (0 : ℝ) ≤ 3 * n)
    have : 0 ≤ n * B := mul_nonneg hn0 hB0
    linarith
  have hXY' : |X * Y - sx ps * sy ps| ≤ 7 * n ^ 3 * (u * B ^ 2) := by
    have h1 : 3 * n * (n * u * B) * (n * B + 3 * n * (n * u * B))
        ≤ 3 * n * (n * u * B) * (n * B + n * B / 2 ^ 19) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) (mul_nonneg (mul_nonneg hn0 hu.le) hB0)); linarith
    have : 0 ≤ n ^ 3 * (u * B ^ 2) := mul_nonneg (pow_nonneg hn0 3) hw
    linarith
  have hDm : |sx ps * sy ps| ≤ n ^ 2 * B ^ 2 := by
    rw [abs_mul]; have := mul_le_mul bsx bsy (abs_nonneg _) (mul_nonneg hn0 hB0); linarith
  have hsmall : 7 * n ^ 3 * (u * B ^ 2) ≤ n ^ 2 * B ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hnu (by positivity : (0 : ℝ) ≤ 7 * n ^ 2 * B ^ 2)
    have : 0 ≤ n ^ 2 * B ^ 2 := by positivity
    linarith
  have hBn2 : B ^ 2 ≤ n ^ 2 * B ^ 2 := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n ^ 2 by nlinarith) hB2'; linarith
  have hBn1 : B ^ 2 ≤ n * B ^ 2 := by
    have := mul_le_mul_of_nonneg_right hl hB2'; linarith
  have hnB2n : n * B ^ 2 ≤ n ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right hnn hB2'
  have hun2 : u * (n ^ 2 * B ^ 2) ≤ n ^ 2 * B ^ 2 / 2 ^ 53 := by
    have := mul_le_mul_of_nonneg_right F4 hB0
    have := mul_le_mul_of_nonneg_left huB2 (sq_nonneg n); linarith
  have hP := M.round_count (c := 1) (by simpa using hXY') hDm hsmall
    (by linarith) le_rfl (by linarith)
  simp only [mul_one, one_mul] at hP
  -- divided by `n`
  have hQ := M.round_div hP hDm (by linarith)
    (by have := mul_le_mul_of_nonneg_left htB2' hn0; linarith) hl (by linarith)
  have hQ' : (7 * n ^ 3 * (u * B ^ 2) + 3 * u * (n ^ 2 * B ^ 2)) / n
      + 3 * u * (n ^ 2 * B ^ 2) / n ≤ 13 * n ^ 2 * (u * B ^ 2) := by
    rw [← add_div, div_le_iff₀ (by linarith)]
    have : 3 * u * (n ^ 2 * B ^ 2) = 3 * (n ^ 2 * (u * B ^ 2)) := by ring
    linarith
  -- the difference
  set Q := M.fl (M.fl (X * Y) / n)
  have hz : |(Sxy - Q) - comoment ps| ≤ 21 * n ^ 2 * (u * B ^ 2) := by
    rw [comoment_eq, ← hnl]
    have : (Sxy - Q) - (sxy ps - sx ps * sy ps / n)
        = (Sxy - sxy ps) - (Q - sx ps * sy ps / n) := by ring
    rw [this]
    refine le_trans (abs_sub _ _) ?_
    linarith
  have hC := abs_comoment_le hb hB0
  rw [← hnl] at hC
  have hsm : 21 * n ^ 2 * (u * B ^ 2) ≤ 4 * n * B ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hnu (mul_nonneg (by linarith) hB2' : (0 : ℝ) ≤ 21 * n * B ^ 2); linarith
  have hfin := M.round_count (c := 1) (by simpa using hz) hC hsm (by linarith) le_rfl
    (by linarith)
  simp only [mul_one, one_mul] at hfin
  unfold StdModel.textbook
  rw [← hnl]
  have : 3 * u * (4 * n * B ^ 2) = 12 * (n * (u * B ^ 2)) := by ring
  have : 64 * n ^ 2 * u * B ^ 2 = 64 * (n ^ 2 * (u * B ^ 2)) := by ring
  have : 0 ≤ n ^ 2 * (u * B ^ 2) := by positivity
  linarith

end

end FloatBounds

end
