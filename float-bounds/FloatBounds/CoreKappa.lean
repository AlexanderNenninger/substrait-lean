module

public import FloatBounds.CovTwoPass
public import FloatBounds.CoreStats

/-!
# The statistical aggregates the core trusts, to first order in the spread (#85)

The properties of `SubstraitLean/StatProps.lean` in the form of
`TwoPassRel.lean`, `CovTwoPass.lean`, `MergeRel.lean` and `CovRel.lean`,
proved for the algorithm Lean computes (two-pass) on the doubles
`FloatCode.toFloat` decodes. Decoding moves a co-moment by
`2u (√(S_xx Q'_y) + √(S_yy Q'_x)) + 4u² √(Q'_x Q'_y)` (`decode_cov`), with
`Q' = Σ (|x| + tiny)²` of the exact values.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- The co-moment is bilinear. -/
theorem comoment_map_add {α : Type*} (qs : List α) (a b e f : α → ℝ) :
    comoment (qs.map fun q => (a q + e q, b q + f q))
      = comoment (qs.map fun q => (a q, b q)) + comoment (qs.map fun q => (a q, f q))
        + comoment (qs.map fun q => (e q, b q)) + comoment (qs.map fun q => (e q, f q)) := by
  simp only [comoment_eq, sxy, sx, sy, List.map_map, Function.comp_def, List.length_map]
  have h1 : (qs.map fun q => (a q + e q) * (b q + f q)).sum
      = (qs.map fun q => a q * b q).sum + (qs.map fun q => a q * f q).sum
        + (qs.map fun q => e q * b q).sum + (qs.map fun q => e q * f q).sum := by
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  have h2 : (qs.map fun q => a q + e q).sum = (qs.map a).sum + (qs.map e).sum :=
    List.sum_map_add
  have h3 : (qs.map fun q => b q + f q).sum = (qs.map b).sum + (qs.map f).sum :=
    List.sum_map_add
  rw [h1, h2, h3]
  ring

/-- `|C(a, b)| ≤ √(Σa²) √(Σb²)` over a list. -/
theorem abs_comoment_le_sq {α : Type*} (qs : List α) (a b : α → ℝ) :
    |comoment (qs.map fun q => (a q, b q))|
      ≤ √((qs.map fun q => a q ^ 2).sum) * √((qs.map fun q => b q ^ 2).sum) := by
  have h := sq_comoment_le (qs.map fun q => (a q, b q))
  simp only [List.map_map, Function.comp_def] at h
  have ha := comoment_dupL_le (qs.map a)
  have hb := comoment_dupL_le (qs.map b)
  have ea : comoment (dupL (qs.map a)) = comoment (qs.map fun q => (a q, a q)) := by
    simp [dupL, List.map_map, Function.comp_def]
  have eb : comoment (dupL (qs.map b)) = comoment (qs.map fun q => (b q, b q)) := by
    simp [dupL, List.map_map, Function.comp_def]
  rw [ea] at ha; rw [eb] at hb
  simp only [List.map_map, Function.comp_def] at ha hb
  have h0a : 0 ≤ comoment (qs.map fun q => (a q, a q)) := by
    rw [← ea]; exact comoment_dupL_nonneg _
  have h0b : 0 ≤ comoment (qs.map fun q => (b q, b q)) := by
    rw [← eb]; exact comoment_dupL_nonneg _
  rw [← Real.sqrt_mul (le_trans h0a ha)]
  apply Real.abs_le_sqrt
  exact le_trans h (mul_le_mul ha hb h0b (le_trans h0a ha))

/-- `|C(a, b)| ≤ √(S_aa) √(Σb²)`. -/
theorem abs_comoment_le_S {α : Type*} (qs : List α) (a b : α → ℝ) :
    |comoment (qs.map fun q => (a q, b q))|
      ≤ √(comoment (qs.map fun q => (a q, a q))) * √((qs.map fun q => b q ^ 2).sum) := by
  have h := sq_comoment_le (qs.map fun q => (a q, b q))
  simp only [List.map_map, Function.comp_def] at h
  have hb := comoment_dupL_le (qs.map b)
  have eb : comoment (dupL (qs.map b)) = comoment (qs.map fun q => (b q, b q)) := by
    simp [dupL, List.map_map, Function.comp_def]
  have ea : comoment (dupL (qs.map a)) = comoment (qs.map fun q => (a q, a q)) := by
    simp [dupL, List.map_map, Function.comp_def]
  rw [eb] at hb
  simp only [List.map_map, Function.comp_def] at hb
  have h0a : 0 ≤ comoment (qs.map fun q => (a q, a q)) := by
    rw [← ea]; exact comoment_dupL_nonneg _
  have h0b : 0 ≤ comoment (qs.map fun q => (b q, b q)) := by
    rw [← eb]; exact comoment_dupL_nonneg _
  rw [← Real.sqrt_mul h0a]
  apply Real.abs_le_sqrt
  exact le_trans h (mul_le_mul_of_nonneg_left hb h0a)

/-- `Σ (x' − x)² ≤ (2u)² Q'` when every `|x' − x| ≤ 2u|x|`. -/
theorem sum_sq_err_le {α : Type*} (qs : List α) (x x' : α → ℝ)
    (hd : ∀ q ∈ qs, |x' q - x q| ≤ 2 * u * |x q|) :
    (qs.map fun q => (x' q - x q) ^ 2).sum ≤ (2 * u) ^ 2 * (qs.map fun q => (|x q| + tiny) ^ 2).sum := by
  have hu := u_pos
  have ht := tiny_pos
  rw [← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro q hq
  have h := hd q hq
  have h1 : (x' q - x q) ^ 2 ≤ (2 * u * |x q|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : (2 * u * |x q|) ^ 2 ≤ (2 * u) ^ 2 * (|x q| + tiny) ^ 2 := by
    rw [mul_pow]; gcongr; have := abs_nonneg (x q); linarith
  linarith

/-- **Decoding moves a co-moment by little**: for doubles `x'` within `2u|x|` of
the values `x`,
`|C' − C| ≤ 2u (√S_xx √Q'_y + √S_yy √Q'_x) + 4u² √Q'_x √Q'_y`. -/
theorem decode_cov {qs : List ((ℝ × ℝ) × (ℝ × ℝ))}
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|) :
    |comoment (qs.map (·.1)) - comoment (qs.map (·.2))|
      ≤ 2 * u * (√(comoment (qs.map fun q => (q.2.1, q.2.1)))
            * √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum)
          + √(comoment (qs.map fun q => (q.2.2, q.2.2)))
            * √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum))
        + 4 * u ^ 2 * (√((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
          * √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum)) := by
  have hu := u_pos
  have e1 : qs.map (·.1) = qs.map fun q => (q.2.1 + (q.1.1 - q.2.1), q.2.2 + (q.1.2 - q.2.2)) := by
    congr 1; funext q; ext <;> simp
  have e2 : qs.map (·.2) = qs.map fun q => (q.2.1, q.2.2) := by
    congr 1
  rw [e1, e2, comoment_map_add]
  obtain ⟨Qx, hQx⟩ : ∃ Q, Q = (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum := ⟨_, rfl⟩
  obtain ⟨Qy, hQy⟩ : ∃ Q, Q = (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum := ⟨_, rfl⟩
  rw [← hQx, ← hQy]
  have hQx0 : 0 ≤ Qx := by
    rw [hQx]; exact List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hQy0 : 0 ≤ Qy := by
    rw [hQy]; exact List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have fx := sum_sq_err_le qs (fun q => q.2.1) (fun q => q.1.1) (fun q hq => (hd q hq).1)
  have fy := sum_sq_err_le qs (fun q => q.2.2) (fun q => q.1.2) (fun q hq => (hd q hq).2)
  rw [← hQx] at fx; rw [← hQy] at fy
  have rx : √((qs.map fun q => (q.1.1 - q.2.1) ^ 2).sum) ≤ 2 * u * √Qx := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hQx0]; exact fx
  have ry : √((qs.map fun q => (q.1.2 - q.2.2) ^ 2).sum) ≤ 2 * u * √Qy := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hQy0]; exact fy
  have k1 := abs_comoment_le_S qs (fun q => q.2.1) (fun q => q.1.2 - q.2.2)
  have k2 := abs_comoment_le_S qs (fun q => q.2.2) (fun q => q.1.1 - q.2.1)
  have k3 := abs_comoment_le_sq qs (fun q => q.1.1 - q.2.1) (fun q => q.1.2 - q.2.2)
  have c2 : comoment (qs.map fun q => (q.1.1 - q.2.1, q.2.2))
      = comoment (qs.map fun q => (q.2.2, q.1.1 - q.2.1)) := by
    rw [comoment_eq, comoment_eq]; simp [sxy, sx, sy, List.map_map, Function.comp_def, mul_comm]
  rw [← c2] at k2
  have m1 := mul_le_mul_of_nonneg_left ry (Real.sqrt_nonneg (comoment (qs.map fun q => (q.2.1, q.2.1))))
  have m2 := mul_le_mul_of_nonneg_left rx (Real.sqrt_nonneg (comoment (qs.map fun q => (q.2.2, q.2.2))))
  have m3 := mul_le_mul rx ry (Real.sqrt_nonneg _) (by positivity)
  have t := abs_add_le (comoment (qs.map fun q => (q.2.1, q.1.2 - q.2.2))
    + comoment (qs.map fun q => (q.1.1 - q.2.1, q.2.2))) (comoment (qs.map fun q => (q.1.1 - q.2.1, q.1.2 - q.2.2)))
  have t2 := abs_add_le (comoment (qs.map fun q => (q.2.1, q.1.2 - q.2.2)))
    (comoment (qs.map fun q => (q.1.1 - q.2.1, q.2.2)))
  have e : comoment (qs.map fun q => (q.2.1, q.2.2)) + comoment (qs.map fun q => (q.2.1, q.1.2 - q.2.2))
      + comoment (qs.map fun q => (q.1.1 - q.2.1, q.2.2))
      + comoment (qs.map fun q => (q.1.1 - q.2.1, q.1.2 - q.2.2)) - comoment (qs.map fun q => (q.2.1, q.2.2))
      = (comoment (qs.map fun q => (q.2.1, q.1.2 - q.2.2)) + comoment (qs.map fun q => (q.1.1 - q.2.1, q.2.2)))
        + comoment (qs.map fun q => (q.1.1 - q.2.1, q.1.2 - q.2.2)) := by ring
  rw [e]
  nlinarith

/-- The arithmetic of `tp_exact`: the bound on the decoded doubles (primed) and
the decoding's error, in the exact values' terms. -/
theorem kappa_arith {n X D sx sy qx qy sx' sy' qx' qy' : ℝ} (hn1 : 1 ≤ n)
    (hsx : 0 ≤ sx) (hsy : 0 ≤ sy) (hqx : 0 ≤ qx) (hqy : 0 ≤ qy)
    (hsx' : 0 ≤ sx') (hsy' : 0 ≤ sy') (_hqx' : 0 ≤ qx') (hqy' : 0 ≤ qy')
    (hX : X ≤ 6 * n * u * (sx' * sy') + 1.1 * u * (qy' * sx' + qx' * sy')
      + 120 * n ^ 2 * u ^ 2 * (qx' * qy') + 4 * n ^ 2 * u * tiny)
    (hD : D ≤ 2 * u * (sx * qy + sy * qx) + 4 * u ^ 2 * (qx * qy))
    (ax : sx' ≤ sx + 2 * u * qx) (ay : sy' ≤ sy + 2 * u * qy)
    (bx : qx' ≤ (1 + 2 * u) * qx) (by' : qy' ≤ (1 + 2 * u) * qy) :
    X + D ≤ 7 * n * u * (sx * sy) + 3.2 * n * u * (qy * sx + qx * sy)
      + 130 * n ^ 2 * u ^ 2 * (qx * qy) + 4 * n ^ 2 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  obtain ⟨v, hv⟩ : ∃ v, v = n * u := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have huv : u ≤ v := by rw [hv]; nlinarith
  -- the primed products
  have p1 : sx' * sy' ≤ (sx + 2 * u * qx) * (sy + 2 * u * qy) := mul_le_mul ax ay hsy' (by positivity)
  have p2 : qy' * sx' ≤ (1 + 2 * u) * qy * (sx + 2 * u * qx) := mul_le_mul by' ax hsx' (by positivity)
  have p3 : qx' * sy' ≤ (1 + 2 * u) * qx * (sy + 2 * u * qy) := mul_le_mul bx ay hsy' (by positivity)
  have p4 : qx' * qy' ≤ (1 + 2 * u) * qx * ((1 + 2 * u) * qy) := mul_le_mul bx by' hqy' (by positivity)
  -- atoms
  obtain ⟨P, hP⟩ : ∃ P, P = sx * sy := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = qy * sx + qx * sy := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = qx * qy := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have e1 : (sx + 2 * u * qx) * (sy + 2 * u * qy) = P + 2 * u * K + 4 * u ^ 2 * W := by
    rw [hP, hK, hW]; ring
  have e2 : (1 + 2 * u) * qy * (sx + 2 * u * qx) + (1 + 2 * u) * qx * (sy + 2 * u * qy)
      = (1 + 2 * u) * K + 4 * u * (1 + 2 * u) * W := by rw [hK, hW]; ring
  have e3 : (1 + 2 * u) * qx * ((1 + 2 * u) * qy) = (1 + 2 * u) ^ 2 * W := by rw [hW]; ring
  have e4 : sx * qy + sy * qx = K := by rw [hK]; ring
  rw [e1] at p1; rw [e3] at p4; rw [e4, ← hW] at hD
  -- `X` in the atoms
  have q1 := mul_le_mul_of_nonneg_left p1 (by positivity : (0 : ℝ) ≤ 6 * n * u)
  have q2 := mul_le_mul_of_nonneg_left (add_le_add p2 p3) (by positivity : (0 : ℝ) ≤ 1.1 * u)
  rw [e2] at q2
  have q3 := mul_le_mul_of_nonneg_left p4 (by positivity : (0 : ℝ) ≤ 120 * n ^ 2 * u ^ 2)
  -- the small terms
  have s1 : 6 * n * u * (2 * u * K) ≤ 0.001 * (v * K) := by
    have : 6 * n * u * (2 * u * K) = 12 * u * (v * K) := by rw [hv]; ring
    rw [this]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have s2 : 6 * n * u * (4 * u ^ 2 * W) ≤ 0.001 * (v * (v * W)) := by
    have : 6 * n * u * (4 * u ^ 2 * W) = 24 * u * (u * (v * W)) := by rw [hv]; ring
    rw [this]
    have a : u * (v * W) ≤ v * (v * W) := mul_le_mul_of_nonneg_right huv (by positivity)
    have b : 24 * u * (u * (v * W)) ≤ 24 * u * (v * (v * W)) := mul_le_mul_of_nonneg_left a (by positivity)
    have c : 24 * u * (v * (v * W)) ≤ 0.001 * (v * (v * W)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have s3 : 1.1 * u * ((1 + 2 * u) * K) ≤ 1.11 * (u * K) := by
    have : 1.1 * u * ((1 + 2 * u) * K) = 1.1 * (u * K) + 2.2 * u * (u * K) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (by linarith : 2.2 * u ≤ 0.01) (by positivity : 0 ≤ u * K)
    linarith
  have huuW : u * (u * W) ≤ v * (v * W) := by
    have a : u * (u * W) ≤ v * (u * W) := mul_le_mul_of_nonneg_right huv (by positivity)
    have b : v * (u * W) ≤ v * (v * W) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right huv hW0) hv0
    linarith
  have s4 : 1.1 * u * (4 * u * (1 + 2 * u) * W) ≤ 5 * (v * (v * W)) := by
    have : 1.1 * u * (4 * u * (1 + 2 * u) * W) = 4.4 * (1 + 2 * u) * (u * (u * W)) := by ring
    rw [this]
    have b : 4.4 * (1 + 2 * u) ≤ 5 := by linarith
    have c := mul_le_mul_of_nonneg_right b (by positivity : 0 ≤ u * (u * W))
    linarith
  have s5 : 120 * n ^ 2 * u ^ 2 * ((1 + 2 * u) ^ 2 * W) ≤ 120.1 * (v * (v * W)) := by
    have : 120 * n ^ 2 * u ^ 2 * ((1 + 2 * u) ^ 2 * W) = 120 * (1 + 2 * u) ^ 2 * (v * (v * W)) := by
      rw [hv]; ring
    rw [this]
    have : 120 * (1 + 2 * u) ^ 2 ≤ 120.1 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have s6 : 2 * u * K ≤ 2 * (v * K) := by
    have := mul_le_mul_of_nonneg_right huv hK0; linarith
  have s7 : 4 * u ^ 2 * W ≤ 4 * (v * (v * W)) := by
    have : u ^ 2 * W = u * (u * W) := by ring
    linarith
  have s8 : u * K ≤ v * K := mul_le_mul_of_nonneg_right huv hK0
  have f1 : 6 * n * u * P = 6 * (v * P) := by rw [hv]; ring
  have f2 : 7 * n * u * P = 7 * (v * P) := by rw [hv]; ring
  have f3 : 3.2 * n * u * K = 3.2 * (v * K) := by rw [hv]; ring
  have f4 : 130 * n ^ 2 * u ^ 2 * W = 130 * (v * (v * W)) := by rw [hv]; ring
  have e5 : 6 * n * u * (P + 2 * u * K + 4 * u ^ 2 * W)
      = 6 * n * u * P + 6 * n * u * (2 * u * K) + 6 * n * u * (4 * u ^ 2 * W) := by ring
  have e6 : 1.1 * u * ((1 + 2 * u) * K + 4 * u * (1 + 2 * u) * W)
      = 1.1 * u * ((1 + 2 * u) * K) + 1.1 * u * (4 * u * (1 + 2 * u) * W) := by ring
  rw [← hP, ← hK, ← hW]
  have : 0 ≤ v * P := by positivity
  have : 0 ≤ v * (v * W) := by positivity
  have : 0 ≤ v * K := by positivity
  linarith

variable (M : StdModel)

/-- `√S'_xx ≤ √S_xx + 2u √Q'_x` for decoded doubles. -/
theorem sqrt_S_decoded {qs : List ((ℝ × ℝ) × (ℝ × ℝ))}
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1|) :
    √(comoment (qs.map fun q => (q.1.1, q.1.1)))
      ≤ √(comoment (qs.map fun q => (q.2.1, q.2.1)))
        + 2 * u * √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum) := by
  have hu := u_pos
  have h := decode_cov (qs := qs.map fun q => ((q.1.1, q.1.1), (q.2.1, q.2.1)))
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨hd r hr, hd r hr⟩)
  simp only [List.map_map, Function.comp_def] at h
  obtain ⟨S, hS⟩ : ∃ S, S = comoment (qs.map fun q => (q.2.1, q.2.1)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum := ⟨_, rfl⟩
  rw [← hS, ← hQ] at h ⊢
  have hS0 : 0 ≤ S := by
    rw [hS]
    have := comoment_dupL_nonneg (qs.map fun q => q.2.1)
    simpa [dupL, List.map_map, Function.comp_def] using this
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  rw [Real.sqrt_le_left (by positivity)]
  have hs := Real.sq_sqrt hS0
  have hq := Real.sq_sqrt hQ0
  have h1 := (abs_le.mp h).2
  have e : (√S + 2 * u * √Q) ^ 2 = √S ^ 2 + 4 * u * (√S * √Q) + 4 * u ^ 2 * √Q ^ 2 := by ring
  rw [e, hs, hq]
  have e2 : 2 * u * (√S * √Q + √S * √Q) + 4 * u ^ 2 * (√Q * √Q) = 4 * u * (√S * √Q) + 4 * u ^ 2 * Q := by
    rw [Real.mul_self_sqrt hQ0]; ring
  linarith

/-- `√Q''_x ≤ (1 + 2u) √Q'_x` for decoded doubles. -/
theorem sqrt_Q_decoded {qs : List ((ℝ × ℝ) × (ℝ × ℝ))}
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1|) :
    √((qs.map fun q => (|q.1.1| + tiny) ^ 2).sum)
      ≤ (1 + 2 * u) * √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum) := by
  have hu := u_pos
  have ht := tiny_pos
  have h : (qs.map fun q => (|q.1.1| + tiny) ^ 2).sum
      ≤ (1 + 2 * u) ^ 2 * (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum := by
    rw [← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro q hq
    have h1 := abs_sub_abs_le_abs_sub q.1.1 q.2.1
    have h2 := hd q hq
    have h3 : |q.1.1| + tiny ≤ (1 + 2 * u) * (|q.2.1| + tiny) := by
      have := abs_nonneg q.2.1; nlinarith
    have h4 : 0 ≤ |q.1.1| + tiny := by positivity
    rw [← mul_pow]; exact pow_le_pow_left₀ h4 h3 2
  have hQ0 : 0 ≤ (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum :=
    List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  calc _ ≤ √((1 + 2 * u) ^ 2 * (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum) := Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

set_option maxHeartbeats 1000000 in
/-- **Two-pass on the decoded doubles, against the exact co-moment**, in the
exact values' `S` and `Q'`:
`7 n u √S_xx √S_yy + 3.2 n u (√Q'_y √S_xx + √Q'_x √S_yy) + 130 n² u² √Q'_x √Q'_y + 4 n² u · tiny`. -/
theorem StdModel.tp_exact {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) (hB : ∀ q ∈ qs, |q.2.1| ≤ 2 ^ 398 ∧ |q.2.2| ≤ 2 ^ 398)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|) :
    |M.twoPass (qs.map (·.1)) - comoment (qs.map (·.2))|
      ≤ 7 * qs.length * u * (√(comoment (qs.map fun q => (q.2.1, q.2.1)))
          * √(comoment (qs.map fun q => (q.2.2, q.2.2))))
        + 3.2 * qs.length * u * (√((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum)
            * √(comoment (qs.map fun q => (q.2.1, q.2.1)))
          + √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
            * √(comoment (qs.map fun q => (q.2.2, q.2.2))))
        + 130 * qs.length ^ 2 * u ^ 2 * (√((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
          * √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum))
        + 4 * qs.length ^ 2 * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hb' : Bounded (2 ^ 399) (qs.map (·.1)) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨b1, b2⟩ := hB q hq
    obtain ⟨d1, d2⟩ := hd q hq
    have k : ∀ {a b : ℝ}, |b| ≤ 2 ^ 398 → |a - b| ≤ 2 * u * |b| → |a| ≤ 2 ^ 399 := by
      intro a b hb hab
      have := abs_sub_abs_le_abs_sub a b
      have : 2 * u * |b| ≤ 2 * u * 2 ^ 398 := mul_le_mul_of_nonneg_left hb (by positivity)
      have : 2 * u * (2 : ℝ) ^ 398 ≤ 2 ^ 398 := by nlinarith
      have : (2 : ℝ) ^ 398 + 2 ^ 398 = 2 ^ 399 := by norm_num
      linarith
    exact ⟨k b1 d1, k b2 d2⟩
  have h1 := M.twoPass_cov_rel (ps := qs.map (·.1)) (by simpa using hne) (by simpa using hN) hb'
  have q1 : 0 ≤ (qs.map fun q => (|q.1.1| + tiny) ^ 2).sum :=
    List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have q2 : 0 ≤ (qs.map fun q => (|q.1.2| + tiny) ^ 2).sum :=
    List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have ex : dupL ((qs.map (·.1)).map Prod.fst) = qs.map fun q => (q.1.1, q.1.1) := by
    simp [dupL, List.map_map, Function.comp_def]
  have ey : dupL ((qs.map (·.1)).map Prod.snd) = qs.map fun q => (q.1.2, q.1.2) := by
    simp [dupL, List.map_map, Function.comp_def]
  rw [ex, ey] at h1
  simp only [List.map_map, Function.comp_def, List.length_map] at h1
  have s0x : 0 ≤ comoment (qs.map fun q => (q.1.1, q.1.1)) := by
    rw [← ex]; exact comoment_dupL_nonneg _
  rw [Real.sqrt_mul s0x, Real.sqrt_mul q2, Real.sqrt_mul q1, Real.sqrt_mul q1] at h1
  have hD := decode_cov hd
  have ax := sqrt_S_decoded (qs := qs) (fun q hq => (hd q hq).1)
  have bx := sqrt_Q_decoded (qs := qs) (fun q hq => (hd q hq).1)
  have ay := sqrt_S_decoded (qs := qs.map fun q => ((q.1.2, q.1.1), (q.2.2, q.2.1)))
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact (hd r hr).2)
  have by' := sqrt_Q_decoded (qs := qs.map fun q => ((q.1.2, q.1.1), (q.2.2, q.2.1)))
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact (hd r hr).2)
  simp only [List.map_map, Function.comp_def] at ay by'
  have hn1 : (1 : ℝ) ≤ qs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have k := kappa_arith (n := qs.length) hn1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) h1 hD ax ay bx by'
  have t := abs_add_le (M.twoPass (qs.map (·.1)) - comoment (qs.map (·.1)))
    (comoment (qs.map (·.1)) - comoment (qs.map (·.2)))
  have e : M.twoPass (qs.map (·.1)) - comoment (qs.map (·.2))
      = (M.twoPass (qs.map (·.1)) - comoment (qs.map (·.1)))
        + (comoment (qs.map (·.1)) - comoment (qs.map (·.2))) := by ring
  rw [e]
  linarith
