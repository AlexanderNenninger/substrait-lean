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
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
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
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
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
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
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
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
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

/-! ## The bounds `StatProps` states -/

/-- The error of a co-moment of pairs, with `r₁ ≥ √(Q'_x S_yy)`,
`r₂ ≥ √(Q'_y S_xx)`, `r_s ≥ √(S_xx S_yy)`, `r_q ≥ √(Q'_x Q'_y)`. -/
noncomputable def covErr (n r1 r2 rs rq : ℝ) : ℝ :=
  70 * n * u * (r1 + r2) + 11 * n * u * rs + 3961 * n ^ 2 * u ^ 2 * rq + 793 * n ^ 2 * u * tiny

/-- The error of a co-moment of one side, with `r ≥ √(Q' S)`. -/
noncomputable def varErr (n r Q : ℝ) : ℝ :=
  148 * n * u * r + 3961 * n ^ 2 * u ^ 2 * Q + 793 * n ^ 2 * u * tiny

/-- The tolerance of `COVAR_*`, `C / d`. -/
noncomputable def covTol (n d r1 r2 rs rq : ℝ) : ℝ :=
  (71 * n * u * (r1 + r2) + 15 * n * u * rs + 3970 * n ^ 2 * u ^ 2 * rq
    + 800 * n ^ 2 * u * tiny) / d

/-- The tolerance of `VAR_*`, `S / d`. -/
noncomputable def varTol (n d r Q : ℝ) : ℝ :=
  (160 * n * u * r + 3970 * n ^ 2 * u ^ 2 * Q + 800 * n ^ 2 * u * tiny) / d

/-- Dividing a co-moment within `E` of `C` by `d`, rounded. -/
theorem StdModel.div_kappa {C Ch E rs n d : ℝ} (h : |Ch - C| ≤ E) (hC : |C| ≤ rs) (hE0 : 0 ≤ E)
    (hrs : 0 ≤ rs) (hn1 : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) (hbig : rs + E + n * tiny ≤ 2 ^ 999) :
    |M.fl (Ch / d) - C / d| ≤ (E + 3 * u * E + 3 * u * rs + 3 * n * u * tiny) / d := by
  have ht := tiny_pos
  have hnt : 0 ≤ n * tiny := mul_nonneg (by linarith) ht.le
  have hdt : d * tiny ≤ n * tiny := mul_le_mul_of_nonneg_right hdn ht.le
  have := M.covar_error (Cm := rs + E + n * tiny) h (by linarith) (by linarith)
    (by linarith) hd (by linarith)
  have e : E / d + 3 * u * (rs + E + n * tiny) / d = (E + 3 * u * E + 3 * u * rs + 3 * n * u * tiny) / d := by
    ring
  linarith

/-- `S ≤ Q' ≤ 2⁸³⁰` for `n ≤ 2³²` values at most `2³⁹⁸`. -/
theorem SQ_facts {α : Type*} {qs : List α} (y : α → ℝ) (hN : qs.length ≤ 2 ^ 32)
    (hB : ∀ q ∈ qs, |y q| ≤ 2 ^ 398) :
    0 ≤ comoment (qs.map fun q => (y q, y q)) ∧
    comoment (qs.map fun q => (y q, y q)) ≤ (qs.map fun q => (|y q| + tiny) ^ 2).sum ∧
    (qs.map fun q => (|y q| + tiny) ^ 2).sum ≤ 2 ^ 830 := by
  obtain ⟨-, -, ht, ht1, -⟩ := fpFacts
  have e : comoment (dupL (qs.map y)) = comoment (qs.map fun q => (y q, y q)) := by
    simp [dupL, List.map_map, Function.comp_def]
  refine ⟨by rw [← e]; exact comoment_dupL_nonneg _, ?_, ?_⟩
  · rw [← e]
    refine le_trans (comoment_dupL_le _) ?_
    simp only [List.map_map, Function.comp_def]
    apply List.sum_le_sum; intro q _
    have := abs_nonneg (y q)
    calc y q ^ 2 = |y q| ^ 2 := (sq_abs _).symm
      _ ≤ (|y q| + tiny) ^ 2 := by gcongr; linarith
  · have h := abs_sum_le_of_bound (B := (2 ^ 398 + 1) ^ 2) (xs := qs.map fun q => (|y q| + tiny) ^ 2) (by
      intro z hz; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      rw [abs_of_nonneg (by positivity)]
      have := hB q hq
      gcongr)
    simp only [List.length_map] at h
    have h2 := le_abs_self (qs.map fun q => (|y q| + tiny) ^ 2).sum
    have hNr : (qs.length : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
    have h3 : (qs.length : ℝ) * (2 ^ 398 + 1) ^ 2 ≤ 2 ^ 32 * (2 ^ 398 + 1) ^ 2 := by gcongr
    have h4 : (2 : ℝ) ^ 32 * (2 ^ 398 + 1) ^ 2 ≤ 2 ^ 830 := by norm_num
    linarith

theorem covTol_mono {n d r1 r2 rs rq r1' r2' rs' rq' : ℝ} (hn : 0 ≤ n) (hd : 0 < d)
    (h1 : r1 ≤ r1') (h2 : r2 ≤ r2') (hs : rs ≤ rs') (hq : rq ≤ rq') :
    covTol n d r1 r2 rs rq ≤ covTol n d r1' r2' rs' rq' := by
  have hu := u_pos
  unfold covTol
  apply div_le_div_of_nonneg_right _ hd.le
  have a := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0 : ℝ) ≤ 71 * n * u)
  have b := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 15 * n * u)
  have c := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 3970 * n ^ 2 * u ^ 2)
  linarith

set_option maxHeartbeats 1000000 in
/-- **`COVAR_*` the core trusts** (`covOf_props`): `fl(Ĉ / d)` within
`covTol` of `C / d`, for any `r₁ ≥ √(Q'_x S_yy)`, `r₂ ≥ √(Q'_y S_xx)`,
`r_s ≥ √(S_xx S_yy)`, `r_q ≥ √(Q'_x Q'_y)`. -/
theorem StdModel.core_cov_k {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) (hB : ∀ q ∈ qs, |q.2.1| ≤ 2 ^ 398 ∧ |q.2.2| ≤ 2 ^ 398)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|)
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ qs.length) {r1 r2 rs rq : ℝ}
    (h1 : √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
      * √(comoment (qs.map fun q => (q.2.2, q.2.2))) ≤ r1)
    (h2 : √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum)
      * √(comoment (qs.map fun q => (q.2.1, q.2.1))) ≤ r2)
    (hs : √(comoment (qs.map fun q => (q.2.1, q.2.1)))
      * √(comoment (qs.map fun q => (q.2.2, q.2.2))) ≤ rs)
    (hq : √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
      * √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum) ≤ rq) :
    |M.fl (M.twoPass (qs.map (·.1)) / d) - comoment (qs.map (·.2)) / d|
      ≤ covTol qs.length d r1 r2 rs rq := by
  obtain ⟨hu, hu', ht, ht1, -⟩ := fpFacts
  have h0 := M.tp_exact hne hN hB hd
  obtain ⟨hSx0, hSQx, hQx⟩ := SQ_facts (qs := qs) (fun q => q.2.1) hN (fun q hq => (hB q hq).1)
  obtain ⟨hSy0, hSQy, hQy⟩ := SQ_facts (qs := qs) (fun q => q.2.2) hN (fun q hq => (hB q hq).2)
  -- names
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = qs.length := ⟨_, rfl⟩
  obtain ⟨sx, hsx⟩ : ∃ r, r = √(comoment (qs.map fun q => (q.2.1, q.2.1))) := ⟨_, rfl⟩
  obtain ⟨sy, hsy⟩ : ∃ r, r = √(comoment (qs.map fun q => (q.2.2, q.2.2))) := ⟨_, rfl⟩
  obtain ⟨qx, hqx⟩ : ∃ r, r = √((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum) := ⟨_, rfl⟩
  obtain ⟨qy, hqy⟩ : ∃ r, r = √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum) := ⟨_, rfl⟩
  rw [← hn, ← hsx, ← hsy, ← hqx, ← hqy] at h0
  simp only [← hsx, ← hsy, ← hqx, ← hqy] at h1 h2 hs hq
  have hgoal : covTol (qs.length : ℝ) d r1 r2 rs rq = covTol n d r1 r2 rs rq := by rw [hn]
  rw [hgoal]
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast List.length_pos_iff.mpr hne
  have hNr : n ≤ 2 ^ 32 := by rw [hn]; exact_mod_cast hN
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdn' : (d : ℝ) ≤ n := by rw [hn]; exact_mod_cast hdn
  have hsx0 : 0 ≤ sx := by rw [hsx]; positivity
  have hsy0 : 0 ≤ sy := by rw [hsy]; positivity
  have hqx0 : 0 ≤ qx := by rw [hqx]; positivity
  have hqy0 : 0 ≤ qy := by rw [hqy]; positivity
  -- sizes: everything at most `2⁴¹⁵`
  have b415 : ∀ {z : ℝ}, 0 ≤ z → z ≤ 2 ^ 830 → √z ≤ 2 ^ 415 := by
    intro z hz hz'
    rw [Real.sqrt_le_left (by positivity)]
    have : ((2 : ℝ) ^ 415) ^ 2 = 2 ^ 830 := by norm_num
    linarith
  have bsx : sx ≤ 2 ^ 415 := by rw [hsx]; exact b415 hSx0 (le_trans hSQx hQx)
  have bsy : sy ≤ 2 ^ 415 := by rw [hsy]; exact b415 hSy0 (le_trans hSQy hQy)
  have bqx : qx ≤ 2 ^ 415 := by rw [hqx]; exact b415 (le_trans hSx0 hSQx) hQx
  have bqy : qy ≤ 2 ^ 415 := by rw [hqy]; exact b415 (le_trans hSy0 hSQy) hQy
  have p1 : sx * sy ≤ 2 ^ 830 := by
    have := mul_le_mul bsx bsy hsy0 (by norm_num); norm_num at this ⊢; linarith
  have p2 : qy * sx + qx * sy ≤ 2 ^ 831 := by
    have a := mul_le_mul bqy bsx hsx0 (by norm_num)
    have b := mul_le_mul bqx bsy hsy0 (by norm_num)
    have : (2 : ℝ) ^ 415 * 2 ^ 415 + 2 ^ 415 * 2 ^ 415 = 2 ^ 831 := by norm_num
    linarith
  have p3 : qx * qy ≤ 2 ^ 830 := by
    have := mul_le_mul bqx bqy hqy0 (by norm_num); norm_num at this ⊢; linarith
  obtain ⟨E, hE⟩ : ∃ E, E = 7 * n * u * (sx * sy) + 3.2 * n * u * (qy * sx + qx * sy)
      + 130 * n ^ 2 * u ^ 2 * (qx * qy) + 4 * n ^ 2 * u * tiny := ⟨_, rfl⟩
  rw [← hE] at h0
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hnu : n * u ≤ 1 / 2 ^ 21 := by
    calc n * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  have hEb : E ≤ 2 ^ 840 := by
    have hnu0 : 0 ≤ n * u := by positivity
    have v2 : n ^ 2 * u ^ 2 ≤ 1 := by
      have := mul_le_mul hnu hnu hnu0 (by norm_num)
      have e : n ^ 2 * u ^ 2 = (n * u) * (n * u) := by ring
      rw [e]; linarith
    have v3 : n ^ 2 * u ≤ 2 ^ 32 := by
      have := mul_le_mul hNr hnu hnu0 (by norm_num)
      have e : n ^ 2 * u = n * (n * u) := by ring
      rw [e]; norm_num at this ⊢; linarith
    have k1 : 7 * n * u * (sx * sy) ≤ 7 * 2 ^ 830 := by
      have := mul_le_mul (by linarith : 7 * n * u ≤ 7) p1 (by positivity) (by norm_num); linarith
    have k2 : 3.2 * n * u * (qy * sx + qx * sy) ≤ 4 * 2 ^ 831 := by
      have := mul_le_mul (by linarith : 3.2 * n * u ≤ 4) p2 (by positivity) (by norm_num); linarith
    have k3 : 130 * n ^ 2 * u ^ 2 * (qx * qy) ≤ 130 * 2 ^ 830 := by
      have := mul_le_mul (by linarith : 130 * n ^ 2 * u ^ 2 ≤ 130) p3 (by positivity) (by norm_num)
      linarith
    have k4 : 4 * n ^ 2 * u * tiny ≤ 4 * 2 ^ 32 := by
      have := mul_le_mul (by linarith : 4 * n ^ 2 * u ≤ 4 * 2 ^ 32) ht1 ht.le (by norm_num); linarith
    rw [hE]
    have : (7 : ℝ) * 2 ^ 830 + 4 * 2 ^ 831 + 130 * 2 ^ 830 + 4 * 2 ^ 32 ≤ 2 ^ 840 := by norm_num
    linarith
  -- `|C| ≤ s_x s_y`
  have hC : |comoment (qs.map (·.2))| ≤ sx * sy := by
    have h := sq_comoment_le (qs.map (·.2))
    simp only [List.map_map, Function.comp_def] at h
    rw [hsx, hsy, ← Real.sqrt_mul hSx0]
    exact Real.abs_le_sqrt h
  have hdiv := M.div_kappa h0 hC hE0 (by positivity) hn1 hd' hdn' (by
    have : n * tiny ≤ 2 ^ 32 := by nlinarith
    have : (2 : ℝ) ^ 830 + 2 ^ 840 + 2 ^ 32 ≤ 2 ^ 999 := by norm_num
    linarith)
  refine le_trans hdiv ?_
  -- the arithmetic
  refine le_trans ?_ (covTol_mono (n := n) (by linarith) (by linarith) h1 h2 hs hq)
  unfold covTol
  apply div_le_div_of_nonneg_right _ (by linarith)
  have uE : 3 * u * E ≤ 0.001 * E := mul_le_mul_of_nonneg_right (by linarith) hE0
  have a1 : 3 * u * (sx * sy) ≤ 3 * n * u * (sx * sy) := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : (0 : ℝ) ≤ 3 * u * (sx * sy)); nlinarith
  have a2 : 3 * n * u * tiny ≤ 3 * n ^ 2 * u * tiny := by
    have : n ≤ n ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 3 * u * tiny); nlinarith
  have a3 : 3.2 * n * u * (qy * sx + qx * sy) ≤ 70 * n * u * (qx * sy + qy * sx) := by
    have : 0 ≤ n * u * (qy * sx + qx * sy) := by positivity
    nlinarith
  have q1 : 0 ≤ n * u * (sx * sy) := by positivity
  have q2 : 0 ≤ n ^ 2 * u ^ 2 * (qx * qy) := by positivity
  have q3 : 0 ≤ n ^ 2 * u * tiny := by positivity
  have q4 : 0 ≤ n * u * (qx * sy + qy * sx) := by positivity
  rw [hE] at uE ⊢
  nlinarith

/-- **`VAR_*` the core trusts** (`varOf_props`): `fl(Ŝ / d)` is `≥ 0` and
within `varTol` of `S / d`, for any `r ≥ √(Q' S)`. -/
theorem StdModel.core_var_k {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32)
    (hB : ∀ p ∈ ps, |p.2| ≤ 2 ^ 398) (hd : ∀ p ∈ ps, |p.1 - p.2| ≤ 2 * u * |p.2|)
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ ps.length) {r : ℝ}
    (hr : √((ps.map fun p => (|p.2| + tiny) ^ 2).sum)
      * √(comoment (ps.map fun p => (p.2, p.2))) ≤ r) :
    0 ≤ M.fl (M.twoPass (ps.map fun p => (p.1, p.1)) / d) ∧
      |M.fl (M.twoPass (ps.map fun p => (p.1, p.1)) / d) - comoment (ps.map fun p => (p.2, p.2)) / d|
        ≤ varTol ps.length d r (ps.map fun p => (|p.2| + tiny) ^ 2).sum := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  obtain ⟨hS0, hSQ, -⟩ := SQ_facts (qs := ps) (fun p => p.2) hN hB
  have hQ0 : 0 ≤ (ps.map fun p => (|p.2| + tiny) ^ 2).sum := le_trans hS0 hSQ
  have hsq : √(comoment (ps.map fun p => (p.2, p.2))) ≤ √((ps.map fun p => (|p.2| + tiny) ^ 2).sum) :=
    Real.sqrt_le_sqrt hSQ
  have hrs : √(comoment (ps.map fun p => (p.2, p.2))) * √(comoment (ps.map fun p => (p.2, p.2))) ≤ r :=
    le_trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)) hr
  have hrq : √((ps.map fun p => (|p.2| + tiny) ^ 2).sum) * √((ps.map fun p => (|p.2| + tiny) ^ 2).sum)
      ≤ (ps.map fun p => (|p.2| + tiny) ^ 2).sum := le_of_eq (Real.mul_self_sqrt hQ0)
  have hr' : √((ps.map fun p => (|p.2| + tiny) ^ 2).sum) * √(comoment (ps.map fun p => (p.2, p.2)))
      ≤ r := hr
  have h := M.core_cov_k (qs := ps.map fun p => ((p.1, p.1), (p.2, p.2))) (by simpa using hne)
    (by simpa using hN) (fun q hq => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨hB p hp, hB p hp⟩)
    (fun q hq => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨hd p hp, hd p hp⟩)
    hd1 (by simpa using hdn) (r1 := r) (r2 := r) (rs := r)
    (rq := (ps.map fun p => (|p.2| + tiny) ^ 2).sum)
    (by simpa [List.map_map, Function.comp_def] using hr')
    (by simpa [List.map_map, Function.comp_def] using hr')
    (by simpa [List.map_map, Function.comp_def] using hrs)
    (by simpa [List.map_map, Function.comp_def] using hrq)
  simp only [List.map_map, Function.comp_def, List.length_map] at h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd1
  refine ⟨M.nonneg _ (div_nonneg (M.twoPass_dup_nonneg ps) hd'.le), le_trans h ?_⟩
  unfold covTol varTol
  apply div_le_div_of_nonneg_right _ hd'.le
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have : 0 ≤ (ps.length : ℝ) * u * r := by positivity
  nlinarith

/-- The two-pass bound of one side, within `varErr`. -/
theorem tp_var_le {n s q r Q : ℝ} (hn1 : 1 ≤ n) (hs : 0 ≤ s) (hsq : s ≤ q) (hQ : q * q = Q)
    (hr : q * s ≤ r) :
    7 * n * u * (s * s) + 3.2 * n * u * (q * s + q * s) + 130 * n ^ 2 * u ^ 2 * (q * q)
        + 4 * n ^ 2 * u * tiny ≤ varErr n r Q := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  unfold varErr
  have a : s * s ≤ q * s := mul_le_mul_of_nonneg_right hsq hs
  have b : 0 ≤ n * u := by positivity
  have c := mul_le_mul_of_nonneg_left (le_trans a hr) b
  have d := mul_le_mul_of_nonneg_left hr b
  have hq0 : 0 ≤ q := le_trans hs hsq
  have hQ0 : 0 ≤ Q := by rw [← hQ]; positivity
  have e : 0 ≤ n ^ 2 * u ^ 2 * Q := by positivity
  have f : 0 ≤ n ^ 2 * u * tiny := by positivity
  have g : 0 ≤ n * u * r := le_trans (by positivity) d
  rw [hQ]
  linarith

/-- The two-pass bound of the pairs, within `covErr`. -/
theorem tp_cov_le {n sx sy qx qy r1 r2 rs rq : ℝ} (hn1 : 1 ≤ n) (hsx : 0 ≤ sx) (hsy : 0 ≤ sy)
    (hqx : 0 ≤ qx) (hqy : 0 ≤ qy) (h1 : qx * sy ≤ r1) (h2 : qy * sx ≤ r2) (hs : sx * sy ≤ rs)
    (hq : qx * qy ≤ rq) :
    7 * n * u * (sx * sy) + 3.2 * n * u * (qy * sx + qx * sy) + 130 * n ^ 2 * u ^ 2 * (qx * qy)
        + 4 * n ^ 2 * u * tiny ≤ covErr n r1 r2 rs rq := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  unfold covErr
  have b : 0 ≤ n * u := by positivity
  have c1 := mul_le_mul_of_nonneg_left hs b
  have c2 := mul_le_mul_of_nonneg_left (add_le_add h2 h1) b
  have c3 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ n ^ 2 * u ^ 2)
  have p1 : 0 ≤ n * u * (sx * sy) := by positivity
  have p2 : 0 ≤ n * u * (qy * sx + qx * sy) := by positivity
  have p3 : 0 ≤ n ^ 2 * u ^ 2 * (qx * qy) := by positivity
  have p4 : 0 ≤ n ^ 2 * u * tiny := by positivity
  have p5 : 0 ≤ n * u * (r2 + r1) := le_trans (by positivity) c2
  have p6 : 0 ≤ n ^ 2 * u ^ 2 * rq := le_trans p3 c3
  linarith


/-- The error budget of `CORR`, with one `R` at least `√(Q' S)` of each side,
`√(Q'_x S_yy)`, `√(Q'_y S_xx)` and `√(S_xx S_yy)`, and `Q = Q'_x + Q'_y`. -/
noncomputable def corrErr (n R Q : ℝ) : ℝ :=
  447 * n * u * R + 11883 * n ^ 2 * u ^ 2 * Q + 2379 * n ^ 2 * u * tiny

theorem corrErr_ge {n R Qx Qy qx qy : ℝ} (_hn : 0 ≤ n) (hqx : 0 ≤ qx) (hqy : 0 ≤ qy)
    (hQx : qx * qx = Qx) (hQy : qy * qy = Qy) :
    varErr n R Qx + varErr n R Qy + covErr n R R R (qx * qy) ≤ corrErr n R (Qx + Qy) := by
  have hu := u_pos
  unfold varErr covErr corrErr
  have a : qx * qy ≤ Qx + Qy := by rw [← hQx, ← hQy]; nlinarith [sq_nonneg (qx - qy)]
  have b := mul_le_mul_of_nonneg_left a (by positivity : (0 : ℝ) ≤ 3961 * n ^ 2 * u ^ 2)
  have c : 0 ≤ n ^ 2 * u ^ 2 * (Qx + Qy) := by rw [← hQx, ← hQy]; positivity
  have d : 0 ≤ n ^ 2 * u * tiny := by have := tiny_pos; positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **`CORR` the core trusts** (`corrOf_props`): with `E = corrErr n R Q`, for
`R` at least the square roots above and `Q = Q'_x + Q'_y`, and both sides'
co-moments at least `L ≥ 8E` (`L ≥ 2⁻⁵⁰⁰`, their product at most `2¹⁰⁰⁰`),
`|Ĉ / fl(√fl(Ŝx Ŝy))| ≤ 1 + 3E/L + 8u`. -/
theorem StdModel.core_corr_k {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) (hB : ∀ q ∈ qs, |q.2.1| ≤ 2 ^ 398 ∧ |q.2.2| ≤ 2 ^ 398)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|)
    {R L : ℝ}
    (hR : ∀ a ∈ [(qs.map fun q => (|q.2.1| + tiny) ^ 2).sum, (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum,
        comoment (qs.map fun q => (q.2.1, q.2.1))],
      ∀ b ∈ [comoment (qs.map fun q => (q.2.1, q.2.1)), comoment (qs.map fun q => (q.2.2, q.2.2))],
        √a * √b ≤ R)
    (hL : 8 * corrErr qs.length R ((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum
      + (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum) ≤ L)
    (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hSx : L ≤ comoment (qs.map fun q => (q.2.1, q.2.1)))
    (hSy : L ≤ comoment (qs.map fun q => (q.2.2, q.2.2)))
    (hbig : comoment (qs.map fun q => (q.2.1, q.2.1)) * comoment (qs.map fun q => (q.2.2, q.2.2))
      ≤ 2 ^ 1000) :
    |M.fl (M.twoPass (qs.map (·.1)) /
        M.fl √(M.fl (M.twoPass (qs.map fun q => (q.1.1, q.1.1))
          * M.twoPass (qs.map fun q => (q.1.2, q.1.2)))))|
      ≤ 1 + 3 * corrErr qs.length R ((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum
        + (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum) / L + 8 * u := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hc := M.tp_exact hne hN hB hd
  have hx := M.tp_exact (qs := qs.map fun q => ((q.1.1, q.1.1), (q.2.1, q.2.1)))
    (by simpa using hne) (by simpa using hN)
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hB r hr).1, (hB r hr).1⟩)
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hd r hr).1, (hd r hr).1⟩)
  have hy := M.tp_exact (qs := qs.map fun q => ((q.1.2, q.1.2), (q.2.2, q.2.2)))
    (by simpa using hne) (by simpa using hN)
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hB r hr).2, (hB r hr).2⟩)
    (fun q hq => by obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hd r hr).2, (hd r hr).2⟩)
  simp only [List.map_map, Function.comp_def, List.length_map] at hx hy
  obtain ⟨hSx0, hSQx, -⟩ := SQ_facts (qs := qs) (fun q => q.2.1) hN (fun q hq => (hB q hq).1)
  obtain ⟨hSy0, hSQy, -⟩ := SQ_facts (qs := qs) (fun q => q.2.2) hN (fun q hq => (hB q hq).2)
  have hn1 : (1 : ℝ) ≤ qs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have r1 := hR (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum (by simp)
    (comoment (qs.map fun q => (q.2.1, q.2.1))) (by simp)
  have r2 := hR (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum (by simp)
    (comoment (qs.map fun q => (q.2.2, q.2.2))) (by simp)
  have r3 := hR (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum (by simp)
    (comoment (qs.map fun q => (q.2.2, q.2.2))) (by simp)
  have r4 := hR (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum (by simp)
    (comoment (qs.map fun q => (q.2.1, q.2.1))) (by simp)
  have r5 := hR (comoment (qs.map fun q => (q.2.1, q.2.1))) (by simp)
    (comoment (qs.map fun q => (q.2.2, q.2.2))) (by simp)
  have hQx0 := le_trans hSx0 hSQx
  have hQy0 := le_trans hSy0 hSQy
  have ex := tp_var_le hn1 (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hSQx)
    (Real.mul_self_sqrt hQx0) r1
  have ey := tp_var_le hn1 (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hSQy)
    (Real.mul_self_sqrt hQy0) r2
  have ec := tp_cov_le hn1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) r3 r4 r5 le_rfl
  have hE := corrErr_ge (n := qs.length) (R := R) (by positivity) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.mul_self_sqrt hQx0) (Real.mul_self_sqrt hQy0)
  have hvx0 : 0 ≤ varErr qs.length R (qs.map fun q => (|q.2.1| + tiny) ^ 2).sum :=
    le_trans (by positivity) ex
  have hvy0 : 0 ≤ varErr qs.length R (qs.map fun q => (|q.2.2| + tiny) ^ 2).sum :=
    le_trans (by positivity) ey
  have hcv0 : 0 ≤ covErr qs.length R R R (√((qs.map fun q => (|q.2.1| + tiny) ^ 2).sum)
      * √((qs.map fun q => (|q.2.2| + tiny) ^ 2).sum)) := le_trans (by positivity) ec
  have hCS := sq_comoment_le (qs.map (·.2))
  simp only [List.map_map, Function.comp_def] at hCS
  exact M.corr_le hCS (by linarith) (by linarith) (by linarith) hL (by linarith) hSx hSy hLt hbig

/-- The `STDDEV_*` property (`core_stddev`) holds for any larger tolerance, so for
every witness `r` above `√(Q' S)`. -/
theorem sd_mono {σ V τ τ' : ℝ} (h : τ ≤ τ')
    (h1 : σ ≤ u * tiny ∨ (σ - u * tiny) ^ 2 ≤ (1 + u) ^ 2 * (V + τ))
    (h2 : (1 - u) ^ 2 * (V - τ) ≤ (σ + u * tiny) ^ 2) :
    (σ ≤ u * tiny ∨ (σ - u * tiny) ^ 2 ≤ (1 + u) ^ 2 * (V + τ')) ∧
      (1 - u) ^ 2 * (V - τ') ≤ (σ + u * tiny) ^ 2 := by
  have p : 0 ≤ (1 + u) ^ 2 := sq_nonneg _
  have q : 0 ≤ (1 - u) ^ 2 := sq_nonneg _
  refine ⟨h1.imp id fun h1 => le_trans h1 ?_, le_trans ?_ h2⟩
  · exact mul_le_mul_of_nonneg_left (by linarith) p
  · exact mul_le_mul_of_nonneg_left (by linarith) q
