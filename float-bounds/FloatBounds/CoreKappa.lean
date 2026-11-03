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
