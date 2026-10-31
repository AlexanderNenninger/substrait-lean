module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The standard model of binary64 rounding

Error bounds for floating-point sums (#85) need a model of rounding over the
reals. This is the *standard model* (Higham, *Accuracy and Stability of
Numerical Algorithms*, §2.2): without overflow, a rounded result is the exact
one times `1 + δ` with `|δ| ≤ u`, where `u = 2⁻⁵³` is the unit roundoff of
binary64 with round to nearest.

The model is a structure, not an axiom: a theorem about sums takes a
`StdModel` as a hypothesis. The link to Lean's native `Float` (that
`Float.add` rounds as some `StdModel` does) is a separate, trusted assumption,
like `Impl.Faithful` in `SubstraitLean/Guards.lean` (stage 2 of #85).
-/

@[expose] public section

namespace FloatBounds

/-- The unit roundoff of binary64 with round to nearest. -/
noncomputable def u : ℝ := (2 : ℝ)⁻¹ ^ 53

/-- The largest finite binary64 value, `(2 − 2⁻⁵²) · 2¹⁰²³`. -/
noncomputable def maxFinite : ℝ := (2 - (2 : ℝ)⁻¹ ^ 52) * 2 ^ 1023

theorem u_pos : 0 < u := by unfold u; positivity

/-- A rounding `fl` from the reals to the reals (to the representable values)
that meets the standard model wherever the result does not overflow. -/
structure StdModel where
  fl : ℝ → ℝ
  rel : ∀ x, |x| ≤ maxFinite → ∃ δ, |δ| ≤ u ∧ fl x = x * (1 + δ)

variable (M : StdModel)

/-- A rounded addition. -/
noncomputable def StdModel.add (a b : ℝ) : ℝ := M.fl (a + b)

/-- **One rounded addition** is within `u` of the exact sum, relatively. -/
theorem StdModel.add_error {a b : ℝ} (h : |a + b| ≤ maxFinite) :
    |M.add a b - (a + b)| ≤ u * |a + b| := by
  obtain ⟨δ, hδ, he⟩ := M.rel (a + b) h
  unfold StdModel.add
  rw [he, show (a + b) * (1 + δ) - (a + b) = (a + b) * δ by ring, abs_mul, mul_comm u]
  exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)

end FloatBounds

end
