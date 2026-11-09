module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The standard model of binary64 rounding

Error bounds for floating-point aggregates (#85) need a model of rounding
over the reals. This is the *standard model* (Higham, *Accuracy and
Stability of Numerical Algorithms*, §2.1, (2.8)), with its underflow term:
without overflow, a rounded result is the exact one `z` up to
`u · |z| + η`, where `u = 2⁻⁵³` is the unit roundoff of binary64 with round
to nearest and `η = 2⁻¹⁰⁷⁵` is half the spacing of the subnormals. We write
the bound as `u · (|z| + tiny)`, with `tiny = η / u = 2⁻¹⁰²²` the smallest
normal double. Without the `η` term, no rounding meets the model: `2⁻¹⁰⁸⁰`
rounds to `0` or `2⁻¹⁰⁷⁴`, a relative error of at least `1/2`.

The model is a structure, not an axiom: a theorem takes a `StdModel` as a
hypothesis. The link to Lean's native `Float` (that its operations round as
some `StdModel` does) is a separate, trusted assumption, `NativeLink` in
`FloatBounds/Link.lean`, like `Impl.Faithful` in `analysis/Sverify/Analysis/Guards.lean`.

`γ n = n·u / (1 − n·u)` bounds the relative error of `n` roundings
(Higham §3.1); `one_add_gamma` writes `1 + γ n` as `1 / (1 − n·u)`, which is
how the lemmas below compose it.
-/

@[expose] public section

namespace FloatBounds

/-- The unit roundoff of binary64 with round to nearest. -/
noncomputable def u : ℝ := (2 : ℝ)⁻¹ ^ 53

/-- The smallest positive normal binary64 value; `u · tiny = 2⁻¹⁰⁷⁵` bounds
the absolute error of a rounding in the subnormal range. -/
noncomputable def tiny : ℝ := (2 : ℝ)⁻¹ ^ 1022

/-- The largest finite binary64 value, `(2 − 2⁻⁵²) · 2¹⁰²³`. -/
noncomputable def maxFinite : ℝ := (2 - (2 : ℝ)⁻¹ ^ 52) * 2 ^ 1023

theorem u_pos : 0 < u := by unfold u; positivity

theorem tiny_pos : 0 < tiny := by unfold tiny; positivity

theorem u_le : u ≤ 2⁻¹ ^ 53 := le_rfl

/-- The value of `u`. Proofs that need the number go through this lemma or
`fpFacts`, never `unfold u`, so the precision is written down here only. -/
theorem u_val : u = 1 / 2 ^ 53 := by unfold u; norm_num

/-- What nearly every bound opens with: the signs and sizes of `u`, `tiny`
and `maxFinite`. A proof takes the ones it needs with
`obtain ⟨hu, hu', ht, ht1, hmax⟩ := fpFacts`, writing `-` for the others. -/
structure FpFacts : Prop where
  u_pos : 0 < u
  u_le : u ≤ 1 / 2 ^ 53
  tiny_pos : 0 < tiny
  tiny_le : tiny ≤ 1
  max_ge : (2 : ℝ) ^ 1023 ≤ maxFinite

theorem fpFacts : FpFacts where
  u_pos := u_pos
  u_le := u_val.le
  tiny_pos := tiny_pos
  tiny_le := by unfold tiny; exact pow_le_one₀ (by norm_num) (by norm_num)
  max_ge := by unfold maxFinite; norm_num

/-- A rounding `fl` from the reals to the reals (to the representable values)
that meets the standard model wherever the result does not overflow, keeps
the sign, and leaves representable values alone, as rounding to nearest
does. -/
structure StdModel where
  fl : ℝ → ℝ
  err : ∀ z, |z| ≤ maxFinite → |fl z - z| ≤ u * (|z| + tiny)
  /-- Rounding keeps the sign (it is monotone and `fl 0 = 0`). -/
  nonneg : ∀ z, 0 ≤ z → 0 ≤ fl z
  nonpos : ∀ z, z ≤ 0 → fl z ≤ 0
  /-- A representable value rounds to itself, so rounding twice is rounding
  once; `0` is representable. True of binary64: `x − 0`, `x / 1` and `0 + x`
  are exact for a double `x`. -/
  idem : ∀ z, fl (fl z) = fl z
  zero : fl 0 = 0

variable (M : StdModel)

/-- A rounded addition. -/
noncomputable def StdModel.add (a b : ℝ) : ℝ := M.fl (a + b)

/-- One rounded addition is within `u · (|a + b| + tiny)` of the exact sum. -/
theorem StdModel.add_error {a b : ℝ} (h : |a + b| ≤ maxFinite) :
    |M.add a b - (a + b)| ≤ u * (|a + b| + tiny) :=
  M.err _ h

/-- A rounding of `z` computed from an approximation `z'` of it: the error
of `z'` plus that of the rounding. -/
theorem StdModel.round_near {z z' e : ℝ} (hz : |z' - z| ≤ e) (h : |z'| ≤ maxFinite) :
    |M.fl z' - z| ≤ e + u * (|z| + e + tiny) := by
  have h1 := M.err z' h
  have h2 : |z'| ≤ |z| + e := by
    have := abs_sub_abs_le_abs_sub z' z; linarith
  have hu := u_pos
  calc |M.fl z' - z| = |(M.fl z' - z') + (z' - z)| := by ring_nf
    _ ≤ |M.fl z' - z'| + |z' - z| := abs_add_le _ _
    _ ≤ u * (|z'| + tiny) + e := add_le_add h1 hz
    _ ≤ u * (|z| + e + tiny) + e := by gcongr
    _ = e + u * (|z| + e + tiny) := by ring

/-! ## `γ n` -/

/-- `γ n = n·u / (1 − n·u)`, for `n·u < 1`. -/
noncomputable def gamma (n : ℕ) : ℝ := n * u / (1 - n * u)

theorem gamma_nonneg {n : ℕ} (h : (n : ℝ) * u < 1) : 0 ≤ gamma n := by
  unfold gamma
  have := u_pos
  apply div_nonneg (by positivity); linarith

theorem one_add_gamma {n : ℕ} (h : (n : ℝ) * u < 1) : 1 + gamma n = 1 / (1 - n * u) := by
  unfold gamma; field_simp; ring

theorem gamma_mono {m n : ℕ} (hmn : m ≤ n) (h : (n : ℝ) * u < 1) : gamma m ≤ gamma n := by
  have hu := u_pos
  have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hmu : (m : ℝ) * u ≤ n * u := by gcongr
  unfold gamma
  apply div_le_div₀ (by positivity) hmu (by linarith) (by linarith)

/-- `(1 + γ j)(1 + u) ≤ 1 + γ (j + 1)`: one more rounding. -/
theorem gamma_succ {j : ℕ} (h : ((j + 1 : ℕ) : ℝ) * u < 1) :
    (1 + gamma j) * (1 + u) ≤ 1 + gamma (j + 1) := by
  have hu := u_pos
  push_cast at h
  have hj : (j : ℝ) * u < 1 := by nlinarith
  rw [one_add_gamma hj, one_add_gamma (by push_cast; exact h)]
  push_cast
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by linarith) (by linarith)]
  have : (0 : ℝ) ≤ ((j : ℝ) + 1) * u * u := by positivity
  nlinarith

/-- `(1 + γ a)(1 + γ b) ≤ 1 + γ (a + b)` (Higham, Lemma 3.3). -/
theorem gamma_add {a b : ℕ} (h : ((a + b : ℕ) : ℝ) * u < 1) :
    (1 + gamma a) * (1 + gamma b) ≤ 1 + gamma (a + b) := by
  have hu := u_pos
  push_cast at h
  have ha : (a : ℝ) * u < 1 := by
    have : (0 : ℝ) ≤ b * u := by positivity
    nlinarith
  have hb : (b : ℝ) * u < 1 := by
    have : (0 : ℝ) ≤ a * u := by positivity
    nlinarith
  rw [one_add_gamma ha, one_add_gamma hb, one_add_gamma (by push_cast; exact h)]
  push_cast
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by nlinarith) (by linarith)]
  have : (0 : ℝ) ≤ a * u * (b * u) := by positivity
  nlinarith

end FloatBounds

end
