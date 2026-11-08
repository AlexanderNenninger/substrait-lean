module

public import FloatBounds.Epsilon
public import FloatBounds.TwoPass

/-!
# A threshold's margin, checked on the data (#929)

A filter `SUM(x) > t` keeps a group on an engine exactly when it keeps it on
the reference if the engine's sum is far enough from `t`: farther than twice
its distance to the reference. That distance has a bound per group, from its
row count `n` and `Σ |xᵢ|`, whatever order the engine adds in
(`StdModel.epsilon_group`, Higham §4.2 and the reference's one rounding).
`Σ |xᵢ|` is not known statically, but the engine can bound it from its own
`SUM(ABS(x))` (`StdModel.mag_le_absSummed`).

So the check is computed by the engine, per group, in doubles:

  `|fl(v − t)| > fl(cₙ · fl(A + n · tiny))`, `cₙ = (8n + 16) · 2⁻⁵³`,

with `v` its `SUM(x)` and `A` its `SUM(ABS(x))`. `cₙ` and `n · tiny` are an
integer times a power of two, exact in doubles for `n < 2⁴⁹`; the sum and the
product round once each. `check_sound` shows that a group passing it has
`|v − t| > 2E`, `E` its bound, with room for those roundings; `margin_sound`
that then every evaluation of the sum within `E` of the reference's lies on
the reference's side of `t`, for `<`, `≤`, `>`, `≥` and `=`. The factor 2
covers a sum the engine computes twice (a CTE read by the check and by the
sink), in two orders.
-/

@[expose] public section

namespace FloatBounds

variable (M : StdModel)

theorem absSum_le_mag : ∀ xs : List ℝ, (xs.map abs).sum ≤ mag xs
  | [] => by simp
  | x :: xs => by
    have := absSum_le_mag xs
    have := tiny_pos
    simp only [List.map_cons, List.sum_cons, mag_cons]
    linarith

/-- **A group's sum, any order, against the reference's** (D25): within
`(γₙ + u) · mag xs` of a value within `u` of the exact sum, relatively. -/
theorem StdModel.epsilon_group {xs : List ℝ} {s r : ℝ} (h : M.Summed xs s)
    (hfix : ∀ x ∈ xs, M.fl x = x) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite) (hr : |r - xs.sum| ≤ u * |xs.sum|) :
    |s - r| ≤ (gamma xs.length + u) * mag xs := by
  have a := StdModel.Summed.near M h hfix hn hov
  have b : |xs.sum| ≤ mag xs := (Rnd.abs_sum_le_absSum xs).trans (absSum_le_mag xs)
  have hu := u_pos
  have : u * |xs.sum| ≤ u * mag xs := mul_le_mul_of_nonneg_left b hu.le
  calc |s - r| = |(s - xs.sum) - (r - xs.sum)| := by ring_nf
    _ ≤ |s - xs.sum| + |r - xs.sum| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- **`Σ |xᵢ|` from the engine's own `SUM(ABS(x))`**, any order: `mag xs`
is at most `(A + n · tiny) / (1 − γₙ)`. -/
theorem StdModel.mag_le_absSummed {xs : List ℝ} {A : ℝ} (h : M.Summed (xs.map abs) A)
    (hfix : ∀ x ∈ xs, M.fl |x| = |x|) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite) :
    mag xs * (1 - gamma xs.length) ≤ A + xs.length * tiny := by
  have hfix' : ∀ y ∈ xs.map abs, M.fl y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hfix x hx
  have a := StdModel.Summed.near M h hfix' (by simpa using hn) (by rw [mag_map_abs]; exact hov)
  rw [mag_map_abs, List.length_map] at a
  have e := mag_eq xs
  have hs : ((xs.map abs).map id).sum = (xs.map abs).sum := by simp
  have := (abs_le.1 a).1
  have hm := mag_nonneg xs
  nlinarith

/-- **The check, computed in doubles, is sound**: a group whose engine sum
`v` passes `|fl(v − t)| > fl(cₙ · fl(A + n · tiny))` is farther than `2E`
from `t`, for `E = (γₙ + u) · m` and any `m ≥ tiny` with `m (1 − γₙ) ≤ A + n · tiny`
(`StdModel.mag_le_absSummed`; `mag xs ≥ tiny` for a group with a value). -/
theorem StdModel.check_sound {v t A m : ℝ} {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ 2 ^ 32)
    (hm : m * (1 - gamma n) ≤ A + n * tiny) (hmt : tiny ≤ m)
    (hov1 : |v - t| ≤ maxFinite) (hov2 : A + n * tiny ≤ maxFinite)
    (hov3 : (8 * n + 16) * u * M.fl (A + n * tiny) ≤ maxFinite)
    (hpass : M.fl ((8 * n + 16) * u * M.fl (A + n * tiny)) < |M.fl (v - t)|) :
    2 * ((gamma n + u) * m) < |v - t| := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have h2n := nu_lt hn
  have hg : gamma n ≤ 2 * (n * u) := by
    have : (n : ℝ) * u ≤ 1 / 2 := by push_cast at h2n; linarith
    have := gamma_le_two this; linarith
  have hg0 := gamma_nonneg (n := n) (by push_cast at h2n; nlinarith)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hw : (n : ℝ) * u ≤ 1 / 2 ^ 21 := by
    have := mul_le_mul hn hu' hu.le (by norm_num); linarith [show (2 : ℝ) ^ 32 * (1 / 2 ^ 53) = 1 / 2 ^ 21 by norm_num]
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  set P := A + n * tiny with hP
  set X := |v - t| with hX
  have hm0 : 0 ≤ m := by linarith
  have h12 : (1 : ℝ) / 2 ≤ 1 - gamma n := by linarith
  -- `P ≥ m (1 − γ) ≥ m / 2 ≥ tiny / 2`.
  have hPt : tiny ≤ 2 * P := by have := mul_le_mul_of_nonneg_left h12 hm0; linarith
  have hP0 : 0 ≤ P := by linarith
  -- `fl P ≥ P (1 − u) − u tiny`.
  have e1 := M.err P (by rw [abs_of_nonneg hP0]; exact hov2)
  rw [abs_of_nonneg hP0] at e1
  have f1 : P * (1 - u) - u * tiny ≤ M.fl P := by linarith [(abs_le.1 e1).1]
  have f1' : 0 ≤ M.fl P := M.nonneg _ hP0
  set c : ℝ := (8 * n + 16) * u with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 / 2 ^ 17 := by rw [hc]; linarith
  clear_value P c
  set z := c * M.fl P with hzdef
  have hz : 0 ≤ z := mul_nonneg hc0 f1'
  -- `fl z ≥ z (1 − u) − u tiny`.
  have e2 := M.err z (by rw [abs_of_nonneg hz]; exact hov3)
  rw [abs_of_nonneg hz] at e2
  have f2 : z * (1 - u) - u * tiny ≤ M.fl z := by linarith [(abs_le.1 e2).1]
  -- `|fl(v − t)| ≤ X (1 + u) + u tiny`.
  have e3 := M.err (v - t) hov1
  have f3 : |M.fl (v - t)| ≤ X * (1 + u) + u * tiny := by
    have := abs_sub_abs_le_abs_sub (M.fl (v - t)) (v - t); rw [← hX] at e3; linarith
  -- So `z (1 − u) < X (1 + u) + 2u tiny`.
  have k1 : z * (1 - u) < X * (1 + u) + 2 * (u * tiny) := by linarith
  -- And `z ≥ c (P (1 − u) − u tiny)`.
  have k2 : c * (P * (1 - u) - u * tiny) ≤ z := mul_le_mul_of_nonneg_left f1 hc0
  -- `m ≤ 2P`, then `m ≤ P + 4nuP`.
  have hm2 : m ≤ 2 * P := by have := mul_le_mul_of_nonneg_left h12 hm0; linarith
  have hgm : gamma n * m ≤ 2 * (n * u) * (2 * P) := mul_le_mul hg hm2 hm0 (by positivity)
  have hm3 : m ≤ P + 4 * (n * u) * P := by linarith
  -- `2(γ + u) m ≤ (8n + 4) u P`.
  have hE : 2 * ((gamma n + u) * m) ≤ (8 * n + 4) * u * P := by
    have a : (gamma n + u) * m ≤ (2 * (n * u) + u) * (P + 4 * (n * u) * P) :=
      mul_le_mul (by linarith) hm3 hm0 (by positivity)
    have b : (2 * (n * u) + u) * (P + 4 * (n * u) * P) ≤ (4 * n + 2) * u * P := by
      have : (2 * (n * u) + u) * (4 * (n * u) * P) ≤ (2 * (n * u) + u) * P := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 4 * (n * u) ≤ 1 := by linarith
        have := mul_le_mul_of_nonneg_right this hP0
        linarith
      linarith
    linarith
  -- The slack: `c (1 − u)(P (1 − u) − u tiny) − 2u tiny ≥ (8n + 4) u P (1 + u)`.
  have hs : (8 * n + 4) * u * P * (1 + u) + 2 * (u * tiny) ≤
      c * (P * (1 - u) - u * tiny) * (1 - u) := by
    have q1 : c * (P * (1 - u) - u * tiny) * (1 - u) =
        (8 * n + 16) * u * P - (8 * n + 16) * u * (2 * u * P - u * u * P + u * tiny - u * u * tiny) := by
      rw [hc]; ring
    have q2 : (8 * n + 16) * u * (2 * u * P - u * u * P + u * tiny - u * u * tiny) ≤
        (8 * n + 16) * u * (2 * u * P + u * tiny) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_nonneg (mul_nonneg hu.le hu.le) hP0
      have := mul_nonneg (mul_nonneg hu.le hu.le) ht.le
      linarith
    have q3 : (8 * n + 16) * u * (2 * u * P + u * tiny) ≤ (1 / 2 ^ 17) * (2 * u * P + u * tiny) :=
      mul_le_mul_of_nonneg_right (by rw [← hc]; exact hc1) (by positivity)
    have q4 : (8 * n + 4) * u * P * (1 + u) = (8 * n + 4) * u * P + (8 * n + 4) * u * (u * P) := by ring
    have q5 : (8 * n + 4) * u * (u * P) ≤ (1 / 2 ^ 17) * (u * P) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have q6 : u * tiny ≤ u * (2 * P) := mul_le_mul_of_nonneg_left hPt hu.le
    have q7 : (8 * n + 16) * u * P = (8 * n + 4) * u * P + 12 * (u * P) := by ring
    calc (8 * n + 4) * u * P * (1 + u) + 2 * (u * tiny)
        = (8 * n + 4) * u * P + (8 * n + 4) * u * (u * P) + 2 * (u * tiny) := by rw [q4]
      _ ≤ (8 * n + 4) * u * P + (1 / 2 ^ 17) * (u * P) + 4 * (u * P) := by linarith
      _ ≤ (8 * n + 16) * u * P - (1 / 2 ^ 17) * (2 * u * P + u * tiny) := by
        rw [q7]; have : 0 ≤ u * P := by positivity
        linarith
      _ ≤ (8 * n + 16) * u * P -
          (8 * n + 16) * u * (2 * u * P - u * u * P + u * tiny - u * u * tiny) := by linarith
      _ = c * (P * (1 - u) - u * tiny) * (1 - u) := q1.symm
  -- `2E (1 + u) < X (1 + u)`.
  have : 2 * ((gamma n + u) * m) * (1 + u) < X * (1 + u) := by
    have k3 : c * (P * (1 - u) - u * tiny) * (1 - u) ≤ z * (1 - u) :=
      mul_le_mul_of_nonneg_right k2 (by linarith)
    have k4 : 2 * ((gamma n + u) * m) * (1 + u) ≤ (8 * n + 4) * u * P * (1 + u) :=
      mul_le_mul_of_nonneg_right hE (by linarith)
    linarith
  exact lt_of_mul_lt_mul_right this (by linarith)

/-- **The margin decides the comparison** (#929): two evaluations `v₁`, `v₂`
of the sum, each within `E` of the reference's `r`, and `v₁` farther than `2E`
from `t`: `v₂` and `r` fall on the same side of `t`. -/
theorem margin_sound {v₁ v₂ r t E : ℝ} (h₁ : |v₁ - r| ≤ E) (h₂ : |v₂ - r| ≤ E)
    (hm : 2 * E < |v₁ - t|) :
    (t < v₂ ↔ t < r) ∧ (t ≤ v₂ ↔ t ≤ r) ∧ (v₂ < t ↔ r < t) ∧ (v₂ ≤ t ↔ r ≤ t) ∧
      (v₂ = t ↔ r = t) := by
  have a := abs_le.1 h₁; have b := abs_le.1 h₂
  rcases lt_abs.1 hm with h | h
  · have : t < r := by linarith
    have : t < v₂ := by linarith
    refine ⟨by simp_all, by constructor <;> intro <;> linarith, by constructor <;> intro <;> linarith,
      by constructor <;> intro <;> linarith, by constructor <;> intro <;> linarith⟩
  · have : r < t := by linarith
    have : v₂ < t := by linarith
    refine ⟨by constructor <;> intro <;> linarith, by constructor <;> intro <;> linarith,
      by simp_all, by constructor <;> intro <;> linarith, by constructor <;> intro <;> linarith⟩

/-- **The margin check, end to end** (#929): an engine's sum of a group `s₁`,
with its `SUM(ABS(x))` `A`, passes the check; then another of its sums `s₂`,
in any order, lies on the reference's side of `t`, for every comparison. The
engine's orders are `StdModel.Summed`, its `sum_order` row's. -/
theorem StdModel.margin_check {xs : List ℝ} {s₁ s₂ A r t : ℝ} (h₁ : M.Summed xs s₁)
    (h₂ : M.Summed xs s₂) (hA : M.Summed (xs.map abs) A) (hfix : ∀ x ∈ xs, M.fl x = x)
    (hfixA : ∀ x ∈ xs, M.fl |x| = |x|) (hn1 : 1 ≤ xs.length) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite) (hr : |r - xs.sum| ≤ u * |xs.sum|)
    (hov1 : |s₁ - t| ≤ maxFinite) (hov2 : A + xs.length * tiny ≤ maxFinite)
    (hov3 : (8 * xs.length + 16) * u * M.fl (A + xs.length * tiny) ≤ maxFinite)
    (hpass : M.fl ((8 * xs.length + 16) * u * M.fl (A + xs.length * tiny)) < |M.fl (s₁ - t)|) :
    (t < s₂ ↔ t < r) ∧ (t ≤ s₂ ↔ t ≤ r) ∧ (s₂ < t ↔ r < t) ∧ (s₂ ≤ t ↔ r ≤ t) ∧
      (s₂ = t ↔ r = t) := by
  have hmt : tiny ≤ mag xs := by
    rw [mag_eq]
    have : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
    have : (1 : ℝ) ≤ xs.length := by exact_mod_cast hn1
    have := tiny_pos
    nlinarith
  exact margin_sound (StdModel.epsilon_group M h₁ hfix hn hov hr)
    (StdModel.epsilon_group M h₂ hfix hn hov hr)
    (StdModel.check_sound M hn1 hn (StdModel.mag_le_absSummed M hA hfixA hn hov) hmt hov1 hov2
      hov3 hpass)

end FloatBounds
