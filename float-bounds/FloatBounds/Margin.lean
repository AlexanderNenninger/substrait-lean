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

/-! ## `AVG` -/

/-- **A group's mean, any order, against the reference's** (D25): the
engine's `fl(s / n)` is within `(γₙ + 4u) · mag xs / n` of a value within
`u` of the exact mean, relatively. -/
theorem StdModel.epsilon_group_avg {xs : List ℝ} {s r : ℝ} (h : M.Summed xs s)
    (hfix : ∀ x ∈ xs, M.fl x = x) (hne : xs ≠ []) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite)
    (hr : |r - xs.sum / xs.length| ≤ u * |xs.sum / xs.length|) :
    |M.fl (s / xs.length) - r| ≤ (gamma xs.length + 4 * u) * mag xs / xs.length := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have a := StdModel.Summed.near M h hfix hn hov
  have b : |xs.sum| ≤ mag xs := (Rnd.abs_sum_le_absSum xs).trans (absSum_le_mag xs)
  have hl : (0 : ℝ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hl1 : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have h2n := nu_lt hn
  have hg : gamma xs.length ≤ 2 * (xs.length * u) := by
    have : (xs.length : ℝ) * u ≤ 1 / 2 := by push_cast at h2n; linarith
    have := gamma_le_two this; linarith
  have hg0 := gamma_nonneg (n := xs.length) (by push_cast at h2n; nlinarith)
  have hg1 : gamma xs.length ≤ 1 := by
    have : (xs.length : ℝ) * u ≤ 1 / 2 := by push_cast at h2n; linarith
    linarith
  set n : ℝ := (xs.length : ℝ) with hn'
  set mg := mag xs with hmg
  have hm0 : 0 ≤ mg := mag_nonneg xs
  -- `mag ≥ n · tiny`, so `tiny ≤ mag / n`.
  have hmt : n * tiny ≤ mg := by
    rw [hmg, mag_eq]; have : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp); linarith
  have hs : |s| ≤ 2 * mg := by
    have := abs_sub_abs_le_abs_sub s xs.sum
    have : gamma xs.length * mg ≤ mg := by nlinarith
    linarith
  have hsn : |s / n| ≤ maxFinite := by
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]; nlinarith
  have e := M.err (s / n) hsn
  have hd : |s / n - xs.sum / n| ≤ gamma xs.length * mg / n := by
    rw [← sub_div, abs_div, abs_of_pos hl]; exact div_le_div_of_nonneg_right a hl.le
  have hr' : u * |xs.sum / n| ≤ u * mg / n := by
    rw [abs_div, abs_of_pos hl, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right b hl.le) hu.le
  have hsn2 : |s / n| ≤ 2 * mg / n := by
    rw [abs_div, abs_of_pos hl]; exact div_le_div_of_nonneg_right hs hl.le
  have htn : tiny ≤ mg / n := by rw [le_div_iff₀ hl]; linarith
  have k : u * (|s / n| + tiny) ≤ 3 * u * mg / n := by
    have : |s / n| + tiny ≤ 3 * mg / n := by
      have : 2 * mg / n + mg / n = 3 * mg / n := by ring
      linarith
    calc u * (|s / n| + tiny) ≤ u * (3 * mg / n) := mul_le_mul_of_nonneg_left this hu.le
      _ = 3 * u * mg / n := by ring
  calc |M.fl (s / n) - r|
      = |(M.fl (s / n) - s / n) + (s / n - xs.sum / n) - (r - xs.sum / n)| := by ring_nf
    _ ≤ |M.fl (s / n) - s / n| + |s / n - xs.sum / n| + |r - xs.sum / n| := by
        have := abs_sub (M.fl (s / n) - s / n + (s / n - xs.sum / n)) (r - xs.sum / n)
        have := abs_add_le (M.fl (s / n) - s / n) (s / n - xs.sum / n)
        linarith
    _ ≤ 3 * u * mg / n + gamma xs.length * mg / n + u * mg / n := by linarith
    _ = (gamma xs.length + 4 * u) * mg / n := by ring

/-- **The check for an `AVG`, computed in doubles, is sound**: a group whose
engine mean `v` passes `|fl(v − t)| > fl(cₙ · fl(fl(A + n · tiny) / n))`,
`cₙ = (8n + 32) · 2⁻⁵³`, is farther than `2E` from `t`, for
`E = (γₙ + 4u) · m / n` and any `m ≥ n · tiny` with `m (1 − γₙ) ≤ A + n · tiny`. -/
theorem StdModel.check_sound_avg {v t A m : ℝ} {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ 2 ^ 32)
    (hm : m * (1 - gamma n) ≤ A + n * tiny) (hmt : n * tiny ≤ m)
    (hov1 : |v - t| ≤ maxFinite) (hov2 : A + n * tiny ≤ maxFinite)
    (hov4 : M.fl (A + n * tiny) / n ≤ maxFinite)
    (hov3 : (8 * n + 32) * u * M.fl (M.fl (A + n * tiny) / n) ≤ maxFinite)
    (hpass : M.fl ((8 * n + 32) * u * M.fl (M.fl (A + n * tiny) / n)) < |M.fl (v - t)|) :
    2 * ((gamma n + 4 * u) * m / n) < |v - t| := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have h2n := nu_lt hn
  have hg : gamma n ≤ 2 * (n * u) := by
    have : (n : ℝ) * u ≤ 1 / 2 := by push_cast at h2n; linarith
    have := gamma_le_two this; linarith
  have hg0 := gamma_nonneg (n := n) (by push_cast at h2n; nlinarith)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : (0 : ℝ) < n := by linarith
  have hw : (n : ℝ) * u ≤ 1 / 2 ^ 21 := by
    have := mul_le_mul hn hu' hu.le (by norm_num); linarith [show (2 : ℝ) ^ 32 * (1 / 2 ^ 53) = 1 / 2 ^ 21 by norm_num]
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hm0 : 0 ≤ m := le_trans (by positivity) hmt
  have h12 : (1 : ℝ) / 2 ≤ 1 - gamma n := by linarith
  set P := A + n * tiny with hP
  set X := |v - t| with hX
  -- `P ≥ m / 2 ≥ n tiny / 2`, so `P / n ≥ tiny / 2`.
  have hPm : m ≤ 2 * P := by have := mul_le_mul_of_nonneg_left h12 hm0; linarith
  have hP0 : 0 ≤ P := by linarith
  set Pn := P / n with hPn
  have hPnt : tiny ≤ 2 * Pn := by
    have : tiny ≤ 2 * P / n := by rw [le_div_iff₀ hl]; linarith
    rw [hPn]; linarith [show 2 * P / n = 2 * (P / n) by ring]
  have hPn0 : 0 ≤ Pn := by positivity
  -- `fl P ≥ P (1 − u) − u tiny`.
  have e1 := M.err P (by rw [abs_of_nonneg hP0]; exact hov2)
  rw [abs_of_nonneg hP0] at e1
  have f1 : P * (1 - u) - u * tiny ≤ M.fl P := by linarith [(abs_le.1 e1).1]
  have f1' : 0 ≤ M.fl P := M.nonneg _ hP0
  -- `Q = fl P / n ≥ Pn (1 − u) − u tiny`.
  set Q := M.fl P / n with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have fq : Pn * (1 - u) - u * tiny ≤ Q := by
    have : (P * (1 - u) - u * tiny) / n ≤ Q := div_le_div_of_nonneg_right f1 hl.le
    have h2 : u * tiny / n ≤ u * tiny := div_le_self (by positivity) hn1'
    have h3 : (P * (1 - u) - u * tiny) / n = Pn * (1 - u) - u * tiny / n := by rw [hPn]; ring
    linarith
  have e2 := M.err Q (by rw [abs_of_nonneg hQ0]; exact hov4)
  rw [abs_of_nonneg hQ0] at e2
  have f2 : Q * (1 - u) - u * tiny ≤ M.fl Q := by linarith [(abs_le.1 e2).1]
  have f2' : 0 ≤ M.fl Q := M.nonneg _ hQ0
  -- `fl Q ≥ Pn (1 − 2u) − 2u tiny`.
  have fq2 : Pn * (1 - 2 * u) - 2 * (u * tiny) ≤ M.fl Q := by
    have : (Pn * (1 - u) - u * tiny) * (1 - u) ≤ Q * (1 - u) :=
      mul_le_mul_of_nonneg_right fq (by linarith)
    have : 0 ≤ Pn * (u * u) := by positivity
    have : 0 ≤ u * tiny * u := by positivity
    nlinarith
  set c : ℝ := (8 * n + 32) * u with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 / 2 ^ 17 := by rw [hc]; linarith
  clear_value P Pn Q c
  set z := c * M.fl Q with hzdef
  have hz : 0 ≤ z := mul_nonneg hc0 f2'
  have e3 := M.err z (by rw [abs_of_nonneg hz]; exact hov3)
  rw [abs_of_nonneg hz] at e3
  have f3 : z * (1 - u) - u * tiny ≤ M.fl z := by linarith [(abs_le.1 e3).1]
  have e4 := M.err (v - t) hov1
  have f4 : |M.fl (v - t)| ≤ X * (1 + u) + u * tiny := by
    have := abs_sub_abs_le_abs_sub (M.fl (v - t)) (v - t); rw [← hX] at e4; linarith
  have k1 : z * (1 - u) < X * (1 + u) + 2 * (u * tiny) := by linarith
  have k2 : c * (Pn * (1 - 2 * u) - 2 * (u * tiny)) ≤ z := mul_le_mul_of_nonneg_left fq2 hc0
  -- `m / n ≤ Pn + 4nu Pn`, and `2(γ + 4u) m / n ≤ (8n + 16) u Pn`.
  have hgm : gamma n * m ≤ 2 * (n * u) * (2 * P) := mul_le_mul hg hPm hm0 (by positivity)
  have hm3 : m ≤ P + 4 * (n * u) * P := by linarith
  have hmn : m / n ≤ Pn + 4 * (n * u) * Pn := by
    rw [hPn, div_le_iff₀ hl]
    have : (P / n + 4 * (n * u) * (P / n)) * n = P + 4 * (n * u) * P := by field_simp
    linarith
  have hE : 2 * ((gamma n + 4 * u) * m / n) ≤ (8 * n + 16) * u * Pn := by
    have e : (gamma n + 4 * u) * m / n = (gamma n + 4 * u) * (m / n) := by ring
    have hmn0 : 0 ≤ m / n := by positivity
    have a : (gamma n + 4 * u) * (m / n) ≤ (2 * (n * u) + 4 * u) * (Pn + 4 * (n * u) * Pn) :=
      mul_le_mul (by linarith) hmn hmn0 (by positivity)
    have b : (2 * (n * u) + 4 * u) * (4 * (n * u) * Pn) ≤ (2 * (n * u) + 4 * u) * Pn := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 4 * (n * u) ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_right this hPn0
      linarith
    rw [e]; linarith
  -- The slack, as for `SUM`, with `16 u Pn` to spare.
  have hs : (8 * n + 16) * u * Pn * (1 + u) + 2 * (u * tiny) ≤
      c * (Pn * (1 - 2 * u) - 2 * (u * tiny)) * (1 - u) := by
    have q1 : c * (Pn * (1 - 2 * u) - 2 * (u * tiny)) * (1 - u) =
        (8 * n + 32) * u * Pn -
          (8 * n + 32) * u * (3 * u * Pn - 2 * u * u * Pn + 2 * (u * tiny) - 2 * (u * tiny) * u) := by
      rw [hc]; ring
    have q2 : (8 * n + 32) * u * (3 * u * Pn - 2 * u * u * Pn + 2 * (u * tiny) - 2 * (u * tiny) * u) ≤
        (8 * n + 32) * u * (3 * u * Pn + 2 * (u * tiny)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have := mul_nonneg (mul_nonneg hu.le hu.le) hPn0
      have := mul_nonneg (mul_nonneg hu.le ht.le) hu.le
      linarith
    have q3 : (8 * n + 32) * u * (3 * u * Pn + 2 * (u * tiny)) ≤
        (1 / 2 ^ 17) * (3 * u * Pn + 2 * (u * tiny)) :=
      mul_le_mul_of_nonneg_right (by rw [← hc]; exact hc1) (by positivity)
    have q4 : (8 * n + 16) * u * Pn * (1 + u) = (8 * n + 16) * u * Pn + (8 * n + 16) * u * (u * Pn) := by
      ring
    have q5 : (8 * n + 16) * u * (u * Pn) ≤ (1 / 2 ^ 17) * (u * Pn) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have q6 : u * tiny ≤ u * (2 * Pn) := mul_le_mul_of_nonneg_left hPnt hu.le
    have q7 : (8 * n + 32) * u * Pn = (8 * n + 16) * u * Pn + 16 * (u * Pn) := by ring
    have : 0 ≤ u * Pn := by positivity
    calc (8 * n + 16) * u * Pn * (1 + u) + 2 * (u * tiny)
        = (8 * n + 16) * u * Pn + (8 * n + 16) * u * (u * Pn) + 2 * (u * tiny) := by rw [q4]
      _ ≤ (8 * n + 16) * u * Pn + (1 / 2 ^ 17) * (u * Pn) + 4 * (u * Pn) := by linarith
      _ ≤ (8 * n + 32) * u * Pn - (1 / 2 ^ 17) * (3 * u * Pn + 2 * (u * tiny)) := by
        rw [q7]; linarith
      _ ≤ (8 * n + 32) * u * Pn -
          (8 * n + 32) * u * (3 * u * Pn - 2 * u * u * Pn + 2 * (u * tiny) - 2 * (u * tiny) * u) := by
        linarith
      _ = c * (Pn * (1 - 2 * u) - 2 * (u * tiny)) * (1 - u) := q1.symm
  have : 2 * ((gamma n + 4 * u) * m / n) * (1 + u) < X * (1 + u) := by
    have k3 : c * (Pn * (1 - 2 * u) - 2 * (u * tiny)) * (1 - u) ≤ z * (1 - u) :=
      mul_le_mul_of_nonneg_right k2 (by linarith)
    have k4 : 2 * ((gamma n + 4 * u) * m / n) * (1 + u) ≤ (8 * n + 16) * u * Pn * (1 + u) :=
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

/-- **The margin check of an `AVG`, end to end** (#929): an engine's mean of a
group `fl(s₁ / n)`, with its `SUM(ABS(x))` `A`, passes the `AVG` check; then
another of its means `fl(s₂ / n)`, in any order, lies on the reference's side
of `t`, for every comparison. -/
theorem StdModel.margin_check_avg {xs : List ℝ} {s₁ s₂ A r t : ℝ} (h₁ : M.Summed xs s₁)
    (h₂ : M.Summed xs s₂) (hA : M.Summed (xs.map abs) A) (hfix : ∀ x ∈ xs, M.fl x = x)
    (hfixA : ∀ x ∈ xs, M.fl |x| = |x|) (hn1 : 1 ≤ xs.length) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite)
    (hr : |r - xs.sum / xs.length| ≤ u * |xs.sum / xs.length|)
    (hov1 : |M.fl (s₁ / xs.length) - t| ≤ maxFinite) (hov2 : A + xs.length * tiny ≤ maxFinite)
    (hov4 : M.fl (A + xs.length * tiny) / xs.length ≤ maxFinite)
    (hov3 : (8 * xs.length + 32) * u * M.fl (M.fl (A + xs.length * tiny) / xs.length) ≤ maxFinite)
    (hpass : M.fl ((8 * xs.length + 32) * u * M.fl (M.fl (A + xs.length * tiny) / xs.length)) <
      |M.fl (M.fl (s₁ / xs.length) - t)|) :
    (t < M.fl (s₂ / xs.length) ↔ t < r) ∧ (t ≤ M.fl (s₂ / xs.length) ↔ t ≤ r) ∧
      (M.fl (s₂ / xs.length) < t ↔ r < t) ∧ (M.fl (s₂ / xs.length) ≤ t ↔ r ≤ t) ∧
      (M.fl (s₂ / xs.length) = t ↔ r = t) := by
  have hne : xs ≠ [] := List.ne_nil_of_length_pos hn1
  have hmt : (xs.length : ℝ) * tiny ≤ mag xs := by
    rw [mag_eq]; have : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp); linarith
  have e := StdModel.check_sound_avg M hn1 hn (StdModel.mag_le_absSummed M hA hfixA hn hov) hmt
    hov1 hov2 hov4 hov3 hpass
  exact margin_sound (StdModel.epsilon_group_avg M h₁ hfix hne hn hov hr)
    (StdModel.epsilon_group_avg M h₂ hfix hne hn hov hr) (by rw [mul_div_assoc] at e ⊢; linarith)

end FloatBounds
