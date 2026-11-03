module

public import FloatBounds.WelfordRel

/-!
# Chan's merge, to first order in the spread (#85)

DuckDB aggregates in parallel: each thread runs Welford's update
(`WelfordRel.lean`) over its rows, and the threads' states are merged by
Chan's formula. This file extends the first-order bound to any tree of
updates and merges.

The weight that bounds the merges is `L n = 2 n (⌈log₂ n⌉ + 1)`
(`Lw`): a merge of `a` and `b` values adds at most `2 min(a, b)` to it
(`Lw_merge`), and a value Welford's update adds, `2` (`Lw_succ`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- `L n = 2 n (⌈log₂ n⌉ + 1)`. -/
noncomputable def Lw (n : ℕ) : ℝ := 2 * n * (Nat.clog 2 n + 1)

theorem clog_add_ge {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Nat.clog 2 a + 1 ≤ Nat.clog 2 (a + b) := by
  by_contra h
  have h1 : Nat.clog 2 (a + b) ≤ Nat.clog 2 a := by omega
  have h2 : a + b ≤ 2 ^ Nat.clog 2 a :=
    le_trans (Nat.le_pow_clog (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) h1)
  rcases Nat.lt_or_ge 1 a with ha1 | ha1
  · have h3 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) ha1
    simp only [Nat.pred_eq_sub_one] at h3
    have h4 : 0 < Nat.clog 2 a := Nat.clog_pos (by norm_num) ha1
    have : 2 ^ Nat.clog 2 a = 2 * 2 ^ (Nat.clog 2 a - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : a = 1 := by omega
    subst this
    simp at h2; omega

theorem Lw_nonneg (n : ℕ) : 0 ≤ Lw n := by unfold Lw; positivity

theorem Lw_merge_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Lw a + Lw b + 2 * (a : ℝ) ≤ Lw (a + b) := by
  have h1 := clog_add_ge ha hab
  have h2 := Nat.clog_mono_right 2 (show b ≤ a + b by omega)
  have h1' : (Nat.clog 2 a : ℝ) + 1 ≤ Nat.clog 2 (a + b) := by exact_mod_cast h1
  have h2' : (Nat.clog 2 b : ℝ) ≤ Nat.clog 2 (a + b) := by exact_mod_cast h2
  unfold Lw; push_cast
  have : (0 : ℝ) ≤ a := by positivity
  have : (0 : ℝ) ≤ b := by positivity
  nlinarith

/-- A merge adds at least `2 min(a, b)` to the weight. -/
theorem Lw_merge {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Lw a + Lw b + 2 * ((min a b : ℕ) : ℝ) ≤ Lw (a + b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]; exact Lw_merge_le ha hab
  · rw [min_eq_right hab, add_comm a b]
    have := Lw_merge_le hb hab; linarith

/-- Welford's update adds at least `2` to the weight. -/
theorem Lw_succ (K : ℕ) : Lw K + 2 ≤ Lw (K + 1) := by
  have h := Nat.clog_mono_right 2 (show K ≤ K + 1 by omega)
  have h' : (Nat.clog 2 K : ℝ) ≤ Nat.clog 2 (K + 1) := by exact_mod_cast h
  unfold Lw; push_cast
  have : (0 : ℝ) ≤ K := by positivity
  have : (0 : ℝ) ≤ Nat.clog 2 K := by positivity
  nlinarith

theorem Lw_ge (n : ℕ) : 2 * ((n : ℝ) - 1) ≤ Lw n ∧ (n : ℝ) ≤ Lw n := by
  unfold Lw
  have : (0 : ℝ) ≤ Nat.clog 2 n := by positivity
  have : (0 : ℝ) ≤ n := by positivity
  constructor <;> nlinarith

theorem Lw_le {n : ℕ} (h : n ≤ 2 ^ 32) : Lw n ≤ 66 * n := by
  have hc : Nat.clog 2 n ≤ 32 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr h
  have hc' : (Nat.clog 2 n : ℝ) ≤ 32 := by exact_mod_cast hc
  unfold Lw
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-! ## The error terms of a merge -/

/-- The difference of the means, `Δ̂ = fl(m̂_b − m̂_a)`, against `Δ = M_b − M_a`. -/
theorem delta_err {Δ Δt Δh A : ℝ} (hA : tiny ≤ A)
    (h1 : |Δt - Δ| ≤ 6 * u * A) (h2 : |Δh - Δt| ≤ u * (|Δt| + tiny)) :
    |Δh - Δ| ≤ 7.1 * u * A + u * |Δ| := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hA0 : 0 ≤ A := le_trans tiny_pos.le hA
  have a1 : |Δt| ≤ |Δ| + 6 * u * A := by have := abs_sub_abs_le_abs_sub Δt Δ; linarith
  have a2 : u * |Δt| ≤ u * |Δ| + u * (6 * u * A) := by
    have := mul_le_mul_of_nonneg_left a1 hu.le; linarith
  have a3 : u * (6 * u * A) ≤ 0.05 * (u * A) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 6 * u ≤ 0.05) (by positivity : 0 ≤ u * A)
    linarith
  have a4 : u * tiny ≤ u * A := mul_le_mul_of_nonneg_left hA hu.le
  have e : Δh - Δ = (Δh - Δt) + (Δt - Δ) := by ring
  rw [e]
  have h3 := abs_add_le (Δh - Δt) (Δt - Δ)
  have h4 : u * (|Δt| + tiny) = u * |Δt| + u * tiny := by ring
  have h5 : (7.1 : ℝ) * u * A = 7.1 * (u * A) := by ring
  have h6 : (6 : ℝ) * u * A = 6 * (u * A) := by ring
  rw [h4] at h2; rw [h6] at h1; rw [h5]
  have h7 : 0 ≤ u * A := by positivity
  linarith

/-- `h |Δ̂² − Δ²| ≤ 14.2 u A (h |Δ|) + 2 u ΔS + 103 u² h A²`, `ΔS = Δ² h`, when
`|Δ̂ − Δ| ≤ 7.1 u A + u |Δ|` and `|Δ| ≤ A`. -/
theorem sq_err {Δ Δh A h : ℝ} (hh : 0 ≤ h) (hA0 : 0 ≤ A) (hΔA : |Δ| ≤ A)
    (he : |Δh - Δ| ≤ 7.1 * u * A + u * |Δ|) :
    h * |Δh ^ 2 - Δ ^ 2| ≤ 14.2 * u * A * (h * |Δ|) + 2 * u * (Δ ^ 2 * h)
      + 103 * u ^ 2 * h * A ^ 2 := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  set e := 7.1 * u * A + u * |Δ|
  have he0 : 0 ≤ e := by positivity
  have h1 : |Δh ^ 2 - Δ ^ 2| ≤ e * (2 * |Δ| + e) := by
    have : Δh ^ 2 - Δ ^ 2 = (Δh - Δ) * (Δh + Δ) := by ring
    rw [this, abs_mul]
    have : |Δh + Δ| ≤ 2 * |Δ| + e := by
      have := abs_add_le (Δh - Δ) (2 * Δ)
      have e2 : Δh + Δ = (Δh - Δ) + 2 * Δ := by ring
      rw [e2]; rw [abs_mul, abs_two] at this; linarith
    exact mul_le_mul he this (abs_nonneg _) he0
  have h2 : e * e ≤ 2 * ((7.1 * u * A) ^ 2 + (u * |Δ|) ^ 2) := by
    simp only [e]; nlinarith [sq_nonneg (7.1 * u * A - u * |Δ|)]
  have h3 : (u * |Δ|) ^ 2 ≤ (u * A) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΔA hu.le
    exact pow_le_pow_left₀ (by positivity) this 2
  have h4 : h * (e * (2 * |Δ| + e)) = 2 * (h * |Δ|) * e + h * (e * e) := by ring
  have h5 : 2 * (h * |Δ|) * e = 14.2 * u * A * (h * |Δ|) + 2 * u * (Δ ^ 2 * h) := by
    simp only [e]; rw [← sq_abs Δ]; ring
  have h6 : h * (e * e) ≤ 103 * u ^ 2 * h * A ^ 2 := by
    calc h * (e * e) ≤ h * (2 * ((7.1 * u * A) ^ 2 + (u * A) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hh; nlinarith
      _ ≤ 103 * u ^ 2 * h * A ^ 2 := by nlinarith [sq_nonneg (u * A), mul_nonneg hh (sq_nonneg (u * A))]
  calc h * |Δh ^ 2 - Δ ^ 2| ≤ h * (e * (2 * |Δ| + e)) := mul_le_mul_of_nonneg_left h1 hh
    _ ≤ _ := by rw [h4, h5]; linarith

/-- The merge's term `T̂ ≈ Δ̂² h`, against `ΔS = Δ² h`, from the error of `Δ̂²`. -/
theorem T_err {T Q ΔS X A h : ℝ} (hX : 0 ≤ X) (hΔS : 0 ≤ ΔS) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hQ : |Q - ΔS| ≤ 14.2 * u * A * X + 2 * u * ΔS + 103 * u ^ 2 * h * A ^ 2)
    (hT : |T - Q| ≤ 5 * u * (Q + (1 + h) * tiny)) :
    |T - ΔS| ≤ 14.3 * u * A * X + 7.1 * u * ΔS + 104 * u ^ 2 * h * A ^ 2
      + 5 * u * (1 + h) * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hQ' : Q ≤ ΔS + (14.2 * u * A * X + 2 * u * ΔS + 103 * u ^ 2 * h * A ^ 2) := by
    have := (abs_le.mp hQ).2; linarith
  have h1 : 5 * u * Q ≤ 5 * u * ΔS + 5 * u * (14.2 * u * A * X + 2 * u * ΔS + 103 * u ^ 2 * h * A ^ 2) :=
    by have := mul_le_mul_of_nonneg_left hQ' (by positivity : (0 : ℝ) ≤ 5 * u); linarith
  have p1 : 0 ≤ u * A * X := by positivity
  have p2 : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
  have p3 : 0 ≤ u * ΔS := by positivity
  have h2 : 5 * u * (14.2 * u * A * X + 2 * u * ΔS + 103 * u ^ 2 * h * A ^ 2)
      ≤ 0.1 * (u * A * X) + 0.01 * (u * ΔS) + 1 * (u ^ 2 * h * A ^ 2) := by
    have q1 : 5 * u * (14.2 * u * A * X) ≤ 0.1 * (u * A * X) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 71 * u ≤ 0.1) p1; nlinarith
    have q2 : 5 * u * (2 * u * ΔS) ≤ 0.01 * (u * ΔS) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 10 * u ≤ 0.01) p3; nlinarith
    have q3 : 5 * u * (103 * u ^ 2 * h * A ^ 2) ≤ 1 * (u ^ 2 * h * A ^ 2) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 515 * u ≤ 1) p2; nlinarith
    linarith
  have e : T - ΔS = (T - Q) + (Q - ΔS) := by ring
  rw [e]
  have h3 := abs_add_le (T - Q) (Q - ΔS)
  have h4 : 5 * u * (Q + (1 + h) * tiny) = 5 * u * Q + 5 * u * (1 + h) * tiny := by ring
  have e1 : 14.3 * u * A * X = 14.3 * (u * A * X) := by ring
  have e2 : 14.2 * u * A * X = 14.2 * (u * A * X) := by ring
  have e3 : 104 * u ^ 2 * h * A ^ 2 = 104 * (u ^ 2 * h * A ^ 2) := by ring
  have e4 : 103 * u ^ 2 * h * A ^ 2 = 103 * (u ^ 2 * h * A ^ 2) := by ring
  have e5 : 7.1 * u * ΔS = 7.1 * (u * ΔS) := by ring
  have e6 : 2 * u * ΔS = 2 * (u * ΔS) := by ring
  have e7 : 5 * u * ΔS = 5 * (u * ΔS) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- The co-moment after a merge: `Ŝ₁ = fl(Ŝ_a + Ŝ_b)`, then `Ŝ = fl(Ŝ₁ + T̂)`. -/
theorem merge_com {Sa Sb ΔS Sha Shb Sh1 T Sh Ea Eb X A h : ℝ} (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb)
    (hΔS : 0 ≤ ΔS) (hX : 0 ≤ X) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hEa : |Sha - Sa| ≤ Ea) (hEb : |Shb - Sb| ≤ Eb)
    (hT : |T - ΔS| ≤ 14.3 * u * A * X + 7.1 * u * ΔS + 104 * u ^ 2 * h * A ^ 2
      + 5 * u * (1 + h) * tiny)
    (h1 : |Sh1 - (Sha + Shb)| ≤ u * (|Sha + Shb| + tiny))
    (h2 : |Sh - (Sh1 + T)| ≤ u * (|Sh1 + T| + tiny)) :
    |Sh - (Sa + Sb + ΔS)| ≤ (1 + u) ^ 2 * (Ea + Eb) + 14.4 * u * A * X
      + 8.2 * u * (Sa + Sb + ΔS) + 105 * u ^ 2 * h * A ^ 2 + (7.1 + 5.1 * h) * u * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have hE0 : 0 ≤ Ea + Eb := by
    have := abs_nonneg (Sha - Sa); have := abs_nonneg (Shb - Sb); linarith
  -- the sum of the children's co-moments
  have k1 : |Sha + Shb| ≤ Sa + Sb + (Ea + Eb) := by
    have e : Sha + Shb = (Sa + Sb) + ((Sha - Sa) + (Shb - Sb)) := by ring
    rw [e]; have := abs_add_le (Sa + Sb) ((Sha - Sa) + (Shb - Sb))
    have := abs_add_le (Sha - Sa) (Shb - Sb)
    rw [abs_of_nonneg (by positivity : 0 ≤ Sa + Sb)] at *; linarith
  have k2 : |Sh1 - (Sa + Sb)| ≤ (1 + u) * (Ea + Eb) + u * (Sa + Sb) + u * tiny := by
    have e : Sh1 - (Sa + Sb) = (Sh1 - (Sha + Shb)) + ((Sha - Sa) + (Shb - Sb)) := by ring
    rw [e]
    have := abs_add_le (Sh1 - (Sha + Shb)) ((Sha - Sa) + (Shb - Sb))
    have := abs_add_le (Sha - Sa) (Shb - Sb)
    have := mul_le_mul_of_nonneg_left k1 hu.le
    nlinarith
  set Z := (1 + u) * (Ea + Eb) + u * (Sa + Sb) + u * tiny + (14.3 * u * A * X + 7.1 * u * ΔS
    + 104 * u ^ 2 * h * A ^ 2 + 5 * u * (1 + h) * tiny) with hZ
  have k3 : |Sh1 + T - (Sa + Sb + ΔS)| ≤ Z := by
    have e : Sh1 + T - (Sa + Sb + ΔS) = (Sh1 - (Sa + Sb)) + (T - ΔS) := by ring
    rw [e]; have := abs_add_le (Sh1 - (Sa + Sb)) (T - ΔS); linarith
  have k4 : |Sh1 + T| ≤ (Sa + Sb + ΔS) + Z := by
    have := abs_sub_abs_le_abs_sub (Sh1 + T) (Sa + Sb + ΔS)
    rw [abs_of_nonneg (by positivity : 0 ≤ Sa + Sb + ΔS)] at this; linarith
  have k5 : |Sh - (Sa + Sb + ΔS)| ≤ (1 + u) * Z + u * (Sa + Sb + ΔS) + u * tiny := by
    have e : Sh - (Sa + Sb + ΔS) = (Sh - (Sh1 + T)) + (Sh1 + T - (Sa + Sb + ΔS)) := by ring
    rw [e]
    have := abs_add_le (Sh - (Sh1 + T)) (Sh1 + T - (Sa + Sb + ΔS))
    have := mul_le_mul_of_nonneg_left k4 hu.le
    nlinarith
  refine le_trans k5 ?_
  -- `(1 + u) Z` with the small terms by `1.001`
  have p1 : 0 ≤ u * A * X := by positivity
  have p2 : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
  have p3 : 0 ≤ u * (Sa + Sb) := by positivity
  have p4 : 0 ≤ u * ΔS := by positivity
  have p5 : 0 ≤ u * tiny := by positivity
  have p6 : 0 ≤ h * (u * tiny) := by positivity
  set W := u * (Sa + Sb) + u * tiny + (14.3 * u * A * X + 7.1 * u * ΔS + 104 * u ^ 2 * h * A ^ 2
    + 5 * u * (1 + h) * tiny) with hW
  have hW0 : 0 ≤ W := by simp only [hW]; positivity
  have hZW : Z = (1 + u) * (Ea + Eb) + W := by simp only [hZ, hW]; ring
  have k6 : (1 + u) * W ≤ W + W / 2 ^ 50 := by
    have := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1 / 2 ^ 50) hW0; nlinarith
  have k7 : W / 2 ^ 50 ≤ 0.0001 * (u * A * X) + 0.0001 * (u * (Sa + Sb)) + 0.0001 * (u * ΔS)
      + 0.0001 * (u ^ 2 * h * A ^ 2) + 0.0001 * (u * tiny) + 0.0001 * (h * (u * tiny)) := by
    simp only [hW]
    have : 5 * u * (1 + h) * tiny = 5 * (u * tiny) + 5 * (h * (u * tiny)) := by ring
    rw [this]
    have e1 : 14.3 * u * A * X = 14.3 * (u * A * X) := by ring
    have e2 : 104 * u ^ 2 * h * A ^ 2 = 104 * (u ^ 2 * h * A ^ 2) := by ring
    have e3 : 7.1 * u * ΔS = 7.1 * (u * ΔS) := by ring
    rw [e1, e2, e3]
    linarith
  have e4 : (1 + u) * Z = (1 + u) ^ 2 * (Ea + Eb) + (1 + u) * W := by rw [hZW]; ring
  rw [e4]
  have hsplit : u * (Sa + Sb + ΔS) = u * (Sa + Sb) + u * ΔS := by ring
  have e5 : 8.2 * u * (Sa + Sb + ΔS) = 8.2 * (u * (Sa + Sb)) + 8.2 * (u * ΔS) := by ring
  have e6 : (7.1 + 5.1 * h) * u * tiny = 7.1 * (u * tiny) + 5.1 * (h * (u * tiny)) := by ring
  have e7 : 14.4 * u * A * X = 14.4 * (u * A * X) := by ring
  have e8 : 105 * u ^ 2 * h * A ^ 2 = 105 * (u ^ 2 * h * A ^ 2) := by ring
  have hWe : W = u * (Sa + Sb) + u * tiny + 14.3 * (u * A * X) + 7.1 * (u * ΔS)
      + 104 * (u ^ 2 * h * A ^ 2) + 5 * (u * tiny) + 5 * (h * (u * tiny)) := by
    simp only [hW]; ring
  rw [e5, e6, e7, e8, hsplit]
  linarith

end FloatBounds

end
