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

/-- `(1 + u)² (1 + 3 k u) ≤ 1 + 3 n u` for `k + 1 ≤ n`. -/
theorem fac_merge {k n : ℝ} (_hk : 0 ≤ k) (hkn : k + 1 ≤ n) (hn : n * u ≤ 1 / 2 ^ 21) :
    (1 + u) ^ 2 * (1 + 3 * k * u) ≤ 1 + 3 * n * u := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hku : k * u ≤ 1 / 2 ^ 21 := by nlinarith
  have h1 : (1 + u) ^ 2 * (1 + 3 * k * u) = 1 + 3 * k * u + (2 * u + u ^ 2) * (1 + 3 * k * u) := by
    ring
  have h2 : (2 * u + u ^ 2) * (1 + 3 * k * u) ≤ 3 * u := by
    have : 1 + 3 * k * u ≤ 1 + 3 / 2 ^ 21 := by linarith
    have : 2 * u + u ^ 2 ≤ 2 * u + u / 2 ^ 53 := by nlinarith
    nlinarith
  have h3 : 3 * k * u + 3 * u ≤ 3 * n * u := by nlinarith
  linarith

/-- The terms of `merge_fold`: the children's bounds and a merge's new terms
fit in the merged bound. -/
theorem fold_terms {na nb m h Aa Ab Da Db X Sa Sb ΔS La Lb L : ℝ}
    (hna : 1 ≤ na) (hnb : 1 ≤ nb) (hm1 : 1 ≤ m) (_hma : m ≤ na) (_hmb : m ≤ nb) (_hh : 0 ≤ h)
    (hhm : h ≤ m) (hAa : 0 ≤ Aa) (hAb : 0 ≤ Ab)
    (hDa : 0 ≤ Da) (hDb : 0 ≤ Db) (hX : 0 ≤ X) (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb) (hΔS : 0 ≤ ΔS)
    (hLa : 0 ≤ La) (hLb : 0 ≤ Lb) (hL : La + Lb + 2 * m ≤ L) :
    (17 * u * Aa * Da + 9 * u * na * Sa + 60 * u ^ 2 * La * Aa ^ 2 + 12 * u * tiny * La)
      + (17 * u * Ab * Db + 9 * u * nb * Sb + 60 * u ^ 2 * Lb * Ab ^ 2 + 12 * u * tiny * Lb)
      + (14.4 * u * (Aa + Ab) * X + 8.2 * u * (Sa + Sb + ΔS) + 105 * u ^ 2 * h * (Aa + Ab) ^ 2
        + (7.1 + 5.1 * h) * u * tiny)
      ≤ 17 * u * (Aa + Ab) * (Da + Db + X) + 9 * u * (na + nb) * (Sa + Sb + ΔS)
        + 60 * u ^ 2 * L * (Aa + Ab) ^ 2 + 12 * u * tiny * L := by
  have hu := u_pos
  have ht := tiny_pos
  have a1 : u * Aa * Da ≤ u * (Aa + Ab) * Da := by
    have := mul_le_mul_of_nonneg_right (by linarith : Aa ≤ Aa + Ab) (by positivity : 0 ≤ u * Da)
    linarith
  have a2 : u * Ab * Db ≤ u * (Aa + Ab) * Db := by
    have := mul_le_mul_of_nonneg_right (by linarith : Ab ≤ Aa + Ab) (by positivity : 0 ≤ u * Db)
    linarith
  have a3 : 0 ≤ u * (Aa + Ab) * X := by positivity
  have b1 : u * (na * Sa) ≤ u * ((na + nb - 1) * Sa) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hSa) hu.le
  have b2 : u * (nb * Sb) ≤ u * ((na + nb - 1) * Sb) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hSb) hu.le
  have b3 : 0 ≤ u * ((na + nb - 1) * ΔS) := by
    have : 0 ≤ na + nb - 1 := by linarith
    positivity
  have b4 : 0 ≤ u * (Sa + Sb + ΔS) := by positivity
  have e1 : Aa ^ 2 ≤ (Aa + Ab) ^ 2 := by nlinarith
  have e2 : Ab ^ 2 ≤ (Aa + Ab) ^ 2 := by nlinarith
  have e3 : u ^ 2 * La * Aa ^ 2 ≤ u ^ 2 * La * (Aa + Ab) ^ 2 :=
    mul_le_mul_of_nonneg_left e1 (by positivity)
  have e4 : u ^ 2 * Lb * Ab ^ 2 ≤ u ^ 2 * Lb * (Aa + Ab) ^ 2 :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have e5 : u ^ 2 * h * (Aa + Ab) ^ 2 ≤ u ^ 2 * m * (Aa + Ab) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhm (by positivity)) (by positivity)
  have e6 : u ^ 2 * (La + Lb + 2 * m) * (Aa + Ab) ^ 2 ≤ u ^ 2 * L * (Aa + Ab) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity)) (by positivity)
  have e7 : 0 ≤ u ^ 2 * m * (Aa + Ab) ^ 2 := by
    have : 0 ≤ m := by linarith
    positivity
  have f1 : u * tiny * (7.1 + 5.1 * h) ≤ u * tiny * (24 * m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have f2 : u * tiny * (La + Lb + 2 * m) ≤ u * tiny * L := mul_le_mul_of_nonneg_left hL (by positivity)
  linarith

/-- **A merge keeps the invariant's bound**, with `m = min(n_a, n_b)`,
`h = n_a n_b / n ≤ m` and `X = h |Δ|`. -/
theorem merge_fold {na nb m h Aa Ab Da Db X Sa Sb ΔS Ea Eb La Lb L : ℝ}
    (hna : 1 ≤ na) (hnb : 1 ≤ nb) (hm1 : 1 ≤ m) (hma : m ≤ na) (hmb : m ≤ nb) (hh : 0 ≤ h)
    (hhm : h ≤ m) (hn : (na + nb) * u ≤ 1 / 2 ^ 21) (hAa : 0 ≤ Aa) (hAb : 0 ≤ Ab)
    (hDa : 0 ≤ Da) (hDb : 0 ≤ Db) (hX : 0 ≤ X) (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb) (hΔS : 0 ≤ ΔS)
    (hLa : 0 ≤ La) (hLb : 0 ≤ Lb) (hL : La + Lb + 2 * m ≤ L)
    (hEa : Ea ≤ (1 + 3 * na * u) * (17 * u * Aa * Da + 9 * u * na * Sa + 60 * u ^ 2 * La * Aa ^ 2
      + 12 * u * tiny * La))
    (hEb : Eb ≤ (1 + 3 * nb * u) * (17 * u * Ab * Db + 9 * u * nb * Sb + 60 * u ^ 2 * Lb * Ab ^ 2
      + 12 * u * tiny * Lb)) :
    (1 + u) ^ 2 * (Ea + Eb) + 14.4 * u * (Aa + Ab) * X + 8.2 * u * (Sa + Sb + ΔS)
        + 105 * u ^ 2 * h * (Aa + Ab) ^ 2 + (7.1 + 5.1 * h) * u * tiny
      ≤ (1 + 3 * (na + nb) * u) * (17 * u * (Aa + Ab) * (Da + Db + X)
        + 9 * u * (na + nb) * (Sa + Sb + ΔS) + 60 * u ^ 2 * L * (Aa + Ab) ^ 2
        + 12 * u * tiny * L) := by
  have hu := u_pos
  have ht := tiny_pos
  set A := Aa + Ab
  set S := Sa + Sb + ΔS
  set n := na + nb
  have hA0 : 0 ≤ A := by positivity
  set Ta := 17 * u * Aa * Da + 9 * u * na * Sa + 60 * u ^ 2 * La * Aa ^ 2 + 12 * u * tiny * La
  set Tb := 17 * u * Ab * Db + 9 * u * nb * Sb + 60 * u ^ 2 * Lb * Ab ^ 2 + 12 * u * tiny * Lb
  have hTa : 0 ≤ Ta := by positivity
  have hTb : 0 ≤ Tb := by positivity
  set Tn := 17 * u * A * (Da + Db + X) + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * tiny * L
  -- the children
  have fa := fac_merge (by linarith) (by linarith : na + 1 ≤ n) hn
  have fb := fac_merge (by linarith) (by linarith : nb + 1 ≤ n) hn
  have k1 : (1 + u) ^ 2 * (Ea + Eb) ≤ (1 + 3 * n * u) * (Ta + Tb) := by
    have g1 : (1 + u) ^ 2 * Ea ≤ (1 + 3 * n * u) * Ta := by
      calc (1 + u) ^ 2 * Ea ≤ (1 + u) ^ 2 * ((1 + 3 * na * u) * Ta) := by gcongr
        _ = ((1 + u) ^ 2 * (1 + 3 * na * u)) * Ta := by ring
        _ ≤ _ := by gcongr
    have g2 : (1 + u) ^ 2 * Eb ≤ (1 + 3 * n * u) * Tb := by
      calc (1 + u) ^ 2 * Eb ≤ (1 + u) ^ 2 * ((1 + 3 * nb * u) * Tb) := by gcongr
        _ = ((1 + u) ^ 2 * (1 + 3 * nb * u)) * Tb := by ring
        _ ≤ _ := by gcongr
    linarith
  have k2 := fold_terms hna hnb hm1 hma hmb hh hhm hAa hAb hDa hDb hX hSa hSb hΔS hLa hLb hL
  have hnew0 : 0 ≤ 14.4 * u * A * X + 8.2 * u * S + 105 * u ^ 2 * h * A ^ 2
      + (7.1 + 5.1 * h) * u * tiny := by positivity
  have k3 : 14.4 * u * A * X + 8.2 * u * S + 105 * u ^ 2 * h * A ^ 2 + (7.1 + 5.1 * h) * u * tiny
      ≤ (1 + 3 * n * u) * (14.4 * u * A * X + 8.2 * u * S + 105 * u ^ 2 * h * A ^ 2
        + (7.1 + 5.1 * h) * u * tiny) := le_mul_of_one_le_left hnew0 (by nlinarith)
  calc _ ≤ (1 + 3 * n * u) * (Ta + Tb) + (1 + 3 * n * u) * (14.4 * u * A * X + 8.2 * u * S
        + 105 * u ^ 2 * h * A ^ 2 + (7.1 + 5.1 * h) * u * tiny) := by linarith
    _ = (1 + 3 * n * u) * (Ta + Tb + (14.4 * u * A * X + 8.2 * u * S + 105 * u ^ 2 * h * A ^ 2
        + (7.1 + 5.1 * h) * u * tiny)) := by ring
    _ ≤ (1 + 3 * n * u) * Tn := by gcongr

/-- **The merged mean**: from a computed weighted mean within
`6 u (n_b A_a + n_a A_b) / n` of the children's, the merged mean is within
`6 u (A_a + A_b)` of the exact one. -/
theorem merge_mean {na nb ma mb Ma Mb Aa Ab mh : ℝ} (hna : 1 ≤ na) (hnb : 1 ≤ nb)
    (hAa : 0 ≤ Aa) (hAb : 0 ≤ Ab)
    (ha : |ma - Ma| ≤ 6 * u * Aa) (hb : |mb - Mb| ≤ 6 * u * Ab)
    (hm : |mh - (na * ma + nb * mb) / (na + nb)| ≤ 6 * u * (nb * Aa + na * Ab) / (na + nb)) :
    |mh - (na * Ma + nb * Mb) / (na + nb)| ≤ 6 * u * (Aa + Ab) := by
  have hu := u_pos
  have hn0 : 0 < na + nb := by linarith
  have h1 : |(na * ma + nb * mb) / (na + nb) - (na * Ma + nb * Mb) / (na + nb)|
      ≤ (na * (6 * u * Aa) + nb * (6 * u * Ab)) / (na + nb) := by
    rw [← sub_div, abs_div, abs_of_pos hn0]
    apply div_le_div_of_nonneg_right _ hn0.le
    have e : na * ma + nb * mb - (na * Ma + nb * Mb) = na * (ma - Ma) + nb * (mb - Mb) := by ring
    rw [e]
    have := abs_add_le (na * (ma - Ma)) (nb * (mb - Mb))
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < na),
      abs_of_pos (by linarith : (0 : ℝ) < nb)] at this
    have := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ na)
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ nb)
    linarith
  have e : mh - (na * Ma + nb * Mb) / (na + nb)
      = (mh - (na * ma + nb * mb) / (na + nb))
        + ((na * ma + nb * mb) / (na + nb) - (na * Ma + nb * Mb) / (na + nb)) := by ring
  rw [e]
  refine le_trans (abs_add_le _ _) ?_
  have h2 : 6 * u * (nb * Aa + na * Ab) / (na + nb) + (na * (6 * u * Aa) + nb * (6 * u * Ab)) / (na + nb)
      ≤ 6 * u * (Aa + Ab) := by
    rw [← add_div, div_le_iff₀ hn0]
    have : 0 ≤ u * (nb * Aa + na * Ab) := by positivity
    nlinarith
  linarith

/-! ## DuckDB's merge -/

variable (M : StdModel)

theorem u_pows : (1 + u) ^ 4 ≤ 1 + 4.01 * u ∧ 1 - 4 * u ≤ (1 - u) ^ 4 ∧ (1 + u) ^ 3 ≤ 1.01 ∧
    (1 + u) ^ 2 ≤ 1.01 := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have h2 : u ^ 2 ≤ u / 2 ^ 53 := by nlinarith
  have h3 : u ^ 3 ≤ u / 2 ^ 53 := by nlinarith
  have h4 : u ^ 4 ≤ u / 2 ^ 53 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- One rounding of a value `z ≥ 0`: between `(1 − u) z − u·tiny` and
`(1 + u) z + u·tiny`, and `≥ 0`. -/
theorem StdModel.rnd_nonneg {z : ℝ} (hz : 0 ≤ z) (hb : z ≤ maxFinite) :
    0 ≤ M.fl z ∧ M.fl z ≤ (1 + u) * z + u * tiny ∧ (1 - u) * z - u * tiny ≤ M.fl z := by
  have h := abs_le.mp (M.err z (by rwa [abs_of_nonneg hz]))
  rw [abs_of_nonneg hz] at h
  exact ⟨M.nonneg _ hz, by linarith [h.2], by linarith [h.1]⟩

set_option maxHeartbeats 800000 in
/-- DuckDB's `T = Δ · Δ · n_s · n_t / n`, each operation rounded: within
`5 u (Δ² h + (1 + h) tiny)` of `Δ² h`, `h = n_s n_t / n`. -/
theorem StdModel.T_chain {D : ℝ} {ns nt : ℕ} (hs : 1 ≤ ns) (ht1 : 1 ≤ nt)
    (hn : ns + nt ≤ 2 ^ 32) (hD : |D| ≤ 2 ^ 420) :
    |M.fl (M.fl (M.fl (M.fl (D * D) * ns) * nt) / ((ns : ℝ) + nt))
        - D ^ 2 * ((ns : ℝ) * nt / ((ns : ℝ) + nt))|
      ≤ 5 * u * (D ^ 2 * ((ns : ℝ) * nt / ((ns : ℝ) + nt))
        + (1 + (ns : ℝ) * nt / ((ns : ℝ) + nt)) * tiny) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hsr : (1 : ℝ) ≤ ns := by exact_mod_cast hs
  have htr : (1 : ℝ) ≤ nt := by exact_mod_cast ht1
  have hnr : (ns : ℝ) + nt ≤ 2 ^ 32 := by exact_mod_cast hn
  obtain ⟨n, hn'⟩ : ∃ n : ℝ, n = (ns : ℝ) + nt := ⟨_, rfl⟩
  rw [← hn']
  have hn0 : 0 < n := by linarith
  obtain ⟨P, hP⟩ : ∃ P, P = D ^ 2 := ⟨_, rfl⟩
  rw [← hP, show D * D = P by rw [hP]; ring]
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hPb : P ≤ 2 ^ 840 := by
    rw [hP, ← sq_abs]; calc |D| ^ 2 ≤ (2 ^ 420) ^ 2 := by gcongr
      _ = 2 ^ 840 := by norm_num
  have hut : u * tiny ≤ 1 := le_trans (mul_le_mul hu' (by unfold tiny; norm_num : tiny ≤ 1)
    ht.le (by norm_num)) (by norm_num)
  have hu1 : u ≤ 1 / 2 := by linarith
  -- the four roundings
  obtain ⟨q10, q1u, q1l⟩ := M.rnd_nonneg hP0 (by linarith)
  set q1 := M.fl P
  have huP : u * P ≤ P := by have := mul_le_mul_of_nonneg_right hu1 hP0; linarith
  have hq1 : q1 ≤ 2 ^ 842 := by linarith
  have hq1b : q1 * ns ≤ 2 ^ 900 := by
    have := mul_le_mul hq1 (by linarith : (ns : ℝ) ≤ 2 ^ 32) (by positivity) (by norm_num)
    linarith
  obtain ⟨q20, q2u, q2l⟩ := M.rnd_nonneg (by positivity : 0 ≤ q1 * ns) (by linarith)
  set q2 := M.fl (q1 * ns)
  have hq2 : q2 ≤ 2 ^ 902 := by
    have := mul_le_mul_of_nonneg_right hu1 (by positivity : 0 ≤ q1 * ns); linarith
  have hq2b : q2 * nt ≤ 2 ^ 950 := by
    have := mul_le_mul hq2 (by linarith : (nt : ℝ) ≤ 2 ^ 32) (by positivity) (by norm_num)
    linarith
  obtain ⟨q30, q3u, q3l⟩ := M.rnd_nonneg (by positivity : 0 ≤ q2 * nt) (by linarith)
  set q3 := M.fl (q2 * nt)
  have hq3 : q3 ≤ 2 ^ 952 := by
    have := mul_le_mul_of_nonneg_right hu1 (by positivity : 0 ≤ q2 * nt); linarith
  have hq3b : q3 / n ≤ 2 ^ 960 := by
    calc q3 / n ≤ q3 := div_le_self q30 (by linarith)
      _ ≤ _ := by linarith
  obtain ⟨-, q4u, q4l⟩ := M.rnd_nonneg (by positivity : 0 ≤ q3 / n) (by linarith)
  -- `h`, `nt / n`, `1 / n`
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (ns : ℝ) * nt / n := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (nt : ℝ) / n := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 1 / n := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have ha1 : a ≤ 1 := by rw [hadef, div_le_one hn0]; linarith
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hb1 : b ≤ 1 := by rw [hbdef, div_le_one hn0]; linarith
  have eh : (ns : ℝ) * nt * b = h := by rw [hbdef, hh]; ring
  have ea : (nt : ℝ) * b = a := by rw [hadef, hbdef]; ring
  have e3 : q3 / n = q3 * b := by rw [hbdef]; ring
  rw [e3] at q4u q4l ⊢
  -- upper: `T ≤ (1+u)⁴ P h + u t ((1+u)³ h + (1+u)² a + (1+u) b + 1)`
  have up : M.fl (q3 * b) ≤ (1 + u) ^ 4 * (P * h)
      + u * tiny * ((1 + u) ^ 3 * h + (1 + u) ^ 2 * a + (1 + u) * b + 1) := by
    have s2 : q2 ≤ (1 + u) * (((1 + u) * P + u * tiny) * ns) + u * tiny := by
      have := mul_le_mul_of_nonneg_right q1u (by positivity : (0 : ℝ) ≤ ns)
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + u); linarith
    have s3 : q3 ≤ (1 + u) * (((1 + u) * (((1 + u) * P + u * tiny) * ns) + u * tiny) * nt)
        + u * tiny := by
      have := mul_le_mul_of_nonneg_right s2 (by positivity : (0 : ℝ) ≤ nt)
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + u); linarith
    have s4 : M.fl (q3 * b) ≤ (1 + u) * (((1 + u) * (((1 + u) * (((1 + u) * P + u * tiny) * ns)
        + u * tiny) * nt) + u * tiny) * b) + u * tiny := by
      have := mul_le_mul_of_nonneg_right s3 hb0
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + u); linarith
    have e : (1 + u) * (((1 + u) * (((1 + u) * (((1 + u) * P + u * tiny) * ns) + u * tiny) * nt)
        + u * tiny) * b) + u * tiny = (1 + u) ^ 4 * (P * ((ns : ℝ) * nt * b))
        + u * tiny * ((1 + u) ^ 3 * ((ns : ℝ) * nt * b) + (1 + u) ^ 2 * ((nt : ℝ) * b)
          + (1 + u) * b + 1) := by ring
    rw [e, eh, ea] at s4; exact s4
  -- lower: `T ≥ (1−u)⁴ P h − u t ((1+u)³ h + (1+u)² a + (1+u) b + 1)`
  have lo : (1 - u) ^ 4 * (P * h) - u * tiny * ((1 + u) ^ 3 * h + (1 + u) ^ 2 * a + (1 + u) * b + 1)
      ≤ M.fl (q3 * b) := by
    have hu0 : 0 ≤ 1 - u := by linarith
    have s2 : (1 - u) * (((1 - u) * P - u * tiny) * ns) - u * tiny ≤ q2 := by
      have := mul_le_mul_of_nonneg_right q1l (by positivity : (0 : ℝ) ≤ ns)
      have := mul_le_mul_of_nonneg_left this hu0; linarith
    have s3 : (1 - u) * (((1 - u) * (((1 - u) * P - u * tiny) * ns) - u * tiny) * nt) - u * tiny
        ≤ q3 := by
      have := mul_le_mul_of_nonneg_right s2 (by positivity : (0 : ℝ) ≤ nt)
      have := mul_le_mul_of_nonneg_left this hu0; linarith
    have s4 : (1 - u) * (((1 - u) * (((1 - u) * (((1 - u) * P - u * tiny) * ns) - u * tiny) * nt)
        - u * tiny) * b) - u * tiny ≤ M.fl (q3 * b) := by
      have := mul_le_mul_of_nonneg_right s3 hb0
      have := mul_le_mul_of_nonneg_left this hu0; linarith
    have e : (1 - u) * (((1 - u) * (((1 - u) * (((1 - u) * P - u * tiny) * ns) - u * tiny) * nt)
        - u * tiny) * b) - u * tiny = (1 - u) ^ 4 * (P * ((ns : ℝ) * nt * b))
        - u * tiny * ((1 - u) ^ 3 * ((ns : ℝ) * nt * b) + (1 - u) ^ 2 * ((nt : ℝ) * b)
          + (1 - u) * b + 1) := by ring
    rw [e, eh, ea] at s4
    have c : u * tiny * ((1 - u) ^ 3 * h + (1 - u) ^ 2 * a + (1 - u) * b + 1)
        ≤ u * tiny * ((1 + u) ^ 3 * h + (1 + u) ^ 2 * a + (1 + u) * b + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have c1 : (1 - u) ^ 3 ≤ (1 + u) ^ 3 := by gcongr; linarith
      have c2 : (1 - u) ^ 2 ≤ (1 + u) ^ 2 := by gcongr; linarith
      have := mul_le_mul_of_nonneg_right c1 hh0
      have := mul_le_mul_of_nonneg_right c2 ha0
      have := mul_le_mul_of_nonneg_right (by linarith : 1 - u ≤ 1 + u) hb0
      linarith
    linarith
  -- the constants
  obtain ⟨f4, g4, f3, f2⟩ := u_pows
  have hPh : 0 ≤ P * h := by positivity
  have k1 : (1 + u) ^ 4 * (P * h) ≤ P * h + 4.01 * u * (P * h) := by
    have := mul_le_mul_of_nonneg_right f4 hPh; linarith
  have k2 : P * h - 4 * u * (P * h) ≤ (1 - u) ^ 4 * (P * h) := by
    have := mul_le_mul_of_nonneg_right g4 hPh; linarith
  have k3 : u * tiny * ((1 + u) ^ 3 * h + (1 + u) ^ 2 * a + (1 + u) * b + 1)
      ≤ u * tiny * (1.01 * h + 3.02) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_right f3 hh0
    have := mul_le_mul f2 ha1 ha0 (by norm_num)
    have := mul_le_mul (by linarith : 1 + u ≤ 1.01) hb1 hb0 (by norm_num)
    linarith
  have k4 : u * tiny * (1.01 * h + 3.02) ≤ 5 * u * ((1 + h) * tiny) := by
    have : 0 ≤ u * tiny := by positivity
    have := mul_le_mul_of_nonneg_left (by linarith : 1.01 * h + 3.02 ≤ 5 * (1 + h)) this
    linarith
  rw [abs_le]
  have p : 0 ≤ u * (P * h) := by positivity
  have e5 : 5 * u * (P * h + (1 + h) * tiny) = 5 * (u * (P * h)) + 5 * u * ((1 + h) * tiny) := by ring
  have e6 : 4.01 * u * (P * h) = 4.01 * (u * (P * h)) := by ring
  have e7 : 4 * u * (P * h) = 4 * (u * (P * h)) := by ring
  constructor <;> linarith

/-- `|r Δ̂ − w Δ|` from the errors of `r ≈ w` and `Δ̂ ≈ Δ`. -/
theorem fma_prod_err {r w Dh D : ℝ} (hw : 0 ≤ w) (ha : |r - w| ≤ 1.0001 * u * w)
    (eD : |Dh - D| ≤ u * (|D| + tiny)) :
    |r * Dh - w * D| ≤ 2.0002 * u * w * |D| + 1.0001 * u * w * tiny := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  obtain ⟨d, hd⟩ : ∃ d, d = |D| := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = |Dh - D| := ⟨_, rfl⟩
  rw [← hd]; rw [← hd, ← hb] at eD
  have hd0 : 0 ≤ d := by rw [hd]; exact abs_nonneg _
  have hb0 : 0 ≤ b := by rw [hb]; exact abs_nonneg _
  have hDh' : |Dh| ≤ d + b := by
    have := abs_sub_abs_le_abs_sub Dh D; rw [hd, hb]; linarith
  have e : r * Dh - w * D = (r - w) * Dh + w * (Dh - D) := by ring
  rw [e]
  have k1 := abs_add_le ((r - w) * Dh) (w * (Dh - D))
  rw [abs_mul, abs_mul, abs_of_nonneg hw, ← hb] at k1
  have k2 : |r - w| * |Dh| ≤ 1.0001 * u * w * (d + b) :=
    mul_le_mul ha hDh' (abs_nonneg _) (by positivity)
  have k3 : (1.0001 * u * w + w) * b ≤ (1.0001 * u * w + w) * (u * (d + tiny)) :=
    mul_le_mul_of_nonneg_left eD (by positivity)
  have k4 : 0 ≤ u * w * (d + tiny) := by positivity
  have k5 : (1.0001 * u) * (u * w * (d + tiny)) ≤ 0.0001 * (u * w * (d + tiny)) :=
    mul_le_mul_of_nonneg_right (by linarith) k4
  linarith

/-- The arithmetic at the end of `dmean_spec`. -/
theorem dmean_arith {ns nt n d E Y ms mt As At : ℝ} (hsr : 1 ≤ ns) (htr : 1 ≤ nt)
    (hn' : n = nt + ns) (hu1 : u ≤ 0.001)
    (k1 : E ≤ 2.03 * u * (ns * d) + u * Y + 2.03 * u * (n * tiny))
    (hY : Y ≤ nt * |mt| + ns * |ms|) (hd : d ≤ |ms| + |mt|)
    (hms : ns * |ms| ≤ 1.01 * As) (hmt : nt * |mt| ≤ 1.01 * At)
    (hAs : ns * tiny ≤ As) (hAt : nt * tiny ≤ At) :
    E ≤ 6 * u * (ns * At + nt * As) := by
  have hu := u_pos
  have ht := tiny_pos
  have hAs0 : 0 ≤ As := le_trans (by positivity) hAs
  have hAt0 : 0 ≤ At := le_trans (by positivity) hAt
  have m1 : ns * |mt| ≤ 1.01 * (ns * At) := by
    have : |mt| ≤ nt * |mt| := le_mul_of_one_le_left (abs_nonneg _) htr
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ ns)
    have := mul_le_mul_of_nonneg_left hmt (by linarith : (0 : ℝ) ≤ ns)
    linarith
  have m2 : As ≤ nt * As := le_mul_of_one_le_left hAs0 htr
  have m3 : At ≤ ns * At := le_mul_of_one_le_left hAt0 hsr
  have m4 : n * tiny ≤ As + At := by rw [hn']; linarith
  have m5 : ns * d ≤ ns * |ms| + ns * |mt| := by
    have := mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ ns); linarith
  have q1 := mul_le_mul_of_nonneg_left m5 hu.le
  have q2 := mul_le_mul_of_nonneg_left hY hu.le
  have q3 := mul_le_mul_of_nonneg_left m4 hu.le
  have q4 := mul_le_mul_of_nonneg_left hms hu.le
  have q5 := mul_le_mul_of_nonneg_left hmt hu.le
  have q6 := mul_le_mul_of_nonneg_left m1 hu.le
  have q7 := mul_le_mul_of_nonneg_left m2 hu.le
  have q8 := mul_le_mul_of_nonneg_left m3 hu.le
  have p1 : 0 ≤ u * (ns * At) := by positivity
  have p2 : 0 ≤ u * (nt * As) := by positivity
  linarith

/-- DuckDB's merged mean `fma(fl(n_s / n), fl(m_s − m_t), m_t)`, one rounding
for the fused multiply-add: within `6 u (n_s A_t + n_t A_s) / n` of the
children's weighted mean, when `n_x |m_x| ≤ 1.01 A_x` and `n_x tiny ≤ A_x`. -/
theorem StdModel.dmean_spec {ns nt : ℕ} (hs : 1 ≤ ns) (ht1 : 1 ≤ nt) (hn : ns + nt ≤ 2 ^ 32)
    {ms mt As At : ℝ} (hms : ns * |ms| ≤ 1.01 * As) (hmt : nt * |mt| ≤ 1.01 * At)
    (hAs : ns * tiny ≤ As) (hAt : nt * tiny ≤ At) (hbs : |ms| ≤ 2 ^ 401) (hbt : |mt| ≤ 2 ^ 401) :
    |M.fl (M.fl ((ns : ℝ) / ((nt : ℝ) + ns)) * M.fl (ms - mt) + mt)
        - ((nt : ℝ) * mt + ns * ms) / ((nt : ℝ) + ns)|
      ≤ 6 * u * ((ns : ℝ) * At + nt * As) / ((nt : ℝ) + ns) := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht' : tiny ≤ 1 / 2 ^ 1000 := by unfold tiny; norm_num
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  have hsr : (1 : ℝ) ≤ ns := by exact_mod_cast hs
  have htr : (1 : ℝ) ≤ nt := by exact_mod_cast ht1
  have hnr : (ns : ℝ) + nt ≤ 2 ^ 32 := by exact_mod_cast hn
  obtain ⟨n, hn'⟩ : ∃ n : ℝ, n = (nt : ℝ) + ns := ⟨_, rfl⟩
  rw [← hn']
  have hn0 : 0 < n := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (ns : ℝ) / n := ⟨_, rfl⟩
  rw [← hw]
  have hw1 : w ≤ 1 := by rw [hw, div_le_one hn0]; linarith
  have hwn : n * w = ns := by rw [hw]; field_simp
  have hw0 : 1 / 2 ^ 32 ≤ w := by
    rw [hw, le_div_iff₀ hn0]; linarith
  -- `fl(n_s / n)` and `fl(m_s − m_t)`
  obtain ⟨D, hD⟩ : ∃ D, D = ms - mt := ⟨_, rfl⟩
  rw [← hD]
  have hDb : |D| ≤ 2 ^ 402 := by
    rw [hD]; have := abs_sub ms mt; linarith
  have er := M.err w (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [abs_of_nonneg (by linarith : 0 ≤ w)] at er
  have eD := M.err D (by linarith)
  generalize M.fl w = r at er ⊢
  generalize M.fl D = Dh at eD ⊢
  have htw : u * tiny ≤ u * (0.0001 * w) := mul_le_mul_of_nonneg_left (by linarith) hu.le
  have ha : |r - w| ≤ 1.0001 * u * w := by linarith
  have E1 := fma_prod_err (by linarith) ha eD
  -- `y`, the exact weighted mean
  have hy : w * D + mt = ((nt : ℝ) * mt + ns * ms) / n := by
    rw [eq_div_iff hn0.ne', hD, hw, hn']; field_simp; ring
  rw [← hy]
  have hyb : n * |w * D + mt| ≤ nt * |mt| + ns * |ms| := by
    rw [hy, abs_div, abs_of_pos hn0, mul_div_cancel₀ _ hn0.ne']
    have := abs_add_le ((nt : ℝ) * mt) (ns * ms)
    rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast] at this; exact this
  have hz : |r * Dh + mt| ≤ |w * D + mt| + |r * Dh - w * D| := by
    have := abs_sub_abs_le_abs_sub (r * Dh + mt) (w * D + mt)
    have e : r * Dh + mt - (w * D + mt) = r * Dh - w * D := by ring
    rw [e] at this; linarith
  have hd0 : 0 ≤ |D| := abs_nonneg _
  have hzb : |r * Dh + mt| ≤ maxFinite := by
    have : |w * D + mt| ≤ 2 ^ 404 := by
      have := abs_add_le (w * D) mt
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ w)] at this
      have := mul_le_mul hw1 hDb hd0 (by norm_num); linarith
    have : u * w * |D| ≤ 1 / 2 ^ 53 * 1 * 2 ^ 402 :=
      mul_le_mul (mul_le_mul hu' hw1 (by linarith) (by positivity)) hDb hd0 (by positivity)
    have : u * w * tiny ≤ 1 / 2 ^ 53 * 1 * (1 / 2 ^ 1000) :=
      mul_le_mul (mul_le_mul hu' hw1 (by linarith) (by positivity)) ht' ht.le (by positivity)
    have : |r * Dh - w * D| ≤ 2 ^ 351 := by
      have c : (2.0002 : ℝ) * (1 / 2 ^ 53 * 1 * 2 ^ 402) + 1.0001 * (1 / 2 ^ 53 * 1 * (1 / 2 ^ 1000))
          ≤ 2 ^ 351 := by norm_num
      linarith
    linarith
  have ef := M.err (r * Dh + mt) hzb
  generalize M.fl (r * Dh + mt) = mh at ef ⊢
  -- the final error, times `n`
  have hfin : |mh - (w * D + mt)|
      ≤ (1 + u) * (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + u * |w * D + mt| + u * tiny := by
    have e : mh - (w * D + mt) = (mh - (r * Dh + mt)) + (r * Dh - w * D) := by ring
    rw [e]
    have := abs_add_le (mh - (r * Dh + mt)) (r * Dh - w * D)
    have := mul_le_mul_of_nonneg_left hz hu.le
    have := mul_le_mul_of_nonneg_left E1 hu.le
    linarith
  rw [le_div_iff₀ hn0, mul_comm]
  have k1 : n * |mh - (w * D + mt)|
      ≤ 2.03 * u * (ns * |D|) + u * (n * |w * D + mt|) + 2.03 * u * (n * tiny) := by
    have h1 := mul_le_mul_of_nonneg_left hfin hn0.le
    have h2 : n * ((1 + u) * (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + u * |w * D + mt|
        + u * tiny) = (1 + u) * (2.0002 * u * (n * w) * |D| + 1.0001 * u * (n * w) * tiny)
          + u * (n * |w * D + mt|) + u * (n * tiny) := by ring
    rw [h2, hwn] at h1
    have p1 : 0 ≤ u * (ns * |D|) := by positivity
    have p2 : 0 ≤ u * (ns * tiny) := by positivity
    have h3 : u * (u * (ns * |D|)) ≤ 0.001 * (u * (ns * |D|)) :=
      mul_le_mul_of_nonneg_right (by linarith) p1
    have h4 : u * (u * (ns * tiny)) ≤ 0.001 * (u * (ns * tiny)) :=
      mul_le_mul_of_nonneg_right (by linarith) p2
    have h5 : u * (ns * tiny) ≤ u * (n * tiny) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact mul_le_mul_of_nonneg_right (by linarith) ht.le
    linarith
  exact dmean_arith hsr htr hn' (by linarith) k1 hyb (by rw [hD]; exact abs_sub _ _) hms hmt hAs hAt

/-! ## The tree of updates and merges -/

/-- The facts about the values a bound needs: for `n ≤ 2³²` values at most
`2³⁹⁹` in magnitude. -/
theorem list_facts {xs : List ℝ} (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32)
    (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) :
    0 ≤ mag xs ∧ mag xs ≤ 2 ^ 432 ∧ xs.length * tiny ≤ mag xs ∧
      |mx (dupL xs)| * xs.length ≤ mag xs ∧ |mx (dupL xs)| ≤ 2 ^ 400 ∧
      0 ≤ comoment (dupL xs) ∧ comoment (dupL xs) ≤ 2 ^ 830 := by
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hK1 : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hK : (xs.length : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hmag := mag_le_of_bound hB
  have hm := abs_mx_dupL xs
  refine ⟨mag_nonneg xs, ?_, length_mul_tiny_le_mag xs, hm, ?_, comoment_dupL_nonneg xs, ?_⟩
  · have : (xs.length : ℝ) * (2 ^ 399 + tiny) ≤ 2 ^ 32 * (2 ^ 399 + 1) :=
      mul_le_mul hK (by linarith) (by positivity) (by norm_num)
    linarith
  · have h1 : |mx (dupL xs)| * xs.length ≤ xs.length * (2 ^ 399 + tiny) := le_trans hm hmag
    have h2 : |mx (dupL xs)| ≤ 2 ^ 399 + tiny := by
      rw [mul_comm] at h1; exact le_of_mul_le_mul_left h1 (by linarith)
    linarith
  · have h1 := comoment_dupL_le xs
    have h2 := abs_sum_le_of_bound (B := 2 ^ 798) (xs := xs.map (· ^ 2)) (by
      intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      rw [abs_of_nonneg (sq_nonneg z)]
      calc z ^ 2 = |z| ^ 2 := (sq_abs z).symm
        _ ≤ (2 ^ 399) ^ 2 := by gcongr; exact hB z hz
        _ = 2 ^ 798 := by norm_num)
    simp only [List.length_map] at h2
    have h3 := le_abs_self (xs.map (· ^ 2)).sum
    have : (xs.length : ℝ) * 2 ^ 798 ≤ 2 ^ 32 * 2 ^ 798 := by gcongr
    linarith

/-- The bound of the tree invariant, `(1 + 3nu)(17 u A D + 9 u n S + 60 u² L A² + 12 u tiny L)`. -/
noncomputable def tBound (n A Ds S L : ℝ) : ℝ :=
  (1 + 3 * n * u) * (17 * u * A * Ds + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * tiny * L)

theorem tBound_le {K A Ds S L : ℝ} (hK1 : 1 ≤ K) (hK : K ≤ 2 ^ 32) (hA0 : 0 ≤ A)
    (hA : A ≤ 2 ^ 432) (hDs0 : 0 ≤ Ds) (hDs : Ds ≤ 2 ^ 436) (hS0 : 0 ≤ S) (hS : S ≤ 2 ^ 830)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 ^ 39) : tBound K A Ds S L ≤ 2 ^ 900 := by
  unfold tBound
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht1 : tiny ≤ 1 := by unfold tiny; norm_num
  have hKu : K * u ≤ 1 / 2 ^ 21 := by
    calc K * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  have hLu : L * u ≤ 1 / 2 ^ 14 := by
    calc L * u ≤ 2 ^ 39 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 14 := by norm_num
  have c0 : 1 + 3 * K * u ≤ 2 := by linarith
  have hAD : A * Ds ≤ 2 ^ 868 := by
    have := mul_le_mul hA hDs hDs0 (by norm_num); norm_num at this ⊢; linarith
  have c1 : 17 * u * A * Ds ≤ 2 ^ 868 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : 17 * u ≤ 1) (by positivity : 0 ≤ A * Ds)
    linarith
  have c2 : 9 * u * K * S ≤ 2 ^ 830 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : 9 * (K * u) ≤ 1) hS0; linarith
  have hA2 : A ^ 2 ≤ 2 ^ 864 := by
    calc A ^ 2 ≤ (2 ^ 432) ^ 2 := by gcongr
      _ = 2 ^ 864 := by norm_num
  have c3 : 60 * u ^ 2 * L * A ^ 2 ≤ 2 ^ 864 := by
    have h1 : 60 * u ^ 2 * L ≤ 1 := by
      have : u * (L * u) ≤ 1 / 2 ^ 53 * (1 / 2 ^ 14) := mul_le_mul hu' hLu (by positivity) (by norm_num)
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg A); linarith
  have c4 : 12 * u * tiny * L ≤ 1 := by
    have := mul_le_mul hLu ht1 ht.le (by norm_num); nlinarith
  have hsum : 17 * u * A * Ds + 9 * u * K * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * tiny * L
      ≤ 2 ^ 870 := by linarith
  have h0 : 0 ≤ 17 * u * A * Ds + 9 * u * K * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * tiny * L := by
    positivity
  have := mul_le_mul c0 hsum h0 (by norm_num)
  linarith

/-- `Ds ≤ 2⁴³⁶` from `Ds² ≤ L S`. -/
theorem Ds_le {Ds L S : ℝ} (hDs0 : 0 ≤ Ds) (hS0 : 0 ≤ S) (hL : L ≤ 2 ^ 39) (hS : S ≤ 2 ^ 830)
    (h : Ds ^ 2 ≤ L * S) : Ds ≤ 2 ^ 436 := by
  have h1 : L * S ≤ 2 ^ 39 * 2 ^ 830 := by
    rcases le_total 0 L with hL0 | hL0
    · exact mul_le_mul hL hS hS0 (by norm_num)
    · have : L * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL0 hS0
      have : (0 : ℝ) ≤ 2 ^ 39 * 2 ^ 830 := by positivity
      linarith
  have h2 : Ds ^ 2 ≤ (2 ^ 436) ^ 2 := by
    have : (2 : ℝ) ^ 39 * 2 ^ 830 ≤ (2 ^ 436) ^ 2 := by norm_num
    linarith
  nlinarith [h2]

/-- Cauchy–Schwarz for three terms: `(a + b + c)² ≤ (p + q + r)(x + y + z)` when
`a² ≤ p x`, `b² ≤ q y`, `c² ≤ r z`. -/
theorem cs3 {a b c p q r x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : a ^ 2 ≤ p * x) (h2 : b ^ 2 ≤ q * y) (h3 : c ^ 2 ≤ r * z) :
    (a + b + c) ^ 2 ≤ (p + q + r) * (x + y + z) := by
  -- `2 a b ≤ p y + q x` from `(a b)² ≤ (p y)(q x)`
  have k : ∀ {a b p q x y : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ p → 0 ≤ q → 0 ≤ x → 0 ≤ y →
      a ^ 2 ≤ p * x → b ^ 2 ≤ q * y → 2 * (a * b) ≤ p * y + q * x := by
    intro a b p q x y ha hb hp hq hx hy h1 h2
    have e1 : (a * b) ^ 2 ≤ (p * y) * (q * x) := by
      have := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      nlinarith
    have e2 : 0 ≤ p * y := by positivity
    have e3 : 0 ≤ q * x := by positivity
    nlinarith [sq_nonneg (p * y - q * x), sq_nonneg (a * b), mul_nonneg ha hb]
  have k1 := k ha hb hp hq hx hy h1 h2
  have k2 := k ha hc hp hr hx hz h1 h3
  have k3 := k hb hc hq hr hy hz h2 h3
  nlinarith

/-- The invariant of a tree of Welford updates and Chan merges over `xs`:
the mean within `6 u A`, and the co-moment within `tBound`, where
`(Σ|D|)² ≤ L(n) S`. -/
def TInv (xs : List ℝ) (s : ℕ × ℝ × ℝ) : Prop :=
  s.1 = xs.length ∧ |s.2.1 - mx (dupL xs)| ≤ 6 * u * mag xs ∧
    ∃ Ds : ℝ, 0 ≤ Ds ∧ Ds ^ 2 ≤ Lw xs.length * comoment (dupL xs) ∧
      |s.2.2 - comoment (dupL xs)|
        ≤ tBound xs.length (mag xs) Ds (comoment (dupL xs)) (Lw xs.length)

theorem Lw_two (n : ℕ) : 2 * (n : ℝ) ≤ Lw n := by
  unfold Lw
  have : (0 : ℝ) ≤ Nat.clog 2 n := by positivity
  have : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- A thread's state, from Welford's updates, meets the tree invariant. -/
theorem tInv_of_wInv {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : WInv xs s) : TInv xs s := by
  obtain ⟨hn, hm, Ds, hDs0, hDs, hC⟩ := h
  refine ⟨hn, hm, Ds, hDs0, ?_, le_trans hC ?_⟩
  · have := (Lw_ge xs.length).1
    have := comoment_dupL_nonneg xs
    nlinarith
  · unfold tBound
    have hu := u_pos
    have ht := tiny_pos
    have h2 := Lw_two xs.length
    have hS := comoment_dupL_nonneg xs
    have hA := mag_nonneg xs
    have hn0 : (0 : ℝ) ≤ xs.length := by positivity
    have a1 : 1 + 2 * (xs.length : ℝ) * u ≤ 1 + 3 * xs.length * u := by nlinarith
    have a2 : 17 * u * mag xs * Ds + 7 * u * xs.length * comoment (dupL xs)
        + 103 * u ^ 2 * xs.length * mag xs ^ 2 + 3 * xs.length * u * tiny
        ≤ 17 * u * mag xs * Ds + 9 * u * xs.length * comoment (dupL xs)
          + 60 * u ^ 2 * Lw xs.length * mag xs ^ 2 + 12 * u * tiny * Lw xs.length := by
      have p1 : 0 ≤ u * xs.length * comoment (dupL xs) := by positivity
      have p2 : 103 * u ^ 2 * xs.length * mag xs ^ 2 ≤ 60 * u ^ 2 * Lw xs.length * mag xs ^ 2 := by
        have : 0 ≤ u ^ 2 * mag xs ^ 2 := by positivity
        nlinarith
      have p3 : 3 * xs.length * u * tiny ≤ 12 * u * tiny * Lw xs.length := by
        have : 0 ≤ u * tiny := by positivity
        nlinarith
      linarith
    exact mul_le_mul a1 a2 (by positivity) (by positivity)

/-- **One merge keeps the co-moment's bound**: the error terms of a merge
(`delta_err`, `sq_err`, `T_err`, `merge_com`) folded into the tree bound
(`merge_fold`). -/
theorem merge_step_arith {na nb m h Aa Ab Da Db Sa Sb La Lb L Ma Mb ma mb Dh T Sha Shb Sh1 Sh : ℝ}
    (hna : 1 ≤ na) (hnb : 1 ≤ nb) (hm1 : 1 ≤ m) (hma : m ≤ na) (hmb : m ≤ nb) (hh : 0 ≤ h)
    (hhm : h ≤ m) (hn : (na + nb) * u ≤ 1 / 2 ^ 21) (hAa : 0 ≤ Aa) (hAb : 0 ≤ Ab)
    (htA : tiny ≤ Aa + Ab) (hMa : |Ma| ≤ Aa) (hMb : |Mb| ≤ Ab)
    (ea : |ma - Ma| ≤ 6 * u * Aa) (eb : |mb - Mb| ≤ 6 * u * Ab)
    (eD : |Dh - (mb - ma)| ≤ u * (|mb - ma| + tiny))
    (eT : |T - Dh ^ 2 * h| ≤ 5 * u * (Dh ^ 2 * h + (1 + h) * tiny))
    (hDa : 0 ≤ Da) (hDb : 0 ≤ Db) (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb) (hLa : 0 ≤ La) (hLb : 0 ≤ Lb)
    (hL : La + Lb + 2 * m ≤ L)
    (hEa : |Sha - Sa| ≤ tBound na Aa Da Sa La) (hEb : |Shb - Sb| ≤ tBound nb Ab Db Sb Lb)
    (h1 : |Sh1 - (Sha + Shb)| ≤ u * (|Sha + Shb| + tiny))
    (h2 : |Sh - (Sh1 + T)| ≤ u * (|Sh1 + T| + tiny)) :
    |Sh - (Sa + Sb + (Mb - Ma) ^ 2 * h)|
      ≤ tBound (na + nb) (Aa + Ab) (Da + Db + h * |Mb - Ma|) (Sa + Sb + (Mb - Ma) ^ 2 * h) L := by
  have hA0 : 0 ≤ Aa + Ab := by positivity
  have hΔA : |Mb - Ma| ≤ Aa + Ab := by have := abs_sub Mb Ma; linarith
  have h1' : |(mb - ma) - (Mb - Ma)| ≤ 6 * u * (Aa + Ab) := by
    have e : (mb - ma) - (Mb - Ma) = (mb - Mb) - (ma - Ma) := by ring
    rw [e]; have := abs_sub (mb - Mb) (ma - Ma); linarith
  have hd := delta_err htA h1' eD
  have hs := sq_err hh hA0 hΔA hd
  have hQ : |Dh ^ 2 * h - (Mb - Ma) ^ 2 * h| ≤ 14.2 * u * (Aa + Ab) * (h * |Mb - Ma|)
      + 2 * u * ((Mb - Ma) ^ 2 * h) + 103 * u ^ 2 * h * (Aa + Ab) ^ 2 := by
    have e : Dh ^ 2 * h - (Mb - Ma) ^ 2 * h = h * (Dh ^ 2 - (Mb - Ma) ^ 2) := by ring
    rw [e, abs_mul, abs_of_nonneg hh]; exact hs
  have hX : 0 ≤ h * |Mb - Ma| := by positivity
  have hT := T_err hX (by positivity) hh hA0 hQ eT
  have hc := merge_com hSa hSb (by positivity : 0 ≤ (Mb - Ma) ^ 2 * h) hX hA0 hh hEa hEb hT h1 h2
  refine le_trans hc ?_
  unfold tBound at hEa hEb ⊢
  have hf := merge_fold hna hnb hm1 hma hmb hh hhm hn hAa hAb hDa hDb hX hSa hSb
    (by positivity : 0 ≤ (Mb - Ma) ^ 2 * h) hLa hLb hL le_rfl le_rfl
  have e : tBound na Aa Da Sa La = (1 + 3 * na * u) * (17 * u * Aa * Da + 9 * u * na * Sa
      + 60 * u ^ 2 * La * Aa ^ 2 + 12 * u * tiny * La) := rfl
  have e' : tBound nb Ab Db Sb Lb = (1 + 3 * nb * u) * (17 * u * Ab * Db + 9 * u * nb * Sb
      + 60 * u ^ 2 * Lb * Ab ^ 2 + 12 * u * tiny * Lb) := rfl
  rw [← e, ← e'] at hf
  exact hf

end FloatBounds

end
