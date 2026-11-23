module

public import FloatBounds.CovRel
public import FloatBounds.CovTwoPass
public import FloatBounds.SchubertGertz

/-!
# Polars's covariance: Schubert and Gertz's merge of pairs (#1808, ruling 271)

Polars's `CovState::combine` (`crates/polars-compute/src/moment.rs`, py-2.1.0)
merges the state `s` of `n_b` pairs into `t` of `n_a`: the means move by
`fl(Δ̂ · fl(n_b / n))` (`sgMean`, as for one variable), and the co-moment
takes `fl(n_b · fl(m_bx − m̂_x)) · Δ̂_y`. `insert_one` is the merge with a state
of one pair, so a grouped run is a tree of these merges too.

`sgCov_spec`: the merge meets `CMergeSpec` at `CConst.sg`. The means are the
variance's (`sgMerge_spec`). The increment is the variance's with `Δ̂_y` in
place of the second `Δ̂` (`sg_T2`), and its error in the exact `h Δx Δy`
(`h = n_a n_b / n`) takes `ad = 13` in place of Chan's 8.5: the cancellation
`m_b − m̂` costs `1.03 u A_x h |Δy|`, and the absolute underflow terms of its
roundings, `n_b · tiny ≤ h A`, about `5 u A_x h |Δy|` more.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- Schubert and Gertz's constants: `13` for both of the bound's `A · D` and
the merge's `A · h|Δ|` (ruling 271). -/
def CConst.sg : CConst := ⟨13, 13, by norm_num, by norm_num, by norm_num⟩

/-- Polars's merge of the pairs' state `s` into `t` (`CovState::combine`):
`fl(m_t + fl(fl(m_s − m_t) · fl(n_s / n)))` for each mean, and
`fl(Ĉ_t + fl(Ĉ_s + fl(fl(n_s · fl(m_sx − m̂_x)) · fl(m_sy − m_ty))))`. With no
pairs on one side the state is the other's. -/
noncomputable def StdModel.sgCov (t s : WState) : WState :=
  if s.n = 0 then t else if t.n = 0 then s else
    ⟨t.n + s.n, M.sgMean (t.n, t.mx, 0) (s.n, s.mx, 0), M.sgMean (t.n, t.my, 0) (s.n, s.my, 0),
      M.fl (t.c + M.fl (s.c + M.fl (M.fl ((s.n : ℝ) * M.fl (s.mx - M.sgMean (t.n, t.mx, 0) (s.n, s.mx, 0)))
        * M.fl (s.my - t.my))))⟩

/-- The increment `T̂ = fl(fl(n_b q̂) Δ̂_y)`, `q̂ = fl(m_b − m̂)`, against
`Δ̂_x Δ̂_y n_b v`, from the deviation's error `E_q` (`sg_T` with two
differences). -/
theorem sg_T2 {mb m' q r T Dx Dy v nb Eq : ℝ} (hnb : 1 ≤ nb) (hv0 : 0 ≤ v) (hEq0 : 0 ≤ Eq)
    (hd : |(mb - m') - Dx * v| ≤ Eq)
    (e4 : |q - (mb - m')| ≤ u * (|mb - m'| + tiny))
    (e5 : |r - nb * q| ≤ u * (|nb * q| + tiny))
    (e6 : |T - r * Dy| ≤ u * (|r * Dy| + tiny)) :
    |T - Dx * Dy * (nb * v)| ≤ 1.01 * (nb * |Dy| * Eq) + 3.02 * u * (|Dx| * |Dy| * (nb * v))
      + 1.01 * u * (|Dy| * tiny * (nb + 1)) + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  set a := |Dx| with ha_def
  set b := |Dy| with hb_def
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hnb0 : 0 ≤ nb := by linarith
  have hDv : |Dx * v| = a * v := by rw [abs_mul, abs_of_nonneg hv0]
  have hm : |mb - m'| ≤ a * v + Eq := by
    have := abs_sub_abs_le_abs_sub (mb - m') (Dx * v); rw [hDv] at this; linarith
  set Q1 := (1 + u) * Eq + u * (a * v) + u * tiny with hQ1
  have hq : |q - Dx * v| ≤ Q1 := by
    have e : q - Dx * v = (q - (mb - m')) + ((mb - m') - Dx * v) := by ring
    rw [e]
    have := abs_add_le (q - (mb - m')) ((mb - m') - Dx * v)
    have := mul_le_mul_of_nonneg_left hm hu.le
    linarith
  have hnq : |nb * q| ≤ nb * (a * v) + nb * Q1 := by
    rw [abs_mul, abs_of_nonneg hnb0]
    have : |q| ≤ a * v + Q1 := by
      have := abs_sub_abs_le_abs_sub q (Dx * v); rw [hDv] at this; linarith
    have := mul_le_mul_of_nonneg_left this hnb0; linarith
  have hnv : 0 ≤ nb * v := mul_nonneg hnb0 hv0
  set R1 := (1 + u) * (nb * Q1) + u * (a * (nb * v)) + u * tiny with hR1
  have hr : |r - Dx * (nb * v)| ≤ R1 := by
    have e : r - Dx * (nb * v) = (r - nb * q) + nb * (q - Dx * v) := by ring
    rw [e]
    have := abs_add_le (r - nb * q) (nb * (q - Dx * v))
    have h3 : |nb * (q - Dx * v)| = nb * |q - Dx * v| := by rw [abs_mul, abs_of_nonneg hnb0]
    have := mul_le_mul_of_nonneg_left hq hnb0
    have := mul_le_mul_of_nonneg_left hnq hu.le
    linarith
  have hrD : |r * Dy| ≤ (a * (nb * v) + R1) * b := by
    rw [abs_mul]
    have : |r| ≤ a * (nb * v) + R1 := by
      have := abs_sub_abs_le_abs_sub r (Dx * (nb * v))
      rw [abs_mul Dx, abs_of_nonneg hnv] at this; linarith
    exact mul_le_mul_of_nonneg_right this hb
  have hT : |T - Dx * Dy * (nb * v)| ≤ (1 + u) * (b * R1) + u * (a * b * (nb * v)) + u * tiny := by
    have e : T - Dx * Dy * (nb * v) = (T - r * Dy) + Dy * (r - Dx * (nb * v)) := by ring
    rw [e]
    have := abs_add_le (T - r * Dy) (Dy * (r - Dx * (nb * v)))
    have h3 : |Dy * (r - Dx * (nb * v))| ≤ b * R1 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr hb
    have := mul_le_mul_of_nonneg_left hrD hu.le
    have e2 : u * ((a * (nb * v) + R1) * b) = u * (a * b * (nb * v)) + u * (b * R1) := by ring
    linarith
  refine le_trans hT ?_
  have E : (1 + u) * (b * R1) + u * (a * b * (nb * v)) + u * tiny
      = (1 + u) ^ 3 * (nb * b * Eq) + ((1 + u) ^ 2 + (1 + u) + 1) * (u * (a * b * (nb * v)))
        + (1 + u) ^ 2 * (u * (b * tiny * nb)) + (1 + u) * (u * (b * tiny)) + u * tiny := by
    simp only [hR1, hQ1]; ring
  rw [E]
  obtain ⟨-, -, f3, f2⟩ := u_pows
  have p1 : 0 ≤ nb * b * Eq := mul_nonneg (mul_nonneg hnb0 hb) hEq0
  have p2 : 0 ≤ u * (a * b * (nb * v)) := mul_nonneg hu.le (mul_nonneg (mul_nonneg ha hb) hnv)
  have p3 : 0 ≤ u * (b * tiny * nb) := mul_nonneg hu.le (mul_nonneg (mul_nonneg hb ht.le) hnb0)
  have p4 : 0 ≤ u * (b * tiny) := mul_nonneg hu.le (mul_nonneg hb ht.le)
  have d1 := mul_le_mul_of_nonneg_right f3 p1
  have d2 := mul_le_mul_of_nonneg_right (by linarith : (1 + u) ^ 2 + (1 + u) + 1 ≤ 3.02) p2
  have d3 := mul_le_mul_of_nonneg_right f2 p3
  have d4 := mul_le_mul_of_nonneg_right (by linarith : 1 + u ≤ 1.01) p4
  have e5 : 1.01 * u * (b * tiny * (nb + 1))
      = 1.01 * (u * (b * tiny * nb)) + 1.01 * (u * (b * tiny)) := by ring
  have e6 : 3.02 * u * (a * b * (nb * v)) = 3.02 * (u * (a * b * (nb * v))) := by ring
  linarith

/-- The co-moment after Polars's merge, `Ĉ = fl(Ĉ_a + fl(Ĉ_b + T̂))`, of either
sign (`sg_assemble` for pairs): the first rounding is in `|C_b|`, which
`C_a + C_b` may cancel, so the bound reads `|C_a| + |C_b|`. -/
theorem sg_assemble2 {Ca Cb ΔC Sha Shb T Sh1 Sh Ea Eb ET : ℝ}
    (hEa : |Sha - Ca| ≤ Ea) (hEb : |Shb - Cb| ≤ Eb) (hT : |T - ΔC| ≤ ET)
    (h1 : |Sh1 - (Shb + T)| ≤ u * (|Shb + T| + tiny))
    (h2 : |Sh - (Sha + Sh1)| ≤ u * (|Sha + Sh1| + tiny)) :
    |Sh - (Ca + Cb + ΔC)| ≤ (1 + u) ^ 2 * (Ea + Eb) + 1.0001 * ET + 2.0001 * u * (|Ca| + |Cb|)
      + 2.0001 * u * |ΔC| + 2.0001 * u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hEa0 : 0 ≤ Ea := le_trans (abs_nonneg _) hEa
  have hEb0 : 0 ≤ Eb := le_trans (abs_nonneg _) hEb
  have hET0 : 0 ≤ ET := le_trans (abs_nonneg _) hT
  have hb1 : |Cb + ΔC| ≤ |Cb| + |ΔC| := abs_add_le _ _
  have hb2 : |Ca + Cb + ΔC| ≤ |Ca| + |Cb| + |ΔC| := by
    have := abs_add_le (Ca + Cb) ΔC; have := abs_add_le Ca Cb; linarith
  have a1 : |Shb + T| ≤ |Cb| + |ΔC| + Eb + ET := by
    have e : Shb + T = (Cb + ΔC) + ((Shb - Cb) + (T - ΔC)) := by ring
    rw [e]
    have := abs_add_le (Cb + ΔC) ((Shb - Cb) + (T - ΔC))
    have := abs_add_le (Shb - Cb) (T - ΔC)
    linarith
  have a2 : |Sh1 - (Cb + ΔC)| ≤ (1 + u) * (Eb + ET) + u * (|Cb| + |ΔC| + tiny) := by
    have e : Sh1 - (Cb + ΔC) = (Sh1 - (Shb + T)) + ((Shb - Cb) + (T - ΔC)) := by ring
    rw [e]
    have := abs_add_le (Sh1 - (Shb + T)) ((Shb - Cb) + (T - ΔC))
    have := abs_add_le (Shb - Cb) (T - ΔC)
    have := mul_le_mul_of_nonneg_left a1 hu.le
    linarith
  set K1 := (1 + u) * (Eb + ET) + u * (|Cb| + |ΔC| + tiny) with hK1
  have a3 : |Sha + Sh1| ≤ |Ca| + |Cb| + |ΔC| + Ea + K1 := by
    have e : Sha + Sh1 = (Ca + Cb + ΔC) + ((Sha - Ca) + (Sh1 - (Cb + ΔC))) := by ring
    rw [e]
    have := abs_add_le (Ca + Cb + ΔC) ((Sha - Ca) + (Sh1 - (Cb + ΔC)))
    have := abs_add_le (Sha - Ca) (Sh1 - (Cb + ΔC))
    linarith
  have a4 : |Sh - (Ca + Cb + ΔC)| ≤ (1 + u) * (Ea + K1) + u * (|Ca| + |Cb| + |ΔC| + tiny) := by
    have e : Sh - (Ca + Cb + ΔC) = (Sh - (Sha + Sh1)) + ((Sha - Ca) + (Sh1 - (Cb + ΔC))) := by
      ring
    rw [e]
    have := abs_add_le (Sh - (Sha + Sh1)) ((Sha - Ca) + (Sh1 - (Cb + ΔC)))
    have := abs_add_le (Sha - Ca) (Sh1 - (Cb + ΔC))
    have := mul_le_mul_of_nonneg_left a3 hu.le
    linarith
  refine le_trans a4 ?_
  have e : (1 + u) * (Ea + K1) + u * (|Ca| + |Cb| + |ΔC| + tiny)
      = (1 + u) * Ea + (1 + u) ^ 2 * Eb + (1 + u) ^ 2 * ET + (1 + u) * (u * (|Cb| + |ΔC| + tiny))
        + u * (|Ca| + |Cb| + |ΔC| + tiny) := by simp only [hK1]; ring
  rw [e]
  have b1 : (1 + u) * Ea ≤ (1 + u) ^ 2 * Ea := by
    have : 1 + u ≤ (1 + u) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hEa0
  have b2 : (1 + u) ^ 2 * ET ≤ 1.0001 * ET := by
    have : (1 + u) ^ 2 ≤ 1.0001 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hET0
  have b3 : (1 + u) * (u * (|Cb| + |ΔC| + tiny)) ≤ 1.0001 * (u * (|Cb| + |ΔC| + tiny)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p1 : 0 ≤ u * |Ca| := by positivity
  linarith

/-- The small facts about `u` the increment's bound uses. -/
theorem u_small : (1 + u) ^ 2 ≤ 1.0001 ∧ 1 + u ≤ 1.0001 ∧ 6.5001 * u ≤ 0.0001 ∧
    u ^ 2 ≤ u / 2 ^ 53 ∧ 6.5001 * u * (1 + u) ≤ 0.0001 ∧ u * (6.5001 * u) ^ 2 ≤ 0.0001 * u ^ 2 := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have h2 : u ^ 2 ≤ u / 2 ^ 53 := by nlinarith
  refine ⟨by nlinarith, by linarith, by linarith, h2, by nlinarith, by nlinarith⟩

theorem sg_k_n {n Q PX PY W G : ℝ} (hn : 0 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21) (hQ : 0 ≤ Q)
    (hPX : 0 ≤ PX) (hPY : 0 ≤ PY) (hW : 0 ≤ W)
    (hG : G ≤ (1 + u) ^ 2 * Q + 6.5001 * u * (1 + u) * (PX + PY) + (6.5001 * u) ^ 2 * W) :
    u * n * G ≤ 1.0001 * (u * n * Q) + 0.0001 * u * (PX + PY) + 0.0001 * u ^ 2 * W := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  obtain ⟨f1, -, -, -, -, -⟩ := u_small
  have hun : 0 ≤ u * n := by positivity
  have h1 := mul_le_mul_of_nonneg_left hG hun
  have g1 := mul_le_mul_of_nonneg_right f1 (by positivity : (0 : ℝ) ≤ u * n * Q)
  have g2 : u * n * (6.5001 * u * (1 + u)) ≤ 0.0001 * u := by
    have : n * u * (6.5001 * (1 + u)) ≤ 1 / 2 ^ 21 * 7 :=
      mul_le_mul hnu (by linarith) (by positivity) (by norm_num)
    nlinarith
  have g2' := mul_le_mul_of_nonneg_right g2 (by positivity : (0 : ℝ) ≤ PX + PY)
  have g3 : u * n * (6.5001 * u) ^ 2 ≤ 0.0001 * u ^ 2 := by
    have : n * u * (42.26 * u) ≤ 1 / 2 ^ 21 * (42.26 * u) :=
      mul_le_mul_of_nonneg_right hnu (by positivity)
    nlinarith
  have g3' := mul_le_mul_of_nonneg_right g3 hW
  nlinarith

theorem sg_k_one {Q PX PY W G : ℝ} (hQ : 0 ≤ Q) (hPX : 0 ≤ PX) (hPY : 0 ≤ PY) (hW : 0 ≤ W)
    (hG : G ≤ (1 + u) ^ 2 * Q + 6.5001 * u * (1 + u) * (PX + PY) + (6.5001 * u) ^ 2 * W) :
    u * G ≤ 1.0001 * (u * Q) + 0.0001 * u * (PX + PY) + 0.0001 * u ^ 2 * W := by
  obtain ⟨hu, -, -, -, -⟩ := fpFacts
  obtain ⟨f1, -, -, -, fcu, fc2⟩ := u_small
  have h1 := mul_le_mul_of_nonneg_left hG hu.le
  have g1 := mul_le_mul_of_nonneg_right f1 (by positivity : (0 : ℝ) ≤ u * Q)
  have g2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fcu (by positivity :
    (0 : ℝ) ≤ PX + PY)) hu.le
  have g3 := mul_le_mul_of_nonneg_right fc2 hW
  nlinarith

theorem sg_k_A {PY W Ab : ℝ} (hPY : 0 ≤ PY)
    (h : Ab ≤ (1 + u) * PY + 6.5001 * u * W) : u * Ab ≤ 1.0001 * (u * PY) + 6.5001 * u ^ 2 * W := by
  obtain ⟨hu, -, -, -, -⟩ := fpFacts
  obtain ⟨-, f2, -, -, -, -⟩ := u_small
  have h1 := mul_le_mul_of_nonneg_left h hu.le
  have g1 := mul_le_mul_of_nonneg_right f2 (by positivity : (0 : ℝ) ≤ u * PY)
  nlinarith

theorem sg_k_X {Q PX Xb : ℝ} (hQ : 0 ≤ Q) (hPX : 0 ≤ PX)
    (h : Xb ≤ u * ((1 + u) * Q + 6.5001 * u * PX)) : Xb ≤ 1.0001 * (u * Q) + 0.0001 * u * PX := by
  obtain ⟨hu, -, -, -, -⟩ := fpFacts
  obtain ⟨-, f2, fc, -, -, -⟩ := u_small
  have g1 := mul_le_mul_of_nonneg_right f2 (by positivity : (0 : ℝ) ≤ u * Q)
  have g2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fc hPX) hu.le
  nlinarith

theorem sg_k_uu {P : ℝ} (hP : 0 ≤ P) : u ^ 2 * P ≤ 0.0001 * (u * P) := by
  obtain ⟨hu, -, -, -, -⟩ := fpFacts
  obtain ⟨-, -, -, hu2, -, -⟩ := u_small
  have := mul_le_mul_of_nonneg_right hu2 hP
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The increment's error in the exact `h Δx Δy`**, from `sg_T2`'s bound in
the rounded differences `Δ̂`, the deviation's error `E_q` and each `Δ̂`'s error
in `Δ`. `n_b ≤ n h`, `n_b · tiny ≤ h A_x` and `tiny ≤ h A_x` turn `n_b` and the
underflow terms into `h`. -/
theorem sg_cov_ET {n h w nb Ax Ay P Eq T Dx Dy ΔX ΔY : ℝ}
    (hh0 : 0 ≤ h) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hwh : w ≤ h) (hnbh : nb ≤ n * h)
    (hn0 : 0 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hnbt : nb * tiny ≤ h * Ax) (htA : tiny ≤ h * Ax) (htx : 2 * tiny ≤ Ax) (hty : 2 * tiny ≤ Ay)
    (hP : nb * P ≤ 1.02 * Ax * w)
    (hEq : Eq = u * |Dx| * (1.0003 + 2.0001 * w) + u * (P + tiny) + 2.0002 * u * tiny)
    (hT : |T - Dx * Dy * h| ≤ 1.01 * (nb * |Dy| * Eq) + 3.02 * u * (|Dx| * |Dy| * h)
      + 1.01 * u * (|Dy| * tiny * (nb + 1)) + u * tiny)
    (hDx : |Dx - ΔX| ≤ u * |ΔX| + 6.0001 * u * Ax + u * tiny)
    (hDy : |Dy - ΔY| ≤ u * |ΔY| + 6.0001 * u * Ay + u * tiny) :
    |T - ΔX * ΔY * h| ≤ 3.032 * u * n * (h * (|ΔX| * |ΔY|)) + 5.04 * u * (h * (|ΔX| * |ΔY|))
      + 12.59 * u * (Ax * (h * |ΔY|)) + 6.51 * u * (Ay * (h * |ΔX|)) + 82 * u ^ 2 * h * (Ax * Ay)
      + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  set a := |Dx| with ha_def
  set b := |Dy| with hb_def
  set X := |ΔX| with hX_def
  set Y := |ΔY| with hY_def
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hX : 0 ≤ X := abs_nonneg _
  have hY : 0 ≤ Y := abs_nonneg _
  -- Step A: `|T − D̂x D̂y h|` in `a`, `b`.
  have t1 : nb * b * Eq = u * (a * b * nb) * (1.0003 + 2.0001 * w) + u * b * (nb * P)
      + 3.0002 * u * b * (nb * tiny) := by rw [hEq]; ring
  have t2 : u * (a * b * nb) * (1.0003 + 2.0001 * w) ≤ 3.0004 * u * (n * h * (a * b)) := by
    have k1 : a * b * nb ≤ a * b * (n * h) := mul_le_mul_of_nonneg_left hnbh (by positivity)
    have k2 : (1.0003 : ℝ) + 2.0001 * w ≤ 3.0004 := by linarith
    have := mul_le_mul (mul_le_mul_of_nonneg_left k1 hu.le) k2 (by positivity) (by positivity)
    nlinarith
  have t3 : u * b * (nb * P) ≤ 1.02 * u * (Ax * h * b) := by
    have : nb * P ≤ 1.02 * Ax * h := le_trans hP (mul_le_mul_of_nonneg_left hwh (by positivity))
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hu.le hb)
    nlinarith
  have t4 : u * b * (nb * tiny) ≤ u * (Ax * h * b) := by
    have := mul_le_mul_of_nonneg_left hnbt (mul_nonneg hu.le hb); nlinarith
  have t5 : 1.01 * u * (b * tiny * (nb + 1)) ≤ 2.02 * u * (Ax * h * b) := by
    have k1 := mul_le_mul_of_nonneg_left hnbt (mul_nonneg hu.le hb)
    have k2 := mul_le_mul_of_nonneg_left htA (mul_nonneg hu.le hb)
    nlinarith
  have hA : |T - Dx * Dy * h| ≤ 3.0305 * u * (n * h * (a * b)) + 3.02 * u * (h * (a * b))
      + 6.081 * u * (Ax * h * b) + u * tiny := by
    have p1 : 0 ≤ u * (n * h * (a * b)) := by positivity
    have p2 : 0 ≤ u * (Ax * h * b) := by positivity
    have e : 3.02 * u * (a * b * h) = 3.02 * u * (h * (a * b)) := by ring
    rw [t1] at hT
    linarith
  -- Step B: from `D̂x D̂y` to `Δx Δy`.
  have hB : h * |Dx * Dy - ΔX * ΔY| ≤ h * b * (u * X + 6.0001 * u * Ax + u * tiny)
      + h * X * (u * Y + 6.0001 * u * Ay + u * tiny) := by
    have e : Dx * Dy - ΔX * ΔY = (Dx - ΔX) * Dy + ΔX * (Dy - ΔY) := by ring
    have k : |Dx * Dy - ΔX * ΔY| ≤ |Dx - ΔX| * b + X * |Dy - ΔY| := by
      rw [e]; have := abs_add_le ((Dx - ΔX) * Dy) (ΔX * (Dy - ΔY))
      rw [abs_mul, abs_mul] at this; exact this
    have k1 := mul_le_mul_of_nonneg_right hDx hb
    have k2 := mul_le_mul_of_nonneg_left hDy hX
    have := mul_le_mul_of_nonneg_left (le_trans k (add_le_add k1 k2)) hh0
    nlinarith
  -- Step C: `a ≤ X (1 + u) + 6.5001 u A_x`, `b` likewise.
  have hut : u * tiny ≤ 0.5 * u * Ax := by nlinarith
  have hut' : u * tiny ≤ 0.5 * u * Ay := by nlinarith
  have haX : a ≤ X + u * X + 6.5001 * u * Ax := by
    have := abs_sub_abs_le_abs_sub Dx ΔX; linarith
  have hbY : b ≤ Y + u * Y + 6.5001 * u * Ay := by
    have := abs_sub_abs_le_abs_sub Dy ΔY; linarith
  -- the products
  have hab : a * b ≤ (X + u * X + 6.5001 * u * Ax) * (Y + u * Y + 6.5001 * u * Ay) :=
    mul_le_mul haX hbY hb (by positivity)
  -- names for the terms of the result
  set Q := h * (X * Y) with hQ
  set PX := Ay * (h * X) with hPX
  set PY := Ax * (h * Y) with hPY
  set W := h * (Ax * Ay) with hW
  have hQ0 : 0 ≤ Q := by positivity
  have hPX0 : 0 ≤ PX := by positivity
  have hPY0 : 0 ≤ PY := by positivity
  have hW0 : 0 ≤ W := by positivity
  set c := 6.5001 * u with hc
  have hc0 : 0 ≤ c := by positivity
  have hG : h * (a * b) ≤ (1 + u) ^ 2 * Q + c * (1 + u) * (PX + PY) + c ^ 2 * W := by
    calc h * (a * b) ≤ h * ((X + u * X + c * Ax) * (Y + u * Y + c * Ay)) :=
          mul_le_mul_of_nonneg_left hab hh0
      _ = (1 + u) ^ 2 * Q + c * (1 + u) * (PX + PY) + c ^ 2 * W := by
          simp only [hQ, hPX, hPY, hW]; ring
  -- `Ax h b ≤ (1 + u) PY + c W`, `h X b ≤ (1 + u) Q + c PX`
  have hAb : Ax * h * b ≤ (1 + u) * PY + c * W := by
    calc Ax * h * b ≤ Ax * h * (Y + u * Y + c * Ay) := mul_le_mul_of_nonneg_left hbY (by positivity)
      _ = (1 + u) * PY + c * W := by simp only [hPY, hW]; ring
  have hXb : h * b * (u * X) ≤ u * ((1 + u) * Q + c * PX) := by
    calc h * b * (u * X) ≤ h * (Y + u * Y + c * Ay) * (u * X) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbY hh0) (by positivity)
      _ = u * ((1 + u) * Q + c * PX) := by simp only [hQ, hPX]; ring
  -- the step from the rounded differences
  have hTot : |T - ΔX * ΔY * h| ≤ |T - Dx * Dy * h| + h * |Dx * Dy - ΔX * ΔY| := by
    have e : T - ΔX * ΔY * h = (T - Dx * Dy * h) + h * (Dx * Dy - ΔX * ΔY) := by ring
    rw [e]
    calc |(T - Dx * Dy * h) + h * (Dx * Dy - ΔX * ΔY)|
        ≤ |T - Dx * Dy * h| + |h * (Dx * Dy - ΔX * ΔY)| := abs_add_le _ _
      _ = |T - Dx * Dy * h| + h * |Dx * Dy - ΔX * ΔY| := by rw [abs_mul, abs_of_nonneg hh0]
  have hbt : h * b * (u * tiny) ≤ 0.5 * u * (Ax * h * b) := by
    have := mul_le_mul_of_nonneg_left hut (by positivity : (0 : ℝ) ≤ h * b); nlinarith
  have hXt : h * X * (u * tiny) ≤ 0.5 * u * PX := by
    have := mul_le_mul_of_nonneg_left hut' (by positivity : (0 : ℝ) ≤ h * X)
    simp only [hPX]; linarith
  have eB : h * b * (u * X + 6.0001 * u * Ax + u * tiny) + h * X * (u * Y + 6.0001 * u * Ay + u * tiny)
      = h * b * (u * X) + 6.0001 * u * (Ax * h * b) + h * b * (u * tiny) + u * Q
        + 6.0001 * u * PX + h * X * (u * tiny) := by simp only [hQ, hPX]; ring
  -- every term, against the result's
  have k1 := sg_k_n hn0 hnu hQ0 hPX0 hPY0 hW0 hG
  have k2 := sg_k_one hQ0 hPX0 hPY0 hW0 hG
  have k3 := sg_k_A hPY0 hAb
  have k4 := sg_k_X hQ0 hPX0 hXb
  have k5 := sg_k_uu hPY0
  have k6 := sg_k_uu hPX0
  have e1 : u * (n * h * (a * b)) = u * n * (h * (a * b)) := by ring
  rw [eB] at hB
  have hu0 := hu.le
  have ht0 := ht.le
  have eW : u ^ 2 * W = u ^ 2 * h * (Ax * Ay) := by rw [hW]; ring
  have S1 := le_trans hTot (add_le_add hA hB)
  have S2 : |T - ΔX * ΔY * h| ≤ 3.0305 * (1.0001 * (u * n * Q) + 0.0001 * u * (PX + PY)
      + 0.0001 * u ^ 2 * W) + 3.02 * (1.0001 * (u * Q) + 0.0001 * u * (PX + PY) + 0.0001 * u ^ 2 * W)
      + 12.5811 * (1.0001 * (u * PY) + 6.5001 * u ^ 2 * W) + u * tiny
      + (1.0001 * (u * Q) + 0.0001 * u * PX) + u * Q + 6.5001 * u * PX := by
    have i1 := mul_le_mul_of_nonneg_left k1 (by norm_num : (0 : ℝ) ≤ 3.0305)
    have i2 := mul_le_mul_of_nonneg_left k2 (by norm_num : (0 : ℝ) ≤ 3.02)
    have i3 := mul_le_mul_of_nonneg_left k3 (by norm_num : (0 : ℝ) ≤ 12.5811)
    linarith only [S1, hbt, hXt, i1, i2, i3, k4, e1]
  linarith only [S2, eW, hQ0, hPX0, hPY0, hW0, hu0, ht0, mul_nonneg hu0 hQ0, mul_nonneg hu0 hPX0,
    mul_nonneg hu0 hPY0, mul_nonneg (mul_nonneg hu0 hn0) hQ0, mul_nonneg (pow_nonneg hu0 2) hW0]

/-- **Polars's merge adds what `cMergeNew` allows at `CConst.sg`**: the
increment's error (`sg_cov_ET`) and the two roundings of the sum
(`sg_assemble2`), with `|C_a| + |C_b| ≤ R` and `h|Δx||Δy| ≤ R`. -/
theorem sg_cov_new {n h Ax Ay X Y R Ca Cb ET : ℝ} (hn0 : 0 ≤ n) (hh0 : 0 ≤ h) (hAx : 0 ≤ Ax)
    (hAy : 0 ≤ Ay) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hR1 : |Ca| + |Cb| ≤ R) (hYR : h * (X * Y) ≤ R)
    (hET : ET ≤ 3.032 * u * n * (h * (X * Y)) + 5.04 * u * (h * (X * Y))
      + 12.59 * u * (Ax * (h * Y)) + 6.51 * u * (Ay * (h * X)) + 82 * u ^ 2 * h * (Ax * Ay)
      + u * tiny) :
    1.0001 * ET + 2.0001 * u * (|Ca| + |Cb|) + 2.0001 * u * (h * (X * Y)) + 2.0001 * u * tiny
      ≤ cMergeNew CConst.sg n h Ax Ay X Y R := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  unfold cMergeNew CConst.sg
  dsimp only
  have p1 : 0 ≤ u * n * (h * (X * Y)) := by positivity
  have p2 : 0 ≤ u * (Ax * (h * Y)) := by positivity
  have p3 : 0 ≤ u * (Ay * (h * X)) := by positivity
  have p4 : 0 ≤ u ^ 2 * h * (Ax * Ay) := by positivity
  have p5 : 0 ≤ u * tiny := by positivity
  have p6 : 0 ≤ h * u * tiny := by positivity
  have q1 : u * (h * (X * Y)) ≤ u * R := mul_le_mul_of_nonneg_left hYR hu.le
  have q2 : u * (|Ca| + |Cb|) ≤ u * R := mul_le_mul_of_nonneg_left hR1 hu.le
  have e1 : 4 * u * n * (h * (X * Y)) = 4 * (u * n * (h * (X * Y))) := by ring
  have e2 : 13 * u * (Ax * (h * Y) + Ay * (h * X)) = 13 * (u * (Ax * (h * Y))) + 13 * (u * (Ay * (h * X))) := by
    ring
  have e3 : (7.1 + 5.1 * h) * u * tiny = 7.1 * (u * tiny) + 5.1 * (h * u * tiny) := by ring
  have hR0 : 0 ≤ u * R := by
    have : 0 ≤ |Ca| + |Cb| := by positivity
    exact mul_nonneg hu.le (by linarith)
  linarith

/-- One variable of a side of a merge of pairs, as a side of the variance's
merge with no co-moment: its mean's bounds are the same. -/
theorem CMergeSide.xSide {n : ℕ} {mx my Mx My Ax Ay C Ch E : ℝ}
    (h : CMergeSide n mx my Mx My Ax Ay C Ch E) :
    MergeSide n mx Mx (Ax - n * tiny) 0 0 0 ∧ MergeSide n my My (Ay - n * tiny) 0 0 0 := by
  have := h.MxA; have := h.MyA; have := abs_nonneg Mx; have := abs_nonneg My
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨⟨h.one, by nlinarith, by linarith [h.Axb], by linarith, h.Mxb, by
      rw [sub_add_cancel]; exact h.ex, le_rfl, by norm_num, by simp, by norm_num⟩,
    ⟨h.one, by nlinarith, by linarith [h.Ayb], by linarith, h.Myb, by
      rw [sub_add_cancel]; exact h.ey, le_rfl, by norm_num, by simp, by norm_num⟩⟩

set_option maxHeartbeats 4000000 in
/-- **Polars's merge of pairs meets `CMergeSpec` at `CConst.sg`** (#1808,
ruling 271): the means are the variance's (`sgMerge_spec`), and the co-moment
is within `cMergeNew` at Schubert and Gertz's constants (`sg_T2`,
`sg_cov_ET`, `sg_assemble2`, `sg_cov_new`). -/
theorem StdModel.sgCov_spec : CMergeSpec CConst.sg M.sgCov := by
  intro na nb mxa mya mxb myb Mxa Mya Mxb Myb Axa Aya Axb Ayb Ca Cb Sha Shb Ea Eb hN sa sb R
    hR1 hR2 hY
  obtain ⟨hu, hu', htn, htn1, hmax⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  have hla := sa.one
  have hlb := sb.one
  have h1 : na ≠ 0 := by omega
  have h2 : nb ≠ 0 := by omega
  have hsx := M.sgMerge_spec hN sa.xSide.1 sb.xSide.1
  have hsy := M.sgMerge_spec hN sa.xSide.2 sb.xSide.2
  simp only [StdModel.sgMerge, h1, h2, ite_false] at hsx hsy
  have hdm : M.sgCov ⟨na, mxa, mya, Sha⟩ ⟨nb, mxb, myb, Shb⟩ = ⟨na + nb,
      M.sgMean (na, mxa, 0) (nb, mxb, 0), M.sgMean (na, mya, 0) (nb, myb, 0),
      M.fl (Sha + M.fl (Shb + M.fl (M.fl ((nb : ℝ) * M.fl (mxb - M.sgMean (na, mxa, 0) (nb, mxb, 0)))
        * M.fl (myb - mya))))⟩ := by
    simp only [StdModel.sgCov, h1, h2, ite_false]
  rw [hdm]
  have hna1 : (1 : ℝ) ≤ na := by exact_mod_cast hla
  have hnb1 : (1 : ℝ) ≤ nb := by exact_mod_cast hlb
  have hnab : (na : ℝ) + nb ≤ 2 ^ 32 := by exact_mod_cast hN
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have := hsx.2.1
    simp only [sub_add_cancel] at this
    exact this
  · have := hsy.2.1
    simp only [sub_add_cancel] at this
    exact this
  · show |M.fl (Sha + M.fl (Shb + M.fl (M.fl ((nb : ℝ) * M.fl (mxb - M.sgMean (na, mxa, 0) (nb, mxb, 0)))
        * M.fl (myb - mya)))) - _| ≤ _
    simp only [StdModel.sgMean]
    -- the sides
    set Aa := Axa with hAa
    set Ab := Axb with hAb
    have hAa0 := sa.Ax0
    have hAb0 := sb.Ax0
    have hAya0 := sa.Ay0
    have hAyb0 := sb.Ay0
    have hnat : (0 : ℝ) ≤ na * tiny := mul_nonneg (by linarith) htn.le
    have hnbt : (0 : ℝ) ≤ nb * tiny := mul_nonneg (by linarith) htn.le
    obtain ⟨hma1, hmab, hMaA⟩ := mean_mag hna1 (by linarith) hAa0 sa.Axb
      (by have := sa.MxA; linarith) sa.Mxb sa.ex
    obtain ⟨hmb1, hmbb, hMbA⟩ := mean_mag hnb1 (by linarith) hAb0 sb.Axb
      (by have := sb.MxA; linarith) sb.Mxb sb.ex
    obtain ⟨hmya1, hmyab, hMyaA⟩ := mean_mag hna1 (by linarith) hAya0 sa.Ayb
      (by have := sa.MyA; linarith) sa.Myb sa.ey
    obtain ⟨hmyb1, hmybb, hMybA⟩ := mean_mag hnb1 (by linarith) hAyb0 sb.Ayb
      (by have := sb.MyA; linarith) sb.Myb sb.ey
    -- the weights
    set n : ℝ := (na : ℝ) + nb with hn
    have hn0 : 0 < n := by linarith
    have hne : n ≠ 0 := ne_of_gt hn0
    have hnu : n * u ≤ 1 / 2 ^ 21 := by
      calc n * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul hnab hu' hu.le (by norm_num)
        _ = 1 / 2 ^ 21 := by norm_num
    set w : ℝ := (nb : ℝ) / n with hw
    have hwn : n * w = nb := by rw [hw]; exact mul_div_cancel₀ _ hn0.ne'
    have hw1 : w ≤ 1 := by rw [hw, div_le_one hn0]; linarith
    have hw0 : 1 / 2 ^ 32 ≤ w := by rw [hw, le_div_iff₀ hn0]; linarith
    have hw0' : 0 ≤ w := by linarith
    set h : ℝ := (na : ℝ) * nb / n with hh
    have hnh : n * h = na * nb := by rw [hh]; exact mul_div_cancel₀ _ hn0.ne'
    have hh2 : 1 / 2 ≤ h := by rw [hh, hn]; exact h_ge_half hla hlb
    have hh0 : 0 ≤ h := by linarith
    have hwh : w ≤ h := by
      rw [hw, hh]; apply div_le_div_of_nonneg_right _ hn0.le; nlinarith
    have hv : (nb : ℝ) * (1 - w) = h := by
      rw [hh, hw, hn]; field_simp [hne]; ring
    -- the roundings of the `x` mean
    set D := mxb - mxa with hD
    have hDb : |D| ≤ 2 ^ 402 := by rw [hD]; have := abs_sub mxb mxa; linarith
    obtain ⟨ef, hfb⟩ := M.err_le (z := w) (B := 1) (by rw [abs_of_nonneg hw0']; exact hw1) le_rfl
      (by norm_num)
    rw [abs_of_nonneg hw0'] at ef
    obtain ⟨eD, hDhb⟩ := M.err_le (z := D) (B := 2 ^ 402) hDb (by norm_num) (by norm_num)
    set f := M.fl w with hf
    set Dh := M.fl D with hDh
    have hfw : |f - w| ≤ 1.0001 * u * w := by
      have : u * tiny ≤ u * (0.0001 * w) := mul_le_mul_of_nonneg_left (by linarith) hu.le
      linarith
    have E1 := fma_prod_err hw0' hfw eD
    rw [mul_comm f Dh] at E1
    have hDf : |Dh * f| ≤ 2 ^ 404 := by
      rw [abs_mul]
      have := mul_le_mul hDhb hfb (abs_nonneg _) (by positivity)
      linarith
    obtain ⟨ep, hpb⟩ := M.err_le (z := Dh * f) (B := 2 ^ 404) hDf (by norm_num) (by norm_num)
    set p := M.fl (Dh * f) with hp
    have hmp : |mxa + p| ≤ 2 ^ 406 := by have := abs_add_le mxa p; linarith
    obtain ⟨em, hm'b⟩ := M.err_le (z := mxa + p) (B := 2 ^ 406) hmp (by norm_num) (by norm_num)
    set m' := M.fl (mxa + p) with hm'
    -- `n |m_a + p| ≤ 1.02 A_x`
    have hy : mxa + w * D = ((na : ℝ) * mxa + nb * mxb) / n := by
      rw [eq_div_iff hn0.ne', hD, hw, hn]; field_simp [hne]; ring
    have hny : n * |mxa + w * D| ≤ 1.01 * (Aa + Ab) := by
      have : n * |mxa + w * D| ≤ na * |mxa| + nb * |mxb| := by
        rw [hy, abs_div, abs_of_pos hn0, mul_div_cancel₀ _ hn0.ne']
        have := abs_add_le ((na : ℝ) * mxa) (nb * mxb)
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast] at this; exact this
      linarith
    have hpy : |(mxa + p) - (mxa + w * D)| ≤ u * (w * |D| + (2.0002 * u * w * |D|
        + 1.0001 * u * w * tiny) + tiny) + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) := by
      have e : (mxa + p) - (mxa + w * D) = (p - Dh * f) + (Dh * f - w * D) := by ring
      rw [e]
      have := abs_add_le (p - Dh * f) (Dh * f - w * D)
      have hDf' : |Dh * f| ≤ w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) := by
        have := abs_sub_abs_le_abs_sub (Dh * f) (w * D)
        rw [abs_mul w D, abs_of_nonneg hw0'] at this; linarith
      have := mul_le_mul_of_nonneg_left hDf' hu.le
      linarith
    have hA0 : 0 ≤ Aa + Ab := add_nonneg hAa0 hAb0
    have hnmp : n * |mxa + p| ≤ 1.02 * (Aa + Ab) := by
      have hnD : n * w * |D| ≤ 2 ^ 32 * (1.01 * (Aa + Ab)) := by
        rw [hwn]
        have h0 : |D| ≤ |mxa| + |mxb| := by have := abs_sub mxb mxa; rw [hD]; linarith
        have h1 := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ nb)
        have h3 : (nb : ℝ) * |mxa| ≤ nb * (na * |mxa|) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hna1) (by linarith)
        have h4 := mul_le_mul_of_nonneg_left hma1 (by linarith : (0 : ℝ) ≤ nb)
        have h5 : (nb : ℝ) * (1.01 * Aa) ≤ 2 ^ 32 * (1.01 * Aa) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h6 : (1.01 : ℝ) * Ab ≤ 2 ^ 32 * (1.01 * Ab) :=
          le_mul_of_one_le_left (by positivity) (by norm_num)
        linarith
      have hnt : n * tiny ≤ Aa + Ab := by
        have : n * tiny = na * tiny + nb * tiny := by rw [hn]; ring
        have := sa.Axt; have := sb.Axt
        linarith
      have hnwt : n * w * tiny ≤ Aa + Ab := by rw [hwn]; have := sb.Axt; linarith
      exact sg_nmp hn0.le hw0' hA0 hpy hny hnD hnwt hnt
    -- the deviation `m_b − m̂`
    have hdev := sg_dev (ma := mxa) (mb := mxb) hw0' eD ef ep em
    set Eq := u * |Dh| * (1.0003 + 2.0001 * w) + u * (|mxa + p| + tiny) + 2.0002 * u * tiny
      with hEq
    have hEq0 : 0 ≤ Eq := by simp only [hEq]; positivity
    -- the roundings of the increment
    have hmbm : |mxb - m'| ≤ 2 ^ 408 := by have := abs_sub mxb m'; linarith
    obtain ⟨eq', hqb⟩ := M.err_le (z := mxb - m') (B := 2 ^ 408) hmbm (by norm_num) (by norm_num)
    set q := M.fl (mxb - m') with hq
    have hnq : |(nb : ℝ) * q| ≤ 2 ^ 441 := by
      rw [abs_mul, Nat.abs_cast]
      have := mul_le_mul (by linarith : (nb : ℝ) ≤ 2 ^ 32) hqb (abs_nonneg _) (by norm_num)
      linarith
    obtain ⟨er, hrb⟩ := M.err_le (z := (nb : ℝ) * q) (B := 2 ^ 441) hnq (by norm_num) (by norm_num)
    set r := M.fl ((nb : ℝ) * q) with hr
    have hDyb : |myb - mya| ≤ 2 ^ 402 := by have := abs_sub myb mya; linarith
    obtain ⟨eDy, hDyhb⟩ := M.err_le (z := myb - mya) (B := 2 ^ 402) hDyb (by norm_num) (by norm_num)
    set Dy := M.fl (myb - mya) with hDy
    have hrD : |r * Dy| ≤ 2 ^ 845 := by
      rw [abs_mul]
      have := mul_le_mul hrb hDyhb (abs_nonneg _) (by positivity)
      linarith
    obtain ⟨eT, hTb⟩ := M.err_le (z := r * Dy) (B := 2 ^ 845) hrD (by norm_num) (by norm_num)
    set T := M.fl (r * Dy) with hT
    have hT1 := sg_T2 (v := 1 - w) hnb1 (by linarith) hEq0 hdev eq' er eT
    rw [hv] at hT1
    -- the rounded differences against the exact ones
    have hDDx : |Dh - (Mxb - Mxa)| ≤ u * |Mxb - Mxa| + 6.0001 * u * (Aa + Ab) + u * tiny := by
      have h1 : |D - (Mxb - Mxa)| ≤ 6 * u * (Aa + Ab) := by
        have e : D - (Mxb - Mxa) = (mxb - Mxb) - (mxa - Mxa) := by rw [hD]; ring
        rw [e]; have := abs_sub (mxb - Mxb) (mxa - Mxa); have := sa.ex; have := sb.ex; linarith
      have h2 : |D| ≤ |Mxb - Mxa| + 6 * u * (Aa + Ab) := by
        have := abs_sub_abs_le_abs_sub D (Mxb - Mxa); linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hu.le
      have h4 : u * (6 * u * (Aa + Ab)) ≤ 0.0001 * u * (Aa + Ab) := by
        have := mul_le_mul_of_nonneg_right (by linarith : 6 * u ≤ 0.0001) (mul_nonneg hu.le hA0)
        linarith
      have e : Dh - (Mxb - Mxa) = (Dh - D) + (D - (Mxb - Mxa)) := by ring
      rw [e]
      have := abs_add_le (Dh - D) (D - (Mxb - Mxa))
      linarith
    have hAy0 : 0 ≤ Aya + Ayb := add_nonneg hAya0 hAyb0
    have hDDy : |Dy - (Myb - Mya)| ≤ u * |Myb - Mya| + 6.0001 * u * (Aya + Ayb) + u * tiny := by
      have h1 : |(myb - mya) - (Myb - Mya)| ≤ 6 * u * (Aya + Ayb) := by
        have e : (myb - mya) - (Myb - Mya) = (myb - Myb) - (mya - Mya) := by ring
        rw [e]; have := abs_sub (myb - Myb) (mya - Mya); have := sa.ey; have := sb.ey; linarith
      have h2 : |myb - mya| ≤ |Myb - Mya| + 6 * u * (Aya + Ayb) := by
        have := abs_sub_abs_le_abs_sub (myb - mya) (Myb - Mya); linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hu.le
      have h4 : u * (6 * u * (Aya + Ayb)) ≤ 0.0001 * u * (Aya + Ayb) := by
        have := mul_le_mul_of_nonneg_right (by linarith : 6 * u ≤ 0.0001) (mul_nonneg hu.le hAy0)
        linarith
      have e : Dy - (Myb - Mya) = (Dy - (myb - mya)) + ((myb - mya) - (Myb - Mya)) := by ring
      rw [e]
      have := abs_add_le (Dy - (myb - mya)) ((myb - mya) - (Myb - Mya))
      linarith
    -- the increment's error
    have hnbh : (nb : ℝ) ≤ n * h := by
      rw [hnh]
      have := mul_le_mul_of_nonneg_right hna1 (by linarith : (0 : ℝ) ≤ nb)
      linarith only [this]
    have hntx : n * tiny ≤ Aa + Ab := by
      have e : n * tiny = na * tiny + nb * tiny := by rw [hn]; ring
      have := sa.Axt; have := sb.Axt; linarith only [e, this, sa.Axt]
    have hnty : n * tiny ≤ Aya + Ayb := by
      have e : n * tiny = na * tiny + nb * tiny := by rw [hn]; ring
      have := sa.Ayt; have := sb.Ayt; linarith only [e, this, sa.Ayt]
    have hn2 : 2 ≤ n := by rw [hn]; linarith only [hna1, hnb1]
    have h2t : 2 * tiny ≤ n * tiny := mul_le_mul_of_nonneg_right hn2 htn.le
    have h2tx : 2 * tiny ≤ Aa + Ab := by linarith only [h2t, hntx]
    have h2ty : 2 * tiny ≤ Aya + Ayb := by linarith only [h2t, hnty]
    have hnbt' : (nb : ℝ) * tiny ≤ h * (Aa + Ab) := by
      have e : h * (n * tiny) = na * nb * tiny := by rw [← mul_assoc, mul_comm h n, hnh]
      have k := mul_le_mul_of_nonneg_left hntx hh0
      have k2 := mul_le_mul_of_nonneg_right hna1 (by positivity : (0 : ℝ) ≤ nb * tiny)
      linarith only [e, k, k2]
    have htA : tiny ≤ h * (Aa + Ab) := by
      have := mul_le_mul_of_nonneg_right hh2 hA0
      linarith only [this, h2tx]
    have hP : (nb : ℝ) * |mxa + p| ≤ 1.02 * (Aa + Ab) * w := by
      have e : (nb : ℝ) * |mxa + p| = w * (n * |mxa + p|) := by rw [← hwn]; ring
      rw [e]; have := mul_le_mul_of_nonneg_left hnmp hw0'; linarith
    have hET := sg_cov_ET (n := n) (P := |mxa + p|) hh0 hw0' hw1 hwh hnbh hn0.le hnu hA0 hAy0
      hnbt' htA h2tx h2ty hP rfl hT1 hDDx hDDy
    -- the sum
    have hSS : |Shb + T| ≤ 2 ^ 902 := by
      have := abs_add_le Shb T
      have := abs_sub_abs_le_abs_sub Shb Cb
      have := sb.com; have := sb.Eb; have := sb.Cb
      linarith
    obtain ⟨e1, hS1b⟩ := M.err_le (z := Shb + T) (B := 2 ^ 902) hSS (by norm_num) (by norm_num)
    set Sh1 := M.fl (Shb + T) with hSh1
    have hSS2 : |Sha + Sh1| ≤ 2 ^ 904 := by
      have := abs_add_le Sha Sh1
      have := abs_sub_abs_le_abs_sub Sha Ca
      have := sa.com; have := sa.Eb; have := sa.Cb
      linarith
    obtain ⟨e2, -⟩ := M.err_le (z := Sha + Sh1) (B := 2 ^ 904) hSS2 (by norm_num) (by norm_num)
    have hc := sg_assemble2 (ΔC := (Mxb - Mxa) * (Myb - Mya) * h) sa.com sb.com le_rfl e1 e2
    -- in the spec's terms
    have eX : |Mxb - Mxa| = |Mxa - Mxb| := abs_sub_comm _ _
    have eY : |Myb - Mya| = |Mya - Myb| := abs_sub_comm _ _
    have eC : (Mxb - Mxa) * (Myb - Mya) * h = (Mxa - Mxb) * (Mya - Myb) * h := by ring
    have hΔC : |(Mxb - Mxa) * (Myb - Mya) * h| = h * (|Mxa - Mxb| * |Mya - Myb|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hh0, eX, eY]; ring
    rw [hΔC] at hc
    rw [eX, eY] at hET
    have hYR : h * (|Mxa - Mxb| * |Mya - Myb|) ≤ R := hY
    have hnew := sg_cov_new hn0.le hh0 hA0 hAy0 (abs_nonneg _) (abs_nonneg _) hR1 hYR hET
    rw [← eC]
    linarith only [hc, hnew]

/-! ## The two-pass block of pairs -/

/-- A product of two rounded differences, rounded (`prod_step`) or fused into
its addition: within `3.02 u |a||b| + 1.02 u·tiny (|a| + |b|) + 1.01 u·tiny` of
`a b`. -/
theorem StdModel.prod_step_or {a b w : ℝ} (ha : |a| ≤ 2 ^ 450) (hb : |b| ≤ 2 ^ 450)
    (hw : w = M.fl (M.fl a * M.fl b) ∨ w = M.fl a * M.fl b) :
    |w - a * b| ≤ 3.02 * u * (|a| * |b|) + 1.02 * u * tiny * (|a| + |b|) + 1.01 * u * tiny := by
  obtain ⟨hu, hu', ht, -, hmax⟩ := fpFacts
  have hA := abs_nonneg a
  have hB := abs_nonneg b
  have p1 : 0 ≤ u * (|a| * |b|) := by positivity
  have p2 : 0 ≤ u * tiny * (|a| + |b|) := by positivity
  rcases hw with rfl | rfl
  · have := M.prod_step ha hb
    have e : 1.01 * u * (tiny * |a| + tiny * |b|) = 1.01 * (u * tiny * (|a| + |b|)) := by ring
    linarith
  · have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
    have ea := M.err a (by linarith)
    have eb := M.err b (by linarith)
    have hfb : |M.fl b| ≤ |b| + u * (|b| + tiny) := by
      have := abs_sub_abs_le_abs_sub (M.fl b) b; linarith
    have e : M.fl a * M.fl b - a * b = (M.fl a - a) * M.fl b + a * (M.fl b - b) := by ring
    rw [e]
    have := abs_add_le ((M.fl a - a) * M.fl b) (a * (M.fl b - b))
    rw [abs_mul, abs_mul] at this
    have k1 := mul_le_mul ea hfb (abs_nonneg _) (by positivity)
    have k2 := mul_le_mul_of_nonneg_left eb hA
    have hu2 : u * u ≤ u / 2 ^ 53 := by nlinarith
    have q : u * (|a| + tiny) * (|b| + u * (|b| + tiny)) + |a| * (u * (|b| + tiny))
        ≤ 3.02 * u * (|a| * |b|) + 1.02 * u * tiny * (|a| + |b|) + 1.01 * u * tiny := by
      have e2 : u * (|a| + tiny) * (|b| + u * (|b| + tiny)) + |a| * (u * (|b| + tiny))
          = 2 * (u * (|a| * |b|)) + u * u * (|a| * |b|) + u * tiny * |b| + u * u * (tiny * |b|)
            + u * u * (|a| * tiny) + u * u * (tiny * tiny) + u * tiny * |a| := by ring
      have r1 := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ |a| * |b|)
      have r2 := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ tiny * |b|)
      have r3 := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ |a| * tiny)
      have r4 := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ tiny * tiny)
      have tt : tiny * tiny ≤ tiny := by nlinarith
      have r5 := mul_le_mul_of_nonneg_left tt (by positivity : (0 : ℝ) ≤ u / 2 ^ 53)
      have : 0 ≤ u * tiny := by positivity
      nlinarith
    linarith

/-- The products of a block's rounded deviations from `a` and `b`, each
rounded or fused into its addition: their sum within
`3.02 u K + 1.02 u·tiny (T_x + T_y) + 1.01 n u·tiny` of the exact products'
sum, with `K = Σ |x − a| |y − b|` and `T_x = Σ |x − a|`. -/
theorem StdModel.cblock_prods {a b : ℝ} : ∀ {ps : List (ℝ × ℝ)} {ws : List ℝ},
    List.Forall₂ (fun p w => w = M.fl (M.fl (p.1 - a) * M.fl (p.2 - b))
      ∨ w = M.fl (p.1 - a) * M.fl (p.2 - b)) ps ws →
    (∀ p ∈ ps, |p.1 - a| ≤ 2 ^ 450 ∧ |p.2 - b| ≤ 2 ^ 450) →
    |ws.sum - (ps.map fun p => (p.1 - a) * (p.2 - b)).sum|
        ≤ 3.02 * u * (ps.map fun p => |p.1 - a| * |p.2 - b|).sum
          + 1.02 * u * tiny * ((ps.map fun p => |p.1 - a|).sum + (ps.map fun p => |p.2 - b|).sum)
          + 1.01 * u * tiny * ps.length
      ∧ (ws.map abs).sum ≤ (1 + 3.02 * u) * (ps.map fun p => |p.1 - a| * |p.2 - b|).sum
          + 1.02 * u * tiny * ((ps.map fun p => |p.1 - a|).sum + (ps.map fun p => |p.2 - b|).sum)
          + 1.01 * u * tiny * ps.length
      ∧ ∀ w ∈ ws, |w| ≤ 2 ^ 901 := by
  intro ps ws h
  induction h with
  | nil => intro _; simp
  | @cons p w ps ws hpw _ ih =>
    intro hb
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun q hq => hb q (by simp [hq]))
    obtain ⟨ha, hb'⟩ := hb p (by simp)
    have k := M.prod_step_or ha hb' hpw
    have hk2 : |w| ≤ |p.1 - a| * |p.2 - b| + (3.02 * u * (|p.1 - a| * |p.2 - b|)
        + 1.02 * u * tiny * (|p.1 - a| + |p.2 - b|) + 1.01 * u * tiny) := by
      have := abs_sub_abs_le_abs_sub w ((p.1 - a) * (p.2 - b))
      rw [abs_mul] at this; linarith
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      have e : w + ws.sum - ((p.1 - a) * (p.2 - b) + (ps.map fun p => (p.1 - a) * (p.2 - b)).sum)
          = (w - (p.1 - a) * (p.2 - b))
            + (ws.sum - (ps.map fun p => (p.1 - a) * (p.2 - b)).sum) := by ring
      rw [e]
      have := abs_add_le (w - (p.1 - a) * (p.2 - b))
        (ws.sum - (ps.map fun p => (p.1 - a) * (p.2 - b)).sum)
      linarith
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · obtain ⟨hu, hu', ht, ht1, -⟩ := fpFacts
        have hA := abs_nonneg (p.1 - a)
        have hB := abs_nonneg (p.2 - b)
        have hab : |p.1 - a| * |p.2 - b| ≤ 2 ^ 900 := by
          have := mul_le_mul ha hb' hB (by norm_num)
          have e : (2 : ℝ) ^ 450 * 2 ^ 450 = 2 ^ 900 := by norm_num
          linarith
        have q1 : 3.02 * u * (|p.1 - a| * |p.2 - b|) ≤ 2 ^ 899 := by
          have := mul_le_mul (by linarith : 3.02 * u ≤ 3.02 * (1 / 2 ^ 53)) hab (by positivity)
            (by norm_num)
          have : (3.02 : ℝ) * (1 / 2 ^ 53) * 2 ^ 900 ≤ 2 ^ 899 := by norm_num
          linarith
        have q2 : 1.02 * u * tiny * (|p.1 - a| + |p.2 - b|) ≤ 1 := by
          have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
          have h1 : 1.02 * u * tiny ≤ 1.02 * (1 / 2 ^ 53) * (1 / 2 ^ 1022) :=
            mul_le_mul (by linarith) htt ht.le (by norm_num)
          have := mul_le_mul h1 (by linarith : |p.1 - a| + |p.2 - b| ≤ 2 ^ 451) (by positivity)
            (by norm_num)
          have : (1.02 : ℝ) * (1 / 2 ^ 53) * (1 / 2 ^ 1022) * 2 ^ 451 ≤ 1 := by norm_num
          linarith
        have q3 : 1.01 * u * tiny ≤ 1 := by
          have := mul_le_mul (by linarith : 1.01 * u ≤ 1) ht1 ht.le (by norm_num); linarith
        have : (2 : ℝ) ^ 900 + 2 ^ 899 + 1 + 1 ≤ 2 ^ 901 := by norm_num
        linarith
      · exact ih3 z hz

/-- `T ≤ √(n S) + n |ε|` from `T² ≤ n (S + n ε²)`. -/
theorem abs_dev_sum_le {n T S ε : ℝ} (hn : 0 ≤ n) (_hT0 : 0 ≤ T) (hS : 0 ≤ S)
    (hT : T ^ 2 ≤ n * (S + n * ε ^ 2)) : T ≤ √(n * S) + n * |ε| := by
  have h1 := Real.sq_sqrt (mul_nonneg hn hS)
  have h2 : 0 ≤ √(n * S) * (n * |ε|) := by positivity
  have e : (√(n * S) + n * |ε|) ^ 2 = n * S + 2 * (√(n * S) * (n * |ε|)) + n ^ 2 * ε ^ 2 := by
    rw [add_sq, h1, mul_pow, sq_abs]; ring
  have h3 : n * (S + n * ε ^ 2) ≤ (√(n * S) + n * |ε|) ^ 2 := by rw [e]; nlinarith
  exact (abs_le_of_sq_le_sq' (le_trans hT h3) (by positivity)).2

/-- The arithmetic at the end of `cInvC_block`: a pair block's errors in
`cBoundC CConst.sg`, with `AD = A_x D_y + A_y D_x` and `AA = A_x A_y`. -/
theorem cblock_arith {n g K TT X Y Z R AD AA t L : ℝ} (hn1 : 1 ≤ n) (hn : n ≤ 128) (hR : 0 ≤ R)
    (hAD : 0 ≤ AD) (hAA : 0 ≤ AA) (ht : 0 ≤ t) (hK0 : 0 ≤ K) (hTT0 : 0 ≤ TT)
    (hK : K ≤ R + 3.02 * u * AD + 9.13 * n * u ^ 2 * AA) (hTT : TT ≤ AD + 6.04 * u * AA)
    (hg : g ≤ 1.01 * n * u)
    (hX : X ≤ g * ((1 + 3.02 * u) * K + 1.02 * u * TT + 1.01 * u * t * n + n * t))
    (hY : Y ≤ 3.02 * u * K + 1.02 * u * TT + 1.01 * u * t * n) (hZ : Z ≤ 9.13 * n * u ^ 2 * AA)
    (hL : 2 * n ≤ L) (hLt : n * (1.02 * n + 4) ≤ 12 * L) :
    X + Y + Z ≤ (1 + 3 * n * u) * (13 * u * AD + 10 * u * n * R + 60 * u ^ 2 * L * AA
      + 12 * u * t * L) := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hn0 : 0 ≤ n := by linarith
  have hnu : n * u ≤ 1 / 2 ^ 46 := by
    have := mul_le_mul hn hu' hu.le (by norm_num)
    have e : (128 : ℝ) * (1 / 2 ^ 53) = 1 / 2 ^ 46 := by norm_num
    linarith
  -- the factor of the tree's error
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = (1 + 3.02 * u) * K + 1.02 * u * TT + 1.01 * u * t * n + n * t :=
    ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQd]; positivity
  have hQ : Q ≤ 1.01 * R + 4.1 * u * AD + 16 * n * u ^ 2 * AA + 1.001 * n * t := by
    have a1 : (1 + 3.02 * u) * K ≤ 1.01 * K :=
      mul_le_mul_of_nonneg_right (by linarith) hK0
    have a2 := mul_le_mul_of_nonneg_left hTT (by positivity : (0 : ℝ) ≤ 1.02 * u)
    have a3 : u * (t * n) ≤ 1 / 2 ^ 53 * (t * n) := mul_le_mul_of_nonneg_right hu' (by positivity)
    have a4 : u ^ 2 * AA ≤ n * (u ^ 2 * AA) := le_mul_of_one_le_left (by positivity) hn1
    have a5 : 0 ≤ t * n := by positivity
    have a6 : 0 ≤ u * AD := by positivity
    have a7 : 0 ≤ n * u ^ 2 * AA := by positivity
    rw [hQd]; linarith
  have hgQ : g * Q ≤ 1.01 * n * u * (1.01 * R + 4.1 * u * AD + 16 * n * u ^ 2 * AA + 1.001 * n * t) :=
    mul_le_mul_of_nonneg_right hg hQ0 |>.trans (mul_le_mul_of_nonneg_left hQ (by positivity))
  rw [← hQd] at hX
  -- the small products
  have p1 : u * (u * AD) ≤ 1 / 2 ^ 53 * (u * AD) := mul_le_mul_of_nonneg_right hu' (by positivity)
  have p2 : u * (n * u ^ 2 * AA) ≤ 1 / 2 ^ 53 * (n * u ^ 2 * AA) :=
    mul_le_mul_of_nonneg_right hu' (by positivity)
  have p3 : n * u * (u * AD) ≤ 1 / 2 ^ 46 * (u * AD) := mul_le_mul_of_nonneg_right hnu (by positivity)
  have p4 : n * u * (n * u ^ 2 * AA) ≤ 1 / 2 ^ 46 * (n * u ^ 2 * AA) :=
    mul_le_mul_of_nonneg_right hnu (by positivity)
  have p5 := mul_le_mul_of_nonneg_left hK hu.le
  have p6 := mul_le_mul_of_nonneg_left hTT hu.le
  have p7 : u * R ≤ n * (u * R) := le_mul_of_one_le_left (by positivity) hn1
  have p8 : u ^ 2 * AA ≤ n * (u ^ 2 * AA) := le_mul_of_one_le_left (by positivity) hn1
  have p9 := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ u ^ 2 * AA)
  have p10 := mul_le_mul_of_nonneg_right hLt (by positivity : (0 : ℝ) ≤ u * t)
  have p11 : 0 ≤ n * (n * (u * t)) := by positivity
  have p12 : 0 ≤ n * (u * t) := by positivity
  have p13 : 0 ≤ u * AD := by positivity
  have p14 : 0 ≤ n * u ^ 2 * AA := by positivity
  have p15 : 0 ≤ n * (u * R) := by positivity
  have hT0 : 0 ≤ 13 * u * AD + 10 * u * n * R + 60 * u ^ 2 * L * AA + 12 * u * t * L := by
    have : 0 ≤ L := by linarith
    positivity
  have hT1 : 13 * u * AD + 10 * u * n * R + 60 * u ^ 2 * L * AA + 12 * u * t * L
      ≤ (1 + 3 * n * u) * (13 * u * AD + 10 * u * n * R + 60 * u ^ 2 * L * AA + 12 * u * t * L) :=
    le_mul_of_one_le_left hT0 (by have : 0 ≤ 3 * n * u := by positivity
                                  linarith)
  linarith only [hX, hgQ, hY, hZ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, hT1]

/-- The states Polars's two-pass block of pairs (`CovState::new`) can give over
`ps`, at most 128 of them: the means `fl(s / n)` of sums `s` of each column in
any order and tree, and the co-moment, a sum in any order and tree of the
products of the rounded deviations, each rounded or fused into its addition. -/
def StdModel.CBlock (ps : List (ℝ × ℝ)) (s : WState) : Prop :=
  ps ≠ [] ∧ ps.length ≤ 128 ∧ ∃ s1x s1y ws sc,
    (∃ ys, ys.Perm (ps.map Prod.fst) ∧ M.toRnd.Tree ys s1x) ∧
    (∃ ys, ys.Perm (ps.map Prod.snd) ∧ M.toRnd.Tree ys s1y) ∧
    List.Forall₂ (fun p w =>
      w = M.fl (M.fl (p.1 - M.fl (s1x / ps.length)) * M.fl (p.2 - M.fl (s1y / ps.length)))
        ∨ w = M.fl (p.1 - M.fl (s1x / ps.length)) * M.fl (p.2 - M.fl (s1y / ps.length))) ps ws ∧
    (∃ ys, ys.Perm ws ∧ M.toRnd.Tree ys sc) ∧
    s = ⟨ps.length, M.fl (s1x / ps.length), M.fl (s1y / ps.length), sc⟩

set_option maxHeartbeats 2000000 in
/-- **A two-pass block of pairs meets the covariance invariant** at
Schubert and Gertz's constants, with `D_x = √(n S_xx)`. -/
theorem StdModel.cInvC_block {ps : List (ℝ × ℝ)} {s : WState} (h : M.CBlock ps s)
    (hB : Bounded (2 ^ 399) ps) : CInvC CConst.sg ps s := by
  obtain ⟨hne, h128, s1x, s1y, ws, sc, tx, ty, hw, ⟨ys2, hp2, t2⟩, rfl⟩ := h
  obtain ⟨hu, hu', ht, ht1, hmax⟩ := fpFacts
  have hN : ps.length ≤ 2 ^ 32 := by omega
  obtain ⟨⟨hAx0, hAxb, hntx, -, hmxb, hSx0, -⟩, ⟨hAy0, hAyb, hnty, -, hmyb, hSy0, -⟩⟩ :=
    pair_facts hne hN hB
  -- the means
  have hεx : |M.fl (s1x / ps.length) - mx ps| ≤ 3.02 * u * mag (ps.map Prod.fst) := by
    have h := M.block_mean (xs := ps.map Prod.fst) (by simpa using hne) (by simpa using h128)
      (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).1) tx
    have e : (ps.map Prod.fst).sum / (ps.length : ℝ) = mx ps := by simp [mx, sx]
    rw [List.length_map, e] at h
    exact h
  have hεy : |M.fl (s1y / ps.length) - my ps| ≤ 3.02 * u * mag (ps.map Prod.snd) := by
    have h := M.block_mean (xs := ps.map Prod.snd) (by simpa using hne) (by simpa using h128)
      (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).2) ty
    have e : (ps.map Prod.snd).sum / (ps.length : ℝ) = my ps := by simp [my, sy]
    rw [List.length_map, e] at h
    exact h
  set mhx := M.fl (s1x / ps.length) with hmhx_def
  set mhy := M.fl (s1y / ps.length) with hmhy_def
  -- names
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ps.length := ⟨_, rfl⟩
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast List.length_pos_iff.mpr hne
  have hn0 : 0 ≤ n := by linarith
  have hn128 : n ≤ 128 := by rw [hn]; exact_mod_cast h128
  have hnu : n * u ≤ 1 / 2 ^ 21 := by
    calc n * u ≤ 128 * (1 / 2 ^ 53) := mul_le_mul hn128 hu' hu.le (by norm_num)
      _ ≤ 1 / 2 ^ 21 := by norm_num
  obtain ⟨Ax, hAx⟩ : ∃ A, A = mag (ps.map Prod.fst) := ⟨_, rfl⟩
  obtain ⟨Ay, hAy⟩ : ∃ A, A = mag (ps.map Prod.snd) := ⟨_, rfl⟩
  obtain ⟨Sx, hSx⟩ : ∃ S, S = comoment (dupL (ps.map Prod.fst)) := ⟨_, rfl⟩
  obtain ⟨Sy, hSy⟩ : ∃ S, S = comoment (dupL (ps.map Prod.snd)) := ⟨_, rfl⟩
  rw [← hAx] at hεx hAx0 hAxb hntx
  rw [← hAy] at hεy hAy0 hAyb hnty
  rw [← hSx] at hSx0
  rw [← hSy] at hSy0
  rw [← hn] at hntx hnty
  have hnt : tiny ≤ n * tiny := le_mul_of_one_le_left ht.le hn1
  have htAx : tiny ≤ Ax := le_trans hnt hntx
  have htAy : tiny ≤ Ay := le_trans hnt hnty
  -- the weight
  have hL2 : 2 * n ≤ Lw ps.length := by rw [hn]; exact Lw_two _
  have hLt : n * (1.02 * n + 4) ≤ 12 * Lw ps.length := by
    have := block_tiny h128
    rw [hn]; unfold Lw
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ ps.length)
    linarith
  refine ⟨rfl, ?_, ?_, √(n * Sx), √(n * Sy), Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · show |mhx - mx ps| ≤ 6 * u * mag (ps.map Prod.fst)
    rw [← hAx]; have := mul_nonneg hu.le hAx0; linarith
  · show |mhy - my ps| ≤ 6 * u * mag (ps.map Prod.snd)
    rw [← hAy]; have := mul_nonneg hu.le hAy0; linarith
  · rw [Real.sq_sqrt (by positivity), ← hSx]
    exact mul_le_mul_of_nonneg_right (by linarith) hSx0
  · rw [Real.sq_sqrt (by positivity), ← hSy]
    exact mul_le_mul_of_nonneg_right (by linarith) hSy0
  show |sc - comoment ps| ≤ cBoundC CConst.sg ps.length (mag (ps.map Prod.fst))
    (mag (ps.map Prod.snd)) (√(n * Sx)) (√(n * Sy))
    (√(comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd)))) (Lw ps.length)
  rw [← hAx, ← hAy, ← hSx, ← hSy]
  -- the deviations
  obtain ⟨εx, hεx'⟩ : ∃ e, e = mhx - mx ps := ⟨_, rfl⟩
  obtain ⟨εy, hεy'⟩ : ∃ e, e = mhy - my ps := ⟨_, rfl⟩
  rw [← hεx'] at hεx
  rw [← hεy'] at hεy
  have hmhx : |mhx| ≤ 2 ^ 401 := by
    have h1 : u * Ax ≤ 1 / 2 ^ 53 * 2 ^ 432 := mul_le_mul hu' hAxb hAx0 (by norm_num)
    have h2 : (3.02 : ℝ) * (1 / 2 ^ 53 * 2 ^ 432) + 2 ^ 400 ≤ 2 ^ 401 := by norm_num
    have : mhx = mx ps + εx := by rw [hεx']; ring
    rw [this]; have := abs_add_le (mx ps) εx; linarith
  have hmhy : |mhy| ≤ 2 ^ 401 := by
    have h1 : u * Ay ≤ 1 / 2 ^ 53 * 2 ^ 432 := mul_le_mul hu' hAyb hAy0 (by norm_num)
    have h2 : (3.02 : ℝ) * (1 / 2 ^ 53 * 2 ^ 432) + 2 ^ 400 ≤ 2 ^ 401 := by norm_num
    have : mhy = my ps + εy := by rw [hεy']; ring
    rw [this]; have := abs_add_le (my ps) εy; linarith
  have hdx : ∀ p ∈ ps, |p.1 - mhx| ≤ 2 ^ 450 := by
    intro p hp; have := abs_sub p.1 mhx; have := (hB p hp).1; linarith
  have hdy : ∀ p ∈ ps, |p.2 - mhy| ≤ 2 ^ 450 := by
    intro p hp; have := abs_sub p.2 mhy; have := (hB p hp).2; linarith
  -- the exact sums
  have hsg : (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum = comoment ps + n * εx * εy := by
    rw [sum_dev_shift hne, hn, hεx', hεy']
  have hZx : (ps.map fun p => (p.1 - mhx) * (p.1 - mhx)).sum = Sx + n * εx ^ 2 := by
    rw [sum_sq_dev_fst hne, hSx, hn, hεx']
  have hZy : (ps.map fun p => (p.2 - mhy) * (p.2 - mhy)).sum = Sy + n * εy ^ 2 := by
    rw [sum_sq_dev_snd hne, hSy, hn, hεy']
  -- `K = Σ |d_x| |d_y|`, `T_x = Σ |d_x|`
  obtain ⟨K, hK⟩ : ∃ K, K = (ps.map fun p => |p.1 - mhx| * |p.2 - mhy|).sum := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hK2 : K ^ 2 ≤ (Sx + n * εx ^ 2) * (Sy + n * εy ^ 2) := by
    have h := list_cs (ps.map fun p => (|p.1 - mhx|, |p.2 - mhy|))
    simp only [List.map_map, Function.comp_def, abs_mul_abs_self] at h
    rw [hK, ← hZx, ← hZy]; exact h
  obtain ⟨Tx, hTx⟩ : ∃ T, T = (ps.map fun p => |p.1 - mhx|).sum := ⟨_, rfl⟩
  obtain ⟨Ty, hTy⟩ : ∃ T, T = (ps.map fun p => |p.2 - mhy|).sum := ⟨_, rfl⟩
  have hTx2 : Tx ^ 2 ≤ n * (Sx + n * εx ^ 2) := by
    have h := sq_abs_sum_le (ps.map fun p => p.1 - mhx)
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [← hn] at h
    rw [hTx, ← hZx]
    have e : (ps.map fun p => (p.1 - mhx) * (p.1 - mhx)) = ps.map fun p => (p.1 - mhx) ^ 2 := by
      congr 1; funext p; ring
    rw [e]; exact h
  have hTy2 : Ty ^ 2 ≤ n * (Sy + n * εy ^ 2) := by
    have h := sq_abs_sum_le (ps.map fun p => p.2 - mhy)
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [← hn] at h
    rw [hTy, ← hZy]
    have e : (ps.map fun p => (p.2 - mhy) * (p.2 - mhy)) = ps.map fun p => (p.2 - mhy) ^ 2 := by
      congr 1; funext p; ring
    rw [e]; exact h
  have hTx0 : 0 ≤ Tx := by
    rw [hTx]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hTy0 : 0 ≤ Ty := by
    rw [hTy]; exact List.sum_nonneg (fun y hy => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy; positivity)
  -- `K ≤ R + 3.02 u (A_x D_y + A_y D_x) + 9.13 n u² A_x A_y`
  have hKb := K_le hK0 hSx0 hSy0 (by positivity) (by positivity) hK2
  obtain ⟨r, hr⟩ : ∃ r, r = √n := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hrr : r * r = n := by rw [hr]; exact Real.mul_self_sqrt hn0
  have e1 : √(n * εx ^ 2) = r * |εx| := by rw [Real.sqrt_mul hn0, Real.sqrt_sq_eq_abs, hr]
  have e2 : √(n * εy ^ 2) = r * |εy| := by rw [Real.sqrt_mul hn0, Real.sqrt_sq_eq_abs, hr]
  have eDx : √(n * Sx) = r * √Sx := by rw [Real.sqrt_mul hn0, hr]
  have eDy : √(n * Sy) = r * √Sy := by rw [Real.sqrt_mul hn0, hr]
  have eR : √(Sx * Sy) = √Sx * √Sy := Real.sqrt_mul hSx0 _
  rw [e1, e2] at hKb
  have hDx0 : 0 ≤ √(n * Sx) := Real.sqrt_nonneg _
  have hDy0 : 0 ≤ √(n * Sy) := Real.sqrt_nonneg _
  have hεε : |εx| * |εy| ≤ 9.13 * u ^ 2 * (Ax * Ay) := by
    have := mul_le_mul hεx hεy (abs_nonneg _) (by positivity)
    have : 0 ≤ u ^ 2 * (Ax * Ay) := by positivity
    have e : 3.02 * u * Ax * (3.02 * u * Ay) = 9.1204 * (u ^ 2 * (Ax * Ay)) := by ring
    linarith
  have hKR : K ≤ √(Sx * Sy) + 3.02 * u * (Ax * √(n * Sy) + Ay * √(n * Sx))
      + 9.13 * n * u ^ 2 * (Ax * Ay) := by
    have k1 := mul_le_mul_of_nonneg_right hεy hDx0
    have k2 := mul_le_mul_of_nonneg_right hεx hDy0
    have k3 := mul_le_mul_of_nonneg_left hεε hn0
    have e : (√Sx + r * |εx|) * (√Sy + r * |εy|)
        = √Sx * √Sy + |εy| * (r * √Sx) + |εx| * (r * √Sy) + (r * r) * (|εx| * |εy|) := by ring
    rw [e, hrr, ← eDx, ← eDy, ← eR] at hKb
    linarith only [hKb, k1, k2, k3]
  -- `tiny (T_x + T_y) ≤ A_x D_y + A_y D_x + 6.04 u A_x A_y`
  have hTT : tiny * Tx + tiny * Ty ≤ (Ax * √(n * Sy) + Ay * √(n * Sx)) + 6.04 * u * (Ax * Ay) := by
    have a1 := abs_dev_sum_le hn0 hTx0 hSx0 hTx2
    have a2 := abs_dev_sum_le hn0 hTy0 hSy0 hTy2
    have b1 := mul_le_mul_of_nonneg_left a1 ht.le
    have b2 := mul_le_mul_of_nonneg_left a2 ht.le
    have c1 := mul_le_mul_of_nonneg_right htAy hDx0
    have c2 := mul_le_mul_of_nonneg_right htAx hDy0
    have d1 : n * tiny * |εx| ≤ Ay * (3.02 * u * Ax) := mul_le_mul hnty hεx (abs_nonneg _) hAy0
    have d2 : n * tiny * |εy| ≤ Ax * (3.02 * u * Ay) := mul_le_mul hntx hεy (abs_nonneg _) hAx0
    linarith only [b1, b2, c1, c2, d1, d2]
  -- the rounded products
  obtain ⟨hW, hWa, hWb⟩ := M.cblock_prods hw (fun p hp => ⟨hdx p hp, hdy p hp⟩)
  rw [← hK, ← hTx, ← hTy, ← hn] at hW hWa
  have hlen : ws.length = ps.length := hw.length_eq.symm
  have hmagw : mag ws = (ws.map abs).sum + n * tiny := by rw [mag_eq, hlen, hn]
  have hmagb : mag ws ≤ 2 ^ 7 * (2 ^ 901 + 1) := by
    have := mag_le_of_bound hWb
    rw [hlen, ← hn] at this
    have : n * (2 ^ 901 + tiny) ≤ 2 ^ 7 * (2 ^ 901 + 1) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    linarith
  have hg := gamma_le_101 (n := ps.length) (by rw [← hn]; exact hnu)
  have hg0 : 0 ≤ gamma ps.length := gamma_nonneg (by rw [← hn]; linarith)
  rw [← hn] at hg
  have hov : (1 + gamma ws.length) * mag ws ≤ maxFinite := by
    rw [hlen]
    have h1 : 1 + gamma ps.length ≤ 2 := by
      have : (1.01 : ℝ) * n * u ≤ 1 := by linarith
      linarith
    have := mul_le_mul h1 hmagb (mag_nonneg _) (by norm_num)
    have : (2 : ℝ) * (2 ^ 7 * (2 ^ 901 + 1)) ≤ 2 ^ 1023 := by norm_num
    linarith
  have hs2 : |sc - ws.sum| ≤ gamma ps.length * mag ws := by
    have := (t2.error (by rw [hp2.length_eq, hlen, ← hn]; linarith)
      (by rw [hp2.length_eq, M.toRnd.mag_perm hp2]; exact hov)).perm hp2
    have e : M.toRnd.Near ws sc = (|sc - ws.sum| ≤ gamma ws.length * mag ws) := rfl
    rw [e, hlen] at this
    exact this
  have hX : |sc - ws.sum| ≤ gamma ps.length * ((1 + 3.02 * u) * K + 1.02 * u * (tiny * Tx + tiny * Ty)
      + 1.01 * u * tiny * n + n * tiny) := by
    refine le_trans hs2 (mul_le_mul_of_nonneg_left ?_ hg0)
    rw [hmagw]; linarith only [hWa]
  have hY : |ws.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum|
      ≤ 3.02 * u * K + 1.02 * u * (tiny * Tx + tiny * Ty) + 1.01 * u * tiny * n := by
    linarith only [hW]
  have hZ : |(ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps|
      ≤ 9.13 * n * u ^ 2 * (Ax * Ay) := by
    rw [hsg, show comoment ps + n * εx * εy - comoment ps = n * (εx * εy) by ring, abs_mul,
      abs_of_nonneg hn0, abs_mul]
    have := mul_le_mul_of_nonneg_left hεε hn0
    linarith
  have hsum : |sc - comoment ps| ≤ |sc - ws.sum|
      + |ws.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum|
      + |(ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps| := by
    have e : sc - comoment ps = (sc - ws.sum)
        + (ws.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum)
        + ((ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum - comoment ps) := by ring
    rw [e]
    have := abs_add_le (sc - ws.sum) (ws.sum - (ps.map fun p => (p.1 - mhx) * (p.2 - mhy)).sum)
    exact le_trans (abs_add_le _ _) (by linarith)
  have key := cblock_arith hn1 hn128 (Real.sqrt_nonneg _) (by positivity) (by positivity) ht.le
    hK0 (by positivity) hKR hTT hg hX hY hZ hL2 hLt
  unfold cBoundC
  rw [← hn, show CConst.sg.ad = 13 from rfl]
  linarith only [hsum, key]

/-! ## Polars's plans of pairs -/

theorem cBoundC_nonneg {C : CConst} {n Ax Ay Dx Dy R L : ℝ} (hn : 0 ≤ n) (hAx : 0 ≤ Ax)
    (hAy : 0 ≤ Ay) (hDx : 0 ≤ Dx) (hDy : 0 ≤ Dy) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    0 ≤ cBoundC C n Ax Ay Dx Dy R L := by
  have hu := u_pos
  have ht := tiny_pos
  have had : 0 ≤ C.ad := le_trans C.nad0 C.nad_le
  unfold cBoundC
  have : 0 ≤ C.ad * u * (Ax * Dy + Ay * Dx) := by positivity
  positivity

/-- One pair's state, `(1, x, y, 0)`, meets the invariant at any constants. -/
theorem cInvC_one (C : CConst) (p : ℝ × ℝ) : CInvC C [p] ⟨1, p.1, p.2, 0⟩ := by
  obtain ⟨x, y⟩ := p
  have hmx : mx [(x, y)] = x := by simp [mx, sx]
  have hmy : my [(x, y)] = y := by simp [my, sy]
  have hc : comoment [(x, y)] = 0 := by simp [comoment, mx, my, sx, sy]
  have hcx : comoment (dupL ([(x, y)].map Prod.fst)) = 0 := by
    simp [comoment, dupL, mx, my, sx, sy]
  have hcy : comoment (dupL ([(x, y)].map Prod.snd)) = 0 := by
    simp [comoment, dupL, mx, my, sx, sy]
  refine ⟨rfl, ?_, ?_, 0, 0, le_rfl, le_rfl, ?_, ?_, ?_⟩
  · show |x - mx [(x, y)]| ≤ _
    simp only [hmx, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) u_pos.le) (mag_nonneg _)
  · show |y - my [(x, y)]| ≤ _
    simp only [hmy, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) u_pos.le) (mag_nonneg _)
  · rw [hcx]; simp
  · rw [hcy]; simp
  · show |0 - comoment [(x, y)]| ≤ _
    rw [hc, sub_self, abs_zero]
    exact cBoundC_nonneg (by positivity) (mag_nonneg _) (mag_nonneg _) le_rfl le_rfl
      (Real.sqrt_nonneg _) (Lw_nonneg _)

/-- The states Polars's `cov` computes over the pairs `ps`, in any order and
any tree: a two-pass block (ungrouped, `CovState::new`), one pair, or a merge
of two of them (`CovState::combine`). A grouped `insert_one` is the merge
with one pair's state. -/
inductive StdModel.PCRun (M : StdModel) : List (ℝ × ℝ) → WState → Prop
  | one (p : ℝ × ℝ) : StdModel.PCRun M [p] ⟨1, p.1, p.2, 0⟩
  | block {ps : List (ℝ × ℝ)} {s : WState} : M.CBlock ps s → StdModel.PCRun M ps s
  | merge {pa pb : List (ℝ × ℝ)} {t s : WState} : StdModel.PCRun M pa t →
      StdModel.PCRun M pb s → StdModel.PCRun M (pa ++ pb) (M.sgCov t s)

theorem StdModel.PCRun.count {ps : List (ℝ × ℝ)} {s : WState} (h : M.PCRun ps s) :
    s.n = ps.length ∧ ps ≠ [] := by
  induction h with
  | one p => simp
  | block hb => obtain ⟨hne, -, -, -, -, -, -, -, -, -, rfl⟩ := hb; exact ⟨rfl, hne⟩
  | @merge pa pb t s' _ _ iht ihs =>
    obtain ⟨h1, h2⟩ := iht
    obtain ⟨h3, h4⟩ := ihs
    refine ⟨?_, by simp [h2]⟩
    simp [StdModel.sgCov, h1, h3, h2, h4]

/-- **Every state Polars's `cov` computes meets the covariance invariant** at
Schubert and Gertz's constants, for `n ≤ 2³²` pairs of doubles at most `2³⁹⁹`
in magnitude. -/
theorem StdModel.cInvC_pcrun {ps : List (ℝ × ℝ)} {s : WState} (h : M.PCRun ps s) :
    ps.length ≤ 2 ^ 32 → Bounded (2 ^ 399) ps → CInvC CConst.sg ps s := by
  induction h with
  | one p => intro _ _; exact cInvC_one _ p
  | block hb => intro _ hB; exact M.cInvC_block hb hB
  | @merge pa pb t s' ha hb iht ihs =>
    intro hN hB
    rw [List.length_append] at hN
    have hBa := (Bounded.append.mp hB).1
    have hBb := (Bounded.append.mp hB).2
    exact cInv_merge_of M.sgCov_spec ha.count.2 hb.count.2 hN hBa hBb (iht (by omega) hBa)
      (ihs (by omega) hBb)

/-- **Polars's covariance, to first order in the spread**: for any plan of
blocks, pairs and merges over `n ≤ 2³²` pairs of doubles at most `2³⁹⁹` in
magnitude, the computed co-moment `Ĉ` is within
`106 n u (√(Q'_x S_yy) + √(Q'_y S_xx)) + 11 n u √(S_xx S_yy) + 3961 n² u² √(Q'_x Q'_y) + 793 n u · tiny`
of `C = Σ (x − x̄)(y − ȳ)`, where `Q'_x = Σ (|x| + tiny)²`, `Q'_y` likewise. -/
theorem StdModel.plCov_rel {ps : List (ℝ × ℝ)} {s : WState} (h : M.PCRun ps s)
    (hN : ps.length ≤ 2 ^ 32) (hB : Bounded (2 ^ 399) ps) :
    |s.c - comoment ps|
      ≤ 106 * ps.length * u
          * (√((ps.map fun p => (|p.1| + tiny) ^ 2).sum * comoment (dupL (ps.map Prod.snd)))
            + √((ps.map fun p => (|p.2| + tiny) ^ 2).sum * comoment (dupL (ps.map Prod.fst))))
        + 11 * ps.length * u
          * √(comoment (dupL (ps.map Prod.fst)) * comoment (dupL (ps.map Prod.snd)))
        + 3961 * ps.length ^ 2 * u ^ 2
          * √((ps.map fun p => (|p.1| + tiny) ^ 2).sum * (ps.map fun p => (|p.2| + tiny) ^ 2).sum)
        + 793 * ps.length * u * tiny := by
  have hc := covRel_of_cInvC (M.cInvC_pcrun h hN hB) h.count.2 hN
  have e : 8.14 * CConst.sg.ad = 105.82 := by norm_num [CConst.sg]
  rw [e] at hc
  obtain ⟨X, hX⟩ : ∃ X, X = √((ps.map fun p => (|p.1| + tiny) ^ 2).sum
      * comoment (dupL (ps.map Prod.snd)))
    + √((ps.map fun p => (|p.2| + tiny) ^ 2).sum * comoment (dupL (ps.map Prod.fst))) := ⟨_, rfl⟩
  rw [← hX] at hc ⊢
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have : 0 ≤ (ps.length : ℝ) * u * X := by have := u_pos; positivity
  have e1 : 105.82 * (ps.length : ℝ) * u * X = 105.82 * ((ps.length : ℝ) * u * X) := by ring
  have e2 : 106 * (ps.length : ℝ) * u * X = 106 * ((ps.length : ℝ) * u * X) := by ring
  rw [e2]; rw [e1] at hc
  linarith

/-- **Polars's `COVAR_*`**: `fl(Ĉ / d)` is within `covTolK 107` of `C / d`
(`StatTol.sg`), for witnesses `r₁ ≥ √(Q'_x S_yy)`, `r₂ ≥ √(Q'_y S_xx)`,
`r_s ≥ √(S_xx S_yy)`, `r_q ≥ √(Q'_x Q'_y)`. -/
theorem StdModel.core_cov_polars {ps : List (ℝ × ℝ)} {s : WState} (h : M.PCRun ps s)
    (hN : ps.length ≤ 2 ^ 32) (hB : Bounded (2 ^ 398) ps)
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ ps.length) {r1 r2 rs rq : ℝ}
    (h1 : √((ps.map fun p => (|p.1| + tiny) ^ 2).sum)
      * √(comoment (ps.map fun p => (p.2, p.2))) ≤ r1)
    (h2 : √((ps.map fun p => (|p.2| + tiny) ^ 2).sum)
      * √(comoment (ps.map fun p => (p.1, p.1))) ≤ r2)
    (hs : √(comoment (ps.map fun p => (p.1, p.1)))
      * √(comoment (ps.map fun p => (p.2, p.2))) ≤ rs)
    (hq : √((ps.map fun p => (|p.1| + tiny) ^ 2).sum)
      * √((ps.map fun p => (|p.2| + tiny) ^ 2).sum) ≤ rq) :
    |M.fl (s.c / d) - comoment ps / d| ≤ covTolK 107 ps.length d r1 r2 rs rq := by
  have hc := M.core_cov_of (k := 106) (by norm_num) (by norm_num) h.count.2 hN hB
    (M.plCov_rel h hN (fun p hp => ⟨le_trans (hB p hp).1 (by norm_num),
      le_trans (hB p hp).2 (by norm_num)⟩)) hd1 hdn h1 h2 hs hq
  have e : (106 : ℝ) + 1 = 107 := by norm_num
  rw [e] at hc
  exact hc

end FloatBounds
