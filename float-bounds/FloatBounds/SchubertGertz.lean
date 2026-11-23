module

public import FloatBounds.ChanCorr

/-!
# Polars's variance: two-pass blocks and Schubert and Gertz's merge (#1808)

Polars's `var` (py-2.1.0, `crates/polars-compute/src/moment.rs`) keeps the
state `(n, x̄, M₂)` of a variance as DuckDB's does, with other kernels:

* ungrouped, each run of at most 128 values is a two-pass block
  (`VarState::new`): the mean `fl(s / n)` of a sum `s` in any order, then the
  sum, in any order, of the squared deviations `fl(x − x̄)²`. `alg_sum_f64`
  adds with `algebraic_add`, which lets the compiler reassociate and fuse, so
  each square is rounded or fused into its addition (`Block`);
* grouped, each value goes through `VarState::insert_one`, Welford's update:
  `StdModel.wStep`, whose product `fl(x − m) · fl(x − m')` Polars writes the
  other way round, the same real product;
* states merge by Schubert and Gertz's update (`VarState::combine`,
  `sgMerge`): with `f = fl(n_b / n)`, `Δ̂ = fl(m_b − m_a)` and
  `m = fl(m_a + fl(Δ̂ f))`, the co-moment is
  `fl(M_a + fl(M_b + fl(fl(n_b · fl(m_b − m)) · Δ̂)))`.

The merge's correction term cancels in `m_b − m`, whose error is about
`u |m|`, not `u |Δ|`. Times `n_b |Δ|` that is `u A h |Δ|` with
`h = n_a n_b / n ≥ n_b / n`, within the tree invariant's `u A Σ|D|` term, and
the rounding of `f` costs `u n Δ² h`, within its `u n S` term. So the merge
meets `MergeSpec` (`sgMerge_spec`), a block meets the tree invariant
(`tInv_block`), and so does every state Polars computes (`tInv_prun`): its
co-moment is within DuckDB's bound (`plVar_rel`), and its `VAR_*`, clamped at
`0` as `VarState::finalize` does, within `varTol` (`core_var_polars`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-! ## The merge -/

/-- Polars's merged mean of `t` and `s`: `fl(m_t + fl(fl(m_s − m_t) · fl(n_s / n)))`. -/
noncomputable def StdModel.sgMean (t s : ℕ × ℝ × ℝ) : ℝ :=
  M.fl (t.2.1 + M.fl (M.fl (s.2.1 - t.2.1) * M.fl ((s.1 : ℝ) / ((t.1 : ℝ) + s.1))))

/-- Polars's merge of the state `s` into `t` (`VarState::combine`, Schubert
and Gertz's update). With no values on one side the state is the other's,
as in IEEE arithmetic: `combine` returns `t` when `s` is empty, and when `t`
is empty (`n_t = 0`, `m_t = M_t = 0`) its `n_s / n_s = 1`, `m_s − 0 = m_s`
and `n_s · (m_s − m_s) = 0` are exact. -/
noncomputable def StdModel.sgMerge (t s : ℕ × ℝ × ℝ) : ℕ × ℝ × ℝ :=
  if s.1 = 0 then t else if t.1 = 0 then s else
    (t.1 + s.1, M.sgMean t s,
      M.fl (t.2.2 + M.fl (s.2.2 + M.fl (M.fl ((s.1 : ℝ) * M.fl (s.2.1 - M.sgMean t s))
        * M.fl (s.2.1 - t.2.1)))))

/-- One rounding, far from overflow: its error, and the rounded value at most `2B`. -/
theorem StdModel.err_le {z B : ℝ} (hz : |z| ≤ B) (hB1 : 1 ≤ B) (hB : B ≤ 2 ^ 1000) :
    |M.fl z - z| ≤ u * (|z| + tiny) ∧ |M.fl z| ≤ 2 * B := by
  obtain ⟨hu, hu', ht, ht1, hmax⟩ := fpFacts
  have h := M.err z (by
    have : (2 : ℝ) ^ 1000 ≤ 2 ^ 1023 := by norm_num
    linarith)
  refine ⟨h, ?_⟩
  have := abs_sub_abs_le_abs_sub (M.fl z) z
  have : u * (|z| + tiny) ≤ 1 / 2 * (B + 1) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  linarith

/-- The merged mean's arithmetic: from `n |m̂ − y| ≤ u n |y| + 3.01 u n_b |Δ| + …`
to `6 u (n_b A_a + n_a A_b)`. -/
theorem sg_mean_arith {na nb E Y Dd ma mb Pa Pb : ℝ} (hna : 1 ≤ na) (hnb : 1 ≤ nb)
    (hPa : 0 ≤ Pa) (hPb : 0 ≤ Pb)
    (hma : na * |ma| ≤ Pa + 0.001 * (Pa + na * tiny))
    (hmb : nb * |mb| ≤ Pb + 0.001 * (Pb + nb * tiny))
    (hY : Y ≤ na * |ma| + nb * |mb|) (hD : Dd ≤ |ma| + |mb|)
    (hE : E ≤ u * Y + 3.01 * u * (nb * Dd) + 2.01 * u * ((na + nb) * tiny)
      + 1.01 * u * (nb * tiny)) :
    E ≤ 6 * u * (nb * (Pa + na * tiny) + na * (Pb + nb * tiny)) := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hna0 : 0 ≤ na := by linarith
  have hnb0 : 0 ≤ nb := by linarith
  have k1 : |ma| ≤ na * |ma| := le_mul_of_one_le_left (abs_nonneg _) hna
  have k2 : nb * |ma| ≤ nb * (Pa + 0.001 * (Pa + na * tiny)) :=
    mul_le_mul_of_nonneg_left (le_trans k1 hma) hnb0
  have k3 : nb * Dd ≤ nb * |ma| + nb * |mb| := by
    have := mul_le_mul_of_nonneg_left hD hnb0; linarith
  have q1 := mul_le_mul_of_nonneg_left hY hu.le
  have q2 := mul_le_mul_of_nonneg_left k3 hu.le
  have q3 := mul_le_mul_of_nonneg_left k2 hu.le
  have q4 := mul_le_mul_of_nonneg_left hma hu.le
  have q5 := mul_le_mul_of_nonneg_left hmb hu.le
  have hnat : 0 ≤ na * tiny := mul_nonneg hna0 ht.le
  have hnbt : 0 ≤ nb * tiny := mul_nonneg hnb0 ht.le
  have r1 : u * Pa ≤ u * (nb * Pa) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPa hnb) hu.le
  have r2 : u * Pb ≤ u * (na * Pb) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPb hna) hu.le
  have r3 : u * (na * tiny) ≤ u * (nb * (na * tiny)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnat hnb) hu.le
  have r4 : u * (nb * tiny) ≤ u * (na * (nb * tiny)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnbt hna) hu.le
  have p1 : 0 ≤ u * (nb * Pa) := mul_nonneg hu.le (mul_nonneg hnb0 hPa)
  have p2 : 0 ≤ u * (na * Pb) := mul_nonneg hu.le (mul_nonneg hna0 hPb)
  have p3 : 0 ≤ u * (nb * (na * tiny)) := mul_nonneg hu.le (mul_nonneg hnb0 hnat)
  linarith

/-- The merged mean against the children's weighted mean `y`, times `n`:
`m̂ = fl(P)` with `P = m_a + p` within `K` of `y`. -/
theorem sg_mean_core {n w y q P D : ℝ} (hn : 0 ≤ n) (hw : 0 ≤ w)
    (hq : |q - P| ≤ u * (|P| + tiny))
    (hP : |P - y| ≤ u * (w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + tiny)
      + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny)) :
    n * |q - y| ≤ u * (n * |y|) + 3.01 * u * (n * w * |D|) + 2.01 * u * (n * tiny)
      + 1.01 * u * (n * w * tiny) := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  set K := u * (w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + tiny)
      + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) with hK
  have hP' : |P| ≤ |y| + K := by have := abs_sub_abs_le_abs_sub P y; linarith
  have k1 : |q - y| ≤ u * |y| + u * tiny + (1 + u) * K := by
    have e : q - y = (q - P) + (P - y) := by ring
    rw [e]
    have := abs_add_le (q - P) (P - y)
    have := mul_le_mul_of_nonneg_left hP' hu.le
    linarith
  have k2 := mul_le_mul_of_nonneg_left k1 hn
  have eK : n * (u * |y| + u * tiny + (1 + u) * K) = u * (n * |y|) + u * (n * tiny)
      + (1 + u) * (u * (n * w * |D|)) + (1 + u) * (1 + u) * (2.0002 * u * (n * w * |D|)
        + 1.0001 * u * (n * w * tiny)) + (1 + u) * (u * (n * tiny)) := by
    rw [hK]; ring
  rw [eK] at k2
  have X1 : 0 ≤ u * (n * w * |D|) := mul_nonneg hu.le (mul_nonneg (mul_nonneg hn hw) (abs_nonneg _))
  have X2 : 0 ≤ u * (n * w * tiny) := mul_nonneg hu.le (mul_nonneg (mul_nonneg hn hw) ht.le)
  have X3 : 0 ≤ u * (n * tiny) := mul_nonneg hu.le (mul_nonneg hn ht.le)
  have c1 : (1 + u) ≤ 1.0001 := by linarith
  have c2 : (1 + u) * (1 + u) ≤ 1.0001 := by nlinarith
  have d1 := mul_le_mul_of_nonneg_right c1 X1
  have d2 := mul_le_mul_of_nonneg_right c1 X3
  have d3 := mul_le_mul_of_nonneg_right c2
    (by linarith : 0 ≤ 2.0002 * u * (n * w * |D|) + 1.0001 * u * (n * w * tiny))
  linarith

/-! ## The correction term -/

/-- `m_b − m̂ ≈ Δ̂ (1 − w)`, `w = n_b / n`: the deviation the correction
term multiplies, with the cancellation `B₃` (the rounding of `m̂`) apart. -/
theorem sg_dev {ma mb Dh f p m' w B3 : ℝ} (hw0 : 0 ≤ w)
    (e0 : |Dh - (mb - ma)| ≤ u * (|mb - ma| + tiny))
    (e1 : |f - w| ≤ u * (w + tiny))
    (e2 : |p - Dh * f| ≤ u * (|Dh * f| + tiny))
    (e3 : |m' - (ma + p)| ≤ B3) :
    |(mb - m') - Dh * (1 - w)| ≤ u * |Dh| * (1.0003 + 2.0001 * w) + B3 + 2.0002 * u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set a := |Dh| with ha_def
  have ha : 0 ≤ a := abs_nonneg _
  set E0 := |Dh - (mb - ma)| with hE0_def
  have hE0 : 0 ≤ E0 := abs_nonneg _
  have g1 : |mb - ma| ≤ a + E0 := by
    have h1 := abs_sub_abs_le_abs_sub (mb - ma) Dh
    have h2 : |mb - ma - Dh| = E0 := abs_sub_comm _ _
    linarith
  have g2 : E0 ≤ 1.0001 * u * (a + tiny) := by
    have h1 := mul_le_mul_of_nonneg_left g1 hu.le
    have k : E0 * 1 ≤ E0 * (1.0001 * (1 - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) hE0
    linarith
  have hf : |f| ≤ w + u * (w + tiny) := by
    have := abs_sub_abs_le_abs_sub f w; rw [abs_of_nonneg hw0] at this; linarith
  have g3 : |Dh * f| ≤ a * (w + u * (w + tiny)) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf ha
  have g4 : |Dh * (f - w)| ≤ a * (u * (w + tiny)) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 ha
  have g5 : u * (|Dh * f| + tiny) ≤ u * (a * (w + u * (w + tiny)) + tiny) := by gcongr
  have e : (mb - m') - Dh * (1 - w)
      = -(Dh - (mb - ma)) - (p - Dh * f) - Dh * (f - w) - (m' - (ma + p)) := by ring
  rw [e]
  have t1 := abs_sub (-(Dh - (mb - ma)) - (p - Dh * f) - Dh * (f - w)) (m' - (ma + p))
  have t2 := abs_sub (-(Dh - (mb - ma)) - (p - Dh * f)) (Dh * (f - w))
  have t3 := abs_sub (-(Dh - (mb - ma))) (p - Dh * f)
  have t4 : |-(Dh - (mb - ma))| = E0 := abs_neg _
  have huw : 0 ≤ u * (a * w) := mul_nonneg hu.le (mul_nonneg ha hw0)
  have hua : 0 ≤ u * a := mul_nonneg hu.le ha
  have s1 : u * (u * (a * w)) ≤ 0.0001 * (u * (a * w)) :=
    mul_le_mul_of_nonneg_right (by linarith) huw
  have hut : u * tiny ≤ 0.0001 := by
    have := mul_le_mul hu' htt ht.le (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 53); linarith
  have s2 : u * a * (u * tiny) ≤ u * a * 0.0001 := mul_le_mul_of_nonneg_left hut hua
  have s3 : u * a * tiny ≤ u * a * 0.0001 := mul_le_mul_of_nonneg_left (by linarith) hua
  have hsum : |-(Dh - (mb - ma)) - (p - Dh * f) - Dh * (f - w) - (m' - (ma + p))|
      ≤ E0 + |p - Dh * f| + |Dh * (f - w)| + |m' - (ma + p)| := by linarith
  have b1 : |p - Dh * f| ≤ u * a * w + u * (u * (a * w)) + u * a * (u * tiny) + u * tiny := by
    have h1 := le_trans e2 g5
    have h2 : u * (a * (w + u * (w + tiny)) + tiny)
        = u * a * w + u * (u * (a * w)) + u * a * (u * tiny) + u * tiny := by ring
    linarith
  have b2 : |Dh * (f - w)| ≤ u * a * w + u * a * tiny := by
    have h2 : a * (u * (w + tiny)) = u * a * w + u * a * tiny := by ring
    linarith
  have b3 : E0 ≤ 1.0001 * (u * a) + 1.0001 * (u * tiny) := by
    have h2 : 1.0001 * u * (a + tiny) = 1.0001 * (u * a) + 1.0001 * (u * tiny) := by ring
    linarith
  have e4 : u * a * (1.0003 + 2.0001 * w) = 1.0003 * (u * a) + 2.0001 * (u * a * w) := by ring
  have e6 : u * (a * w) = u * a * w := by ring
  have hut0 : 0 ≤ u * tiny := by positivity
  rw [e4]
  linarith

/-- The correction term `T̂ = fl(fl(n_b q̂) Δ̂)`, `q̂ = fl(m_b − m̂)`, against
`Δ̂² n_b v`, from the deviation's error `E_q`. -/
theorem sg_T {mb m' q r T Dh v nb Eq : ℝ} (hnb : 1 ≤ nb) (hv0 : 0 ≤ v) (hEq0 : 0 ≤ Eq)
    (hd : |(mb - m') - Dh * v| ≤ Eq)
    (e4 : |q - (mb - m')| ≤ u * (|mb - m'| + tiny))
    (e5 : |r - nb * q| ≤ u * (|nb * q| + tiny))
    (e6 : |T - r * Dh| ≤ u * (|r * Dh| + tiny)) :
    |T - Dh ^ 2 * (nb * v)| ≤ 1.01 * (nb * |Dh| * Eq) + 3.02 * u * (Dh ^ 2 * (nb * v))
      + 1.01 * u * (|Dh| * tiny * (nb + 1)) + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  set a := |Dh| with ha_def
  have ha : 0 ≤ a := abs_nonneg _
  have hnb0 : 0 ≤ nb := by linarith
  have hDv : |Dh * v| = a * v := by rw [abs_mul, abs_of_nonneg hv0]
  -- `q̂`
  have hm : |mb - m'| ≤ a * v + Eq := by
    have := abs_sub_abs_le_abs_sub (mb - m') (Dh * v); rw [hDv] at this; linarith
  set Q1 := (1 + u) * Eq + u * (a * v) + u * tiny with hQ1
  have hQ10 : 0 ≤ Q1 :=
    add_nonneg (add_nonneg (mul_nonneg (by linarith) hEq0) (mul_nonneg hu.le (mul_nonneg ha hv0)))
      (mul_nonneg hu.le ht.le)
  have hq : |q - Dh * v| ≤ Q1 := by
    have e : q - Dh * v = (q - (mb - m')) + ((mb - m') - Dh * v) := by ring
    rw [e]
    have := abs_add_le (q - (mb - m')) ((mb - m') - Dh * v)
    have := mul_le_mul_of_nonneg_left hm hu.le
    linarith
  -- `r̂`
  have hnq : |nb * q| ≤ nb * (a * v) + nb * Q1 := by
    rw [abs_mul, abs_of_nonneg hnb0]
    have : |q| ≤ a * v + Q1 := by
      have := abs_sub_abs_le_abs_sub q (Dh * v); rw [hDv] at this; linarith
    have := mul_le_mul_of_nonneg_left this hnb0; linarith
  have hnv : 0 ≤ nb * v := mul_nonneg hnb0 hv0
  set R1 := (1 + u) * (nb * Q1) + u * (a * (nb * v)) + u * tiny with hR1
  have hr : |r - Dh * (nb * v)| ≤ R1 := by
    have e : r - Dh * (nb * v) = (r - nb * q) + nb * (q - Dh * v) := by ring
    rw [e]
    have := abs_add_le (r - nb * q) (nb * (q - Dh * v))
    have h3 : |nb * (q - Dh * v)| = nb * |q - Dh * v| := by rw [abs_mul, abs_of_nonneg hnb0]
    have := mul_le_mul_of_nonneg_left hq hnb0
    have := mul_le_mul_of_nonneg_left hnq hu.le
    linarith
  -- `T̂`
  have hrD : |r * Dh| ≤ (a * (nb * v) + R1) * a := by
    rw [abs_mul]
    have : |r| ≤ a * (nb * v) + R1 := by
      have := abs_sub_abs_le_abs_sub r (Dh * (nb * v))
      rw [abs_mul Dh, abs_of_nonneg hnv] at this; linarith
    exact mul_le_mul_of_nonneg_right this ha
  have hT : |T - Dh ^ 2 * (nb * v)| ≤ (1 + u) * (a * R1) + u * (a ^ 2 * (nb * v)) + u * tiny := by
    have e : T - Dh ^ 2 * (nb * v) = (T - r * Dh) + Dh * (r - Dh * (nb * v)) := by ring
    rw [e]
    have := abs_add_le (T - r * Dh) (Dh * (r - Dh * (nb * v)))
    have h3 : |Dh * (r - Dh * (nb * v))| ≤ a * R1 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr ha
    have := mul_le_mul_of_nonneg_left hrD hu.le
    have e2 : u * ((a * (nb * v) + R1) * a) = u * (a ^ 2 * (nb * v)) + u * (a * R1) := by ring
    linarith
  -- the constants
  have hsq : Dh ^ 2 = a ^ 2 := (sq_abs Dh).symm
  rw [hsq] at hT ⊢
  refine le_trans hT ?_
  have E : (1 + u) * (a * R1) + u * (a ^ 2 * (nb * v)) + u * tiny
      = (1 + u) ^ 3 * (nb * a * Eq) + ((1 + u) ^ 2 + (1 + u) + 1) * (u * (a ^ 2 * (nb * v)))
        + (1 + u) ^ 2 * (u * (a * tiny * nb)) + (1 + u) * (u * (a * tiny)) + u * tiny := by
    simp only [hR1, hQ1]; ring
  rw [E]
  obtain ⟨-, -, f3, f2⟩ := u_pows
  have p1 : 0 ≤ nb * a * Eq := mul_nonneg (mul_nonneg hnb0 ha) hEq0
  have p2 : 0 ≤ u * (a ^ 2 * (nb * v)) := mul_nonneg hu.le (mul_nonneg (sq_nonneg a) hnv)
  have p3 : 0 ≤ u * (a * tiny * nb) := mul_nonneg hu.le (mul_nonneg (mul_nonneg ha ht.le) hnb0)
  have p4 : 0 ≤ u * (a * tiny) := mul_nonneg hu.le (mul_nonneg ha ht.le)
  have d1 := mul_le_mul_of_nonneg_right f3 p1
  have d2 := mul_le_mul_of_nonneg_right (by linarith : (1 + u) ^ 2 + (1 + u) + 1 ≤ 3.02) p2
  have d3 := mul_le_mul_of_nonneg_right f2 p3
  have d4 := mul_le_mul_of_nonneg_right (by linarith : 1 + u ≤ 1.01) p4
  have e5 : 1.01 * u * (a * tiny * (nb + 1))
      = 1.01 * (u * (a * tiny * nb)) + 1.01 * (u * (a * tiny)) := by ring
  have e6 : 3.02 * u * (a ^ 2 * (nb * v)) = 3.02 * (u * (a ^ 2 * (nb * v))) := by ring
  linarith

/-- The correction term's error in `Δ̂`: the deviation and the cancellation
gathered, the products `|Δ̂| · tiny` by `ab ≤ a²/200 + 50 b²`. -/
theorem sg_T_final {na nb n w h a A X1 E : ℝ} (hna : 1 ≤ na) (hnb : 1 ≤ nb) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hwh : w ≤ h) (hnh : n * h = na * nb)
    (hnbN : nb ≤ 2 ^ 32)
    (hX1 : X1 ≤ u * a ^ 2 * nb * (1.0003 + 2.0001 * w) + 1.03 * u * A * a * w
      + 3.0002 * u * nb * a * tiny)
    (hE : E ≤ 1.01 * X1 + 3.02 * u * (a ^ 2 * h) + 1.01 * u * (a * tiny * (nb + 1)) + u * tiny) :
    E ≤ 3.06 * u * n * (a ^ 2 * h) + 3.02 * u * (a ^ 2 * h) + 1.05 * u * A * (h * a)
      + 1.1 * u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  have hnb0 : 0 ≤ nb := by linarith
  have hh0 : 0 ≤ h := le_trans hw0 hwh
  have hua2 : 0 ≤ u * a ^ 2 * nb := mul_nonneg (mul_nonneg hu.le (sq_nonneg a)) hnb0
  have f1 : u * a ^ 2 * nb * (1.0003 + 2.0001 * w) ≤ 3.0004 * (u * a ^ 2 * nb) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1.0003 + 2.0001 * w ≤ 3.0004) hua2
    linarith
  have f2 : u * a ^ 2 * nb ≤ u * n * (a ^ 2 * h) := by
    have : nb ≤ na * nb := le_mul_of_one_le_left hnb0 hna
    have e : u * n * (a ^ 2 * h) = u * a ^ 2 * (n * h) := by ring
    rw [e, hnh]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hu.le (sq_nonneg a))
  have f3 : u * A * a * w ≤ u * A * (h * a) := by
    have := mul_le_mul_of_nonneg_left hwh (mul_nonneg (mul_nonneg hu.le hA) ha); linarith
  have f4 : a * tiny ≤ 0.005 * a ^ 2 + 50 * tiny ^ 2 := by
    nlinarith [sq_nonneg (0.1 * a - 10 * tiny)]
  have f5 := mul_le_mul_of_nonneg_left f4 (mul_nonneg hu.le hnb0)
  have f6 : nb * tiny ^ 2 ≤ 0.00001 * tiny := by
    have h1 : nb * tiny ≤ 0.00001 := by
      have := mul_le_mul hnbN htt ht.le (by norm_num); linarith
    have := mul_le_mul_of_nonneg_right h1 ht.le; nlinarith
  have f7 : u * (a * tiny) ≤ u * (nb * (a * tiny)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (mul_nonneg ha ht.le) hnb) hu.le
  have f8 := mul_le_mul_of_nonneg_left f6 hu.le
  have p1 : 0 ≤ u * n * (a ^ 2 * h) := le_trans hua2 f2
  have p2 : 0 ≤ u * A * (h * a) := le_trans (mul_nonneg (mul_nonneg (mul_nonneg hu.le hA) ha) hw0) f3
  have p3 : 0 ≤ u * tiny := mul_nonneg hu.le ht.le
  linarith

set_option maxHeartbeats 1000000 in
/-- From `Δ̂` to `Δ`: the correction term's error against `Δ² h`, with
`|Δ̂ − Δ| ≤ u |Δ| + 6.0001 u A + u·tiny`. -/
theorem sg_conv {T Dh Δ A h n : ℝ} (hn : 1 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21) (hh0 : 0 ≤ h)
    (hA : 0 ≤ A)
    (hD : |Dh - Δ| ≤ u * |Δ| + 6.0001 * u * A + u * tiny)
    (hT : |T - Dh ^ 2 * h| ≤ 3.06 * u * n * (Dh ^ 2 * h) + 3.02 * u * (Dh ^ 2 * h)
      + 1.05 * u * A * (h * |Dh|) + 1.1 * u * tiny) :
    |T - Δ ^ 2 * h| ≤ (3.07 * n + 5.3) * u * (Δ ^ 2 * h) + 13.1 * u * A * (h * |Δ|)
      + 115 * u ^ 2 * h * A ^ 2 + 1.1 * u * tiny + 11 * u * h * tiny ^ 2 := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  set d := |Δ| with hd_def
  have hd : 0 ≤ d := abs_nonneg _
  have hd2 : d ^ 2 = Δ ^ 2 := sq_abs Δ
  rw [← hd2]
  set e := u * d + 6.0001 * u * A + u * tiny with he
  have he0 : 0 ≤ e := by positivity
  -- `|Δ̂² − Δ²| ≤ e (2 d + e)`
  have hsq : |Dh ^ 2 - d ^ 2| ≤ e * (2 * d + e) := by
    rw [hd2]
    have e1 : Dh ^ 2 - Δ ^ 2 = (Dh - Δ) * (Dh + Δ) := by ring
    rw [e1, abs_mul]
    have : |Dh + Δ| ≤ 2 * d + e := by
      have := abs_add_le (Dh - Δ) (2 * Δ)
      rw [show Dh - Δ + 2 * Δ = Dh + Δ by ring, abs_mul, abs_two] at this; linarith
    exact mul_le_mul hD this (abs_nonneg _) he0
  set H := h * (e * (2 * d + e)) with hH
  have hH0 : 0 ≤ H := by positivity
  have hPD : |Dh ^ 2 * h - d ^ 2 * h| ≤ H := by
    rw [show Dh ^ 2 * h - d ^ 2 * h = h * (Dh ^ 2 - d ^ 2) by ring, abs_mul, abs_of_nonneg hh0]
    exact mul_le_mul_of_nonneg_left hsq hh0
  -- `H` term by term
  have k1 : 2 * u * tiny * (h * d) ≤ u * h * (0.25 * d ^ 2 + 4 * tiny ^ 2) := by
    have : 2 * tiny * d ≤ 0.25 * d ^ 2 + 4 * tiny ^ 2 := by nlinarith [sq_nonneg (0.5 * d - 2 * tiny)]
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ u * h); linarith
  have k2 : e ^ 2 ≤ 3 * (u ^ 2 * d ^ 2 + 36.0013 * u ^ 2 * A ^ 2 + u ^ 2 * tiny ^ 2) := by
    simp only [he]
    nlinarith [sq_nonneg (u * d - 6.0001 * u * A), sq_nonneg (u * d - u * tiny),
      sq_nonneg (6.0001 * u * A - u * tiny), sq_nonneg (u * A)]
  have k3 := mul_le_mul_of_nonneg_left k2 hh0
  have eH : H = 2 * u * (h * d ^ 2) + 12.0002 * u * A * (h * d) + 2 * u * tiny * (h * d)
      + h * e ^ 2 := by simp only [hH, he]; ring
  have hHb : H ≤ 2.25 * u * (h * d ^ 2) + 3 * u ^ 2 * (h * d ^ 2) + 12.0002 * u * A * (h * d)
      + 108.004 * u ^ 2 * h * A ^ 2 + 4 * u * h * tiny ^ 2 + 3 * u ^ 2 * h * tiny ^ 2 := by
    have : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
    rw [eH]; linarith
  -- the pieces
  have hP : Dh ^ 2 * h ≤ d ^ 2 * h + H := by linarith [(abs_le.mp hPD).2]
  have hhD : h * |Dh| ≤ h * d + h * e := by
    have := abs_sub_abs_le_abs_sub Dh Δ
    have h1 : |Dh| ≤ d + e := by linarith
    have := mul_le_mul_of_nonneg_left h1 hh0
    linarith
  have hTD : |T - d ^ 2 * h| ≤ |T - Dh ^ 2 * h| + H := by
    have e1 : T - d ^ 2 * h = (T - Dh ^ 2 * h) + (Dh ^ 2 * h - d ^ 2 * h) := by ring
    rw [e1]
    have := abs_add_le (T - Dh ^ 2 * h) (Dh ^ 2 * h - d ^ 2 * h)
    linarith
  -- small factors
  have hu2 : u ^ 2 ≤ 0.0001 * u := by
    have := mul_le_mul_of_nonneg_left (show u ≤ 0.0001 by linarith) hu.le; linarith
  have c1 : (3.06 * u * n + 3.02 * u) * H ≤ 0.00001 * H := by
    have : 3.06 * u * n + 3.02 * u ≤ 0.00001 := by linarith
    exact mul_le_mul_of_nonneg_right this hH0
  have c2 : 1.05 * u * A * (h * e) ≤ 0.0002 * u * A * (h * d) + 6.31 * u ^ 2 * h * A ^ 2
      + 0.53 * u ^ 2 * h * A ^ 2 + 0.53 * u ^ 2 * h * tiny ^ 2 := by
    have q1 : A * tiny ≤ (A ^ 2 + tiny ^ 2) / 2 := by nlinarith [sq_nonneg (A - tiny)]
    have q2 := mul_le_mul_of_nonneg_left q1 (by positivity : 0 ≤ 1.05 * u ^ 2 * h)
    have q3 : 1.05 * u ^ 2 * (A * (h * d)) ≤ 0.0002 * u * (A * (h * d)) := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1.05 * u ^ 2 ≤ 0.0002 * u)
        (by positivity : 0 ≤ A * (h * d))
      linarith
    have : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
    have : 0 ≤ u ^ 2 * h * tiny ^ 2 := by positivity
    simp only [he]; linarith
  have hHb' := mul_le_mul_of_nonneg_left hHb (by norm_num : (0 : ℝ) ≤ 0.00001)
  have s1 : u ^ 2 * (h * d ^ 2) ≤ 0.0001 * u * (h * d ^ 2) := by
    have := mul_le_mul_of_nonneg_right hu2 (by positivity : 0 ≤ h * d ^ 2); linarith
  have s2 : u ^ 2 * h * tiny ^ 2 ≤ 0.0001 * u * h * tiny ^ 2 := by
    have := mul_le_mul_of_nonneg_right hu2 (by positivity : 0 ≤ h * tiny ^ 2); linarith
  have s3 : 0 ≤ u * n * (h * d ^ 2) := by have : 0 ≤ n := by linarith
                                          positivity
  have s4 : 0 ≤ u * A * (h * d) := by positivity
  have s5 : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
  have s6 : 0 ≤ u * h * tiny ^ 2 := by positivity
  have s7 : 0 ≤ u * tiny := by positivity
  have s8 : 0 ≤ u * (h * d ^ 2) := by positivity
  have s9 : 0 ≤ u ^ 2 * (h * d ^ 2) := by positivity
  have s10 : 0 ≤ u ^ 2 * h * tiny ^ 2 := by positivity
  have hP' := mul_le_mul_of_nonneg_left hP
    (by have : 0 ≤ n := by linarith
        positivity : 0 ≤ 3.06 * u * n + 3.02 * u)
  have hhD' := mul_le_mul_of_nonneg_left hhD (by positivity : 0 ≤ 1.05 * u * A)
  have eT : 3.06 * u * n * (Dh ^ 2 * h) + 3.02 * u * (Dh ^ 2 * h)
      = (3.06 * u * n + 3.02 * u) * (Dh ^ 2 * h) := by ring
  linarith

/-- The merged co-moment `fl(Ŝ_a + fl(Ŝ_b + T̂))` from the children's and the
correction term's errors. -/
theorem sg_assemble {Sa Sb ΔS Sha Shb T Sh1 Sh Ea Eb ET : ℝ} (hSa : 0 ≤ Sa) (hSb : 0 ≤ Sb)
    (hΔS : 0 ≤ ΔS) (hEa : |Sha - Sa| ≤ Ea) (hEb : |Shb - Sb| ≤ Eb) (hT : |T - ΔS| ≤ ET)
    (h1 : |Sh1 - (Shb + T)| ≤ u * (|Shb + T| + tiny))
    (h2 : |Sh - (Sha + Sh1)| ≤ u * (|Sha + Sh1| + tiny)) :
    |Sh - (Sa + Sb + ΔS)| ≤ (1 + u) ^ 2 * (Ea + Eb) + 1.0001 * ET + 2.0001 * u * (Sa + Sb)
      + 2.0001 * u * ΔS + 2.0001 * u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hEa0 : 0 ≤ Ea := le_trans (abs_nonneg _) hEa
  have hEb0 : 0 ≤ Eb := le_trans (abs_nonneg _) hEb
  have hET0 : 0 ≤ ET := le_trans (abs_nonneg _) hT
  have a1 : |Shb + T| ≤ Sb + ΔS + Eb + ET := by
    have e : Shb + T = (Sb + ΔS) + ((Shb - Sb) + (T - ΔS)) := by ring
    rw [e]
    have := abs_add_le (Sb + ΔS) ((Shb - Sb) + (T - ΔS))
    have := abs_add_le (Shb - Sb) (T - ΔS)
    have := abs_of_nonneg (add_nonneg hSb hΔS)
    linarith
  have a2 : |Sh1 - (Sb + ΔS)| ≤ (1 + u) * (Eb + ET) + u * (Sb + ΔS + tiny) := by
    have e : Sh1 - (Sb + ΔS) = (Sh1 - (Shb + T)) + ((Shb - Sb) + (T - ΔS)) := by ring
    rw [e]
    have := abs_add_le (Sh1 - (Shb + T)) ((Shb - Sb) + (T - ΔS))
    have := abs_add_le (Shb - Sb) (T - ΔS)
    have := mul_le_mul_of_nonneg_left a1 hu.le
    linarith
  set K1 := (1 + u) * (Eb + ET) + u * (Sb + ΔS + tiny) with hK1
  have a3 : |Sha + Sh1| ≤ Sa + Sb + ΔS + Ea + K1 := by
    have e : Sha + Sh1 = (Sa + (Sb + ΔS)) + ((Sha - Sa) + (Sh1 - (Sb + ΔS))) := by ring
    rw [e]
    have := abs_add_le (Sa + (Sb + ΔS)) ((Sha - Sa) + (Sh1 - (Sb + ΔS)))
    have := abs_add_le (Sha - Sa) (Sh1 - (Sb + ΔS))
    have := abs_of_nonneg (add_nonneg hSa (add_nonneg hSb hΔS))
    linarith
  have a4 : |Sh - (Sa + Sb + ΔS)| ≤ (1 + u) * (Ea + K1) + u * (Sa + Sb + ΔS + tiny) := by
    have e : Sh - (Sa + Sb + ΔS) = (Sh - (Sha + Sh1)) + ((Sha - Sa) + (Sh1 - (Sb + ΔS))) := by
      ring
    rw [e]
    have := abs_add_le (Sh - (Sha + Sh1)) ((Sha - Sa) + (Sh1 - (Sb + ΔS)))
    have := abs_add_le (Sha - Sa) (Sh1 - (Sb + ΔS))
    have := mul_le_mul_of_nonneg_left a3 hu.le
    linarith
  refine le_trans a4 ?_
  have e : (1 + u) * (Ea + K1) + u * (Sa + Sb + ΔS + tiny)
      = (1 + u) * Ea + (1 + u) ^ 2 * Eb + (1 + u) ^ 2 * ET + (1 + u) * (u * (Sb + ΔS + tiny))
        + u * (Sa + Sb + ΔS + tiny) := by simp only [hK1]; ring
  rw [e]
  have b1 : (1 + u) * Ea ≤ (1 + u) ^ 2 * Ea := by
    have : 1 + u ≤ (1 + u) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hEa0
  have b2 : (1 + u) ^ 2 * ET ≤ 1.0001 * ET := by
    have : (1 + u) ^ 2 ≤ 1.0001 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hET0
  have b3 : (1 + u) * (u * (Sb + ΔS + tiny)) ≤ 1.0001 * (u * (Sb + ΔS + tiny)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have p1 : 0 ≤ u * Sa := by positivity
  linarith

/-- Polars's new terms are among the ones a merge may add (`mergeNew`), for
`n ≥ 2` and `h ≥ 1/2`. -/
theorem sg_new_le {n A X Sab ΔS h ET : ℝ} (hn : 2 ≤ n) (hh : 1 / 2 ≤ h) (hA : 0 ≤ A)
    (hX : 0 ≤ X) (hSab : 0 ≤ Sab) (hΔS : 0 ≤ ΔS)
    (hET : ET ≤ (3.07 * n + 5.3) * u * ΔS + 13.1 * u * A * X + 115 * u ^ 2 * h * A ^ 2
      + 1.1 * u * tiny + 11 * u * h * tiny ^ 2) :
    1.0001 * ET + 2.0001 * u * Sab + 2.0001 * u * ΔS + 2.0001 * u * tiny
      ≤ mergeNew n A X Sab ΔS h := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  have hh0 : 0 ≤ h := by linarith
  unfold mergeNew
  have p1 : 0 ≤ u * ΔS := by positivity
  have p2 : 2 * (u * ΔS) ≤ n * (u * ΔS) := mul_le_mul_of_nonneg_right hn p1
  have p3 : 0 ≤ u * A * X := by positivity
  have p4 : 0 ≤ u ^ 2 * h * A ^ 2 := by positivity
  have p5 : 0 ≤ u * Sab := by positivity
  have p6 : u * h * tiny ^ 2 ≤ 0.0001 * (h * (u * tiny)) := by
    have h1 : tiny * tiny ≤ 0.0001 * tiny := mul_le_mul_of_nonneg_right (by linarith) ht.le
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ u * h)
    nlinarith
  have p7 : u * tiny ≤ 2 * (h * (u * tiny)) := by
    have := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ u * tiny); nlinarith
  have p8 : 0 ≤ h * (u * tiny) := by positivity
  have e1 : (3.07 * n + 5.3) * u * ΔS = 3.07 * (n * (u * ΔS)) + 5.3 * (u * ΔS) := by ring
  have e2 : 9 * u * n * ΔS = 9 * (n * (u * ΔS)) := by ring
  have e3 : 24 * h * u * tiny = 24 * (h * (u * tiny)) := by ring
  have p9 : 0 ≤ n * (u * ΔS) := by have : 0 ≤ n := by linarith
                                   positivity
  linarith

/-- `n |m_a + p| ≤ 1.02 A`: the merged mean before its rounding is near the
children's weighted mean `y`, `n |y| ≤ 1.01 A`. -/
theorem sg_nmp {n w P y D A : ℝ} (hn : 0 ≤ n) (hw : 0 ≤ w) (hA : 0 ≤ A)
    (hpy : |P - y| ≤ u * (w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + tiny)
      + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny))
    (hny : n * |y| ≤ 1.01 * A) (hnD : n * w * |D| ≤ 2 ^ 32 * (1.01 * A))
    (hnwt : n * w * tiny ≤ A) (hnt : n * tiny ≤ A) :
    n * |P| ≤ 1.02 * A := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have k1 : |P| ≤ |y| + |P - y| := by have := abs_sub_abs_le_abs_sub P y; linarith
  have k2 := mul_le_mul_of_nonneg_left k1 hn
  have q1 := mul_le_mul_of_nonneg_left hpy hn
  have e : n * (u * (w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) + tiny)
      + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny))
      = (u + 2.0002 * u * u + 2.0002 * u) * (n * w * |D|)
        + (1.0001 * u * u + 1.0001 * u) * (n * w * tiny) + u * (n * tiny) := by ring
  have hnwD0 : 0 ≤ n * w * |D| := by positivity
  have hnwt0 : 0 ≤ n * w * tiny := by positivity
  have huu : u * u ≤ 1 / 2 ^ 53 * u := mul_le_mul_of_nonneg_right hu' hu.le
  have c1 : (u + 2.0002 * u * u + 2.0002 * u) * (n * w * |D|)
      ≤ (4 / 2 ^ 53) * (2 ^ 32 * (1.01 * A)) := by
    apply mul_le_mul _ hnD hnwD0 (by norm_num)
    linarith
  have c2 : (1.0001 * u * u + 1.0001 * u) * (n * w * tiny) ≤ (3 / 2 ^ 53) * A := by
    apply mul_le_mul _ hnwt hnwt0 (by norm_num)
    linarith
  have c3 : u * (n * tiny) ≤ (1 / 2 ^ 53) * A := mul_le_mul hu' hnt (by positivity) (by norm_num)
  linarith

/-- The correction term's `n_b |Δ̂| E_q` in the form `sg_T_final` reads, with
`n_b |m_a + p| ≤ 1.02 A w`. -/
theorem sg_X1 {nb a P w A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hw : 0 ≤ w)
    (hk : nb * P ≤ 1.02 * A * w) :
    nb * a * (u * a * (1.0003 + 2.0001 * w) + u * (P + tiny) + 2.0002 * u * tiny)
      ≤ u * a ^ 2 * nb * (1.0003 + 2.0001 * w) + 1.03 * u * A * a * w
        + 3.0002 * u * nb * a * tiny := by
  obtain ⟨hu, -, -, -, -⟩ := fpFacts
  have k2 := mul_le_mul_of_nonneg_left hk (mul_nonneg hu.le ha)
  have e : nb * a * (u * a * (1.0003 + 2.0001 * w) + u * (P + tiny) + 2.0002 * u * tiny)
      = u * a ^ 2 * nb * (1.0003 + 2.0001 * w) + u * a * (nb * P)
        + 3.0002 * u * nb * a * tiny := by ring
  rw [e]
  have : 0 ≤ u * a * (0.01 * A * w) := by positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- **Schubert and Gertz's merge meets `MergeSpec`**: the mean
(`sg_mean_core`, `sg_mean_arith`), and the co-moment (`sg_dev`, `sg_T`,
`sg_T_final`, `sg_conv`, `sg_assemble`, `sg_new_le`). -/
theorem StdModel.sgMerge_spec : MergeSpec M.sgMerge := by
  intro na nb ma mb Ma Mb Pa Pb Sa Sb Sha Shb Ea Eb hN sa sb
  obtain ⟨hu, hu', htn, htn1, hmax⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  have hla := sa.one
  have hlb := sb.one
  have hdm : M.sgMerge (na, ma, Sha) (nb, mb, Shb) = (na + nb,
      M.fl (ma + M.fl (M.fl (mb - ma) * M.fl ((nb : ℝ) / ((na : ℝ) + nb)))),
      M.fl (Sha + M.fl (Shb + M.fl (M.fl ((nb : ℝ) * M.fl (mb
        - M.fl (ma + M.fl (M.fl (mb - ma) * M.fl ((nb : ℝ) / ((na : ℝ) + nb))))))
        * M.fl (mb - ma))))) := by
    have h1 : na ≠ 0 := by omega
    have h2 : nb ≠ 0 := by omega
    simp only [StdModel.sgMerge, StdModel.sgMean, h1, h2, ite_false]
  rw [hdm]
  have hna1 : (1 : ℝ) ≤ na := by exact_mod_cast hla
  have hnb1 : (1 : ℝ) ≤ nb := by exact_mod_cast hlb
  have hnab : (na : ℝ) + nb ≤ 2 ^ 32 := by exact_mod_cast hN
  have hne : (na : ℝ) + nb ≠ 0 := ne_of_gt (by linarith)
  have hPa0 := sa.P0
  have hPb0 := sb.P0
  have hnat : (0 : ℝ) ≤ na * tiny := mul_nonneg (by linarith) htn.le
  have hnbt : (0 : ℝ) ≤ nb * tiny := mul_nonneg (by linarith) htn.le
  set Aa := Pa + na * tiny with hAa
  set Ab := Pb + nb * tiny with hAb
  have smean : |ma - Ma| ≤ 6 * u * Aa := sa.mean
  have smean' : |mb - Mb| ≤ 6 * u * Ab := sb.mean
  have sPb : Aa ≤ 2 ^ 432 := sa.Pb
  have sPb' : Ab ≤ 2 ^ 432 := sb.Pb
  have hAa0 : 0 ≤ Aa := add_nonneg hPa0 hnat
  have hAb0 : 0 ≤ Ab := add_nonneg hPb0 hnbt
  have hMaA' : |Ma| * na ≤ Aa := by have := sa.MP; linarith
  have hMbA' : |Mb| * nb ≤ Ab := by have := sb.MP; linarith
  obtain ⟨hma1, hmab, hMaA⟩ := mean_mag hna1 (by linarith) hAa0 sPb hMaA' sa.Mb smean
  obtain ⟨hmb1, hmbb, hMbA⟩ := mean_mag hnb1 (by linarith) hAb0 sPb' hMbA' sb.Mb smean'
  have hnau : (na : ℝ) * u ≤ 1 / 2 ^ 21 := by
    calc (na : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul (by linarith) hu' hu.le (by norm_num)
      _ = 1 / 2 ^ 21 := by norm_num
  have hnbu : (nb : ℝ) * u ≤ 1 / 2 ^ 21 := by
    calc (nb : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul (by linarith) hu' hu.le (by norm_num)
      _ = 1 / 2 ^ 21 := by norm_num
  have hma2 : na * |ma| ≤ Pa + 0.001 * Aa := by
    have h1 : |ma| ≤ |Ma| + 6 * u * Aa := by
      have := abs_sub_abs_le_abs_sub ma Ma; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ na)
    have h3 : (na : ℝ) * (6 * u * Aa) ≤ 0.001 * Aa := by
      have := mul_le_mul_of_nonneg_right hnau hAa0; nlinarith
    have := sa.MP; linarith
  have hmb2 : nb * |mb| ≤ Pb + 0.001 * Ab := by
    have h1 : |mb| ≤ |Mb| + 6 * u * Ab := by
      have := abs_sub_abs_le_abs_sub mb Mb; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ nb)
    have h3 : (nb : ℝ) * (6 * u * Ab) ≤ 0.001 * Ab := by
      have := mul_le_mul_of_nonneg_right hnbu hAb0; nlinarith
    have := sb.MP; linarith
  -- the weights
  set n : ℝ := (na : ℝ) + nb with hn
  have hn0 : 0 < n := by linarith
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
  -- the roundings of the mean
  set D := mb - ma with hD
  have hDb : |D| ≤ 2 ^ 402 := by rw [hD]; have := abs_sub mb ma; linarith
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
  have hmp : |ma + p| ≤ 2 ^ 406 := by have := abs_add_le ma p; linarith
  obtain ⟨em, hm'b⟩ := M.err_le (z := ma + p) (B := 2 ^ 406) hmp (by norm_num) (by norm_num)
  set m' := M.fl (ma + p) with hm'
  -- the children's weighted mean `y`
  have hy : ma + w * D = ((na : ℝ) * ma + nb * mb) / n := by
    rw [eq_div_iff hn0.ne', hD, hw, hn]; field_simp [hne]; ring
  have hny : n * |ma + w * D| ≤ na * |ma| + nb * |mb| := by
    rw [hy, abs_div, abs_of_pos hn0, mul_div_cancel₀ _ hn0.ne']
    have := abs_add_le ((na : ℝ) * ma) (nb * mb)
    rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast] at this; exact this
  have hpy : |(ma + p) - (ma + w * D)| ≤ u * (w * |D| + (2.0002 * u * w * |D|
      + 1.0001 * u * w * tiny) + tiny) + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) := by
    have e : (ma + p) - (ma + w * D) = (p - Dh * f) + (Dh * f - w * D) := by ring
    rw [e]
    have := abs_add_le (p - Dh * f) (Dh * f - w * D)
    have hDf' : |Dh * f| ≤ w * |D| + (2.0002 * u * w * |D| + 1.0001 * u * w * tiny) := by
      have := abs_sub_abs_le_abs_sub (Dh * f) (w * D)
      rw [abs_mul w D, abs_of_nonneg hw0'] at this; linarith
    have := mul_le_mul_of_nonneg_left hDf' hu.le
    linarith
  have hmc := sg_mean_core (n := n) hn0.le hw0' em hpy
  rw [hwn] at hmc
  refine ⟨rfl, ?_, ?_⟩
  · -- the mean
    show |m' - ((na : ℝ) * ma + nb * mb) / n| ≤ 6 * u * ((nb : ℝ) * Aa + na * Ab) / n
    rw [← hy, le_div_iff₀ hn0]
    have := sg_mean_arith (E := n * |m' - (ma + w * D)|) (Y := n * |ma + w * D|) (Dd := |D|)
      hna1 hnb1 hPa0 hPb0 hma2 hmb2 hny (by have := abs_sub mb ma; rw [hD]; linarith) hmc
    linarith
  · -- the co-moment
    dsimp only
    have hA0 : 0 ≤ Aa + Ab := add_nonneg hAa0 hAb0
    -- `n |m_a + p| ≤ 1.02 A`
    have hnmp : n * |ma + p| ≤ 1.02 * (Aa + Ab) := by
      have hnD : n * w * |D| ≤ 2 ^ 32 * (1.01 * (Aa + Ab)) := by
        rw [hwn]
        have h0 : |D| ≤ |ma| + |mb| := by have := abs_sub mb ma; rw [hD]; linarith
        have h1 := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ nb)
        have h3 : (nb : ℝ) * |ma| ≤ nb * (na * |ma|) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hna1) (by linarith)
        have h4 := mul_le_mul_of_nonneg_left hma1 (by linarith : (0 : ℝ) ≤ nb)
        have h5 : (nb : ℝ) * (1.01 * Aa) ≤ 2 ^ 32 * (1.01 * Aa) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h6 : (1.01 : ℝ) * Ab ≤ 2 ^ 32 * (1.01 * Ab) :=
          le_mul_of_one_le_left (by positivity) (by norm_num)
        linarith
      have hnt : n * tiny ≤ Aa + Ab := by
        have : n * tiny = na * tiny + nb * tiny := by rw [hn]; ring
        linarith
      have hnwt : n * w * tiny ≤ Aa + Ab := by rw [hwn]; linarith
      exact sg_nmp hn0.le hw0' hA0 hpy (by linarith) hnD hnwt hnt
    -- the deviation `m_b − m̂`
    have hdev := sg_dev (ma := ma) (mb := mb) hw0' eD ef ep em
    set Eq := u * |Dh| * (1.0003 + 2.0001 * w) + u * (|ma + p| + tiny) + 2.0002 * u * tiny
      with hEq
    have hEq0 : 0 ≤ Eq := by simp only [hEq]; positivity
    -- the roundings of the correction term
    have hmbm : |mb - m'| ≤ 2 ^ 408 := by have := abs_sub mb m'; linarith
    obtain ⟨eq', hqb⟩ := M.err_le (z := mb - m') (B := 2 ^ 408) hmbm (by norm_num) (by norm_num)
    set q := M.fl (mb - m') with hq
    have hnq : |(nb : ℝ) * q| ≤ 2 ^ 441 := by
      rw [abs_mul, Nat.abs_cast]
      have := mul_le_mul (by linarith : (nb : ℝ) ≤ 2 ^ 32) hqb (abs_nonneg _) (by norm_num)
      linarith
    obtain ⟨er, hrb⟩ := M.err_le (z := (nb : ℝ) * q) (B := 2 ^ 441) hnq (by norm_num) (by norm_num)
    set r := M.fl ((nb : ℝ) * q) with hr
    have hrD : |r * Dh| ≤ 2 ^ 845 := by
      rw [abs_mul]
      have := mul_le_mul hrb hDhb (abs_nonneg _) (by positivity)
      linarith
    obtain ⟨eT, hTb⟩ := M.err_le (z := r * Dh) (B := 2 ^ 845) hrD (by norm_num) (by norm_num)
    set T := M.fl (r * Dh) with hT
    have hT1 := sg_T (v := 1 - w) hnb1 (by linarith) hEq0 hdev eq' er eT
    rw [hv] at hT1
    -- the correction term in `Δ̂`
    have hX1 : (nb : ℝ) * |Dh| * Eq ≤ u * |Dh| ^ 2 * nb * (1.0003 + 2.0001 * w)
        + 1.03 * u * (Aa + Ab) * |Dh| * w + 3.0002 * u * nb * |Dh| * tiny := by
      have k : (nb : ℝ) * |ma + p| ≤ 1.02 * (Aa + Ab) * w := by
        have e : (nb : ℝ) * |ma + p| = w * (n * |ma + p|) := by rw [← hwn]; ring
        rw [e]
        have := mul_le_mul_of_nonneg_left hnmp hw0'; linarith
      exact sg_X1 (abs_nonneg Dh) hA0 hw0' k
    have hTf := sg_T_final (A := Aa + Ab) (E := |T - Dh ^ 2 * h|) hna1 hnb1 (abs_nonneg Dh) hA0 hw0' hw1 hwh hnh
      (by linarith) hX1 (by rw [sq_abs]; exact hT1)
    rw [sq_abs] at hTf
    -- from `Δ̂` to `Δ`
    have hDD : |Dh - (Mb - Ma)| ≤ u * |Mb - Ma| + 6.0001 * u * (Aa + Ab) + u * tiny := by
      have h1 : |D - (Mb - Ma)| ≤ 6 * u * (Aa + Ab) := by
        have e : D - (Mb - Ma) = (mb - Mb) - (ma - Ma) := by rw [hD]; ring
        rw [e]; have := abs_sub (mb - Mb) (ma - Ma); linarith
      have h2 : |D| ≤ |Mb - Ma| + 6 * u * (Aa + Ab) := by
        have := abs_sub_abs_le_abs_sub D (Mb - Ma); linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hu.le
      have h4 : u * (6 * u * (Aa + Ab)) ≤ 0.0001 * u * (Aa + Ab) := by
        have := mul_le_mul_of_nonneg_right (by linarith : 6 * u ≤ 0.0001)
          (mul_nonneg hu.le hA0)
        linarith
      have e : Dh - (Mb - Ma) = (Dh - D) + (D - (Mb - Ma)) := by ring
      rw [e]
      have := abs_add_le (Dh - D) (D - (Mb - Ma))
      linarith
    have hTc := sg_conv (by linarith) hnu hh0 hA0 hDD hTf
    -- the co-moment
    have hSS : |Shb + T| ≤ 2 ^ 902 := by
      have := abs_add_le Shb T
      have := abs_sub_abs_le_abs_sub Shb Sb
      have := sb.com; have := sb.Eb; have := sb.Sb; have := abs_of_nonneg sb.S0
      linarith
    obtain ⟨e1, hS1b⟩ := M.err_le (z := Shb + T) (B := 2 ^ 902) hSS (by norm_num) (by norm_num)
    set Sh1 := M.fl (Shb + T) with hSh1
    have hSS2 : |Sha + Sh1| ≤ 2 ^ 904 := by
      have := abs_add_le Sha Sh1
      have := abs_sub_abs_le_abs_sub Sha Sa
      have := sa.com; have := sa.Eb; have := sa.Sb; have := abs_of_nonneg sa.S0
      linarith
    obtain ⟨e2, -⟩ := M.err_le (z := Sha + Sh1) (B := 2 ^ 904) hSS2 (by norm_num) (by norm_num)
    have hX : 0 ≤ h * |Mb - Ma| := mul_nonneg hh0 (abs_nonneg _)
    have hΔS : 0 ≤ (Mb - Ma) ^ 2 * h := mul_nonneg (sq_nonneg _) hh0
    have hc := sg_assemble sa.S0 sb.S0 hΔS sa.com sb.com hTc e1 e2
    have hle := sg_new_le (n := n) (A := Aa + Ab) (by linarith) hh2 hA0 hX
      (add_nonneg sa.S0 sb.S0) hΔS le_rfl
    linarith

/-! ## The two-pass block -/

/-- `γ n ≤ 1.01 n u` for `n u ≤ 2⁻²¹`. -/
theorem gamma_le_101 {n : ℕ} (h : (n : ℝ) * u ≤ 1 / 2 ^ 21) : gamma n ≤ 1.01 * n * u := by
  unfold gamma
  have h0 : 0 ≤ (n : ℝ) * u := mul_nonneg (by positivity) u_pos.le
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 0.01 - 1.01 * ((n : ℝ) * u))]

/-- `1.02 n + 4 ≤ 24 (⌈log₂ n⌉ + 1)` for `1 ≤ n ≤ 128`: a block's underflow
terms fit the tree invariant's. -/
theorem block_tiny {n : ℕ} (h : n ≤ 128) : 1.02 * (n : ℝ) + 4 ≤ 24 * (Nat.clog 2 n + 1) := by
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.clog 2 n := ⟨_, rfl⟩
  rw [← hk]
  have hnk : n ≤ 2 ^ k := hk ▸ Nat.le_pow_clog (by norm_num) n
  have hn' : (n : ℝ) ≤ 128 := by exact_mod_cast h
  have hnk' : (n : ℝ) ≤ 2 ^ k := by exact_mod_cast hnk
  rcases Nat.lt_or_ge k 7 with hc | hc
  · have key : 1.02 * (2 : ℝ) ^ k + 4 ≤ 24 * ((k : ℝ) + 1) := by
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    linarith
  · have h7 : (7 : ℝ) ≤ k := by exact_mod_cast hc
    linarith

/-- A fused square: `fl(z) · fl(z)` within `5u z² + 3u·tiny` of `z²`. -/
theorem StdModel.sq_fused {z : ℝ} (hz : |z| ≤ 2 ^ 450) :
    |M.fl z * M.fl z - z ^ 2| ≤ 5 * u * z ^ 2 + 3 * u * tiny := by
  obtain ⟨hu, hu', ht, -, hmax⟩ := fpFacts
  have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set a := |z|
  have ha : 0 ≤ a := abs_nonneg z
  have hz2 : z ^ 2 = a ^ 2 := (sq_abs z).symm
  have e1 := M.err z (by linarith)
  set d := M.fl z
  have hdz : |d * d - z ^ 2| ≤ u * (a + tiny) * (2 * a + u * (a + tiny)) := by
    have : d * d - z ^ 2 = (d - z) * (d + z) := by ring
    rw [this, abs_mul]
    have h2 : |d + z| ≤ 2 * a + u * (a + tiny) := by
      have := abs_add_le (d - z) (2 * z)
      rw [show d - z + 2 * z = d + z by ring, abs_mul, abs_two] at this; linarith
    exact mul_le_mul e1 h2 (abs_nonneg _) (by positivity)
  have hat : a * tiny ≤ (a ^ 2 + tiny ^ 2) / 2 := by nlinarith [sq_nonneg (a - tiny)]
  have ht2 : tiny ^ 2 ≤ tiny := by nlinarith
  have hsmall : u * (a + tiny) * (2 * a + u * (a + tiny)) ≤ 3.01 * u * a ^ 2 + 1.01 * u * tiny := by
    have hu2 : u * u ≤ u / 2 ^ 53 := by nlinarith
    nlinarith [mul_nonneg hu.le (sq_nonneg a), mul_nonneg hu.le ht.le, mul_nonneg hu.le ha,
      mul_nonneg (mul_nonneg hu.le hu.le) (sq_nonneg (a + tiny))]
  rw [hz2] at hdz ⊢
  have : 0 ≤ u * a ^ 2 := by positivity
  have : 0 ≤ u * tiny := by positivity
  linarith

/-- The rounded or fused squares of a block: their sum within `5u Z + 3nu·tiny`
of `Z = Σ (x − m)²`, each `≥ 0`. -/
theorem StdModel.block_sq {m : ℝ} : ∀ {xs ws : List ℝ},
    List.Forall₂ (fun x w => w = M.fl (M.fl (x - m) * M.fl (x - m))
      ∨ w = M.fl (x - m) * M.fl (x - m)) xs ws → (∀ x ∈ xs, |x - m| ≤ 2 ^ 450) →
    |ws.sum - (xs.map fun x => (x - m) ^ 2).sum|
        ≤ 5 * u * (xs.map fun x => (x - m) ^ 2).sum + xs.length * (3 * u * tiny)
      ∧ ∀ w ∈ ws, 0 ≤ w := by
  intro xs ws h
  induction h with
  | nil => intro _; simp
  | @cons x w xs ws hxw _ ih =>
    intro hb
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => hb y (by simp [hy]))
    have hx := hb x (by simp)
    have k : |w - (x - m) ^ 2| ≤ 5 * u * (x - m) ^ 2 + 3 * u * tiny ∧ 0 ≤ w := by
      rcases hxw with rfl | rfl
      · exact ⟨M.sq_step hx, M.nonneg _ (mul_self_nonneg _)⟩
      · exact ⟨M.sq_fused hx, mul_self_nonneg _⟩
    refine ⟨?_, ?_⟩
    · simp only [List.sum_cons, List.map_cons, List.length_cons]
      have e : w + ws.sum - ((x - m) ^ 2 + (xs.map fun x => (x - m) ^ 2).sum)
          = (w - (x - m) ^ 2) + (ws.sum - (xs.map fun x => (x - m) ^ 2).sum) := by ring
      rw [e]
      have := abs_add_le (w - (x - m) ^ 2) (ws.sum - (xs.map fun x => (x - m) ^ 2).sum)
      push_cast
      linarith [k.1]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact k.2
      · exact ih2 y hy

theorem mag_of_nonneg : ∀ {ws : List ℝ}, (∀ w ∈ ws, 0 ≤ w) → mag ws = ws.sum + ws.length * tiny
  | [], _ => by simp
  | w :: ws, h => by
    simp only [mag_cons, List.sum_cons, List.length_cons]
    rw [abs_of_nonneg (h w (by simp)), mag_of_nonneg (fun z hz => h z (by simp [hz]))]
    push_cast; ring

/-- The states Polars's two-pass block (`VarState::new`) can give over the
values `xs`, at most 128 of them: the mean `m = fl(s₁ / n)` of a sum `s₁` of
the values in any order, and the co-moment, a sum in any order of the squares
`fl(x − m)²`, each rounded or fused into its addition. -/
def StdModel.Block (xs : List ℝ) (s : ℕ × ℝ × ℝ) : Prop :=
  xs ≠ [] ∧ xs.length ≤ 128 ∧ ∃ s1 ws s2, (∃ ys, ys.Perm xs ∧ M.toRnd.Tree ys s1) ∧
    List.Forall₂ (fun x w =>
      w = M.fl (M.fl (x - M.fl (s1 / xs.length)) * M.fl (x - M.fl (s1 / xs.length)))
        ∨ w = M.fl (x - M.fl (s1 / xs.length)) * M.fl (x - M.fl (s1 / xs.length))) xs ws ∧
    (∃ ys, ys.Perm ws ∧ M.toRnd.Tree ys s2) ∧ s = (xs.length, M.fl (s1 / xs.length), s2)

theorem comoment_dupL_eq (xs : List ℝ) :
    comoment (dupL xs) = (xs.map fun x => (x - mx (dupL xs)) ^ 2).sum := by
  unfold comoment
  rw [my_dupL]
  simp only [dupL, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro x _
  ring

/-- The arithmetic at the end of `tInv_block`: the block's errors in the tree
invariant's bound, with `Σ|D| = 0`. -/
theorem block_arith {n S Z W s2 g A ε2 L t : ℝ} (hn1 : 1 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (ht : 0 ≤ t) (hg0 : 0 ≤ g) (hg : g ≤ 1.01 * n * u)
    (hε0 : 0 ≤ ε2) (hZ : Z = S + n * ε2) (hε : ε2 ≤ 9.13 * u ^ 2 * A ^ 2) (hW0 : 0 ≤ W)
    (hW : |W - Z| ≤ 5 * u * Z + n * (3 * u * t)) (hs2 : |s2 - W| ≤ g * (W + n * t))
    (hL : 2 * n ≤ L) (hLt : n * (1.02 * n + 4) ≤ 12 * L) :
    |s2 - S| ≤ (1 + 3 * n * u) * (17 * u * A * 0 + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2
      + 12 * u * t * L) := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hn0 : 0 ≤ n := by linarith
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hW' : W ≤ (1 + 5 * u) * Z + n * (3 * u * t) := by linarith [(abs_le.mp hW).2]
  have k1 : g * (W + n * t) ≤ 1.01 * n * u * ((1 + 5 * u) * Z + n * (3 * u * t) + n * t) :=
    mul_le_mul hg (by linarith) (by positivity) (by positivity)
  have hsum : |s2 - S| ≤ |s2 - W| + |W - Z| + |Z - S| := by
    have e : s2 - S = (s2 - W) + (W - Z) + (Z - S) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by linarith [abs_add_le (s2 - W) (W - Z)])
  have hZS : |Z - S| = n * ε2 := by rw [hZ]; ring_nf; exact abs_of_nonneg (by positivity)
  -- the small products
  have p1 : 0 ≤ n * u * Z := by positivity
  have a1 : n * u * u * Z ≤ 1 / 2 ^ 53 * (n * u * Z) := by
    have := mul_le_mul_of_nonneg_left hu' p1; linarith
  have p2 : 0 ≤ n * n * u * t := by positivity
  have a2 : n * n * u * u * t ≤ 1 / 2 ^ 53 * (n * n * u * t) := by
    have := mul_le_mul_of_nonneg_left hu' p2; linarith
  have p3 : 0 ≤ n * ε2 := by positivity
  have a3 : n * u * (n * ε2) ≤ 1 / 2 ^ 21 * (n * ε2) := mul_le_mul_of_nonneg_right hnu p3
  have a4 : u * (n * ε2) ≤ 1 / 2 ^ 53 * (n * ε2) := mul_le_mul_of_nonneg_right hu' p3
  have a5 : n * u * u * (n * ε2) ≤ 1 / 2 ^ 21 * (n * ε2) := by
    have h1 : n * u * u ≤ 1 / 2 ^ 21 := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 p3
  have a6 : n * ε2 ≤ 9.13 * (n * u ^ 2 * A ^ 2) := by
    have := mul_le_mul_of_nonneg_left hε hn0; linarith
  have a7 : n * u ^ 2 * A ^ 2 ≤ u ^ 2 * L * A ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ u ^ 2 * A ^ 2); linarith
  have a8 : n * u * t * (1.02 * n + 4) ≤ 12 * u * t * L := by
    have := mul_le_mul_of_nonneg_left hLt (by positivity : 0 ≤ u * t); linarith
  have a9 : u * S ≤ n * u * S := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ u * S); linarith
  have p4 : 0 ≤ n * u * S := by positivity
  have p5 : 0 ≤ 17 * u * A * 0 + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * t * L := by
    have : 0 ≤ L := by linarith
    positivity
  have k2 : 17 * u * A * 0 + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2 + 12 * u * t * L
      ≤ (1 + 3 * n * u) * (17 * u * A * 0 + 9 * u * n * S + 60 * u ^ 2 * L * A ^ 2
        + 12 * u * t * L) := le_mul_of_one_le_left p5 (by nlinarith)
  rw [hZ] at k1 a1
  nlinarith

/-- The mean of a block: `fl(s₁ / n)`, with `s₁` the values' sum in any order
and tree, within `3.02 u Σ (|x| + tiny)` of the exact mean. -/
theorem StdModel.block_mean {xs : List ℝ} {s1 : ℝ} (hne : xs ≠ []) (h128 : xs.length ≤ 128)
    (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) (ht1 : ∃ ys, ys.Perm xs ∧ M.toRnd.Tree ys s1) :
    |M.fl (s1 / xs.length) - xs.sum / xs.length| ≤ 3.02 * u * mag xs := by
  obtain ⟨ys1, hp1, t1⟩ := ht1
  obtain ⟨hu, hu', ht, -, hmax⟩ := fpFacts
  have hn1 : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn128 : (xs.length : ℝ) ≤ 128 := by exact_mod_cast h128
  have hnu : (xs.length : ℝ) * u ≤ 1 / 2 ^ 21 := by
    calc (xs.length : ℝ) * u ≤ 128 * (1 / 2 ^ 53) := mul_le_mul hn128 hu' hu.le (by norm_num)
      _ ≤ 1 / 2 ^ 21 := by norm_num
  have hg := gamma_le_101 hnu
  obtain ⟨hA0, hAb, hnt, hMA, -, -, -⟩ := list_facts hne (by omega) hB
  have hn0 : (0 : ℝ) < xs.length := by linarith
  have hov1 : (1 + gamma xs.length) * mag xs ≤ maxFinite := by
    have : (1 + gamma xs.length) * mag xs ≤ 2 * 2 ^ 432 :=
      mul_le_mul (by linarith) hAb hA0 (by norm_num)
    have : (2 : ℝ) * 2 ^ 432 ≤ 2 ^ 1023 := by norm_num
    linarith
  have hs1 : |s1 - xs.sum| ≤ gamma xs.length * mag xs := by
    have := (t1.error (by rw [hp1.length_eq]; linarith)
      (by rw [hp1.length_eq, M.toRnd.mag_perm hp1]; exact hov1)).perm hp1
    exact this
  have hM0 : mx (dupL xs) = xs.sum / xs.length := by
    simp [mx, sx, dupL, List.map_map, Function.comp_def]
  have hs1n : |s1 / xs.length - mx (dupL xs)| ≤ 1.01 * u * mag xs := by
    rw [hM0, ← sub_div, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    have := mul_le_mul_of_nonneg_right hg hA0
    nlinarith
  have hMA' : |mx (dupL xs)| ≤ mag xs := by nlinarith [abs_nonneg (mx (dupL xs))]
  have hnt' : tiny ≤ mag xs := by nlinarith
  have hs1b : |s1 / xs.length| ≤ 2 ^ 433 := by
    have := abs_sub_abs_le_abs_sub (s1 / xs.length) (mx (dupL xs))
    have : 1.01 * u * mag xs ≤ mag xs := by nlinarith
    linarith
  obtain ⟨em, hmb⟩ := M.err_le (z := s1 / xs.length) (B := 2 ^ 433) hs1b (by norm_num)
    (by norm_num)
  set m := M.fl (s1 / xs.length) with hm
  have hmean : |m - mx (dupL xs)| ≤ 3.02 * u * mag xs := by
    have e : m - mx (dupL xs) = (m - s1 / xs.length) + (s1 / xs.length - mx (dupL xs)) := by ring
    rw [e]
    have := abs_add_le (m - s1 / xs.length) (s1 / xs.length - mx (dupL xs))
    have h1 : |s1 / xs.length| ≤ mag xs + 1.01 * u * mag xs := by
      have := abs_sub_abs_le_abs_sub (s1 / xs.length) (mx (dupL xs)); linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hu.le
    have h3 := mul_le_mul_of_nonneg_left hnt' hu.le
    have h4 : u * (1.01 * u * mag xs) ≤ 0.01 * u * mag xs := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1.01 * u ≤ 0.01) (mul_nonneg hu.le hA0)
      linarith
    linarith
  rw [← hM0]; exact hmean

set_option maxHeartbeats 1000000 in
/-- **A two-pass block meets the tree invariant**, with `Σ|D| = 0`. -/
theorem StdModel.tInv_block {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.Block xs s)
    (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) : TInv xs s := by
  obtain ⟨hne, h128, s1, ws, s2, ⟨ys1, hp1, t1⟩, hw, ⟨ys2, hp2, t2⟩, rfl⟩ := h
  obtain ⟨hu, hu', ht, ht1, hmax⟩ := fpFacts
  have htt : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  have hn1 : (1 : ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn128 : (xs.length : ℝ) ≤ 128 := by exact_mod_cast h128
  have hnu : (xs.length : ℝ) * u ≤ 1 / 2 ^ 21 := by
    calc (xs.length : ℝ) * u ≤ 128 * (1 / 2 ^ 53) := mul_le_mul hn128 hu' hu.le (by norm_num)
      _ ≤ 1 / 2 ^ 21 := by norm_num
  have hg := gamma_le_101 hnu
  have hg0 : 0 ≤ gamma xs.length := gamma_nonneg (by linarith)
  have hg1 : gamma xs.length ≤ 1 := by nlinarith
  obtain ⟨hA0, hAb, -, -, hMb, hS0, -⟩ := list_facts hne (by omega) hB
  have hn0 : (0 : ℝ) < xs.length := by linarith
  have hM0 : mx (dupL xs) = xs.sum / xs.length := by
    simp [mx, sx, dupL, List.map_map, Function.comp_def]
  have hmean : |M.fl (s1 / xs.length) - mx (dupL xs)| ≤ 3.02 * u * mag xs := by
    rw [hM0]; exact M.block_mean hne h128 hB ⟨ys1, hp1, t1⟩
  set m := M.fl (s1 / xs.length) with hm
  refine ⟨rfl, ?_, 0, le_rfl, ?_, ?_⟩
  · show |m - mx (dupL xs)| ≤ 6 * u * mag xs
    have := mul_nonneg hu.le hA0
    linarith
  · rw [zero_pow two_ne_zero]; exact mul_nonneg (Lw_nonneg _) hS0
  show |s2 - comoment (dupL xs)| ≤ tBound xs.length (mag xs) 0 (comoment (dupL xs)) (Lw xs.length)
  -- the squares
  set ε := m - mx (dupL xs) with hε
  have hdev : ∀ x ∈ xs, |x - m| ≤ 2 ^ 450 := by
    intro x hx
    have := abs_sub x m
    have := hB x hx
    have : |m| ≤ 2 ^ 434 := by
      have h1 := abs_sub_abs_le_abs_sub m (mx (dupL xs))
      have h2 : 3.02 * u * mag xs ≤ 3.02 * (1 / 2 ^ 53) * 2 ^ 432 :=
        mul_le_mul (by linarith) hAb hA0 (by norm_num)
      linarith
    linarith
  obtain ⟨hws, hws0⟩ := M.block_sq hw hdev
  have hlen : ws.length = xs.length := hw.length_eq.symm
  set Z := (xs.map fun x => (x - m) ^ 2).sum with hZ
  have hZS : Z = comoment (dupL xs) + xs.length * ε ^ 2 := by
    have hsh := sum_sq_shift xs hne ε
    have e1 : xs.sum / xs.length + ε = m := by rw [hε, hM0]; ring
    rw [e1] at hsh
    rw [hZ, hsh, comoment_dupL_eq, hM0]
  -- the sum of the squares
  have hW0 : 0 ≤ ws.sum := List.sum_nonneg hws0
  have hmagw : mag ws = ws.sum + xs.length * tiny := by rw [mag_of_nonneg hws0, hlen]
  have hZb : Z ≤ 2 ^ 32 * 2 ^ 900 := by
    have := abs_sum_le_of_bound (B := 2 ^ 900) (xs := xs.map fun x => (x - m) ^ 2) (by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      rw [abs_of_nonneg (sq_nonneg _)]
      calc (x - m) ^ 2 = |x - m| ^ 2 := (sq_abs _).symm
        _ ≤ (2 ^ 450) ^ 2 := by gcongr; exact hdev x hx
        _ = 2 ^ 900 := by norm_num)
    simp only [List.length_map] at this
    have h1 := le_abs_self Z
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (xs.length : ℝ) ≤ 2 ^ 32)
      (by norm_num : (0 : ℝ) ≤ 2 ^ 900)
    linarith
  have hZ0 : 0 ≤ Z := List.sum_nonneg fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity
  have hov2 : (1 + gamma xs.length) * mag ws ≤ maxFinite := by
    rw [hmagw]
    have h1 : ws.sum ≤ 2 * 2 ^ 932 + 1 := by
      have := (abs_le.mp hws).2
      have : 5 * u * Z ≤ Z := by nlinarith
      have : (xs.length : ℝ) * (3 * u * tiny) ≤ 1 := by
        have : 3 * u * tiny ≤ 1 / 2 ^ 8 := by
          have := mul_le_mul hu' htt ht.le (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 53); nlinarith
        nlinarith
      linarith
    have h2 : ws.sum + xs.length * tiny ≤ 2 ^ 935 := by
      have : (xs.length : ℝ) * tiny ≤ 1 := by nlinarith
      linarith
    have := mul_le_mul (by linarith : 1 + gamma xs.length ≤ 2) h2 (by positivity) (by norm_num)
    have : (2 : ℝ) * 2 ^ 935 ≤ 2 ^ 1023 := by norm_num
    linarith
  have hs2 : |s2 - ws.sum| ≤ gamma xs.length * (ws.sum + xs.length * tiny) := by
    have := (t2.error (by rw [hp2.length_eq, hlen]; linarith)
      (by rw [hp2.length_eq, M.toRnd.mag_perm hp2, hlen]; exact hov2)).perm hp2
    have e : M.toRnd.Near ws s2 = (|s2 - ws.sum| ≤ gamma ws.length * mag ws) := rfl
    rw [e, hlen, hmagw] at this
    exact this
  -- the mean's error, squared
  have hε2 : ε ^ 2 ≤ 9.13 * u ^ 2 * mag xs ^ 2 := by
    have h1 : ε ^ 2 ≤ (3.02 * u * mag xs) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hmean 2
    nlinarith
  -- the weight
  have hL2 : 2 * (xs.length : ℝ) ≤ Lw xs.length := Lw_two _
  have hLt : (xs.length : ℝ) * (1.02 * xs.length + 4) ≤ 12 * Lw xs.length := by
    have := block_tiny h128
    unfold Lw
    have := mul_le_mul_of_nonneg_left this hn0.le
    nlinarith
  unfold tBound
  exact block_arith hn1 hnu hS0 hA0 ht.le hg0 hg (sq_nonneg ε) hZS hε2 hW0
    hws hs2 hL2 hLt

/-! ## Polars's plans -/

/-- The states Polars's `var` computes over the values `xs`, in any order and
any tree: a run of Welford's updates (grouped, `insert_one`), a two-pass
block (ungrouped, `VarState::new`), or a merge of two of them
(`VarState::combine`). -/
inductive StdModel.PRun (M : StdModel) : List ℝ → ℕ × ℝ × ℝ → Prop
  | welford (xs : List ℝ) : StdModel.PRun M xs (M.wState xs)
  | block {xs : List ℝ} {s : ℕ × ℝ × ℝ} : M.Block xs s → StdModel.PRun M xs s
  | merge {xa xb : List ℝ} {t s : ℕ × ℝ × ℝ} : StdModel.PRun M xa t → StdModel.PRun M xb s →
      StdModel.PRun M (xa ++ xb) (M.sgMerge t s)

theorem StdModel.PRun.count {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s) :
    s.1 = xs.length := by
  induction h with
  | welford xs => simp [StdModel.wState, M.foldl_wStep_count]
  | block hb => obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := hb; rfl
  | merge _ _ iht ihs =>
    simp only [StdModel.sgMerge, List.length_append]
    split_ifs with h1 h2
    · omega
    · omega
    · simp [iht, ihs]

/-- **Every state Polars computes meets the tree invariant**, for `n ≤ 2³²`
doubles at most `2³⁹⁹` in magnitude. -/
theorem StdModel.tInv_prun {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s) :
    xs ≠ [] → xs.length ≤ 2 ^ 32 → (∀ x ∈ xs, |x| ≤ 2 ^ 399) → (∀ x ∈ xs, M.fl x = x) →
    TInv xs s := by
  induction h with
  | welford xs => exact fun hne hN hB hrep => tInv_of_wInv (M.wInv_all hne hN hB hrep)
  | block hb => exact fun _ _ hB _ => M.tInv_block hb hB
  | @merge xa xb t s ht hs iht ihs =>
    intro hne hN hB hrep
    simp only [List.length_append, List.mem_append] at hne hN hB hrep
    have hct := ht.count
    have hcs := hs.count
    rcases eq_or_ne xa [] with ha | ha
    · subst ha
      have hb : xb ≠ [] := by simpa using hne
      have hcs' : s.1 ≠ 0 := by rw [hcs]; exact (List.length_pos_iff.mpr hb).ne'
      have : M.sgMerge t s = s := by simp [StdModel.sgMerge, hct, hcs']
      rw [this, List.nil_append]
      exact ihs hb (by simpa using hN) (fun x hx => hB x (Or.inr hx)) (fun x hx => hrep x (Or.inr hx))
    rcases eq_or_ne xb [] with hb | hb
    · subst hb
      have : M.sgMerge t s = t := by simp [StdModel.sgMerge, hcs]
      rw [this, List.append_nil]
      exact iht ha (by simpa using hN) (fun x hx => hB x (Or.inl hx)) (fun x hx => hrep x (Or.inl hx))
    have hla : 1 ≤ xa.length := List.length_pos_iff.mpr ha
    have hlb : 1 ≤ xb.length := List.length_pos_iff.mpr hb
    exact tInv_merge_of M.sgMerge_spec ha hb hN (fun x hx => hB x (Or.inl hx))
      (fun x hx => hB x (Or.inr hx))
      (iht ha (by omega) (fun x hx => hB x (Or.inl hx)) (fun x hx => hrep x (Or.inl hx)))
      (ihs hb (by omega) (fun x hx => hB x (Or.inr hx)) (fun x hx => hrep x (Or.inr hx)))

/-- **Polars's variance, to first order in the spread**: for any state Polars
computes over `n ≤ 2³²` doubles at most `2³⁹⁹` in magnitude, the co-moment is
within DuckDB's bound (`chanVar_rel`), `148 n u √(Q' S) + 3961 n² u² Q' +
793 n u · tiny`. -/
theorem StdModel.plVar_rel {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s) (hne : xs ≠ [])
    (hN : xs.length ≤ 2 ^ 32) (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) (hrep : ∀ x ∈ xs, M.fl x = x) :
    |s.2.2 - comoment (dupL xs)|
      ≤ 148 * xs.length * u * √((xs.map fun x => (|x| + tiny) ^ 2).sum * comoment (dupL xs))
        + 3961 * xs.length ^ 2 * u ^ 2 * (xs.map fun x => (|x| + tiny) ^ 2).sum
        + 793 * xs.length * u * tiny :=
  (M.tInv_prun h hne hN hB hrep).rel hne hN

/-- Polars's `VarState::finalize`: a negative variance becomes `0`. -/
noncomputable def clampVar (v : ℝ) : ℝ := if v < 0 then 0 else v

theorem clampVar_nonneg (v : ℝ) : 0 ≤ clampVar v := by
  unfold clampVar; split_ifs with h
  · exact le_rfl
  · exact not_lt.mp h

theorem abs_clampVar_sub_le {v V : ℝ} (hV : 0 ≤ V) : |clampVar v - V| ≤ |v - V| := by
  unfold clampVar; split_ifs with h
  · rw [zero_sub, abs_neg, abs_of_nonneg hV, abs_of_neg (by linarith)]; linarith
  · exact le_rfl

/-- **Polars's `VAR_*`** (`varOf_props` of the reference, for Polars's
algorithms): `VarState::finalize`'s `fl(M₂ / d)`, clamped at `0`, is `≥ 0` and
within `varTol` of `S / d`, for every `r ≥ √(Q' S)`. -/
theorem StdModel.core_var_polars {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s)
    (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32) (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 398)
    (hrep : ∀ x ∈ xs, M.fl x = x) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ xs.length)
    {r : ℝ} (hr : √((xs.map fun x => (|x| + tiny) ^ 2).sum) * √(comoment (dupL xs)) ≤ r) :
    0 ≤ clampVar (M.fl (s.2.2 / d)) ∧
      |clampVar (M.fl (s.2.2 / d)) - comoment (dupL xs) / d|
        ≤ varTol xs.length d r (xs.map fun x => (|x| + tiny) ^ 2).sum := by
  refine ⟨clampVar_nonneg _, le_trans (abs_clampVar_sub_le
    (div_nonneg (comoment_dupL_nonneg xs) (by positivity))) ?_⟩
  exact M.var_of_rel hne hN hB
    (M.plVar_rel h hne hN (fun x hx => le_trans (hB x hx) (by norm_num)) hrep) hd1 hdn hr

/-- **`"abs"` of a Polars `VAR_*` against the reference (D30)**: within
`varTol + u · |S / d|` of any `v` within `u` of `S / d`, relatively, which the
reference's `varOf` is. -/
theorem StdModel.epsilon_var_polars {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s)
    (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32) (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 398)
    (hrep : ∀ x ∈ xs, M.fl x = x) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ xs.length)
    {r : ℝ} (hr : √((xs.map fun x => (|x| + tiny) ^ 2).sum) * √(comoment (dupL xs)) ≤ r)
    {v : ℝ} (hv : |v - comoment (dupL xs) / d| ≤ u * |comoment (dupL xs) / d|) :
    |clampVar (M.fl (s.2.2 / d)) - v|
      ≤ varTol xs.length d r (xs.map fun x => (|x| + tiny) ^ 2).sum
        + u * |comoment (dupL xs) / d| := by
  have h1 := (M.core_var_polars h hne hN hB hrep hd1 hdn hr).2
  set e := comoment (dupL xs) / d
  calc |clampVar (M.fl (s.2.2 / d)) - v| = |(clampVar (M.fl (s.2.2 / d)) - e) - (v - e)| := by
        ring_nf
    _ ≤ |clampVar (M.fl (s.2.2 / d)) - e| + |v - e| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **`"abs"` of a Polars `STDDEV_*` against the reference (D30)**: the
rounded root of Polars's clamped variance is within
`√τ + u (√V + √τ) + 2u · tiny + u √V` of any `w` within `u (√V + tiny)` of
`√V`, `V = S / d`, `τ = varTol` (`stddev_of_var`). -/
theorem StdModel.epsilon_stddev_polars {xs : List ℝ} {s : ℕ × ℝ × ℝ} (h : M.PRun xs s)
    (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32) (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 398)
    (hrep : ∀ x ∈ xs, M.fl x = x) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ xs.length)
    {r : ℝ} (hr : √((xs.map fun x => (|x| + tiny) ^ 2).sum) * √(comoment (dupL xs)) ≤ r)
    {w : ℝ} (hw : |w - √(comoment (dupL xs) / d)| ≤ u * (√(comoment (dupL xs) / d) + tiny)) :
    |M.fl √(clampVar (M.fl (s.2.2 / d))) - w|
      ≤ √(varTol xs.length d r (xs.map fun x => (|x| + tiny) ^ 2).sum)
        + u * (√(comoment (dupL xs) / d)
          + √(varTol xs.length d r (xs.map fun x => (|x| + tiny) ^ 2).sum))
        + 2 * u * tiny + u * √(comoment (dupL xs) / d) :=
  M.stddev_of_var hN hB hd1 (M.core_var_polars h hne hN hB hrep hd1 hdn hr).1
    (fun _ h' => (M.core_var_polars h hne hN hB hrep hd1 hdn h').2) hr hw

end FloatBounds

end

open Lean in
run_cmd do
  for thm in ["FloatBounds.StdModel.core_var_polars", "FloatBounds.StdModel.epsilon_var_polars",
      "FloatBounds.StdModel.epsilon_stddev_polars"] do
    unless (← getEnv).contains thm.toName do
      throwError "no theorem {thm}"
