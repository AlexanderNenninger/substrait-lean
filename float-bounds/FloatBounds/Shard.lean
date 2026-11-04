module

public import FloatBounds.Core

/-!
# Sharded sums against the sequential sum (#85, stage 5; #428)

`--shard` and `sverify.partition` with `float_order="any"` add each shard's
doubles, then add the partial sums (`floatPartial`, `floatCombine` in
`SubstraitLean/Partition.lean`). The reference adds all of them in one pass
(`floatSum`). This file bounds the difference, from what the shards report:

* `sharded_near`, `sharded_avg_near`: the two-phase `SUM` (and `AVG`) of `k`
  shards of at most `m` values is within
  `(γ (m + k) + γ n) · (mag xs + k · tiny)` of the sequential one over the
  same `n` values in any order (`sharded_error` and `sum_error`, both
  measured against the exact sum).
* `mag_le_absSum`: each shard's rounded `SUM(|x|)` bounds its `Σ |x|` from
  above, so the bound needs only what the partial rows hold: the counts and
  the rounded sums of `|x|`.
* `shardTol_le`, `shardAvgTol_le`: that bound, scaled by `2¹⁰⁷⁴` and rounded
  up, is `shardTolScaled n m k As` (`shardAvgTolScaled`), a few operations on
  natural numbers, defined the same way in `SubstraitLean/Partition.lean`.
* `core_shard_sum`, `core_shard_avg`: the facts the core trusts
  (`floatSum_twoPhase`, `floatAvg_twoPhase` in `SubstraitLean/Partition.lean`),
  for doubles decoded from codes (`Decoded`) of magnitude at most `Bs`, with
  `n (Bs + 2·2⁵²) ≤ 2²⁰⁹⁶`: far from overflow.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

theorem mag_perm {xs ys : List ℝ} (h : xs.Perm ys) : mag xs = mag ys := by
  unfold mag; exact (h.map _).sum_eq

theorem mag_eq (xs : List ℝ) : mag xs = (xs.map abs).sum + xs.length * tiny := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [mag_cons, ih, List.map_cons, List.sum_cons, List.length_cons]; push_cast; ring

theorem mag_map_abs (xs : List ℝ) : mag (xs.map abs) = mag xs := by
  rw [mag_eq, mag_eq]; simp [Function.comp_def]

theorem gamma_lt_one {m : ℕ} (h : ((2 * m : ℕ) : ℝ) * u < 1) : gamma m < 1 := by
  have hu := u_pos
  push_cast at h
  unfold gamma
  rw [div_lt_one (by nlinarith)]; nlinarith

variable (M : StdModel)

/-- A shard's rounded `SUM(|x|)` bounds its magnitude: with at most `m`
values, `(1 − γ m) · mag s ≤ Σ̃ |x| + |s| · tiny`. -/
theorem StdModel.mag_le_absSum {s : List ℝ} {m : ℕ} (hsm : s.length ≤ m) (hm : (m : ℝ) * u < 1)
    (hov : (1 + gamma s.length) * mag s ≤ maxFinite) :
    (1 - gamma m) * mag s ≤ M.sum (s.map abs) + s.length * tiny := by
  have hu := u_pos
  have hs : (s.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hsm) hu.le) hm
  have h := M.sum_error (xs := s.map abs) (by simpa using hs)
    (by simpa [mag_map_abs] using hov)
  simp only [List.length_map, mag_map_abs] at h
  have gm := gamma_mono hsm hm
  have hm0 := mag_nonneg s
  have hge : gamma s.length * mag s ≤ gamma m * mag s := mul_le_mul_of_nonneg_right gm hm0
  have hl := (abs_le.mp h).1
  have he := mag_eq s
  nlinarith

/-- Over all shards: `(1 − γ m) · mag xs ≤ Σ Σ̃ |x| + n · tiny`. -/
theorem StdModel.mag_flatten_le {ss : List (List ℝ)} {m : ℕ} (hm : ∀ s ∈ ss, s.length ≤ m)
    (hmu : (m : ℝ) * u < 1) (hov : ∀ s ∈ ss, (1 + gamma s.length) * mag s ≤ maxFinite) :
    (1 - gamma m) * mag ss.flatten
      ≤ (ss.map fun s => M.sum (s.map abs)).sum + ss.flatten.length * tiny := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have h1 := M.mag_le_absSum (hm s (by simp)) hmu (hov s (by simp))
    have h2 := ih (fun t ht => hm t (by simp [ht])) (fun t ht => hov t (by simp [ht]))
    simp only [List.flatten_cons, mag_append, List.length_append, List.map_cons, List.sum_cons]
    push_cast
    rw [mul_add]
    linarith

/-- **Sharded against sequential**: shards of at most `m` values, `k` of
them, added in two phases, are within `(γ (m + k) + γ n) · (mag xs + k · tiny)`
of the values added in one pass, in any order `ws`. -/
theorem StdModel.sharded_near {ss : List (List ℝ)} {ws : List ℝ} {m : ℕ}
    (hp : ws.Perm ss.flatten) (hm : ∀ s ∈ ss, s.length ≤ m)
    (hn : ((m + ss.length : ℕ) : ℝ) * u < 1) (hw : (ws.length : ℝ) * u < 1)
    (hov : (1 + gamma (m + ss.length)) * (mag ws + ss.length * tiny) ≤ maxFinite)
    (hov' : (1 + gamma ws.length) * mag ws ≤ maxFinite) :
    |M.shardedSum ss - M.sum ws|
      ≤ (gamma (m + ss.length) + gamma ws.length) * (mag ws + ss.length * tiny) := by
  have ht := tiny_pos
  have hmag : mag ws = mag ss.flatten := mag_perm hp
  have hsum : ws.sum = ss.flatten.sum := hp.sum_eq
  have h1 := M.sharded_error hm hn (by rwa [← hmag])
  have h2 := M.sum_error hw hov'
  rw [hsum] at h2
  rw [hmag] at h2 ⊢
  have gw := gamma_nonneg hw
  have kt : 0 ≤ (ss.length : ℝ) * tiny := by positivity
  calc |M.shardedSum ss - M.sum ws|
        = |(M.shardedSum ss - ss.flatten.sum) - (M.sum ws - ss.flatten.sum)| := by ring_nf
    _ ≤ |M.shardedSum ss - ss.flatten.sum| + |M.sum ws - ss.flatten.sum| := abs_sub _ _
    _ ≤ gamma (m + ss.length) * (mag ss.flatten + ss.length * tiny)
          + gamma ws.length * mag ss.flatten := add_le_add h1 h2
    _ ≤ _ := by nlinarith [mul_nonneg gw kt]

/-- **Sharded `AVG` against sequential**: the two sums, each divided by the
count `n` and rounded. -/
theorem StdModel.sharded_avg_near {ss : List (List ℝ)} {ws : List ℝ} {m : ℕ} (hne : ws ≠ [])
    (hp : ws.Perm ss.flatten) (hm : ∀ s ∈ ss, s.length ≤ m)
    (hn : ((m + ss.length + 2 : ℕ) : ℝ) * u < 1) (hw : ((ws.length + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma (m + ss.length)) * (mag ws + ss.length * tiny) ≤ maxFinite)
    (hov' : (1 + gamma ws.length) * mag ws ≤ maxFinite) :
    |M.fl (M.shardedSum ss / ws.length) - M.fl (M.sum ws / ws.length)|
      ≤ (gamma (m + ss.length + 2) + gamma (ws.length + 2)) * (mag ws + ss.length * tiny)
        / ws.length := by
  have ht := tiny_pos
  have hmag : mag ws = mag ss.flatten := mag_perm hp
  have hsum : ws.sum = ss.flatten.sum := hp.sum_eq
  have hl : ss.flatten.length = ws.length := hp.length_eq.symm
  have hne' : ss.flatten ≠ [] := by
    intro h; rw [h] at hp; exact hne (List.Perm.eq_nil hp)
  have h1 := M.sharded_avg_error hne' hm hn (by rwa [← hmag])
  have h2 := M.avg_error hne hw hov'
  rw [hl, ← hsum, ← hmag] at h1
  have hlen : (0 : ℝ) < ws.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn' : (((m + ss.length) + 2 : ℕ) : ℝ) * u < 1 := hn
  have ga := gamma_nonneg hn'
  have gw := gamma_nonneg hw
  have kt : 0 ≤ (ss.length : ℝ) * tiny := by positivity
  calc _ = |(M.fl (M.shardedSum ss / ws.length) - ws.sum / ws.length)
          - (M.fl (M.sum ws / ws.length) - ws.sum / ws.length)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ gamma (m + ss.length + 2) * (mag ws + ss.length * tiny) / ws.length
          + gamma (ws.length + 2) * mag ws / ws.length := add_le_add h1 h2
    _ = (gamma (m + ss.length + 2) * (mag ws + ss.length * tiny)
          + gamma (ws.length + 2) * mag ws) / ws.length := by ring
    _ ≤ _ := by gcongr; nlinarith [mul_nonneg gw kt]

/-! ## Before running: from a cap on the rows and a bound on the values -/

/-- **A-priori bound of a sharded `SUM`**: at most `N` values, each `|x| ≤ B`,
in at most `k` shards. -/
theorem StdModel.sharded_near_of_bound {ss : List (List ℝ)} {ws : List ℝ} {m N k : ℕ} {B : ℝ}
    (hp : ws.Perm ss.flatten) (hm : ∀ s ∈ ss, s.length ≤ m) (hmN : m ≤ N) (hnN : ws.length ≤ N)
    (hk : ss.length ≤ k) (hB0 : 0 ≤ B) (hB : ∀ x ∈ ws, |x| ≤ B)
    (hn : ((N + k : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma (N + k)) * (N * (B + tiny) + k * tiny) ≤ maxFinite) :
    |M.shardedSum ss - M.sum ws| ≤ (gamma (N + k) + gamma N) * (N * (B + tiny) + k * tiny) := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hmk : m + ss.length ≤ N + k := by omega
  have hmku : ((m + ss.length : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu.le) hn
  have hNu : (N : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N ≤ N + k by omega)) hu.le) hn
  have hwu : (ws.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hu.le) hNu
  have g1 := gamma_mono hmk hn
  have g2 := gamma_mono hnN hNu
  have g3 := gamma_mono (show N ≤ N + k by omega) hn
  have g0 := gamma_nonneg hmku
  have g0' := gamma_nonneg hwu
  have hmag : mag ws ≤ N * (B + tiny) := by
    refine le_trans (mag_le_of_bound hB) ?_
    have : (ws.length : ℝ) ≤ N := by exact_mod_cast hnN
    have : 0 ≤ B + tiny := by linarith
    nlinarith
  have hkt : (ss.length : ℝ) * tiny ≤ k * tiny := by
    have : (ss.length : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hm0 := mag_nonneg ws
  have kt : 0 ≤ (ss.length : ℝ) * tiny := by positivity
  have hX : mag ws + ss.length * tiny ≤ N * (B + tiny) + k * tiny := by linarith
  have hov1 : (1 + gamma (m + ss.length)) * (mag ws + ss.length * tiny) ≤ maxFinite :=
    le_trans (mul_le_mul (by linarith) hX (by linarith) (by linarith)) hov
  have hov2 : (1 + gamma ws.length) * mag ws ≤ maxFinite :=
    le_trans (mul_le_mul (by linarith) (by linarith) hm0 (by linarith)) hov
  have h := M.sharded_near hp hm hmku hwu hov1 hov2
  exact le_trans h (mul_le_mul (by linarith) hX (by linarith) (by linarith))

/-- **A-priori bound of a sharded `AVG`**: at most `N ≥ 1` values, each
`|x| ≤ B`, in at most `k` shards. -/
theorem StdModel.sharded_avg_near_of_bound {ss : List (List ℝ)} {ws : List ℝ} {m N k : ℕ} {B : ℝ}
    (hne : ws ≠ []) (hp : ws.Perm ss.flatten) (hm : ∀ s ∈ ss, s.length ≤ m) (hmN : m ≤ N)
    (hnN : ws.length ≤ N) (hk : ss.length ≤ k) (hB0 : 0 ≤ B) (hB : ∀ x ∈ ws, |x| ≤ B)
    (hn : ((N + k + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma (N + k)) * (N * (B + tiny) + k * tiny) ≤ maxFinite) :
    |M.fl (M.shardedSum ss / ws.length) - M.fl (M.sum ws / ws.length)|
      ≤ (gamma (N + k + 2) + gamma (N + 2)) * (B + tiny + k * tiny) := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hl1 : (1 : ℝ) ≤ ws.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hmk : m + ss.length + 2 ≤ N + k + 2 := by omega
  have hmk' : m + ss.length ≤ N + k := by omega
  have hNk : ((N + k : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N + k ≤ N + k + 2 by omega)) hu.le) hn
  have hmku2 : ((m + ss.length + 2 : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu.le) hn
  have hN2 : ((N + 2 : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show N + 2 ≤ N + k + 2 by omega)) hu.le) hn
  have hw2 : ((ws.length + 2 : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show ws.length + 2 ≤ N + 2 by omega)) hu.le) hN2
  have hwu : (ws.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show ws.length ≤ ws.length + 2 by omega)) hu.le) hw2
  have hmku : ((m + ss.length : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hmk') hu.le) hNk
  have g1 := gamma_mono hmk hn
  have g2 := gamma_mono (show ws.length + 2 ≤ N + 2 by omega) hN2
  have g3 := gamma_mono hmk' hNk
  have g4 := gamma_mono (show ws.length ≤ N + k by omega) hNk
  have g0 := gamma_nonneg hmku2
  have g0' := gamma_nonneg hw2
  have g5 := gamma_nonneg hmku
  have g6 := gamma_nonneg hwu
  have hm0 := mag_nonneg ws
  have hmag : mag ws ≤ ws.length * (B + tiny) := mag_le_of_bound hB
  have hmagN : mag ws ≤ N * (B + tiny) := by
    have : (ws.length : ℝ) ≤ N := by exact_mod_cast hnN
    have : 0 ≤ B + tiny := by linarith
    nlinarith
  have hkt : (ss.length : ℝ) * tiny ≤ k * tiny := by
    have : (ss.length : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have kt : 0 ≤ (ss.length : ℝ) * tiny := by positivity
  have hX : mag ws + ss.length * tiny ≤ N * (B + tiny) + k * tiny := by linarith
  have hov1 : (1 + gamma (m + ss.length)) * (mag ws + ss.length * tiny) ≤ maxFinite :=
    le_trans (mul_le_mul (by linarith) hX (by linarith) (by linarith)) hov
  have hov2 : (1 + gamma ws.length) * mag ws ≤ maxFinite :=
    le_trans (mul_le_mul (by linarith) (by linarith) hm0 (by linarith)) hov
  have h := M.sharded_avg_near hne hp hm hmku2 hw2 hov1 hov2
  refine le_trans h ?_
  have hlen : (0 : ℝ) < ws.length := by linarith
  rw [div_le_iff₀ hlen]
  have hY : mag ws + ss.length * tiny ≤ ws.length * (B + tiny + k * tiny) := by
    have : (k : ℝ) * tiny ≤ ws.length * (k * tiny) := by
      have : 0 ≤ (k : ℝ) * tiny := by positivity
      nlinarith
    nlinarith
  have hc : 0 ≤ gamma (N + k + 2) + gamma (N + 2) := by linarith
  calc (gamma (m + ss.length + 2) + gamma (ws.length + 2)) * (mag ws + ss.length * tiny)
      ≤ (gamma (N + k + 2) + gamma (N + 2)) * (ws.length * (B + tiny + k * tiny)) :=
        mul_le_mul (by linarith) hY (by linarith) hc
    _ = _ := by ring

/-! ## The bound from the partial rows, scaled -/

/-- `γ j = j / (2K − j)` with `K = 2⁵²`. -/
theorem gamma_eq_K {j : ℕ} (hj : (j : ℝ) < 2 * K) : gamma j = j / (2 * K - j) := by
  have hK : (0 : ℝ) < K := by unfold K; positivity
  have h1 : (2 * (K : ℝ) - j) ≠ 0 := by linarith
  have h2 : (2 * (K : ℝ)) ≠ 0 := by positivity
  have h3 : (1 - (j : ℝ) * (1 / (2 * K))) = (2 * K - j) / (2 * K) := by field_simp
  unfold gamma; rw [u_eq, h3, div_div_eq_mul_div]
  field_simp

/-- `shardTol n m k A · 2¹⁰⁷⁴`, rounded up, for `As = A · 2¹⁰⁷⁴`: with
`γ j = j / (2K − j)`, it is
`(γ (m + k) + γ n) · ((As + n K) / (1 − γ m) + k K)`. -/
def shardTolScaled (n m k As : ℕ) : ℕ :=
  ceilDiv (((m + k) * (2 * K - n) + n * (2 * K - (m + k)))
      * ((As + n * K) * (2 * K - m) + k * K * (2 * K - 2 * m)))
    ((2 * K - (m + k)) * (2 * K - n) * (2 * K - 2 * m))

/-- `shardAvgTol n m k A · 2¹⁰⁷⁴`, rounded up:
`(γ (m + k + 2) + γ (n + 2)) · ((As + n K) / (1 − γ m) + k K) / n`. -/
def shardAvgTolScaled (n m k As : ℕ) : ℕ :=
  ceilDiv (((m + k + 2) * (2 * K - (n + 2)) + (n + 2) * (2 * K - (m + k + 2)))
      * ((As + n * K) * (2 * K - m) + k * K * (2 * K - 2 * m)))
    ((2 * K - (m + k + 2)) * (2 * K - (n + 2)) * (2 * K - 2 * m) * n)

theorem K_real : (K : ℝ) = 2 ^ 52 := by unfold K; norm_num

theorem K_nat : K = 4503599627370496 := by unfold K; norm_num

/-- The bound in terms of the reported `As` is at most `shardTolScaled`. -/
theorem shardTol_le {n m k As : ℕ} (hn : n ≤ 2 ^ 32) (hm : m ≤ n) (hk : k ≤ n) :
    (gamma (m + k) + gamma n) * ((As / 2 ^ 1074 + n * tiny) / (1 - gamma m) + k * tiny)
      ≤ shardTolScaled n m k As / 2 ^ 1074 := by
  have hK := K_real
  have hnr : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA0 : (0 : ℝ) ≤ As := Nat.cast_nonneg As
  have htiny : tiny = K / 2 ^ 1074 := by rw [← tiny_eq]; field_simp
  have hNK : ∀ j : ℕ, j ≤ 2 * K → (((2 * K - j : ℕ)) : ℝ) = 2 * K - j := fun j hj => by
    rw [Nat.cast_sub hj]; push_cast; ring
  have hn' : n ≤ 4294967296 := by simpa using hn
  have h1 : n ≤ 2 * K := by rw [K_nat]; omega
  have h2 : m + k ≤ 2 * K := by rw [K_nat]; omega
  have h3 : 2 * m ≤ 2 * K := by rw [K_nat]; omega
  have h3' : m ≤ 2 * K := by rw [K_nat]; omega
  have hden : 0 < (2 * K - (m + k)) * (2 * K - n) * (2 * K - 2 * m) := by
    rw [K_nat]; apply Nat.mul_pos (Nat.mul_pos _ _) _ <;> omega
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (ceilDiv_ge _ _ hden) (by positivity))
  rw [gamma_eq_K (j := m + k) (by push_cast; rw [hK]; linarith),
    gamma_eq_K (j := n) (by rw [hK]; linarith), gamma_eq_K (j := m) (by rw [hK]; linarith)]
  push_cast
  rw [hNK n h1, hNK (m + k) h2, hNK (2 * m) h3, hNK m h3', htiny]
  push_cast
  have a1 : (2 * (K : ℝ) - (m + k)) ≠ 0 := by rw [hK]; linarith
  have a2 : (2 * (K : ℝ) - n) ≠ 0 := by rw [hK]; linarith
  have a3 : (2 * (K : ℝ) - 2 * m) ≠ 0 := by rw [hK]; linarith
  have a4 : (2 * (K : ℝ) - m) ≠ 0 := by rw [hK]; linarith
  have a6 : (-(m : ℝ) + K) ≠ 0 := by rw [hK]; linarith
  have a7 : ((K : ℝ) - m) ≠ 0 := by rw [hK]; linarith
  have a5 : (1 - (m : ℝ) / (2 * K - m)) = (2 * K - 2 * m) / (2 * K - m) := by
    field_simp; ring
  rw [a5]
  field_simp

/-- The `AVG` bound in terms of the reported `As` is at most `shardAvgTolScaled`. -/
theorem shardAvgTol_le {n m k As : ℕ} (hn : n ≤ 2 ^ 32) (hn1 : 0 < n) (hm : m ≤ n) (hk : k ≤ n) :
    (gamma (m + k + 2) + gamma (n + 2)) * ((As / 2 ^ 1074 + n * tiny) / (1 - gamma m) + k * tiny)
        / n
      ≤ shardAvgTolScaled n m k As / 2 ^ 1074 := by
  have hK := K_real
  have hnr : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have hn1r : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmr : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA0 : (0 : ℝ) ≤ As := Nat.cast_nonneg As
  have htiny : tiny = K / 2 ^ 1074 := by rw [← tiny_eq]; field_simp
  have hNK : ∀ j : ℕ, j ≤ 2 * K → (((2 * K - j : ℕ)) : ℝ) = 2 * K - j := fun j hj => by
    rw [Nat.cast_sub hj]; push_cast; ring
  have hn' : n ≤ 4294967296 := by simpa using hn
  have h1 : n + 2 ≤ 2 * K := by rw [K_nat]; omega
  have h2 : m + k + 2 ≤ 2 * K := by rw [K_nat]; omega
  have h3 : 2 * m ≤ 2 * K := by rw [K_nat]; omega
  have h3' : m ≤ 2 * K := by rw [K_nat]; omega
  have hden : 0 < (2 * K - (m + k + 2)) * (2 * K - (n + 2)) * (2 * K - 2 * m) * n := by
    rw [K_nat]; apply Nat.mul_pos (Nat.mul_pos (Nat.mul_pos _ _) _) hn1 <;> omega
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (ceilDiv_ge _ _ hden) (by positivity))
  rw [gamma_eq_K (j := m + k + 2) (by push_cast; rw [hK]; linarith),
    gamma_eq_K (j := n + 2) (by push_cast; rw [hK]; linarith),
    gamma_eq_K (j := m) (by rw [hK]; linarith)]
  push_cast
  rw [hNK (n + 2) h1, hNK (m + k + 2) h2, hNK (2 * m) h3, hNK m h3', htiny]
  push_cast
  have a1 : (2 * (K : ℝ) - (m + k + 2)) ≠ 0 := by rw [hK]; linarith
  have a2 : (2 * (K : ℝ) - (n + 2)) ≠ 0 := by rw [hK]; linarith
  have a3 : (2 * (K : ℝ) - 2 * m) ≠ 0 := by rw [hK]; linarith
  have a4 : (2 * (K : ℝ) - m) ≠ 0 := by rw [hK]; linarith
  have a6 : (-(m : ℝ) + K) ≠ 0 := by rw [hK]; linarith
  have a7 : ((K : ℝ) - m) ≠ 0 := by rw [hK]; linarith
  have a5 : (1 - (m : ℝ) / (2 * K - m)) = (2 * K - 2 * m) / (2 * K - m) := by
    field_simp; ring
  rw [a5]
  field_simp

/-! ## What the core trusts -/

/-- `j u ≤ 1/3` for the counts the core allows. -/
theorem small_mul_u {j : ℕ} (hj : j ≤ 2 ^ 34) : (j : ℝ) * u ≤ 1 / 3 := by
  have : (j : ℝ) ≤ 2 ^ 34 := by exact_mod_cast hj
  have hu := u_val
  rw [hu]; rw [mul_one_div, div_le_iff₀ (by norm_num)]; linarith

theorem gamma_le_half {j : ℕ} (hj : j ≤ 2 ^ 34) : gamma j ≤ 1 / 2 := by
  have h := small_mul_u hj
  have hu := u_pos
  have h0 : (0 : ℝ) ≤ j * u := by positivity
  unfold gamma
  rw [div_le_iff₀ (by linarith)]; linarith

/-- The magnitude of the decoded doubles, from a bound on the codes' values,
and far from overflow when `n (Bs + 2K) ≤ 2²⁰⁹⁶`. -/
theorem decoded_mag_le {ws : List (ℝ × ℝ)} (hd : Decoded ws) {Bs : ℕ}
    (hB : ∀ p ∈ ws, |p.2| ≤ Bs / 2 ^ 1074) (hov : ws.length * (Bs + 2 * K) ≤ 2 ^ 2096) :
    mag (ws.map Prod.fst) + ws.length * tiny ≤ 2 ^ 1023 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hu2 : 2 * u ≤ 1 := by rw [u_val]; norm_num
  have hb : ∀ x ∈ ws.map Prod.fst, |x| ≤ 2 * (Bs / 2 ^ 1074) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have h1 := hd p hp
    have h2 := hB p hp
    have := abs_sub_abs_le_abs_sub p.1 p.2
    nlinarith [abs_nonneg p.2]
  have hm := mag_le_of_bound hb
  simp only [List.length_map] at hm
  have hovr : (ws.length : ℝ) * (Bs + 2 * K) ≤ 2 ^ 2096 := by exact_mod_cast hov
  have htiny : tiny = K / 2 ^ 1074 := by rw [← tiny_eq]; field_simp
  rw [htiny] at hm ⊢
  have : (ws.length : ℝ) * (2 * (Bs / 2 ^ 1074) + K / 2 ^ 1074) + ws.length * (K / 2 ^ 1074)
      = 2 * ((ws.length : ℝ) * (Bs + K)) / 2 ^ 1074 := by ring
  have hK0 : (0 : ℝ) ≤ K := by unfold K; positivity
  have hl0 : (0 : ℝ) ≤ ws.length := Nat.cast_nonneg _
  calc _ ≤ 2 * ((ws.length : ℝ) * (Bs + K)) / 2 ^ 1074 := by linarith
    _ ≤ 2 * 2 ^ 2096 / 2 ^ 1074 := by gcongr; nlinarith
    _ = 2 ^ 1023 := by norm_num

theorem two_pow_mul_le_maxFinite {g : ℝ} (hg : g ≤ 1 / 2) : (1 + g) * 2 ^ 1023 ≤ maxFinite := by
  unfold maxFinite
  have : (1 : ℝ) + g ≤ 2 - (2 : ℝ)⁻¹ ^ 52 := by
    have : (2 : ℝ)⁻¹ ^ 52 ≤ 1 / 2 := by norm_num
    linarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **The sharded `SUM` the core trusts** (`floatSum_twoPhase`): the
shards' doubles `ss` (decoded from codes, `Decoded`), at most `m` per shard,
`k` shards, against the same values added in one pass in the order `ws`,
with each shard's rounded `SUM(|x|)` adding up to at most `As / 2¹⁰⁷⁴`. -/
theorem StdModel.core_shard_sum {ss : List (List (ℝ × ℝ))} {ws : List (ℝ × ℝ)} (hd : Decoded ws)
    (hp : ws.Perm ss.flatten) {m Bs As : ℕ} (hm : ∀ s ∈ ss, s.length ≤ m)
    (hmn : m ≤ ws.length) (hk : ss.length ≤ ws.length) (h32 : ws.length ≤ 2 ^ 32)
    (hB : ∀ p ∈ ws, |p.2| ≤ Bs / 2 ^ 1074) (hov : ws.length * (Bs + 2 * K) ≤ 2 ^ 2096)
    (hAs : (ss.map fun s => M.sum (s.map fun p => |p.1|)).sum ≤ As / 2 ^ 1074) :
    |M.shardedSum (ss.map (·.map Prod.fst)) - M.sum (ws.map Prod.fst)|
      ≤ shardTolScaled ws.length m ss.length As / 2 ^ 1074 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  set n := ws.length with hn
  set k := ss.length with hk'
  set xs := ws.map Prod.fst
  set tt := ss.map (·.map Prod.fst) with htt
  have hpx : xs.Perm tt.flatten := by
    have : tt.flatten = ss.flatten.map Prod.fst := by simp [htt, List.map_flatten]
    rw [this]; exact hp.map _
  have hmx : ∀ s ∈ tt, s.length ≤ m := by
    intro s hs; obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hs; simpa using hm t ht'
  have hxl : xs.length = n := by simp [xs, n]
  have htl : tt.length = k := by simp [tt, k]
  have hmag : mag xs + n * tiny ≤ 2 ^ 1023 := decoded_mag_le hd hB hov
  -- the conditions on the counts
  have h32' : n ≤ 4294967296 := by simpa using h32
  have hmk : m + k ≤ 2 ^ 34 := by norm_num; omega
  have hn34 : n ≤ 2 ^ 34 := by norm_num; omega
  have hm34 : m ≤ 2 ^ 34 := by norm_num; omega
  have h2m34 : 2 * m ≤ 2 ^ 34 := by norm_num; omega
  have hnu : (n : ℝ) * u < 1 := by have := small_mul_u hn34; linarith
  have hmku : ((m + k : ℕ) : ℝ) * u < 1 := by have := small_mul_u hmk; linarith
  have hmu : (m : ℝ) * u < 1 := by have := small_mul_u hm34; linarith
  have h2m : ((2 * m : ℕ) : ℝ) * u < 1 := by have := small_mul_u h2m34; linarith
  have gmk := gamma_le_half hmk
  have gn := gamma_le_half hn34
  have gm1 := gamma_lt_one h2m
  have hmag0 := mag_nonneg xs
  have kt : 0 ≤ (k : ℝ) * tiny := by positivity
  have hnk : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hnt : (k : ℝ) * tiny ≤ n * tiny := by gcongr
  have hov1 : (1 + gamma (m + k)) * (mag xs + k * tiny) ≤ maxFinite := by
    refine le_trans ?_ (two_pow_mul_le_maxFinite gmk)
    have hb : mag xs + k * tiny ≤ 2 ^ 1023 := by linarith
    have hg := gamma_nonneg hmku
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  have hov2 : (1 + gamma n) * mag xs ≤ maxFinite := by
    refine le_trans ?_ (two_pow_mul_le_maxFinite gn)
    have hb : mag xs ≤ 2 ^ 1023 := by linarith
    have hg := gamma_nonneg hnu
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  have hnear := M.sharded_near (ss := tt) (ws := xs) hpx hmx (by rw [htl]; exact hmku)
    (by rw [hxl]; exact hnu) (by rw [htl]; exact hov1) (by rw [hxl]; exact hov2)
  rw [htl, hxl] at hnear
  -- the magnitude from the shards' `SUM(|x|)`
  have hovs : ∀ s ∈ tt, (1 + gamma s.length) * mag s ≤ maxFinite := by
    intro s hs
    have hsl := hmx s hs
    have hsm : mag s ≤ mag xs := by
      rw [mag_perm hpx, mag_flatten]
      exact List.single_le_sum (fun t _ => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp ‹_›; exact mag_nonneg r) _
        (List.mem_map.mpr ⟨s, hs, rfl⟩)
    refine le_trans ?_ hov2
    have hsn : s.length ≤ n := le_trans hsl hmn
    have g1 := gamma_mono hsn hnu
    have hsu : (s.length : ℝ) * u < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hsl) hu.le) hmu
    have g2 := gamma_nonneg hsu
    have := mag_nonneg s
    exact mul_le_mul (by linarith) hsm this (by linarith [gamma_nonneg hnu])
  have hfl := M.mag_flatten_le hmx hmu hovs
  have hsums : (tt.map fun s => M.sum (s.map abs)) = ss.map fun s => M.sum (s.map fun p => |p.1|) := by
    simp [htt, Function.comp_def]
  have hlen : tt.flatten.length = n := by rw [← hpx.length_eq, hxl]
  rw [hsums, hlen, ← mag_perm hpx] at hfl
  have hmagle : mag xs ≤ (As / 2 ^ 1074 + n * tiny) / (1 - gamma m) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have htol := shardTol_le (n := n) (m := m) (k := k) (As := As) h32 hmn hk
  have g0 : 0 ≤ gamma (m + k) + gamma n := by
    have := gamma_nonneg hmku; have := gamma_nonneg hnu; linarith
  calc _ ≤ (gamma (m + k) + gamma n) * (mag xs + k * tiny) := hnear
    _ ≤ (gamma (m + k) + gamma n) * ((As / 2 ^ 1074 + n * tiny) / (1 - gamma m) + k * tiny) :=
        mul_le_mul_of_nonneg_left (by linarith) g0
    _ ≤ _ := htol

/-- **The sharded `AVG` the core trusts** (`floatAvg_twoPhase`): the two
sums, each divided by the count `n ≥ 1` and rounded. -/
theorem StdModel.core_shard_avg {ss : List (List (ℝ × ℝ))} {ws : List (ℝ × ℝ)} (hd : Decoded ws)
    (hne : ws ≠ []) (hp : ws.Perm ss.flatten) {m Bs As : ℕ} (hm : ∀ s ∈ ss, s.length ≤ m)
    (hmn : m ≤ ws.length) (hk : ss.length ≤ ws.length) (h32 : ws.length ≤ 2 ^ 32)
    (hB : ∀ p ∈ ws, |p.2| ≤ Bs / 2 ^ 1074) (hov : ws.length * (Bs + 2 * K) ≤ 2 ^ 2096)
    (hAs : (ss.map fun s => M.sum (s.map fun p => |p.1|)).sum ≤ As / 2 ^ 1074) :
    |M.fl (M.shardedSum (ss.map (·.map Prod.fst)) / ws.length)
        - M.fl (M.sum (ws.map Prod.fst) / ws.length)|
      ≤ shardAvgTolScaled ws.length m ss.length As / 2 ^ 1074 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hn1 : 0 < ws.length := List.length_pos_iff.mpr hne
  set n := ws.length with hn
  set k := ss.length with hk'
  set xs := ws.map Prod.fst
  set tt := ss.map (·.map Prod.fst) with htt
  have hpx : xs.Perm tt.flatten := by
    have : tt.flatten = ss.flatten.map Prod.fst := by simp [htt, List.map_flatten]
    rw [this]; exact hp.map _
  have hmx : ∀ s ∈ tt, s.length ≤ m := by
    intro s hs; obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hs; simpa using hm t ht'
  have hxl : xs.length = n := by simp [xs, n]
  have htl : tt.length = k := by simp [tt, k]
  have hxne : xs ≠ [] := by intro h; rw [h] at hxl; simp at hxl; omega
  have hmag : mag xs + n * tiny ≤ 2 ^ 1023 := decoded_mag_le hd hB hov
  have h32' : n ≤ 4294967296 := by simpa using h32
  have hmk : m + k + 2 ≤ 2 ^ 34 := by norm_num; omega
  have hmk' : m + k ≤ 2 ^ 34 := by norm_num; omega
  have hn34 : n + 2 ≤ 2 ^ 34 := by norm_num; omega
  have hn34' : n ≤ 2 ^ 34 := by norm_num; omega
  have hm34 : m ≤ 2 ^ 34 := by norm_num; omega
  have h2m34 : 2 * m ≤ 2 ^ 34 := by norm_num; omega
  have hnu : (n : ℝ) * u < 1 := by have := small_mul_u hn34'; linarith
  have hnu2 : ((n + 2 : ℕ) : ℝ) * u < 1 := by have := small_mul_u hn34; linarith
  have hmku : ((m + k : ℕ) : ℝ) * u < 1 := by have := small_mul_u hmk'; linarith
  have hmku2 : ((m + k + 2 : ℕ) : ℝ) * u < 1 := by have := small_mul_u hmk; linarith
  have hmu : (m : ℝ) * u < 1 := by have := small_mul_u hm34; linarith
  have h2m : ((2 * m : ℕ) : ℝ) * u < 1 := by have := small_mul_u h2m34; linarith
  have gmk := gamma_le_half hmk'
  have gn := gamma_le_half hn34'
  have gm1 := gamma_lt_one h2m
  have hmag0 := mag_nonneg xs
  have kt : 0 ≤ (k : ℝ) * tiny := by positivity
  have hnk : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hnt : (k : ℝ) * tiny ≤ n * tiny := by gcongr
  have hov1 : (1 + gamma (m + k)) * (mag xs + k * tiny) ≤ maxFinite := by
    refine le_trans ?_ (two_pow_mul_le_maxFinite gmk)
    have hb : mag xs + k * tiny ≤ 2 ^ 1023 := by linarith
    have hg := gamma_nonneg hmku
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  have hov2 : (1 + gamma n) * mag xs ≤ maxFinite := by
    refine le_trans ?_ (two_pow_mul_le_maxFinite gn)
    have hb : mag xs ≤ 2 ^ 1023 := by linarith
    have hg := gamma_nonneg hnu
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  have hnear := M.sharded_avg_near (ss := tt) (ws := xs) hxne hpx hmx
    (by rw [htl]; exact hmku2) (by rw [hxl]; exact hnu2) (by rw [htl]; exact hov1)
    (by rw [hxl]; exact hov2)
  rw [htl, hxl] at hnear
  have hovs : ∀ s ∈ tt, (1 + gamma s.length) * mag s ≤ maxFinite := by
    intro s hs
    have hsl := hmx s hs
    have hsm : mag s ≤ mag xs := by
      rw [mag_perm hpx, mag_flatten]
      exact List.single_le_sum (fun t _ => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp ‹_›; exact mag_nonneg r) _
        (List.mem_map.mpr ⟨s, hs, rfl⟩)
    refine le_trans ?_ hov2
    have hsn : s.length ≤ n := le_trans hsl hmn
    have g1 := gamma_mono hsn hnu
    have := mag_nonneg s
    exact mul_le_mul (by linarith) hsm this (by linarith [gamma_nonneg hnu])
  have hfl := M.mag_flatten_le hmx hmu hovs
  have hsums : (tt.map fun s => M.sum (s.map abs)) = ss.map fun s => M.sum (s.map fun p => |p.1|) := by
    simp [htt, Function.comp_def]
  have hlen : tt.flatten.length = n := by rw [← hpx.length_eq, hxl]
  rw [hsums, hlen, ← mag_perm hpx] at hfl
  have hmagle : mag xs ≤ (As / 2 ^ 1074 + n * tiny) / (1 - gamma m) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have htol := shardAvgTol_le (n := n) (m := m) (k := k) (As := As) h32 hn1 hmn hk
  have g0 : 0 ≤ gamma (m + k + 2) + gamma (n + 2) := by
    have := gamma_nonneg hmku2; have := gamma_nonneg hnu2; linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  calc _ ≤ (gamma (m + k + 2) + gamma (n + 2)) * (mag xs + k * tiny) / n := hnear
    _ ≤ (gamma (m + k + 2) + gamma (n + 2))
          * ((As / 2 ^ 1074 + n * tiny) / (1 - gamma m) + k * tiny) / n := by
        gcongr ?_ / _
        exact mul_le_mul_of_nonneg_left (by linarith) g0
    _ ≤ _ := htol

end FloatBounds

end
