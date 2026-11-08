module

public import FloatBounds.Model

/-!
# Rounded sums and means (#85, stages 3 and 4)

`StdModel.sum` adds a list in list order from `0`, rounding each addition,
as `floatSum` in `core/Sverify/Core/Aggregate.lean` does with native doubles.

* `sum_error`: the rounded sum of `n` values is within `γ n · mag xs` of the
  exact sum (Higham, (4.4)), where `mag xs = Σ (|xᵢ| + tiny)`. The `tiny`
  per value is the underflow term of the model; it is `2⁻¹⁰²²`.
* `sharded_error`: adding each shard (at most `m` values), then adding the
  `k` partial sums, is within `γ (m + k) · (mag xs + k · tiny)`. With
  `sum_error`, this bounds how far a sharded sum is from the sequential one.
* `avg_error`, `sharded_avg_error`: one more rounded division by the count
  `n` gives the mean within `γ (n + 2) · mag xs / n`, or
  `γ (m + k + 2) · (mag xs + k · tiny) / n` for shards.
* `sum_error_of_bound`, `avg_error_of_bound`: the same with every
  `|xᵢ| ≤ B`, the form the contract checker uses.

Each theorem assumes that nothing overflows, as a condition on the exact
values: `(1 + γ) · mag xs ≤ maxFinite`.
-/

@[expose] public section

namespace FloatBounds

variable (M : StdModel)

/-- `xs` added in list order from `a`, each addition rounded. -/
noncomputable def StdModel.sumFrom (a : ℝ) (xs : List ℝ) : ℝ := xs.foldl M.add a

/-- `xs` added in list order from `0`, each addition rounded. -/
noncomputable def StdModel.sum (xs : List ℝ) : ℝ := M.sumFrom 0 xs

/-- `Σ (|xᵢ| + tiny)`: the magnitude the error bounds scale with. -/
noncomputable def mag (xs : List ℝ) : ℝ := (xs.map fun x => |x| + tiny).sum

@[simp] theorem mag_nil : mag [] = 0 := rfl

@[simp] theorem mag_cons (x : ℝ) (xs : List ℝ) : mag (x :: xs) = |x| + tiny + mag xs := by
  simp [mag]

theorem mag_append (xs ys : List ℝ) : mag (xs ++ ys) = mag xs + mag ys := by
  simp [mag]

theorem mag_nonneg (xs : List ℝ) : 0 ≤ mag xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [mag_cons]; have := tiny_pos; positivity

theorem abs_sum_le_mag (xs : List ℝ) : |xs.sum| ≤ mag xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, mag_cons]
    have := abs_add_le x xs.sum; have := tiny_pos; linarith

theorem length_mul_tiny_le_mag (xs : List ℝ) : xs.length * tiny ≤ mag xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.length_cons, mag_cons]; push_cast; have := abs_nonneg x; linarith

/-- `mag xs ≤ n · (B + tiny)` when every `|xᵢ| ≤ B`. -/
theorem mag_le_of_bound {B : ℝ} {xs : List ℝ} (h : ∀ x ∈ xs, |x| ≤ B) :
    mag xs ≤ xs.length * (B + tiny) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [mag_cons, List.length_cons]
    have hx := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    push_cast; linarith

/-- **The invariant of a rounded sum.** Started from an `a` within
`γ j · A` of an exact `a'` with `|a'| ≤ A`, adding `xs` stays within
`γ (j + |xs|) · (A + mag xs)` of `a' + Σ xs`. -/
theorem StdModel.sumFrom_error (xs : List ℝ) :
    ∀ {a a' A : ℝ} {j : ℕ}, |a - a'| ≤ gamma j * A → |a'| ≤ A →
      ((j + xs.length : ℕ) : ℝ) * u < 1 →
      (1 + gamma (j + xs.length)) * (A + mag xs) ≤ maxFinite →
      |M.sumFrom a xs - (a' + xs.sum)| ≤ gamma (j + xs.length) * (A + mag xs) := by
  induction xs with
  | nil => intro a a' A j h _ _ _; simpa [StdModel.sumFrom] using h
  | cons x xs ih =>
    intro a a' A j hacc hA hn hov
    simp only [List.length_cons] at hn hov ⊢
    obtain ⟨hu, -, ht, -, -⟩ := fpFacts
    have hjn : j + 1 ≤ j + (xs.length + 1) := by omega
    have hn1 : ((j + 1 : ℕ) : ℝ) * u < 1 :=
      lt_of_le_of_lt (by gcongr) hn
    have hj : (j : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn1
    have gj := gamma_nonneg hj
    have gs := gamma_succ hn1
    have gm := gamma_mono hjn hn
    have gn := gamma_nonneg hn
    have gj' := gamma_mono (show j ≤ j + (xs.length + 1) by omega) hn
    have hmag := mag_nonneg xs
    have hAx : 0 ≤ A := le_trans (abs_nonneg _) hA
    set A₁ := A + |x| + tiny with hA₁
    -- the next partial sum, exact and as computed before rounding
    have hz : |(a + x) - (a' + x)| ≤ gamma j * A := by ring_nf; ring_nf at hacc; exact hacc
    have hzabs : |a' + x| ≤ A + |x| := by have := abs_add_le a' x; linarith
    have hz' : |a + x| ≤ maxFinite := by
      have : |a + x| ≤ |a' + x| + gamma j * A := by
        have := abs_sub_abs_le_abs_sub (a + x) (a' + x); linarith
      calc |a + x| ≤ (1 + gamma j) * A₁ := by nlinarith [abs_nonneg x]
        _ ≤ (1 + gamma (j + (xs.length + 1))) * (A + mag (x :: xs)) := by
          simp only [mag_cons]; gcongr; linarith
        _ ≤ maxFinite := hov
    have step := M.round_near hz hz'
    have hnext : |M.fl (a + x) - (a' + x)| ≤ gamma (j + 1) * A₁ := by
      calc _ ≤ gamma j * A + u * (|a' + x| + gamma j * A + tiny) := step
        _ ≤ gamma j * A₁ + u * ((1 + gamma j) * A₁) := by
          gcongr
          · linarith [abs_nonneg x]
          · nlinarith [abs_nonneg x]
        _ = ((1 + gamma j) * (1 + u) - 1) * A₁ := by ring
        _ ≤ gamma (j + 1) * A₁ := by
          gcongr
          · linarith [abs_nonneg x]
    have := @ih (M.fl (a + x)) (a' + x) A₁ (j + 1) hnext (by linarith [abs_nonneg x])
      (by rw [show j + 1 + xs.length = j + (xs.length + 1) by omega]; exact hn)
      (by
        rw [show j + 1 + xs.length = j + (xs.length + 1) by omega]
        simp only [mag_cons] at hov
        convert hov using 2; ring)
    rw [show j + 1 + xs.length = j + (xs.length + 1) by omega] at this
    simp only [StdModel.sumFrom, List.foldl_cons, List.sum_cons, mag_cons] at this ⊢
    convert this using 2
    · rw [show M.add a x = M.fl (a + x) from rfl]; ring
    · rw [hA₁]; ring

/-- **Sequential sum** (stage 3): `|Σ̃ xs − Σ xs| ≤ γ n · mag xs`. -/
theorem StdModel.sum_error {xs : List ℝ} (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag xs ≤ maxFinite) :
    |M.sum xs - xs.sum| ≤ gamma xs.length * mag xs := by
  have := @M.sumFrom_error xs 0 0 0 0 (by simp [gamma]) (by simp)
    (by simpa using hn) (by simpa using hov)
  simpa [StdModel.sum] using this

/-- The rounded sum is at most `(1 + γ n) · mag xs` in magnitude. -/
theorem StdModel.abs_sum_le {xs : List ℝ} (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag xs ≤ maxFinite) :
    |M.sum xs| ≤ (1 + gamma xs.length) * mag xs := by
  have h1 := M.sum_error hn hov
  have h2 := abs_sum_le_mag xs
  have := abs_sub_abs_le_abs_sub (M.sum xs) xs.sum
  linarith

/-- **A rounded division by a count** adds one rounding (and one for the
underflow term): if `ŝ` is within `γ j · A` of `s`, `|s| ≤ A` and
`n · tiny ≤ A`, then `fl(ŝ / n)` is within `γ (j + 2) · A / n` of `s / n`. -/
theorem StdModel.div_error {s s' A : ℝ} {j n : ℕ} (hn0 : 0 < n)
    (hs : |s' - s| ≤ gamma j * A) (hA : |s| ≤ A) (htA : n * tiny ≤ A)
    (hj : ((j + 2 : ℕ) : ℝ) * u < 1) (hov : (1 + gamma j) * A ≤ maxFinite) :
    |M.fl (s' / n) - s / n| ≤ gamma (j + 2) * A / n := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : ((j + 1 : ℕ) : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; norm_num) hj
  have h0 : (j : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) h1
  have g0 := gamma_nonneg h0
  have g1 := gamma_nonneg h1
  have s1 := gamma_succ h1
  have s0 := gamma_succ (j := j + 1) (by push_cast at hj ⊢; linarith)
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  have hz : |s' / n - s / n| ≤ gamma j * A / n := by
    rw [← sub_div, abs_div, abs_of_pos hnpos]; gcongr
  have hs' : |s'| ≤ (1 + gamma j) * A := by
    have := abs_sub_abs_le_abs_sub s' s; nlinarith
  have hz' : |s' / n| ≤ maxFinite := by
    rw [abs_div, abs_of_pos hnpos]
    calc |s'| / n ≤ |s'| := div_le_self (abs_nonneg _) hn
      _ ≤ _ := le_trans hs' hov
  have step := M.round_near hz hz'
  have htn : tiny ≤ A / n := by rw [le_div_iff₀ hnpos]; linarith
  have hsn : |s / n| ≤ A / n := by rw [abs_div, abs_of_pos hnpos]; gcongr
  have hAn : 0 ≤ A / n := by positivity
  calc _ ≤ gamma j * A / n + u * (|s / n| + gamma j * A / n + tiny) := step
    _ ≤ gamma j * (A / n) + u * (A / n + gamma j * (A / n) + A / n) := by
      rw [mul_div_assoc]; gcongr
    _ = ((1 + gamma j) * (1 + u) - 1 + u) * (A / n) := by ring
    _ ≤ ((1 + gamma (j + 1)) * (1 + u) - 1) * (A / n) := by
      gcongr; nlinarith
    _ ≤ gamma (j + 2) * (A / n) := by gcongr; linarith
    _ = gamma (j + 2) * A / n := by ring

/-- **The mean** (stage 4): `fl(Σ̃ xs / n)` is within `γ (n + 2) · mag xs / n`
of the exact mean. -/
theorem StdModel.avg_error {xs : List ℝ} (hne : xs ≠ [])
    (hn : ((xs.length + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag xs ≤ maxFinite) :
    |M.fl (M.sum xs / xs.length) - xs.sum / xs.length|
      ≤ gamma (xs.length + 2) * mag xs / xs.length := by
  have hu := u_pos
  have hn0 : (xs.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (by gcongr; linarith) hn
  exact M.div_error (List.length_pos_iff.mpr hne) (M.sum_error hn0 hov)
    (abs_sum_le_mag xs) (length_mul_tiny_le_mag xs) hn hov

/-! ## Shards -/

/-- The values of `ss`, each added rounded, then the partial sums added
rounded: a two-phase (sharded) sum. -/
noncomputable def StdModel.shardedSum (ss : List (List ℝ)) : ℝ := M.sum (ss.map M.sum)

theorem mag_flatten (ss : List (List ℝ)) : mag ss.flatten = (ss.map mag).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [mag_append, ih]

theorem abs_sum_map_sub_le {α : Type*} (f g h : α → ℝ) (c : ℝ) :
    ∀ ss : List α, (∀ s ∈ ss, |f s - g s| ≤ c * h s) →
      |(ss.map f).sum - (ss.map g).sum| ≤ c * (ss.map h).sum
  | [], _ => by simp
  | s :: ss, hs => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := hs s (by simp)
    have h2 := abs_sum_map_sub_le f g h c ss fun t ht => hs t (by simp [ht])
    calc _ = |(f s - g s) + ((ss.map f).sum - (ss.map g).sum)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring

theorem mag_map {α : Type*} (f : α → ℝ) :
    ∀ ss : List α, mag (ss.map f) = (ss.map fun s => |f s|).sum + ss.length * tiny
  | [] => by simp
  | s :: ss => by simp [mag_map f ss]; ring

/-- **Sharded sum** (stage 4): shards of at most `m` values, `k` of them,
added in two phases, are within `γ (m + k) · (mag xs + k · tiny)` of the
exact sum of all values. -/
theorem StdModel.sharded_error {ss : List (List ℝ)} {m : ℕ}
    (hm : ∀ s ∈ ss, s.length ≤ m) (hn : ((m + ss.length : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma (m + ss.length)) * (mag ss.flatten + ss.length * tiny) ≤ maxFinite) :
    |M.shardedSum ss - ss.flatten.sum|
      ≤ gamma (m + ss.length) * (mag ss.flatten + ss.length * tiny) := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  set k := ss.length
  have hk : (k : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn
  have hm' : (m : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn
  have gk := gamma_nonneg hk
  have gm := gamma_nonneg hm'
  have gmk := gamma_add (a := m) (b := k) hn
  have gkmk := gamma_mono (Nat.le_add_left k m) hn
  have hmag := mag_nonneg ss.flatten
  -- each shard's rounded sum
  have hshard : ∀ s ∈ ss, |M.sum s - s.sum| ≤ gamma m * mag s ∧
      (1 + gamma s.length) * mag s ≤ (1 + gamma m) * mag s := by
    intro s hs
    have hsm := hm s hs
    have hsl : (s.length : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr) hm'
    have gsm := gamma_mono hsm hm'
    have hmags := mag_nonneg s
    have hsle : mag s ≤ mag ss.flatten := by
      rw [mag_flatten]
      exact List.single_le_sum (fun t _ => by
        obtain ⟨r, _, rfl⟩ := List.mem_map.mp ‹_›; exact mag_nonneg r) _
        (List.mem_map.mpr ⟨s, hs, rfl⟩)
    have hov' : (1 + gamma s.length) * mag s ≤ maxFinite := by
      calc _ ≤ (1 + gamma (m + k)) * (mag ss.flatten + k * tiny) := by
            gcongr
            · linarith [gamma_nonneg hsl]
            · exact gamma_mono (by omega) hn
            · have : (0 : ℝ) ≤ k * tiny := by positivity
              linarith
        _ ≤ maxFinite := hov
    refine ⟨le_trans (M.sum_error hsl hov') (by gcongr), by gcongr⟩
  -- the partial sums: their error and magnitude
  have herr : |(ss.map M.sum).sum - ss.flatten.sum| ≤ gamma m * mag ss.flatten := by
    rw [List.sum_flatten, mag_flatten]
    exact abs_sum_map_sub_le _ _ _ _ ss fun s hs => (hshard s hs).1
  have hmagp : mag (ss.map M.sum) ≤ (1 + gamma m) * mag ss.flatten + k * tiny := by
    have := mag_map M.sum ss
    rw [this, mag_flatten]
    have : (ss.map fun s => |M.sum s|).sum ≤ (1 + gamma m) * (ss.map mag).sum := by
      rw [← List.sum_map_mul_left]
      apply List.sum_le_sum
      intro s hs
      have h1 := (hshard s hs).1
      have := abs_sum_le_mag s
      have := abs_sub_abs_le_abs_sub (M.sum s) s.sum
      linarith
    linarith
  have hlen : (ss.map M.sum).length = k := by simp [k]
  have hov2 : (1 + gamma k) * mag (ss.map M.sum) ≤ maxFinite := by
    calc _ ≤ (1 + gamma k) * ((1 + gamma m) * mag ss.flatten + k * tiny) := by
          gcongr
      _ ≤ (1 + gamma (m + k)) * (mag ss.flatten + k * tiny) := by
          have : (0 : ℝ) ≤ k * tiny := by positivity
          nlinarith
      _ ≤ maxFinite := hov
  have hcomb := M.sum_error (xs := ss.map M.sum) (by rw [hlen]; exact hk) (by rw [hlen]; exact hov2)
  rw [hlen] at hcomb
  unfold StdModel.shardedSum
  have : (0 : ℝ) ≤ k * tiny := by positivity
  calc _ = |(M.sum (ss.map M.sum) - (ss.map M.sum).sum)
        + ((ss.map M.sum).sum - ss.flatten.sum)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ gamma k * ((1 + gamma m) * mag ss.flatten + k * tiny) + gamma m * mag ss.flatten := by
      gcongr; exact le_trans hcomb (by gcongr)
    _ = ((1 + gamma k) * (1 + gamma m) - 1) * mag ss.flatten + gamma k * (k * tiny) := by ring
    _ ≤ gamma (m + k) * mag ss.flatten + gamma (m + k) * (k * tiny) := by
      gcongr; linarith
    _ = _ := by ring

/-- **Sharded mean**: the sharded sum divided by the count `n`. -/
theorem StdModel.sharded_avg_error {ss : List (List ℝ)} {m : ℕ} (hne : ss.flatten ≠ [])
    (hm : ∀ s ∈ ss, s.length ≤ m) (hn : ((m + ss.length + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma (m + ss.length)) * (mag ss.flatten + ss.length * tiny) ≤ maxFinite) :
    |M.fl (M.shardedSum ss / ss.flatten.length) - ss.flatten.sum / ss.flatten.length|
      ≤ gamma (m + ss.length + 2) * (mag ss.flatten + ss.length * tiny)
        / ss.flatten.length := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hk : (0 : ℝ) ≤ ss.length * tiny := by positivity
  have hn' : ((m + ss.length : ℕ) : ℝ) * u < 1 := by
    have : ((m + ss.length : ℕ) : ℝ) ≤ ((m + ss.length + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show m + ss.length ≤ m + ss.length + 2 by omega)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right this hu.le) hn
  apply M.div_error (List.length_pos_iff.mpr hne) (M.sharded_error hm hn' hov)
  · have := abs_sum_le_mag ss.flatten; linarith
  · have := length_mul_tiny_le_mag ss.flatten; linarith
  · exact hn
  · exact hov

/-! ## With a bound on the values -/

/-- `SUM` of `n` values with every `|xᵢ| ≤ B`: within `γ n · n · (B + tiny)`. -/
theorem StdModel.sum_error_of_bound {B : ℝ} {xs : List ℝ} (hB : ∀ x ∈ xs, |x| ≤ B)
    (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * (xs.length * (B + tiny)) ≤ maxFinite) :
    |M.sum xs - xs.sum| ≤ gamma xs.length * (xs.length * (B + tiny)) := by
  have hmag := mag_le_of_bound hB
  have g := gamma_nonneg hn
  have hov' : (1 + gamma xs.length) * mag xs ≤ maxFinite :=
    le_trans (by gcongr) hov
  exact le_trans (M.sum_error hn hov') (by gcongr)

/-- `AVG` of `n ≥ 1` values with every `|xᵢ| ≤ B`: within `γ (n + 2) · (B + tiny)`. -/
theorem StdModel.avg_error_of_bound {B : ℝ} {xs : List ℝ} (hne : xs ≠ [])
    (hB : ∀ x ∈ xs, |x| ≤ B) (hn : ((xs.length + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * (xs.length * (B + tiny)) ≤ maxFinite) :
    |M.fl (M.sum xs / xs.length) - xs.sum / xs.length| ≤ gamma (xs.length + 2) * (B + tiny) := by
  have hmag := mag_le_of_bound hB
  have hu := u_pos
  have hn0 : (xs.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (by gcongr; linarith) hn
  have g0 := gamma_nonneg hn0
  have g2 := gamma_nonneg hn
  have hl : (0 : ℝ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have := M.avg_error hne hn (le_trans (by gcongr) hov)
  refine le_trans (le_of_le_of_eq this (mul_div_assoc _ _ _)) ?_
  gcongr
  rw [div_le_iff₀ hl]; linarith

end FloatBounds

end
