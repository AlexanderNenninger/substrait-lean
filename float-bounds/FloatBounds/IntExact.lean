module

public import FloatBounds.Epsilon

/-!
# Sums of small integers are exact (#1608 12b-1, D35 amended 2026-11-19)

Binary64 holds every integer of magnitude at most `2⁵³`, so rounding to
nearest leaves one as it is. `StdModel.ExactInts` states that of a model:
a hypothesis taken as an argument, as `StdModel.Grid` and `NativeLink` are,
never an axiom (`NativeLink.ofNat_exact` states the same of native counts).

With it, every summation order the engine profiles allow (`StdModel.Summed`:
a tree, a constant run's `fl(k · x)`, Kahan's compensated sum) adds integers
whose magnitudes sum to at most `2⁵³` exactly (`StdModel.Summed.int_exact`):
each partial sum is such an integer, and Kahan's compensation stays `0`. This
backs the conjunct D35's amendment adds to `SumOrder`'s behaviours without a
shape (`core/Sverify/Core/AllowedP.lean`), as `Summed.near` backs `SumBound`;
the core proves the shaped behaviours itself (`SumOrder.int_exact` in
`analysis/Sverify/Analysis/MarginSound.lean`).
-/

@[expose] public section

namespace FloatBounds

/-- Integers up to `2⁵³` in magnitude round to themselves. True of binary64
with any rounding to nearest. -/
structure StdModel.ExactInts (M : StdModel) : Prop where
  int : ∀ k : ℤ, |(k : ℝ)| ≤ 2 ^ 53 → M.fl k = k

/-- Values that are integers, whose magnitudes sum to at most `2⁵³`. -/
def SmallInts (xs : List ℝ) : Prop :=
  (∀ x ∈ xs, ∃ k : ℤ, x = k) ∧ (xs.map abs).sum ≤ 2 ^ 53

variable (M : StdModel)

theorem int_add {a b : ℝ} : (∃ k : ℤ, a = k) → (∃ k : ℤ, b = k) → ∃ k : ℤ, a + b = k
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, by rw [hi, hj]; push_cast; ring⟩

theorem int_sum {xs : List ℝ} (h : ∀ x ∈ xs, ∃ k : ℤ, x = k) : ∃ k : ℤ, xs.sum = k := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
    rw [List.sum_cons]
    exact int_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem abs_sum_le_sum_abs (xs : List ℝ) : |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le _ _).trans (by linarith)

/-- A small integer rounds to itself. -/
theorem StdModel.ExactInts.fl_int {M : StdModel} (hM : M.ExactInts) {z : ℝ} (hz : ∃ k : ℤ, z = k)
    (hb : |z| ≤ 2 ^ 53) : M.fl z = z := by
  obtain ⟨k, rfl⟩ := hz
  exact hM.int k hb

/-- A sequential sum of small integers from a small integer is exact. -/
theorem StdModel.sumFrom_int (hM : M.ExactInts) {xs : List ℝ} (hx : ∀ x ∈ xs, ∃ k : ℤ, x = k) :
    ∀ {a : ℝ}, (∃ k : ℤ, a = k) → |a| + (xs.map abs).sum ≤ 2 ^ 53 → M.sumFrom a xs = a + xs.sum := by
  induction xs with
  | nil => intro a _ _; simp [StdModel.sumFrom]
  | cons x xs ih =>
    intro a ha hb
    simp only [List.map_cons, List.sum_cons] at hb
    have hxi := hx x List.mem_cons_self
    have hsum : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
    have hax : |a + x| ≤ 2 ^ 53 := (abs_add_le _ _).trans (by linarith)
    have hstep : M.add a x = a + x := hM.fl_int (int_add ha hxi) hax
    have : M.sumFrom a (x :: xs) = M.sumFrom (M.add a x) xs := rfl
    rw [this, hstep, ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (int_add ha hxi)
      (by have := abs_add_le a x; linarith), List.sum_cons]
    ring

theorem SmallInts.perm {xs ys : List ℝ} (h : xs.Perm ys) (hs : SmallInts ys) : SmallInts xs :=
  ⟨fun x hx => hs.1 x (h.mem_iff.mp hx), by rw [(h.map abs).sum_eq]; exact hs.2⟩

/-- Every tree sum of small integers is exact. -/
theorem StdModel.TreeSum.int_exact (hM : M.ExactInts) {xs : List ℝ} {s : ℝ} (h : M.TreeSum xs s)
    (hs : SmallInts xs) : s = xs.sum := by
  induction h with
  | @seq xs ws hp =>
    have hw := hs.perm hp
    rw [StdModel.sum, M.sumFrom_int hM hw.1 ⟨0, by simp⟩ (by simpa using hw.2), zero_add, hp.sum_eq]
  | @split zs xs ys a b hp _ _ iha ihb =>
    have h' := hs.perm hp.symm
    have hx : SmallInts xs := ⟨fun x hx => h'.1 x (List.mem_append_left _ hx),
      by have := h'.2; simp only [List.map_append, List.sum_append] at this
         have : 0 ≤ (ys.map abs).sum := List.sum_nonneg (by simp); linarith⟩
    have hy : SmallInts ys := ⟨fun x hx => h'.1 x (List.mem_append_right _ hx),
      by have := h'.2; simp only [List.map_append, List.sum_append] at this
         have : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp); linarith⟩
    rw [iha hx, ihb hy, hp.sum_eq, List.sum_append]
    apply hM.fl_int (int_add (int_sum hx.1) (int_sum hy.1))
    have := abs_sum_le_sum_abs (xs ++ ys)
    rw [List.sum_append] at this
    exact this.trans h'.2
  | const k x =>
    rw [List.sum_replicate, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [M.zero]
    apply hM.fl_int
    · obtain ⟨j, hj⟩ := hs.1 x (List.mem_replicate.mpr ⟨by omega, rfl⟩)
      exact ⟨k * j, by rw [hj]; push_cast; ring⟩
    · have := hs.2
      rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul] at this
      rw [abs_mul, Nat.abs_cast]; exact this

/-- Kahan's step on a small integer leaves the compensation at `0`. -/
theorem kstep_int (hM : M.ExactInts) {s x : ℝ} (hs : ∃ k : ℤ, s = k) (hx : ∃ k : ℤ, x = k)
    (hx' : |x| ≤ 2 ^ 53) (hsx : |s + x| ≤ 2 ^ 53) : M.toRnd.kstep (s, 0) x = (s + x, 0) := by
  have hfx : M.fl x = x := hM.fl_int hx hx'
  have hfsx : M.fl (s + x) = s + x := hM.fl_int (int_add hs hx) hsx
  simp only [Rnd.kstep, StdModel.toRnd, sub_zero, hfx, hfsx, add_sub_cancel_left, sub_self, M.zero]

/-- Kahan's compensated sum of small integers is exact. -/
theorem StdModel.kahan_int (hM : M.ExactInts) {xs : List ℝ} (hs : SmallInts xs) :
    M.toRnd.kahan xs = xs.sum := by
  suffices h : ∀ {s : ℝ}, (∃ k : ℤ, s = k) → |s| + (xs.map abs).sum ≤ 2 ^ 53 →
      xs.foldl M.toRnd.kstep (s, 0) = (s + xs.sum, 0) by
    rw [Rnd.kahan, h ⟨0, by simp⟩ (by simpa using hs.2), zero_add]
  obtain ⟨hx, -⟩ := hs
  induction xs with
  | nil => intro s _ _; simp
  | cons x xs ih =>
    intro s hsi hb
    simp only [List.map_cons, List.sum_cons] at hb
    have hsum : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
    have hxi := hx x List.mem_cons_self
    have hx' : |x| ≤ 2 ^ 53 := by have := abs_nonneg s; linarith
    have hsx : |s + x| ≤ 2 ^ 53 := (abs_add_le _ _).trans (by linarith)
    rw [List.foldl_cons, kstep_int M hM hsi hxi hx' hsx,
      ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (int_add hsi hxi)
        (by have := abs_add_le s x; linarith), List.sum_cons]
    congr 1; ring

/-- **Every order the engine profiles allow adds small integers exactly**:
a tree, a constant run's `fl(k · x)` and Kahan's compensated sum of a
permutation. -/
theorem StdModel.Summed.int_exact (hM : M.ExactInts) {xs : List ℝ} {s : ℝ} (h : M.Summed xs s)
    (hs : SmallInts xs) : s = xs.sum := by
  rcases h with h | ⟨ws, hp, rfl⟩
  · exact h.int_exact M hM hs
  · rw [M.kahan_int hM (hs.perm hp), hp.sum_eq]

end FloatBounds
