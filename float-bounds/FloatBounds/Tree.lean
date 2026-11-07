module

public import FloatBounds.Shard

/-!
# Sums in any order (#444, #85)

The reference allows a double `SUM` any tree of rounded additions over the
values in any order (`FloatSums` in `SubstraitLean/Allowed.lean`: `seq`, a
sequential sum of a permutation, and `split`, two such sums added). DuckDB
adds a constant run of `k` rows as one product `fl(k · x)` (duckdb-sum-double,
`SCALED_CONSTANT`). `StdModel.TreeSum` is the doubles all of these give, over
the reals: `FloatSums` with a third constructor, `const`.

The bounds are proved once, for a rounding `Rnd` with error `u · (|z| + τ)`
on a set of values `G` closed under the operations:

* the standard model (`StdModel.toRnd`): every value, `τ = tiny`. This gives
  the absolute bound, `γ n · mag xs`;
* a model whose roundings of multiples of `2⁻¹⁰⁷⁴` are relative
  (`StdModel.Grid`, `StdModel.gridRnd`): `τ = 0` on the multiples of
  `2⁻¹⁰⁷⁴`. Every double is one, and so is every sum or difference of two
  doubles and every product `k · x` with `k` an integer: a sum that falls
  below the normal range is exact in IEEE 754 (Hauser, *Handling
  floating-point exceptions in numeric programs*, 1996, Theorem 3.4.1). This
  gives Higham's bound `γ n · Σ |xᵢ|` without the underflow term, which for
  values of one sign is relative: `γ n · |Σ xᵢ|`.

* `Rnd.Tree.error`: a tree of `n` values is within `γ n · Σ (|xᵢ| + τ)` of
  the exact sum (Higham, §4.2: an error grows with the additions on one
  value's path to the root, at most `n − 1`; a product `fl(k · x)` rounds
  once).
* `TreeSum.tree`: every `TreeSum` is such a tree, over a permutation of the
  values.
-/

@[expose] public section

namespace FloatBounds

/-- A rounding with error at most `u · (|z| + τ)` on the values `G`, which
hold `0` and the rounded values, and are closed under `+` and `-`. -/
structure Rnd where
  fl : ℝ → ℝ
  τ : ℝ
  G : ℝ → Prop
  τ_nonneg : 0 ≤ τ
  err : ∀ z, G z → |z| ≤ maxFinite → |fl z - z| ≤ u * (|z| + τ)
  idem : ∀ z, fl (fl z) = fl z
  zero : fl 0 = 0
  G_zero : G 0
  G_add : ∀ a b, G a → G b → G (a + b)
  G_neg : ∀ a, G a → G (-a)
  G_fl : ∀ z, G z → G (fl z)

/-- The standard model as a `Rnd`: every value, `τ = tiny`. -/
noncomputable def StdModel.toRnd (M : StdModel) : Rnd where
  fl := M.fl
  τ := tiny
  G := fun _ => True
  τ_nonneg := tiny_pos.le
  err := fun z _ h => M.err z h
  idem := M.idem
  zero := M.zero
  G_zero := trivial
  G_add := fun _ _ _ _ => trivial
  G_neg := fun _ _ => trivial
  G_fl := fun _ _ => trivial

/-- `2⁻¹⁰⁷⁴`, the least positive double. -/
noncomputable def eta : ℝ := (2 : ℝ)⁻¹ ^ 1074

/-- An integer multiple of `2⁻¹⁰⁷⁴`, as every double is. -/
def OnGrid (z : ℝ) : Prop := ∃ m : ℤ, z = m * eta

/-- What IEEE 754 rounding to nearest does beyond the standard model: every
rounded value is a double, so a multiple of `2⁻¹⁰⁷⁴`, and a multiple of
`2⁻¹⁰⁷⁴` rounds with a relative error, since one below the normal range is a
double (Hauser 1996, Theorem 3.4.1: a sum that underflows is exact). -/
structure StdModel.Grid (M : StdModel) : Prop where
  on_grid : ∀ z, OnGrid (M.fl z)
  rel : ∀ z, OnGrid z → |z| ≤ maxFinite → |M.fl z - z| ≤ u * |z|

theorem OnGrid.add {a b : ℝ} : OnGrid a → OnGrid b → OnGrid (a + b)
  | ⟨m, hm⟩, ⟨n, hn⟩ => ⟨m + n, by rw [hm, hn]; push_cast; ring⟩

theorem OnGrid.neg {a : ℝ} : OnGrid a → OnGrid (-a)
  | ⟨m, hm⟩ => ⟨-m, by rw [hm]; push_cast; ring⟩

/-- The model of `Grid` as a `Rnd`: the multiples of `2⁻¹⁰⁷⁴`, `τ = 0`. -/
def StdModel.gridRnd (M : StdModel) (hg : M.Grid) : Rnd where
  fl := M.fl
  τ := 0
  G := OnGrid
  τ_nonneg := le_rfl
  err := fun z hz h => by simpa using hg.rel z hz h
  idem := M.idem
  zero := M.zero
  G_zero := ⟨0, by simp⟩
  G_add := fun _ _ => OnGrid.add
  G_neg := fun _ => OnGrid.neg
  G_fl := fun z _ => hg.on_grid z

namespace Rnd

variable (R : Rnd)

/-- `Σ (|xᵢ| + τ)`: `mag` for `τ = tiny`, `Σ |xᵢ|` for `τ = 0`. -/
noncomputable def mag (xs : List ℝ) : ℝ := (xs.map fun x => |x| + R.τ).sum

@[simp] theorem mag_nil : R.mag [] = 0 := rfl

@[simp] theorem mag_cons (x : ℝ) (xs : List ℝ) : R.mag (x :: xs) = |x| + R.τ + R.mag xs := by
  simp [mag]

theorem mag_append (xs ys : List ℝ) : R.mag (xs ++ ys) = R.mag xs + R.mag ys := by
  simp [mag]

theorem mag_perm {xs ys : List ℝ} (h : xs.Perm ys) : R.mag xs = R.mag ys := by
  unfold mag; exact (h.map _).sum_eq

theorem mag_nonneg (xs : List ℝ) : 0 ≤ R.mag xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [mag_cons]; have := R.τ_nonneg; positivity

theorem abs_sum_le_mag (xs : List ℝ) : |xs.sum| ≤ R.mag xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, mag_cons]
    have := abs_add_le x xs.sum; have := R.τ_nonneg; linarith

theorem abs_sum_add_le_mag {xs : List ℝ} (h : xs ≠ []) : |xs.sum| + R.τ ≤ R.mag xs := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs =>
    simp only [List.sum_cons, mag_cons]
    have := abs_add_le x xs.sum
    have := R.abs_sum_le_mag xs
    linarith

theorem round_near {z z' e : ℝ} (hz : |z' - z| ≤ e) (hG : R.G z') (h : |z'| ≤ maxFinite) :
    |R.fl z' - z| ≤ e + u * (|z| + e + R.τ) := by
  have h1 := R.err z' hG h
  have h2 : |z'| ≤ |z| + e := by
    have := abs_sub_abs_le_abs_sub z' z; linarith
  have hu := u_pos
  calc |R.fl z' - z| = |(R.fl z' - z') + (z' - z)| := by ring_nf
    _ ≤ |R.fl z' - z'| + |z' - z| := abs_add_le _ _
    _ ≤ u * (|z'| + R.τ) + e := add_le_add h1 hz
    _ ≤ u * (|z| + e + R.τ) + e := by gcongr
    _ = e + u * (|z| + e + R.τ) := by ring

theorem G_nsmul {x : ℝ} (hx : R.G x) : ∀ k : ℕ, R.G (k * x)
  | 0 => by simpa using R.G_zero
  | k + 1 => by
    have := R.G_add _ _ (G_nsmul hx k) hx
    push_cast; rwa [add_mul, one_mul]

theorem _root_.FloatBounds.u_le_gamma {k : ℕ} (hk : 1 ≤ k) (hn : (k : ℝ) * u < 1) :
    u ≤ gamma k := by
  have hu := u_pos
  have h1 : ((1 : ℕ) : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr) hn
  have : u ≤ gamma 1 := by
    unfold gamma; push_cast at h1 ⊢
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact le_trans this (gamma_mono hk hn)

/-- A tree of rounded additions over the values `xs`, in any order, with
constant runs added as one rounded product. -/
inductive Tree : List ℝ → ℝ → Prop
  | nil : Tree [] 0
  | leaf {x : ℝ} : R.G x → Tree [x] x
  | node {zs xs ys : List ℝ} {a b : ℝ} : zs.Perm (xs ++ ys) → Tree xs a → Tree ys b →
      Tree zs (R.fl (a + b))
  | const (k : ℕ) {x : ℝ} : R.G x → Tree (List.replicate k x) (R.fl (k * x))

variable {R}

theorem Tree.mem {xs : List ℝ} {s : ℝ} (h : R.Tree xs s) : R.G s := by
  induction h with
  | nil => exact R.G_zero
  | leaf hx => exact hx
  | node _ _ _ ha hb => exact R.G_fl _ (R.G_add _ _ ha hb)
  | const k hx => exact R.G_fl _ (R.G_nsmul hx k)

theorem Tree.zero_of_nil {xs : List ℝ} {s : ℝ} (h : R.Tree xs s) : xs = [] → s = 0 := by
  induction h with
  | nil => intro; rfl
  | leaf _ => intro h; simp at h
  | node hp _ _ iha ihb =>
    intro h; subst h
    have h0 := List.Perm.nil_eq hp
    rw [iha (List.append_eq_nil_iff.mp h0.symm).1, ihb (List.append_eq_nil_iff.mp h0.symm).2,
      add_zero, R.zero]
  | const k _ =>
    intro h
    have : k = 0 := by simpa using h
    subst this; simp [R.zero]

/-- A tree is a rounded value, or a single value as it is. -/
theorem Tree.shape {xs : List ℝ} {s : ℝ} (h : R.Tree xs s) :
    R.fl s = s ∨ (∃ x, xs = [x] ∧ s = x) := by
  cases h with
  | nil => exact .inl R.zero
  | leaf _ => exact .inr ⟨_, rfl, rfl⟩
  | node _ _ _ => exact .inl (R.idem _)
  | const _ _ => exact .inl (R.idem _)

/-- `s` is within `γ n · Σ (|xᵢ| + τ)` of the exact sum of `xs`. -/
def Near (R : Rnd) (xs : List ℝ) (s : ℝ) : Prop := |s - xs.sum| ≤ gamma xs.length * R.mag xs

theorem Near.perm {xs ys : List ℝ} {s : ℝ} (h : xs.Perm ys) (hs : R.Near xs s) : R.Near ys s := by
  unfold Near at *; rwa [← h.length_eq, ← R.mag_perm h, ← h.sum_eq]

/-- The hypotheses of a bound hold of a part. -/
theorem sub_hyps {n : ℕ} {A : ℝ} {l : List ℝ} (hl : l.length ≤ n) (hm : R.mag l ≤ A)
    (hn : (n : ℝ) * u < 1) (hov : (1 + gamma n) * A ≤ maxFinite) :
    (l.length : ℝ) * u < 1 ∧ (1 + gamma l.length) * R.mag l ≤ maxFinite := by
  have hl' : (l.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) u_pos.le) hn
  refine ⟨hl', le_trans ?_ hov⟩
  have := gamma_mono hl hn
  have := gamma_nonneg hl'
  have := R.mag_nonneg l
  nlinarith

/-- A single value, rounded once. -/
theorem near_single {x : ℝ} (hx : R.G x)
    (hn : ((1 : ℕ) : ℝ) * u < 1) (hov : (1 + gamma 1) * R.mag [x] ≤ maxFinite) :
    R.Near [x] (R.fl x) := by
  unfold Near
  simp only [List.sum_cons, List.sum_nil, add_zero, List.length_cons, List.length_nil,
    zero_add, mag_cons, mag_nil] at hov ⊢
  have hu := u_pos
  have g := gamma_nonneg hn
  have := R.τ_nonneg
  have hx' : |x| ≤ maxFinite := by nlinarith [abs_nonneg x]
  calc _ ≤ u * (|x| + R.τ) := R.err x hx hx'
    _ ≤ gamma 1 * (|x| + R.τ) :=
      mul_le_mul_of_nonneg_right (u_le_gamma le_rfl hn) (by positivity)

/-- **Any tree sum** is within `γ n · Σ (|xᵢ| + τ)` of the exact sum. -/
theorem Tree.error {xs : List ℝ} {s : ℝ} (h : R.Tree xs s) :
    (xs.length : ℝ) * u < 1 → (1 + gamma xs.length) * R.mag xs ≤ maxFinite → R.Near xs s := by
  induction h with
  | nil => intro _ _; simp [Near]
  | leaf _ =>
    intro hn _; unfold Near
    simp only [List.sum_cons, List.sum_nil, add_zero, sub_self, abs_zero]
    exact mul_nonneg (gamma_nonneg hn) (R.mag_nonneg _)
  | @const k x hx =>
    intro hn hov
    unfold Near
    obtain ⟨hu, -, -, -, -⟩ := fpFacts
    have hτ := R.τ_nonneg
    simp only [List.length_replicate, List.sum_replicate, nsmul_eq_mul] at hn hov ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [R.zero, gamma]
    have hmag : R.mag (List.replicate k x) = k * (|x| + R.τ) := by
      rw [mag]; simp; ring
    rw [hmag] at hov ⊢
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have g := gamma_nonneg hn
    have hkx : |(k : ℝ) * x| + R.τ ≤ k * (|x| + R.τ) := by
      rw [abs_mul, Nat.abs_cast]; nlinarith [abs_nonneg x]
    have hov' : |(k : ℝ) * x| ≤ maxFinite := by
      have : (0 : ℝ) ≤ k * (|x| + R.τ) := by positivity
      nlinarith
    calc |R.fl (k * x) - k * x| ≤ u * (|(k : ℝ) * x| + R.τ) := R.err _ (R.G_nsmul hx k) hov'
      _ ≤ gamma k * (k * (|x| + R.τ)) := by
        apply mul_le_mul (u_le_gamma hk hn) hkx (by positivity) (by linarith)
  | @node zs xs ys a b hp hta htb iha ihb =>
    intro hn hov
    obtain ⟨hu, -, -, -, -⟩ := fpFacts
    have hτ := R.τ_nonneg
    have hlen : zs.length = xs.length + ys.length := by rw [hp.length_eq, List.length_append]
    have hmag : R.mag zs = R.mag xs + R.mag ys := by rw [R.mag_perm hp, R.mag_append]
    have hsum : zs.sum = xs.sum + ys.sum := by rw [hp.sum_eq, List.sum_append]
    rw [hlen] at hn
    rw [hlen, hmag] at hov
    have hmx := R.mag_nonneg xs
    have hmy := R.mag_nonneg ys
    obtain ⟨hxn, hxo⟩ := sub_hyps (l := xs) (by omega) (by linarith) hn hov
    obtain ⟨hyn, hyo⟩ := sub_hyps (l := ys) (by omega) (by linarith) hn hov
    have ea := iha hxn hxo
    have eb := ihb hyn hyo
    -- a part with no values adds nothing, or rounds a single value once
    rcases eq_or_ne xs [] with hx | hx
    · subst hx
      rw [hta.zero_of_nil rfl, zero_add]
      have hzs : zs.Perm ys := by simpa using hp
      apply Near.perm hzs.symm
      rcases htb.shape with hb | ⟨y, rfl, rfl⟩
      · rw [hb]; exact eb
      · exact near_single htb.mem hyn hyo
    rcases eq_or_ne ys [] with hy | hy
    · subst hy
      rw [htb.zero_of_nil rfl, add_zero]
      have hzs : zs.Perm xs := by simpa using hp
      apply Near.perm hzs.symm
      rcases hta.shape with ha | ⟨y, rfl, rfl⟩
      · rw [ha]; exact ea
      · exact near_single hta.mem hxn hxo
    unfold Near at ea eb ⊢
    rw [hlen, hmag, hsum]
    -- both parts have values: at most `n − 1` each
    have hpx : 1 ≤ xs.length := List.length_pos_iff.mpr hx
    have hpy : 1 ≤ ys.length := List.length_pos_iff.mpr hy
    set n := xs.length + ys.length with hn_def
    have hn1 : ((n - 1 + 1 : ℕ) : ℝ) * u < 1 := by
      rw [show n - 1 + 1 = n by omega]; exact hn
    have hn0 : ((n - 1 : ℕ) : ℝ) * u < 1 :=
      lt_of_le_of_lt (by gcongr; exact_mod_cast Nat.sub_le n 1) hn
    have g1 := gamma_nonneg hn0
    have gxa := gamma_mono (show xs.length ≤ n - 1 by omega) hn0
    have gyb := gamma_mono (show ys.length ≤ n - 1 by omega) hn0
    have gsucc := gamma_succ hn1
    rw [show n - 1 + 1 = n by omega] at gsucc
    set g := gamma (n - 1)
    have hab : |(a + b) - (xs.sum + ys.sum)| ≤ g * (R.mag xs + R.mag ys) := by
      calc _ = |(a - xs.sum) + (b - ys.sum)| := by ring_nf
        _ ≤ |a - xs.sum| + |b - ys.sum| := abs_add_le _ _
        _ ≤ gamma xs.length * R.mag xs + gamma ys.length * R.mag ys := add_le_add ea eb
        _ ≤ g * R.mag xs + g * R.mag ys := by gcongr
        _ = _ := by ring
    have hS : |xs.sum + ys.sum| + R.τ ≤ R.mag xs + R.mag ys := by
      have := R.abs_sum_add_le_mag (xs := xs ++ ys) (by simp [hx])
      rwa [List.sum_append, R.mag_append] at this
    have hov' : |a + b| ≤ maxFinite := by
      have := abs_sub_abs_le_abs_sub (a + b) (xs.sum + ys.sum)
      have : (1 + g) * (R.mag xs + R.mag ys) ≤ (1 + gamma n) * (R.mag xs + R.mag ys) := by
        gcongr; exact gamma_mono (by omega) hn
      nlinarith
    have step := R.round_near hab (R.G_add _ _ hta.mem htb.mem) hov'
    calc _ ≤ g * (R.mag xs + R.mag ys)
          + u * (|xs.sum + ys.sum| + g * (R.mag xs + R.mag ys) + R.τ) := step
      _ ≤ g * (R.mag xs + R.mag ys) + u * ((R.mag xs + R.mag ys) + g * (R.mag xs + R.mag ys)) := by
          have := mul_le_mul_of_nonneg_left hS hu.le; nlinarith
      _ = ((1 + g) * (1 + u) - 1) * (R.mag xs + R.mag ys) := by ring
      _ ≤ gamma n * (R.mag xs + R.mag ys) := by gcongr; linarith

/-- A sequential sum from `0` is a tree. -/
theorem Tree.seq {ws : List ℝ} (hw : ∀ w ∈ ws, R.G w) :
    R.Tree ws (ws.foldl (fun a b => R.fl (a + b)) 0) := by
  induction ws using List.reverseRecOn with
  | nil => exact .nil
  | append_singleton ys y ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact .node (List.Perm.refl _) (ih fun w hw' => hw w (by simp [hw']))
      (.leaf (hw y (by simp)))

end Rnd

/-- The doubles a tree of rounded additions gives for the values `xs`:
`FloatSums` (`SubstraitLean/Allowed.lean`) over the reals, and a constant run
of `k` values `x` added as one rounded product (`SCALED_CONSTANT`). -/
inductive StdModel.TreeSum (M : StdModel) : List ℝ → ℝ → Prop
  | seq {xs ws : List ℝ} : ws.Perm xs → StdModel.TreeSum M xs (M.sum ws)
  | split {zs xs ys : List ℝ} {a b : ℝ} : zs.Perm (xs ++ ys) → StdModel.TreeSum M xs a →
      StdModel.TreeSum M ys b → StdModel.TreeSum M zs (M.fl (a + b))
  | const (k : ℕ) (x : ℝ) : StdModel.TreeSum M (List.replicate k x) (M.fl (k * x))

variable (M : StdModel)

/-- Every `TreeSum` is a tree of a `Rnd` that rounds as `M` does, over a
permutation of the values. -/
theorem StdModel.TreeSum.tree {R : Rnd} (hR : R.fl = M.fl) {xs : List ℝ} {s : ℝ}
    (h : M.TreeSum xs s) : (∀ x ∈ xs, R.G x) → ∃ ys, ys.Perm xs ∧ R.Tree ys s := by
  induction h with
  | @seq xs ws hp =>
    intro hG
    refine ⟨ws, hp, ?_⟩
    have := Rnd.Tree.seq (R := R) (ws := ws) fun w hw => hG w (hp.subset hw)
    rw [hR] at this
    exact this
  | @split zs xs ys a b hp _ _ iha ihb =>
    intro hG
    obtain ⟨xs', hx, ta⟩ := iha fun x h => hG x (hp.symm.subset (by simp [h]))
    obtain ⟨ys', hy, tb⟩ := ihb fun x h => hG x (hp.symm.subset (by simp [h]))
    refine ⟨zs, List.Perm.refl _, ?_⟩
    rw [← hR]
    exact .node (hp.trans (hx.append hy).symm) ta tb
  | const k x =>
    intro hG
    refine ⟨_, List.Perm.refl _, ?_⟩
    rw [← hR]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have := Rnd.Tree.const (R := R) 0 R.G_zero
      simpa using this
    exact .const k (hG x (List.mem_replicate.mpr ⟨by omega, rfl⟩))

/-- **A tree sum, absolutely**: within `γ n · mag xs` of the exact sum. -/
theorem StdModel.TreeSum.error {xs : List ℝ} {s : ℝ} (h : M.TreeSum xs s)
    (hn : (xs.length : ℝ) * u < 1) (hov : (1 + gamma xs.length) * mag xs ≤ maxFinite) :
    |s - xs.sum| ≤ gamma xs.length * mag xs := by
  obtain ⟨ys, hp, t⟩ := StdModel.TreeSum.tree M (R := M.toRnd) rfl h fun _ _ => trivial
  have := (t.error (by rwa [hp.length_eq]) (by rw [hp.length_eq, M.toRnd.mag_perm hp]; exact hov)).perm hp
  exact this

/-- **A tree sum of doubles, without the underflow term** (`Grid`):
within `γ n · Σ |xᵢ|` of the exact sum. -/
theorem StdModel.TreeSum.grid_error (hg : M.Grid) {xs : List ℝ} {s : ℝ} (h : M.TreeSum xs s)
    (hx : ∀ x ∈ xs, OnGrid x) (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * (xs.map abs).sum ≤ maxFinite) :
    |s - xs.sum| ≤ gamma xs.length * (xs.map abs).sum := by
  have hm : ∀ l : List ℝ, (M.gridRnd hg).mag l = (l.map abs).sum := by
    intro l; simp [Rnd.mag, StdModel.gridRnd]
  obtain ⟨ys, hp, t⟩ := StdModel.TreeSum.tree M (R := M.gridRnd hg) rfl h hx
  have := (t.error (by rwa [hp.length_eq])
    (by rw [hp.length_eq, (M.gridRnd hg).mag_perm hp, hm]; exact hov)).perm hp
  unfold Rnd.Near at this
  rwa [hm] at this

/-- **A tree sum keeps the sign** (#1045): every `SUM` order the engines'
`sum_order` rows name but Kahan's (`SEQUENTIAL`, `ANY`, `PAIRWISE`,
`SCALED_CONSTANT`) gives a result `≥ 0` of values `≥ 0`, and `≤ 0` of values
`≤ 0`, since rounding is monotone with `fl 0 = 0`. So a postcondition that
reads only a column's sign holds on such an engine's value as on the
reference's (`floatSumCR_sign`). -/
theorem StdModel.TreeSum.sign {xs : List ℝ} {s : ℝ} (h : M.TreeSum xs s) :
    ((∀ x ∈ xs, 0 ≤ x) → 0 ≤ s) ∧ ((∀ x ∈ xs, x ≤ 0) → s ≤ 0) := by
  induction h with
  | seq hp =>
    exact ⟨fun hx => M.sumFrom_nonneg le_rfl fun y hy => hx y (hp.subset hy),
      fun hx => M.sumFrom_nonpos le_rfl fun y hy => hx y (hp.subset hy)⟩
  | split hp _ _ iha ihb =>
    refine ⟨fun hx => M.nonneg _ (add_nonneg (iha.1 fun y hy => hx y ?_)
        (ihb.1 fun y hy => hx y ?_)), fun hx => M.nonpos _ (add_nonpos
        (iha.2 fun y hy => hx y ?_) (ihb.2 fun y hy => hx y ?_))⟩ <;>
      exact hp.symm.subset (by simp [hy])
  | const k x =>
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [M.zero]
      · exact M.nonneg _ (mul_nonneg (Nat.cast_nonneg k)
          (hx x (List.mem_replicate.mpr ⟨by omega, rfl⟩)))
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [M.zero]
      · exact M.nonpos _ (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k)
          (hx x (List.mem_replicate.mpr ⟨by omega, rfl⟩)))

/-- **An average of a tree sum keeps the sign**: `fl(s / n)` with `s` a tree
sum (`TreeSum.sign`) and `n > 0`. -/
theorem StdModel.TreeSum.avg_sign {xs : List ℝ} {s : ℝ} (h : M.TreeSum xs s) (n : ℕ) :
    ((∀ x ∈ xs, 0 ≤ x) → 0 ≤ M.fl (s / n)) ∧ ((∀ x ∈ xs, x ≤ 0) → M.fl (s / n) ≤ 0) :=
  ⟨fun hx => M.nonneg _ (div_nonneg ((h.sign M).1 hx) (Nat.cast_nonneg n)),
    fun hx => M.nonpos _ (div_nonpos_of_nonpos_of_nonneg ((h.sign M).2 hx) (Nat.cast_nonneg n))⟩

end FloatBounds

end
