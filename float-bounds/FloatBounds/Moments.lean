module

public import FloatBounds.Sum

/-!
# Exact moments, and the scale the variance bounds work at

The variance, covariance and correlation bounds (`FloatBounds/Variance.lean`)
are about pairs `(xᵢ, yᵢ)`; the variance is the case `yᵢ = xᵢ`.

* `mx`, `my`, `comoment`: the exact means and co-moment
  `C = Σ (xᵢ − x̄)(yᵢ − ȳ)`; `comoment_eq` writes `C = Σxy − Σx·Σy / n`, and
  `comoment_snoc`, `comoment_append` are the updates Welford's algorithm and
  Chan's merge make, in exact arithmetic.
* `Scale n B`: the hypotheses every variance bound makes. All values are at
  most `B` in magnitude, with `2⁻⁵⁰⁰ ≤ B ≤ 2⁴⁰⁰`, and there are at most `2³²`
  of them. The lower bound is no restriction (a caller may always raise
  `B`); it makes the underflow term `tiny` negligible next to `B` and `B²`.
  The upper bounds keep every intermediate result far from overflow.
* `StdModel.rnd`: one rounding of an approximation, in the form the
  algorithms' error analyses use.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-! ## Exact moments -/

/-- `Σ xᵢ`. -/
noncomputable def sx (ps : List (ℝ × ℝ)) : ℝ := (ps.map Prod.fst).sum
/-- `Σ yᵢ`. -/
noncomputable def sy (ps : List (ℝ × ℝ)) : ℝ := (ps.map Prod.snd).sum
/-- `Σ xᵢ yᵢ`. -/
noncomputable def sxy (ps : List (ℝ × ℝ)) : ℝ := (ps.map fun p => p.1 * p.2).sum
/-- The mean of the `xᵢ` (`0` for no values). -/
noncomputable def mx (ps : List (ℝ × ℝ)) : ℝ := sx ps / ps.length
/-- The mean of the `yᵢ` (`0` for no values). -/
noncomputable def my (ps : List (ℝ × ℝ)) : ℝ := sy ps / ps.length
/-- The co-moment `Σ (xᵢ − x̄)(yᵢ − ȳ)`. -/
noncomputable def comoment (ps : List (ℝ × ℝ)) : ℝ :=
  (ps.map fun p => (p.1 - mx ps) * (p.2 - my ps)).sum

@[simp] theorem sx_append (ps qs : List (ℝ × ℝ)) : sx (ps ++ qs) = sx ps + sx qs := by
  simp [sx]
@[simp] theorem sy_append (ps qs : List (ℝ × ℝ)) : sy (ps ++ qs) = sy ps + sy qs := by
  simp [sy]
@[simp] theorem sxy_append (ps qs : List (ℝ × ℝ)) : sxy (ps ++ qs) = sxy ps + sxy qs := by
  simp [sxy]
@[simp] theorem sx_singleton (p : ℝ × ℝ) : sx [p] = p.1 := by simp [sx]
@[simp] theorem sy_singleton (p : ℝ × ℝ) : sy [p] = p.2 := by simp [sy]
@[simp] theorem sxy_singleton (p : ℝ × ℝ) : sxy [p] = p.1 * p.2 := by simp [sxy]

/-- `Σ (xᵢ − a)(yᵢ − b) = Σxy − b·Σx − a·Σy + n·a·b`. -/
theorem sum_dev_mul (ps : List (ℝ × ℝ)) (a b : ℝ) :
    (ps.map fun p => (p.1 - a) * (p.2 - b)).sum
      = sxy ps - b * sx ps - a * sy ps + ps.length * a * b := by
  induction ps with
  | nil => simp [sx, sy, sxy]
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    simp only [sx, sy, sxy, List.map_cons, List.sum_cons]; push_cast; ring

/-- `C = Σxy − Σx·Σy / n`. -/
theorem comoment_eq (ps : List (ℝ × ℝ)) :
    comoment ps = sxy ps - sx ps * sy ps / ps.length := by
  unfold comoment
  rw [sum_dev_mul]
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [mx, my, h]
  · have : (ps.length : ℝ) ≠ 0 := by positivity
    simp only [mx, my]; field_simp; ring

/-- **Welford's update**, exactly: one more pair moves the mean by
`(x − x̄)/(k + 1)` and the co-moment by `(x − x̄)(y − ȳ')`, with `ȳ'` the new
mean. -/
theorem mx_snoc (ps : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    mx (ps ++ [p]) = mx ps + (p.1 - mx ps) / (ps.length + 1) := by
  simp only [mx, sx_append, sx_singleton, List.length_append, List.length_singleton]
  push_cast
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [sx, List.length_eq_zero_iff.mp h]
  · have : (ps.length : ℝ) ≠ 0 := by positivity
    field_simp; ring

theorem my_snoc (ps : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    my (ps ++ [p]) = my ps + (p.2 - my ps) / (ps.length + 1) := by
  simp only [my, sy_append, sy_singleton, List.length_append, List.length_singleton]
  push_cast
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [sy, List.length_eq_zero_iff.mp h]
  · have : (ps.length : ℝ) ≠ 0 := by positivity
    field_simp; ring

theorem comoment_snoc (ps : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    comoment (ps ++ [p]) = comoment ps + (p.1 - mx ps) * (p.2 - my (ps ++ [p])) := by
  rw [comoment_eq, comoment_eq, my_snoc]
  simp only [my, mx, sx_append, sy_append, sxy_append, sx_singleton, sy_singleton,
    sxy_singleton, List.length_append, List.length_singleton]
  push_cast
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [sx, sy, sxy, List.length_eq_zero_iff.mp h]
  · have : (ps.length : ℝ) ≠ 0 := by positivity
    field_simp; ring

/-- **Chan's merge**, exactly. -/
theorem mx_append {ps qs : List (ℝ × ℝ)} (hp : ps ≠ []) (hq : qs ≠ []) :
    mx (ps ++ qs) = (qs.length * mx qs + ps.length * mx ps) / (ps.length + qs.length) := by
  have : (ps.length : ℝ) ≠ 0 := by simp [hp]
  have : (qs.length : ℝ) ≠ 0 := by simp [hq]
  simp only [mx, sx_append, List.length_append]; push_cast; field_simp; ring

theorem my_append {ps qs : List (ℝ × ℝ)} (hp : ps ≠ []) (hq : qs ≠ []) :
    my (ps ++ qs) = (qs.length * my qs + ps.length * my ps) / (ps.length + qs.length) := by
  have : (ps.length : ℝ) ≠ 0 := by simp [hp]
  have : (qs.length : ℝ) ≠ 0 := by simp [hq]
  simp only [my, sy_append, List.length_append]; push_cast; field_simp; ring

theorem comoment_append {ps qs : List (ℝ × ℝ)} (hp : ps ≠ []) (hq : qs ≠ []) :
    comoment (ps ++ qs) = comoment qs + comoment ps
      + (mx ps - mx qs) * (my ps - my qs) * qs.length * ps.length
        / (ps.length + qs.length) := by
  have h1 : (ps.length : ℝ) ≠ 0 := by simp [hp]
  have h2 : (qs.length : ℝ) ≠ 0 := by simp [hq]
  have h3 : (ps.length : ℝ) + qs.length ≠ 0 := by positivity
  rw [comoment_eq, comoment_eq, comoment_eq]
  simp only [mx, my, sx_append, sy_append, sxy_append, List.length_append]
  push_cast
  field_simp; ring

/-! ## Bounds on exact moments -/

/-- Every pair within `B`. -/
def Bounded (B : ℝ) (ps : List (ℝ × ℝ)) : Prop := ∀ p ∈ ps, |p.1| ≤ B ∧ |p.2| ≤ B

theorem Bounded.append {B : ℝ} {ps qs : List (ℝ × ℝ)} :
    Bounded B (ps ++ qs) ↔ Bounded B ps ∧ Bounded B qs := by
  simp only [Bounded, List.mem_append]
  exact ⟨fun h => ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩,
    fun h p hp => hp.elim (h.1 p) (h.2 p)⟩

theorem abs_sum_le_of_bound {B : ℝ} {xs : List ℝ} (h : ∀ x ∈ xs, |x| ≤ B) :
    |xs.sum| ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons]; push_cast
    have := abs_add_le x xs.sum
    have := h x (by simp)
    have := ih fun y hy => h y (by simp [hy])
    linarith

theorem abs_mx_le {B : ℝ} {ps : List (ℝ × ℝ)} (hB : Bounded B ps) (h0 : 0 ≤ B) :
    |mx ps| ≤ B := by
  unfold mx
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [h, h0]
  · have hl : (0 : ℝ) < ps.length := by exact_mod_cast h
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]
    have := abs_sum_le_of_bound (B := B) (xs := ps.map Prod.fst)
      (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).1)
    simp only [List.length_map] at this
    unfold sx; linarith

theorem abs_my_le {B : ℝ} {ps : List (ℝ × ℝ)} (hB : Bounded B ps) (h0 : 0 ≤ B) :
    |my ps| ≤ B := by
  unfold my
  rcases Nat.eq_zero_or_pos ps.length with h | h
  · simp [h, h0]
  · have hl : (0 : ℝ) < ps.length := by exact_mod_cast h
    rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]
    have := abs_sum_le_of_bound (B := B) (xs := ps.map Prod.snd)
      (fun x hx => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hB p hp).2)
    simp only [List.length_map] at this
    unfold sy; linarith

/-- `|C| ≤ 4 n B²`: every deviation is at most `2B`. -/
theorem abs_comoment_le {B : ℝ} {ps : List (ℝ × ℝ)} (hB : Bounded B ps) (h0 : 0 ≤ B) :
    |comoment ps| ≤ 4 * ps.length * B ^ 2 := by
  have hx := abs_mx_le hB h0
  have hy := abs_my_le hB h0
  unfold comoment
  have := abs_sum_le_of_bound (B := 4 * B ^ 2)
    (xs := ps.map fun p => (p.1 - mx ps) * (p.2 - my ps)) (by
      simp only [List.mem_map]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨h1, h2⟩ := hB p hp
      rw [abs_mul]
      have a1 : |p.1 - mx ps| ≤ 2 * B := by
        have := abs_sub p.1 (mx ps); linarith
      have a2 : |p.2 - my ps| ≤ 2 * B := by
        have := abs_sub p.2 (my ps); linarith
      nlinarith [abs_nonneg (p.1 - mx ps), abs_nonneg (p.2 - my ps)])
  simp only [List.length_map] at this
  linarith

/-! ## The scale -/

/-- The hypotheses of the variance bounds: `n ≤ 2³²` values, every one at
most `B`, with `2⁻⁵⁰⁰ ≤ B ≤ 2⁴⁰⁰`. -/
structure Scale (n : ℕ) (B : ℝ) : Prop where
  n_le : n ≤ 2 ^ 32
  B_ge : (2 : ℝ)⁻¹ ^ 500 ≤ B
  B_le : B ≤ 2 ^ 400

namespace Scale

variable {n : ℕ} {B : ℝ} (S : Scale n B)
include S

theorem B_pos : 0 < B := lt_of_lt_of_le (by positivity) S.B_ge

theorem n_le' : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast S.n_le

/-- `n · u ≤ 2⁻²¹`. -/
theorem nu_le : (n : ℝ) * u ≤ (2 : ℝ)⁻¹ ^ 21 := by
  have := S.n_le'
  calc (n : ℝ) * u ≤ 2 ^ 32 * u := by have := u_pos; gcongr
    _ = _ := by unfold u; norm_num

/-- `tiny ≤ 2⁻⁵⁰⁰ · B`. -/
theorem tiny_le_B : tiny ≤ (2 : ℝ)⁻¹ ^ 500 * B := by
  have := S.B_ge
  calc tiny = (2 : ℝ)⁻¹ ^ 500 * (2 : ℝ)⁻¹ ^ 522 := by unfold tiny; norm_num
    _ ≤ (2 : ℝ)⁻¹ ^ 500 * B := by
      gcongr; exact le_trans (by norm_num) this

/-- `tiny ≤ 2⁻²² · B²`. -/
theorem tiny_le_B2 : tiny ≤ (2 : ℝ)⁻¹ ^ 22 * B ^ 2 := by
  have := S.B_ge
  calc tiny = (2 : ℝ)⁻¹ ^ 22 * ((2 : ℝ)⁻¹ ^ 500) ^ 2 := by unfold tiny; norm_num
    _ ≤ (2 : ℝ)⁻¹ ^ 22 * B ^ 2 := by gcongr

theorem B2_le : B ^ 2 ≤ 2 ^ 800 := by
  have := S.B_le; have := S.B_pos
  calc B ^ 2 ≤ (2 ^ 400) ^ 2 := by gcongr
    _ = 2 ^ 800 := by norm_num

end Scale

theorem two_pow_le_maxFinite : (2 : ℝ) ^ 1000 ≤ maxFinite := by
  unfold maxFinite; norm_num

/-- One rounding of `z'`, an approximation of `z` within `e`, with
`|z| ≤ Z`, and `e` and `tiny` at most `W`: within `e + u · (Z + 2W)`. -/
theorem StdModel.rnd (M : StdModel) {z' z e Z W : ℝ} (hz : |z' - z| ≤ e) (hZ : |z| ≤ Z)
    (heW : e ≤ W) (htW : tiny ≤ W) (hbig : Z + W ≤ 2 ^ 1000) :
    |M.fl z' - z| ≤ e + u * (Z + 2 * W) := by
  have hu := u_pos
  have h' : |z'| ≤ maxFinite := by
    have := abs_sub_abs_le_abs_sub z' z
    linarith [two_pow_le_maxFinite]
  have := M.round_near hz h'
  have h2 : |z| + e + tiny ≤ Z + 2 * W := by linarith
  calc _ ≤ e + u * (|z| + e + tiny) := this
    _ ≤ e + u * (Z + 2 * W) := by gcongr

end FloatBounds

end
