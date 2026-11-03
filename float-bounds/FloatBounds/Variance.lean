module

public import FloatBounds.Textbook
public import Mathlib.Analysis.Real.Sqrt

/-!
# `VARIANCE`, `STDDEV`, `COVAR` and `CORR`, whatever the algorithm

Engines compute the co-moment `C = Σ (xᵢ − x̄)(yᵢ − ȳ)` (`VARIANCE` is the
case `y = x`) with different algorithms. The bounds here assume none in
particular: each of the three common ones is within the same, generous
bound of `C`,

  `|Ch − C| ≤ 64 · n² · u · B²`,

for `n ≤ 2³²` pairs, all within `B` (`Scale`):

* `twoPass_error`: the mean, then the products of the deviations, added in
  order. This is Lean's own (`sqDevSum`, `coDevSum` in
  `SubstraitLean/Aggregate.lean`).
* `textbook_error`: `Σxy − Σx · Σy / n`, the weakest of the three, with
  absolute error `O(n · u · Σx²)`; `64 · n² · u · B²` is of that form.
* `plan_good` (`FloatBounds/Welford.lean`): Welford's update and Chan's
  merge in any tree, as DuckDB computes it.

From the co-moment, in any of these, with one more rounding each:

* `covar_error`: `VAR_*` and `COVAR_*` divide by `d = n` or `n − 1`.
* `stddev_error`, `stddev_le`: `STDDEV_*` is the square root of a variance.
* `corr_le`: `CORR` is at most `1 + 3E/L + 8u` in magnitude when both
  co-moments of the sides are at least `L`, with `E` the co-moment bound.
  Without such a lower bound, nothing bounds it: `C / √(Sxx · Syy)` with
  `Sxx`, `Syy` near `0` may be anything.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-! ## From the co-moment -/

/-- `|√a − √b| ≤ √|a − b|` for `b ≥ 0` (and `√` of a negative number `0`). -/
theorem abs_sqrt_sub_sqrt_le {a b : ℝ} (hb : 0 ≤ b) : |√a - √b| ≤ √|a - b| := by
  rcases le_total a 0 with ha | ha
  · rw [Real.sqrt_eq_zero'.mpr ha, zero_sub, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith)
  · rw [Real.le_sqrt (abs_nonneg _) (abs_nonneg _), sq_abs]
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    have : a - b = (√a - √b) * (√a + √b) := by nlinarith
    rw [this, abs_mul]
    have : |√a - √b| ≤ √a + √b := by
      rw [abs_le]; constructor <;> nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    rw [← sq_abs]
    nlinarith [abs_nonneg (√a - √b), abs_of_nonneg (by positivity : 0 ≤ √a + √b)]

/-- **`VAR_*` and `COVAR_*`**: a co-moment within `E` of `C` (`|C| ≤ Cm`),
divided by `d` (`n` or `n − 1`) and rounded, is within
`E / d + 3 u Cm / d` of `C / d`. -/
theorem StdModel.covar_error {C Ch E Cm d : ℝ} (h : |Ch - C| ≤ E) (hC : |C| ≤ Cm) (hE : E ≤ Cm)
    (ht : d * tiny ≤ Cm) (hd : 1 ≤ d) (hbig : 2 * Cm ≤ 2 ^ 1000) :
    |M.fl (Ch / d) - C / d| ≤ E / d + 3 * u * Cm / d :=
  M.round_div h hC hE ht hd hbig

/-- **`STDDEV_*`**: the rounded square root of a variance `Vh` within `E` of
`V ≥ 0` is within `√E + u (√V + √E + tiny)` of `√V`. -/
theorem StdModel.stddev_error {V Vh E : ℝ} (hV : 0 ≤ V) (h : |Vh - V| ≤ E)
    (hbig : √V + √E ≤ 2 ^ 1000) :
    |M.fl √Vh - √V| ≤ √E + u * (√V + √E + tiny) := by
  have h1 : |√Vh - √V| ≤ √E :=
    le_trans (abs_sqrt_sub_sqrt_le hV) (Real.sqrt_le_sqrt h)
  have := M.round_near h1 (by
    have := abs_sub_abs_le_abs_sub (√Vh) (√V)
    rw [abs_of_nonneg (Real.sqrt_nonneg V)] at this
    linarith [two_pow_le_maxFinite])
  simpa [abs_of_nonneg (Real.sqrt_nonneg V)] using this

/-- `STDDEV_*` from above: if `Vh ≤ W`, then `fl(√Vh) ≤ (1 + u) √W + u · tiny`. -/
theorem StdModel.stddev_le {Vh W : ℝ} (h : Vh ≤ W) (hbig : √W ≤ 2 ^ 1000) :
    M.fl √Vh ≤ (1 + u) * √W + u * tiny := by
  have hs := Real.sqrt_le_sqrt h
  have := M.err (√Vh) (by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith [two_pow_le_maxFinite])
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hu := u_pos
  have := (abs_le.mp this).2
  nlinarith [Real.sqrt_nonneg Vh]

/-- Cauchy–Schwarz for co-moments: `C² ≤ Sxx · Syy`. -/
theorem sq_comoment_le (ps : List (ℝ × ℝ)) :
    comoment ps ^ 2 ≤ comoment (ps.map fun p => (p.1, p.1))
      * comoment (ps.map fun p => (p.2, p.2)) := by
  have hmx : mx (ps.map fun p => (p.1, p.1)) = mx ps := by simp [mx, sx, Function.comp_def]
  have hmy : my (ps.map fun p => (p.1, p.1)) = mx ps := by simp [mx, my, sx, sy, Function.comp_def]
  have hmx' : mx (ps.map fun p => (p.2, p.2)) = my ps := by simp [mx, my, sx, sy, Function.comp_def]
  have hmy' : my (ps.map fun p => (p.2, p.2)) = my ps := by simp [my, sy, Function.comp_def]
  unfold comoment
  rw [hmx, hmy, hmx', hmy']
  simp only [List.map_map, Function.comp_def]
  -- `Σ (A bᵢ − C aᵢ)² = A (A B − C²)` with `A = Σ aᵢ²`, `B = Σ bᵢ²`, `C = Σ aᵢ bᵢ`
  set f : ℝ × ℝ → ℝ := fun p => p.1 - mx ps
  set g : ℝ × ℝ → ℝ := fun p => p.2 - my ps
  change (ps.map fun p => f p * g p).sum ^ 2
    ≤ (ps.map fun p => f p * f p).sum * (ps.map fun p => g p * g p).sum
  set A := (ps.map fun p => f p * f p).sum
  set Bs := (ps.map fun p => g p * g p).sum
  set Cs := (ps.map fun p => f p * g p).sum
  have key : ∀ qs : List (ℝ × ℝ), (qs.map fun p => (A * g p - Cs * f p) ^ 2).sum
      = A ^ 2 * (qs.map fun p => g p * g p).sum - 2 * A * Cs * (qs.map fun p => f p * g p).sum
        + Cs ^ 2 * (qs.map fun p => f p * f p).sum := by
    intro qs
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  have hnn : 0 ≤ (ps.map fun p => (A * g p - Cs * f p) ^ 2).sum :=
    List.sum_nonneg (fun x hx => by obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx; positivity)
  rw [key] at hnn
  have hA : 0 ≤ A := List.sum_nonneg (fun x hx => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx; exact mul_self_nonneg _)
  have hB : 0 ≤ Bs := List.sum_nonneg (fun x hx => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx; exact mul_self_nonneg _)
  rcases hA.lt_or_eq with hA' | hA'
  · -- `A (A B − C²) ≥ 0`
    have : A * (A * Bs - Cs ^ 2) ≥ 0 := by nlinarith
    have := (mul_nonneg_iff_of_pos_left hA').mp this
    nlinarith
  · -- `A = 0`: every `aᵢ = 0`, so `C = 0`
    have hf : ∀ p ∈ ps, f p = 0 := by
      intro p hp
      have := List.single_le_sum (fun x hx => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx; exact mul_self_nonneg (f q))
        (f p * f p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have h0 : f p * f p ≤ 0 := by linarith
      exact mul_self_eq_zero.mp (le_antisymm h0 (mul_self_nonneg _))
    have : Cs = 0 := by
      simp only [Cs]
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      simp [hf p hp]
    rw [this, ← hA']; simp

/-- A rounding that keeps a value at least `tiny` in magnitude within a
factor `1 ± 2u`. -/
theorem StdModel.rel {z : ℝ} (h : tiny ≤ |z|) (hbig : |z| ≤ maxFinite) :
    |M.fl z - z| ≤ 2 * u * |z| := by
  have := M.err z hbig
  have hu := u_pos
  nlinarith

/-- **`CORR`**, as Lean computes it, `Ch / fl(√fl(Sxh · Syh))`: if the
co-moments `Sxh`, `Syh`, `Ch` are within `E` of `Sx`, `Sy`, `C`, with
`C² ≤ Sx · Sy` (`sq_comoment_le`) and both `Sx, Sy ≥ L ≥ 8E`, then
`|corr| ≤ 1 + 3E/L + 8u`. -/
theorem StdModel.corr_le {C Sx Sy Ch Sxh Syh E L : ℝ} (hCS : C ^ 2 ≤ Sx * Sy)
    (hC : |Ch - C| ≤ E) (hx : |Sxh - Sx| ≤ E) (hy : |Syh - Sy| ≤ E)
    (hL : 8 * E ≤ L) (hE : 0 ≤ E) (hSx : L ≤ Sx) (hSy : L ≤ Sy)
    (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L) (hbig : Sx * Sy ≤ 2 ^ 1000) :
    |M.fl (Ch / M.fl √(M.fl (Sxh * Syh)))| ≤ 1 + 3 * E / L + 8 * u := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have ht' : tiny = (2 : ℝ)⁻¹ ^ 1022 := rfl
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLt
  set x := E / L with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx8 : x ≤ 1 / 8 := by rw [hxdef, div_le_iff₀ hL0]; linarith
  have hEx : E = x * L := by rw [hxdef]; field_simp
  have hSx0 : 0 < Sx := by linarith
  have hSy0 : 0 < Sy := by linarith
  have hQ0 : 0 < Sx * Sy := by positivity
  have hLL : L * L ≤ Sx * Sy := mul_le_mul hSx hSy hL0.le hSx0.le
  -- `r = √(Sx Sy) ≥ L`, and `|C| ≤ r`
  set r := √(Sx * Sy) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hQ0
  have hr2 : r ^ 2 = Sx * Sy := Real.sq_sqrt hQ0.le
  have hrL : L ≤ r := by rw [hrdef, Real.le_sqrt hL0.le hQ0.le]; nlinarith only [hLL, hL0]
  have hCabs : |C| ≤ r := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hCS
  -- the computed co-moments of the sides
  have hxS : x * L ≤ x * Sx := mul_le_mul_of_nonneg_left hSx hx0
  have hyS : x * L ≤ x * Sy := mul_le_mul_of_nonneg_left hSy hx0
  have hx1 := abs_le.mp hx
  have hy1 := abs_le.mp hy
  have hxl : (1 - x) * Sx ≤ Sxh := by linarith [hx1.1]
  have hyl : (1 - x) * Sy ≤ Syh := by linarith [hy1.1]
  have hxu : Sxh ≤ (1 + x) * Sx := by linarith [hx1.2]
  have hyu : Syh ≤ (1 + x) * Sy := by linarith [hy1.2]
  have hxl0 : 0 ≤ (1 - x) * Sx := mul_nonneg (by linarith) hSx0.le
  have hyl0 : 0 ≤ (1 - x) * Sy := mul_nonneg (by linarith) hSy0.le
  have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
  set q := Sxh * Syh with hqdef
  have hq1 : (1 - x) ^ 2 * (Sx * Sy) ≤ q := by
    have := mul_le_mul hxl hyl hyl0 (le_trans hxl0 hxl)
    linarith [show (1 - x) ^ 2 * (Sx * Sy) = ((1 - x) * Sx) * ((1 - x) * Sy) by ring]
  have hq2 : q ≤ 2 * (Sx * Sy) := by
    have h1 := mul_le_mul hxu hyu (le_trans hyl0 hyl) (mul_nonneg (by linarith) hSx0.le)
    have h2 : (1 + x) ^ 2 ≤ 2 := by nlinarith only [hx0, hx8]
    have h3 := mul_le_mul_of_nonneg_right h2 hQ0.le
    have : (1 + x) * Sx * ((1 + x) * Sy) = (1 + x) ^ 2 * (Sx * Sy) := by ring
    linarith
  have hL2 : (2 : ℝ)⁻¹ ^ 1000 ≤ L * L := by
    have := mul_le_mul hLt hLt (by positivity) hL0.le
    linarith [show ((2 : ℝ)⁻¹ ^ 500) * (2 : ℝ)⁻¹ ^ 500 = (2 : ℝ)⁻¹ ^ 1000 by norm_num]
  have hq0 : L * L / 2 ≤ q := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - x) ^ 2 := by nlinarith only [hx0, hx8]
    have h2 := mul_le_mul h1 hLL (by positivity) (sq_nonneg _)
    linarith
  have htq : tiny ≤ q := by
    have : tiny ≤ (2 : ℝ)⁻¹ ^ 1000 / 2 := by rw [ht']; norm_num
    linarith
  have hqpos : 0 < q := by linarith
  -- `fl(q)`
  have hqmax : q ≤ maxFinite := by linarith
  have hr1 := M.rel (by rwa [abs_of_pos hqpos]) (by rwa [abs_of_pos hqpos])
  rw [abs_of_pos hqpos] at hr1
  have hfq1 : (1 - 2 * u) * q ≤ M.fl q := by linarith [(abs_le.mp hr1).1]
  have hfq2 : M.fl q ≤ (1 + 2 * u) * q := by linarith [(abs_le.mp hr1).2]
  have hfq0 : 0 < M.fl q := by
    have : 0 < (1 - 2 * u) * q := mul_pos (by linarith) hqpos
    linarith
  -- `s = √fl(q) ≥ (1 − 2u)(1 − x) r`
  set s := √(M.fl q) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hfq0
  have h12u : 0 ≤ 1 - 2 * u := by linarith
  have hsr : (1 - 2 * u) * (1 - x) * r ≤ s := by
    have h0 : 0 ≤ (1 - 2 * u) * (1 - x) * r := by
      apply mul_nonneg (mul_nonneg h12u (by linarith)) hr0.le
    rw [hsdef, Real.le_sqrt h0 hfq0.le]
    have e1 : ((1 - 2 * u) * (1 - x) * r) ^ 2 = (1 - 2 * u) ^ 2 * ((1 - x) ^ 2 * (Sx * Sy)) := by
      rw [← hr2]; ring
    have e2 : (1 - 2 * u) ^ 2 ≤ 1 - 2 * u := by rw [sq]; exact mul_le_of_le_one_right h12u (by linarith)
    have e3 : 0 ≤ (1 - x) ^ 2 * (Sx * Sy) := mul_nonneg (sq_nonneg _) hQ0.le
    have e4 := mul_le_mul_of_nonneg_right e2 e3
    have e5 := mul_le_mul_of_nonneg_left hq1 h12u
    linarith
  -- `R = fl(s) ≥ (1 − 4u)(1 − x) r`
  have hsL : tiny ≤ s := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - 2 * u) * (1 - x) := by nlinarith only [hx0, hx8, hu, hu']
    have := mul_le_mul h1 hrL hL0.le (mul_nonneg h12u (by linarith))
    have : tiny ≤ L / 4 := by
      have : tiny ≤ (2 : ℝ)⁻¹ ^ 500 / 4 := by rw [ht']; norm_num
      linarith
    linarith
  have hsmax : s ≤ maxFinite := by
    have : s ≤ M.fl q + 1 := by
      rw [hsdef, Real.sqrt_le_left (by linarith)]; nlinarith only [hfq0]
    have : (1 + 2 * u) * q ≤ 2 * q := by nlinarith only [hu, hu', hqpos]
    linarith
  have hr2' := M.rel (by rwa [abs_of_pos hs0]) (by rwa [abs_of_pos hs0])
  rw [abs_of_pos hs0] at hr2'
  set R := M.fl s with hRdef
  have hR1 : (1 - 2 * u) * s ≤ R := by linarith [(abs_le.mp hr2').1]
  have hRr : (1 - 4 * u) * ((1 - x) * r) ≤ R := by
    have h0 : 0 ≤ (1 - x) * r := mul_nonneg (by linarith) hr0.le
    have := mul_le_mul_of_nonneg_left hsr h12u
    have h3 : (1 - 4 * u) ≤ (1 - 2 * u) * (1 - 2 * u) := by nlinarith only [hu]
    have h4 := mul_le_mul_of_nonneg_right h3 h0
    have h5 : (1 - 2 * u) * ((1 - 2 * u) * (1 - x) * r) ≤ (1 - 2 * u) * s := by assumption
    have : (1 - 2 * u) * (1 - 2 * u) * ((1 - x) * r)
        = (1 - 2 * u) * ((1 - 2 * u) * (1 - x) * r) := by ring
    linarith
  have hd0 : 0 < (1 - 4 * u) * ((1 - x) * r) := by
    apply mul_pos (by linarith) (mul_pos (by linarith) hr0)
  have hR0 : 0 < R := lt_of_lt_of_le hd0 hRr
  -- `|Ch| ≤ (1 + x) r`
  have hCh : |Ch| ≤ (1 + x) * r := by
    have := abs_sub_abs_le_abs_sub Ch C
    have : x * L ≤ x * r := mul_le_mul_of_nonneg_left hrL hx0
    linarith
  -- the quotient
  have hq : |Ch / R| ≤ 1 + 3 * x + 6 * u := by
    rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    have h1 : (1 + x) * r ≤ (1 + 3 * x + 6 * u) * ((1 - 4 * u) * ((1 - x) * r)) := by
      have : (1 + x) ≤ (1 + 3 * x + 6 * u) * ((1 - 4 * u) * (1 - x)) := by
        have hxu0 : 0 ≤ x * u := by positivity
        nlinarith only [hx0, hx8, hu, hu', hxu0]
      have := mul_le_mul_of_nonneg_right this hr0.le
      linarith [show (1 + 3 * x + 6 * u) * ((1 - 4 * u) * ((1 - x) * r))
        = (1 + 3 * x + 6 * u) * ((1 - 4 * u) * (1 - x)) * r by ring]
    have h2 := mul_le_mul_of_nonneg_left hRr (by positivity : (0 : ℝ) ≤ 1 + 3 * x + 6 * u)
    linarith
  have hqm : |Ch / R| ≤ maxFinite := by
    have : 1 + 3 * x + 6 * u ≤ 2 := by linarith
    linarith
  have hfin := M.err (Ch / R) hqm
  have := abs_sub_abs_le_abs_sub (M.fl (Ch / R)) (Ch / R)
  have htu : tiny ≤ 1 / 2 := by rw [ht']; norm_num
  have : u * (|Ch / R| + tiny) ≤ u * 2 := by
    have : |Ch / R| + tiny ≤ 2 := by
      have : tiny ≤ 1 / 2 ^ 10 := by rw [ht']; norm_num
      linarith
    exact mul_le_mul_of_nonneg_left this hu.le
  have : 3 * E / L = 3 * x := by rw [hxdef]; ring
  rw [this]
  -- `|fl(z)| ≤ |z| + u (|z| + tiny)`
  linarith

end FloatBounds

end
