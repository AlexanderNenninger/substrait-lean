module

public import FloatBounds.CovSG

/-!
# Polars's `CORR` (#1808)

Polars's `PearsonState` (`crates/polars-compute/src/moment.rs`) keeps one
count, the two means and the three co-moments `dp_xx`, `dp_xy`, `dp_yy`. Its
blocks, single pairs and merges are, side by side, the variance's (`PRun`)
and the covariance's (`PCRun`) over the same means, so each co-moment is
within `plVar_rel`'s or `plCov_rel`'s bound. `finalize` gives
`dp_xy / √(dp_xx · dp_yy)` where the product is positive. With the
co-moments within `E` of the exact ones and both sides at least `L ≥ 8E`,
that is at most `1 + 3E/L + 8u` in magnitude (`corr_pl_le`), the bound of
`corr_le` and of DuckDB's `corr_duck_le`.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- The arithmetic of `corr_pl_le`: three roundings cost less than what
`3x` leaves over `(1 + x)/(1 − x)`. -/
theorem corr_pl_key {x u : ℝ} (hx0 : 0 ≤ x) (hx8 : x ≤ 1 / 8) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 53) :
    (1 + x) * (1 + u) ≤ (1 + 3 * x + 7 * u) * (1 - 1.01 * u) ^ 2 * (1 - x) := by
  have h1 : 1 - 2.02 * u ≤ (1 - 1.01 * u) ^ 2 := by nlinarith [sq_nonneg (1.01 * u)]
  have hA0 : 0 ≤ (1 + 3 * x + 7 * u) * (1 - x) := by nlinarith
  have h2 : (1 + 3 * x + 7 * u) * (1 - x) * (1 - 2.02 * u)
      ≤ (1 + 3 * x + 7 * u) * (1 - 1.01 * u) ^ 2 * (1 - x) := by
    have := mul_le_mul_of_nonneg_left h1 hA0
    have e : (1 + 3 * x + 7 * u) * (1 - 1.01 * u) ^ 2 * (1 - x)
        = (1 + 3 * x + 7 * u) * (1 - x) * (1 - 1.01 * u) ^ 2 := by ring
    linarith
  have hux : u * x ≤ u / 8 := by nlinarith
  have hxx : x * x ≤ x / 8 := by nlinarith
  have huu : u * u ≤ u / 2 ^ 53 := by nlinarith
  have p1 : 0 ≤ u * x * x := by positivity
  have p2 : 0 ≤ u * u * x := by positivity
  have hux2 : u * x * x ≤ u / 64 := by nlinarith
  have hexp : (1 + 3 * x + 7 * u) * (1 - x) * (1 - 2.02 * u)
      = 1 + 2 * x - 3 * (x * x) + 4.98 * u - 11.04 * (u * x) + 6.06 * (u * x * x)
        - 14.14 * (u * u) + 14.14 * (u * u * x) := by ring
  have hl : (1 + x) * (1 + u) = 1 + x + u + u * x := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **`CORR` as Polars computes it**, `dp_xy / √(dp_xx · dp_yy)`
(`PearsonState::finalize`): with the co-moments within `E` of the exact ones,
both sides at least `L ≥ 8E` and their product at most `2¹⁰⁰⁰`, the product
it takes the root of is positive, and `|corr| ≤ 1 + 3E/L + 8u`, the bound of
`corr_le`. -/
theorem StdModel.corr_pl_le {C Sx Sy Ch Sxh Syh E L : ℝ} (hCS : C ^ 2 ≤ Sx * Sy)
    (hC : |Ch - C| ≤ E) (hx : |Sxh - Sx| ≤ E) (hy : |Syh - Sy| ≤ E) (hE0 : 0 ≤ E)
    (hL : 8 * E ≤ L) (hSx : L ≤ Sx) (hSy : L ≤ Sy) (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hSS : Sx * Sy ≤ 2 ^ 1000) :
    0 < M.fl (Sxh * Syh) ∧
      |M.fl (Ch / M.fl √(M.fl (Sxh * Syh)))| ≤ 1 + 3 * E / L + 8 * u := by
  obtain ⟨hu, hu1, ht, -, hmax⟩ := fpFacts
  have hu1' : u ≤ 1 / 2 ^ 53 := hu1
  have ht' : tiny = (2 : ℝ)⁻¹ ^ 1022 := rfl
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLt
  set x := E / L with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx8 : x ≤ 1 / 8 := by rw [hxdef, div_le_iff₀ hL0]; linarith
  have hEx : E = x * L := by rw [hxdef]; field_simp
  -- each side within `x` of its co-moment
  have hEsx : E ≤ x * Sx := by rw [hEx]; exact mul_le_mul_of_nonneg_left hSx hx0
  have hEsy : E ≤ x * Sy := by rw [hEx]; exact mul_le_mul_of_nonneg_left hSy hx0
  have ha : (1 - x) * Sx ≤ Sxh := by linarith [(abs_le.mp hx).1]
  have ha' : Sxh ≤ (1 + x) * Sx := by linarith [(abs_le.mp hx).2]
  have hb : (1 - x) * Sy ≤ Syh := by linarith [(abs_le.mp hy).1]
  have hb' : Syh ≤ (1 + x) * Sy := by linarith [(abs_le.mp hy).2]
  have hSx0 : 0 < Sx := by linarith
  have hSy0 : 0 < Sy := by linarith
  set S := Sx * Sy with hSdef
  have hS0 : 0 < S := by positivity
  have h1x : 0 < 1 - x := by linarith
  have ha0 : 0 ≤ (1 - x) * Sx := by positivity
  have hb0 : 0 ≤ (1 - x) * Sy := by positivity
  -- the product `z = Ŝ_x Ŝ_y`
  set z := Sxh * Syh with hzdef
  have hzlo : (1 - x) ^ 2 * S ≤ z := by
    have := mul_le_mul ha hb hb0 (le_trans ha0 ha)
    rw [hSdef, hzdef]; linarith [show (1 - x) * Sx * ((1 - x) * Sy) = (1 - x) ^ 2 * (Sx * Sy) by ring]
  have hzhi : z ≤ (1 + x) ^ 2 * S := by
    have := mul_le_mul ha' hb' (le_trans hb0 hb) (by positivity)
    rw [hSdef, hzdef]; linarith [show (1 + x) * Sx * ((1 + x) * Sy) = (1 + x) ^ 2 * (Sx * Sy) by ring]
  have hLS : L ^ 2 ≤ S := by
    rw [sq, hSdef]; exact mul_le_mul hSx hSy hL0.le hSx0.le
  have hL2 : (2 : ℝ)⁻¹ ^ 1000 ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hLt 2
    rw [← pow_mul] at this; exact this
  have h1x2 : (49 : ℝ) / 64 ≤ (1 - x) ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) (by linarith : (7 : ℝ) / 8 ≤ 1 - x) 2
    have e : ((7 : ℝ) / 8) ^ 2 = 49 / 64 := by norm_num
    linarith
  have hz0 : (2 : ℝ)⁻¹ ^ 1001 ≤ z := by
    have h := mul_le_mul h1x2 (le_trans hL2 hLS) (by positivity) (by positivity)
    have e : (49 : ℝ) / 64 * (2 : ℝ)⁻¹ ^ 1000 ≥ (2 : ℝ)⁻¹ ^ 1001 := by norm_num
    linarith
  have hzb : z ≤ 2 ^ 1001 := by
    have h1 : (1 + x) ^ 2 ≤ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith : 1 + x ≤ (9 : ℝ) / 8) 2
      have e : ((9 : ℝ) / 8) ^ 2 ≤ 2 := by norm_num
      linarith
    have := mul_le_mul h1 hSS hS0.le (by norm_num)
    have e : (2 : ℝ) * 2 ^ 1000 = 2 ^ 1001 := by norm_num
    linarith
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz0
  have htz : tiny ≤ 1 / 2 ^ 21 * z := by
    have k := mul_le_mul_of_nonneg_left hz0 (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 21)
    have : (2 : ℝ)⁻¹ ^ 1022 ≤ 1 / 2 ^ 21 * (2 : ℝ)⁻¹ ^ 1001 := by norm_num
    rw [ht']; linarith
  -- `P = fl(z) ≥ (1 − 1.01u) z`
  have eP := M.err z (by
    rw [abs_of_pos hzpos]
    have : (2 : ℝ) ^ 1001 ≤ 2 ^ 1023 := by norm_num
    linarith)
  set P := M.fl z with hPdef
  rw [abs_of_pos hzpos] at eP
  have hutz : u * tiny ≤ 0.01 * u * z := by
    have := mul_le_mul_of_nonneg_left htz hu.le
    have : 0 ≤ u * z := by positivity
    have e : u * (1 / 2 ^ 21 * z) = 1 / 2 ^ 21 * (u * z) := by ring
    have e2 : 0.01 * u * z = 0.01 * (u * z) := by ring
    linarith
  have hPlo : (1 - 1.01 * u) * z ≤ P := by linarith [(abs_le.mp eP).1]
  have hPpos : 0 < P := by
    have : 0 < (1 - 1.01 * u) * z := mul_pos (by linarith) hzpos
    linarith
  refine ⟨hPpos, ?_⟩
  have hPb : P ≤ 2 ^ 1002 := by
    have := (abs_le.mp eP).2
    have : u * (z + tiny) ≤ z := by
      have k := mul_le_mul_of_nonneg_right hu1' (by positivity : (0 : ℝ) ≤ z + tiny)
      have : tiny ≤ z := by linarith
      linarith
    have e : (2 : ℝ) ^ 1002 = 2 * 2 ^ 1001 := by norm_num
    linarith
  -- `√P ≥ (1 − 1.01u)(1 − x) √S`
  have h1u : 0 ≤ 1 - 1.01 * u := by linarith
  have hsP : (1 - 1.01 * u) * ((1 - x) * √S) ≤ √P := by
    apply Real.le_sqrt_of_sq_le
    have hsS := Real.sq_sqrt hS0.le
    have e : ((1 - 1.01 * u) * ((1 - x) * √S)) ^ 2 = (1 - 1.01 * u) ^ 2 * ((1 - x) ^ 2 * S) := by
      rw [mul_pow, mul_pow, hsS]
    rw [e]
    have k1 : (1 - 1.01 * u) ^ 2 ≤ 1 - 1.01 * u := by
      have := mul_le_mul_of_nonneg_left (show 1 - 1.01 * u ≤ 1 by linarith) h1u
      rw [sq]; linarith
    have k2 := mul_le_mul k1 hzlo (by positivity) h1u
    linarith
  have hsPb : √P ≤ 2 ^ 501 := by
    rw [Real.sqrt_le_left (by positivity)]
    have e : ((2 : ℝ) ^ 501) ^ 2 = 2 ^ 1002 := by norm_num
    linarith
  have hsS0 : 0 < √S := Real.sqrt_pos.mpr hS0
  have hLsS : L ≤ √S := Real.le_sqrt_of_sq_le hLS
  have hsPlo : (2 : ℝ)⁻¹ ^ 501 ≤ √P := by
    have k : (2 : ℝ)⁻¹ ^ 501 ≤ (1 - 1.01 * u) * ((1 - x) * L) := by
      have k1 : (0.8 : ℝ) ≤ (1 - 1.01 * u) * (1 - x) := by
        have : 0 ≤ u * x := by positivity
        have e : (1 - 1.01 * u) * (1 - x) = 1 - x - 1.01 * u + 1.01 * (u * x) := by ring
        linarith
      have k2 := mul_le_mul_of_nonneg_left hLt (by norm_num : (0 : ℝ) ≤ 0.8)
      have e : (2 : ℝ)⁻¹ ^ 501 ≤ 0.8 * (2 : ℝ)⁻¹ ^ 500 := by norm_num
      have k3 := mul_le_mul_of_nonneg_right k1 hL0.le
      have e2 : (1 - 1.01 * u) * ((1 - x) * L) = (1 - 1.01 * u) * (1 - x) * L := by ring
      linarith
    have : (1 - 1.01 * u) * ((1 - x) * L) ≤ (1 - 1.01 * u) * ((1 - x) * √S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLsS h1x.le) h1u
    linarith
  -- `r = fl(√P) ≥ (1 − 1.01u)² (1 − x) √S`
  obtain ⟨er, -⟩ := M.err_le (z := √P) (B := 2 ^ 501)
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsPb) (by norm_num) (by norm_num)
  set r := M.fl √P with hrdef
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at er
  have hut2 : u * tiny ≤ 0.01 * u * √P := by
    have : tiny ≤ 0.01 * √P := by
      rw [ht']
      have : (2 : ℝ)⁻¹ ^ 1022 ≤ 0.01 * (2 : ℝ)⁻¹ ^ 501 := by norm_num
      linarith
    have := mul_le_mul_of_nonneg_left this hu.le
    linarith
  have hrlo : (1 - 1.01 * u) * √P ≤ r := by linarith [(abs_le.mp er).1]
  set D := (1 - 1.01 * u) ^ 2 * (1 - x) * √S with hDdef
  have hrD : D ≤ r := by
    have := mul_le_mul_of_nonneg_left hsP h1u
    have e : (1 - 1.01 * u) * ((1 - 1.01 * u) * ((1 - x) * √S)) = D := by rw [hDdef]; ring
    linarith
  have hD0 : 0 < D := by
    rw [hDdef]
    have : 0 < 1 - 1.01 * u := by linarith
    positivity
  have hr0 : 0 < r := lt_of_lt_of_le hD0 hrD
  -- `|Ĉ| ≤ (1 + x) √S`
  have hCabs : |C| ≤ √S := Real.abs_le_sqrt hCS
  have hEs : E ≤ x * √S := by rw [hEx]; exact mul_le_mul_of_nonneg_left hLsS hx0
  have hCh : |Ch| ≤ (1 + x) * √S := by
    have := abs_sub_abs_le_abs_sub Ch C
    linarith
  -- the quotient
  set w := Ch / r with hwdef
  have hkey := corr_pl_key hx0 hx8 hu.le hu1'
  have hw : |w| * (1 + u) ≤ 1 + 3 * x + 7 * u := by
    rw [hwdef, abs_div, abs_of_pos hr0, div_mul_eq_mul_div, div_le_iff₀ hr0]
    have k1 : |Ch| * (1 + u) ≤ (1 + x) * √S * (1 + u) :=
      mul_le_mul_of_nonneg_right hCh (by linarith)
    have k2 : (1 + 3 * x + 7 * u) * D ≤ (1 + 3 * x + 7 * u) * r :=
      mul_le_mul_of_nonneg_left hrD (by positivity)
    have k3 := mul_le_mul_of_nonneg_right hkey hsS0.le
    have e1 : (1 + x) * √S * (1 + u) = (1 + x) * (1 + u) * √S := by ring
    have e2 : (1 + 3 * x + 7 * u) * D = (1 + 3 * x + 7 * u) * (1 - 1.01 * u) ^ 2 * (1 - x) * √S := by
      rw [hDdef]; ring
    linarith
  have hwb : |w| ≤ 2 := by
    have : 0 ≤ |w| * u := by positivity
    have e : |w| * (1 + u) = |w| + |w| * u := by ring
    linarith
  obtain ⟨eq, -⟩ := M.err_le (z := w) (B := 2) hwb (by norm_num) (by norm_num)
  have hq : |M.fl w| ≤ |w| + u * (|w| + tiny) := by
    have := abs_sub_abs_le_abs_sub (M.fl w) w; linarith
  have htu : u * tiny ≤ u := by
    have : tiny ≤ 1 := by rw [ht']; norm_num
    have := mul_le_mul_of_nonneg_left this hu.le
    linarith
  have e3 : 3 * E / L = 3 * x := by rw [hxdef]; ring
  rw [e3]
  linarith

/-! ## Polars's `PearsonState` -/

/-- Polars's `PearsonState`: the count, the two means and the co-moments
`dp_xx`, `dp_xy`, `dp_yy`. -/
structure PState where
  n : ℕ
  mx : ℝ
  my : ℝ
  sxx : ℝ
  sxy : ℝ
  syy : ℝ

/-- The `x` side as a variance state. -/
def PState.xs (s : PState) : ℕ × ℝ × ℝ := (s.n, s.mx, s.sxx)

/-- The `y` side as a variance state. -/
def PState.ys (s : PState) : ℕ × ℝ × ℝ := (s.n, s.my, s.syy)

/-- The covariance state. -/
def PState.cov (s : PState) : WState := ⟨s.n, s.mx, s.my, s.sxy⟩

/-- Polars's `PearsonState::combine`: the means of `sgMean`, `dp_xx` and
`dp_yy` as `VarState::combine` (`sgMerge`) and `dp_xy` as
`CovState::combine` (`sgCov`), term for term. -/
noncomputable def StdModel.pearMerge (t s : PState) : PState :=
  if s.n = 0 then t else if t.n = 0 then s else
    ⟨t.n + s.n, M.sgMean t.xs s.xs, M.sgMean t.ys s.ys, (M.sgMerge t.xs s.xs).2.2,
      (M.sgCov t.cov s.cov).c, (M.sgMerge t.ys s.ys).2.2⟩

/-- The states Polars's `corr` computes over the pairs `ps`, in any order and
any tree: a two-pass block (`PearsonState::new`, whose two sides and
products are the variance's and the covariance's blocks over the same
means), one pair (a grouped `insert_one` is the merge with it), or a merge
of two of them. -/
inductive StdModel.PRRun (M : StdModel) : List (ℝ × ℝ) → PState → Prop
  | one (p : ℝ × ℝ) : StdModel.PRRun M [p] ⟨1, p.1, p.2, 0, 0, 0⟩
  | block {ps : List (ℝ × ℝ)} {s : PState} : M.Block (ps.map Prod.fst) s.xs →
      M.Block (ps.map Prod.snd) s.ys → M.CBlock ps s.cov → StdModel.PRRun M ps s
  | merge {pa pb : List (ℝ × ℝ)} {t s : PState} : StdModel.PRRun M pa t →
      StdModel.PRRun M pb s → StdModel.PRRun M (pa ++ pb) (M.pearMerge t s)

/-- One value's Welford state is `(1, x, 0)`. -/
theorem StdModel.wState_one {x : ℝ} (hx : M.fl x = x) : M.wState [x] = (1, x, 0) := by
  simp [StdModel.wState, StdModel.wStep, hx, M.zero]

/-- **A `PearsonState` is the variance's on each side and the covariance's**:
for values that are doubles, its sides are states of `PRun` and its
co-moment of `PCRun`. -/
theorem StdModel.PRRun.proj {ps : List (ℝ × ℝ)} {s : PState} (h : M.PRRun ps s) :
    (∀ p ∈ ps, M.fl p.1 = p.1 ∧ M.fl p.2 = p.2) →
    M.PRun (ps.map Prod.fst) s.xs ∧ M.PRun (ps.map Prod.snd) s.ys ∧ M.PCRun ps s.cov := by
  induction h with
  | one p =>
    intro hrep
    obtain ⟨h1, h2⟩ := hrep p (by simp)
    refine ⟨?_, ?_, StdModel.PCRun.one p⟩
    · have := StdModel.PRun.welford (M := M) [p.1]
      rw [M.wState_one h1] at this; exact this
    · have := StdModel.PRun.welford (M := M) [p.2]
      rw [M.wState_one h2] at this; exact this
  | block hx hy hc => intro _; exact ⟨.block hx, .block hy, .block hc⟩
  | @merge pa pb t s' ha hb iht ihs =>
    intro hrep
    obtain ⟨xt, yt, ct⟩ := iht (fun p hp => hrep p (List.mem_append_left _ hp))
    obtain ⟨xs, ys, cs⟩ := ihs (fun p hp => hrep p (List.mem_append_right _ hp))
    obtain ⟨hnt, hpa⟩ := ct.count
    obtain ⟨hns, hpb⟩ := cs.count
    have ht0 : t.n ≠ 0 := by
      have : t.cov.n = t.n := rfl
      rw [← this, hnt]; exact (List.length_pos_iff.mpr hpa).ne'
    have hs0 : s'.n ≠ 0 := by
      have : s'.cov.n = s'.n := rfl
      rw [← this, hns]; exact (List.length_pos_iff.mpr hpb).ne'
    have ex : (M.pearMerge t s').xs = M.sgMerge t.xs s'.xs := by
      simp [StdModel.pearMerge, StdModel.sgMerge, PState.xs, ht0, hs0]
    have ey : (M.pearMerge t s').ys = M.sgMerge t.ys s'.ys := by
      simp [StdModel.pearMerge, StdModel.sgMerge, PState.ys, ht0, hs0]
    have ec : (M.pearMerge t s').cov = M.sgCov t.cov s'.cov := by
      simp [StdModel.pearMerge, StdModel.sgCov, PState.cov, PState.xs, PState.ys,
        StdModel.sgMean, ht0, hs0]
    rw [ex, ey, ec, List.map_append, List.map_append]
    exact ⟨.merge xt xs, .merge yt ys, .merge ct cs⟩

set_option maxHeartbeats 4000000 in
/-- **Polars's `CORR`** (`corrOf_props` of the reference, for Polars's
algorithm): a `PearsonState` over `n ≤ 2³²` pairs of doubles at most `2³⁹⁸`
in magnitude, `dp_xy / √(dp_xx · dp_yy)`, takes the root of a positive
product and is at most `1 + 3 corrErr / L + 8u` in magnitude, under the
hypotheses of `core_corr_chan` and with `S_xx S_yy ≤ 2¹⁰⁰⁰`, as `corrProps`
states. `corrErr`'s constants are Chan's: Polars's co-moments fit them. -/
theorem StdModel.core_corr_polars {ps : List (ℝ × ℝ)} {s : PState} (h : M.PRRun ps s)
    (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32) (hB : Bounded (2 ^ 398) ps)
    (hrep : ∀ p ∈ ps, M.fl p.1 = p.1 ∧ M.fl p.2 = p.2)
    {R L : ℝ}
    (hR : ∀ a ∈ [(ps.map fun p => (|p.1| + tiny) ^ 2).sum,
        (ps.map fun p => (|p.2| + tiny) ^ 2).sum,
        comoment (ps.map fun p => (p.1, p.1))],
      ∀ b ∈ [comoment (ps.map fun p => (p.1, p.1)), comoment (ps.map fun p => (p.2, p.2))],
        √a * √b ≤ R)
    (hL : 8 * corrErr ps.length R ((ps.map fun p => (|p.1| + tiny) ^ 2).sum
      + (ps.map fun p => (|p.2| + tiny) ^ 2).sum) ≤ L)
    (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hSx : L ≤ comoment (ps.map fun p => (p.1, p.1)))
    (hSy : L ≤ comoment (ps.map fun p => (p.2, p.2)))
    (hSS : comoment (ps.map fun p => (p.1, p.1)) * comoment (ps.map fun p => (p.2, p.2))
      ≤ 2 ^ 1000) :
    0 < M.fl (s.sxx * s.syy) ∧
      |M.fl (s.sxy / M.fl √(M.fl (s.sxx * s.syy)))|
        ≤ 1 + 3 * corrErr ps.length R ((ps.map fun p => (|p.1| + tiny) ^ 2).sum
          + (ps.map fun p => (|p.2| + tiny) ^ 2).sum) / L + 8 * u := by
  obtain ⟨hx, hy, hc⟩ := StdModel.PRRun.proj M h hrep
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  set n : ℕ := ps.length with hn_def
  set Qx := (ps.map fun p => (|p.1| + tiny) ^ 2).sum
  set Qy := (ps.map fun p => (|p.2| + tiny) ^ 2).sum
  set Sxx := comoment (ps.map fun p => (p.1, p.1))
  set Syy := comoment (ps.map fun p => (p.2, p.2))
  set E := corrErr n R (Qx + Qy) with hEdef
  obtain ⟨hSx0, hSxQ, hQxb⟩ := SQ_facts (qs := ps) (fun p => p.1) hN (fun p h => (hB p h).1)
  obtain ⟨hSy0, hSyQ, hQyb⟩ := SQ_facts (qs := ps) (fun p => p.2) hN (fun p h => (hB p h).2)
  have hQx0 : 0 ≤ Qx := le_trans hSx0 hSxQ
  have hQy0 : 0 ≤ Qy := le_trans hSy0 hSyQ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hnN : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hdx : dupL (ps.map Prod.fst) = ps.map fun p => (p.1, p.1) := by
    simp [dupL, List.map_map, Function.comp_def]
  have hdy : dupL (ps.map Prod.snd) = ps.map fun p => (p.2, p.2) := by
    simp [dupL, List.map_map, Function.comp_def]
  -- the witnesses
  have r1 : √Qx * √Syy ≤ R := hR _ (by simp) _ (by simp)
  have r2 : √Qy * √Sxx ≤ R := hR _ (by simp) _ (by simp)
  have rs : √Sxx * √Syy ≤ R := hR _ (by simp) _ (by simp)
  have rx : √Qx * √Sxx ≤ R := hR _ (by simp) _ (by simp)
  have ry : √Qy * √Syy ≤ R := hR _ (by simp) _ (by simp)
  have rxx : √Sxx * √Sxx ≤ R := hR _ (by simp) _ (by simp)
  have hSxx : √Sxx * √Sxx = Sxx := Real.mul_self_sqrt hSx0
  have hLR : L ≤ R := by linarith
  have hR0 : 0 ≤ R := le_trans (by positivity) rs
  have hRQ : √Qx * √Qy ≤ Qx + Qy := by
    have := Real.mul_self_sqrt hQx0; have := Real.mul_self_sqrt hQy0
    nlinarith [sq_nonneg (√Qx - √Qy)]
  have hnu0 : 0 ≤ (n : ℝ) * u := by positivity
  have hnn : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have hntiny : 793 * n * u * tiny ≤ 2379 * n ^ 2 * u * tiny := by
    have : 0 ≤ u * tiny := by positivity
    nlinarith
  -- the three co-moments, each within `E`
  have hEc : |s.sxy - comoment ps| ≤ E := by
    have h := M.plCov_rel hc hN (fun p h => ⟨le_trans (hB p h).1 (by norm_num),
      le_trans (hB p h).2 (by norm_num)⟩)
    rw [hdx, hdy, Real.sqrt_mul hQx0, Real.sqrt_mul hQy0, Real.sqrt_mul hSx0,
      Real.sqrt_mul hQx0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 106 * n * u * (√Qx * √Syy + √Qy * √Sxx) ≤ 212 * n * u * R := by nlinarith
    have a2 : 11 * n * u * (√Sxx * √Syy) ≤ 11 * n * u * R := by nlinarith
    have a3 : 3961 * n ^ 2 * u ^ 2 * (√Qx * √Qy) ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    have : 0 ≤ (n : ℝ) * u * R := by positivity
    linarith
  have hEx : |s.sxx - Sxx| ≤ E := by
    have h := M.plVar_rel hx (by simpa using hne) (by simpa using hN)
      (fun x h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
                     exact le_trans (hB p hp).1 (by norm_num))
      (fun x h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact (hrep p hp).1)
    rw [hdx] at h
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [Real.sqrt_mul hQx0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 148 * n * u * (√Qx * √Sxx) ≤ 447 * n * u * R := by nlinarith
    have a2 : 3961 * n ^ 2 * u ^ 2 * Qx ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    linarith
  have hEy : |s.syy - Syy| ≤ E := by
    have h := M.plVar_rel hy (by simpa using hne) (by simpa using hN)
      (fun x h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
                     exact le_trans (hB p hp).2 (by norm_num))
      (fun x h => by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact (hrep p hp).2)
    rw [hdy] at h
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [Real.sqrt_mul hQy0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 148 * n * u * (√Qy * √Syy) ≤ 447 * n * u * R := by nlinarith
    have a2 : 3961 * n ^ 2 * u ^ 2 * Qy ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    linarith
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) hEc
  exact M.corr_pl_le (sq_comoment_le ps) hEc hEx hEy hE0 hL hSx hSy hLt hSS

end FloatBounds

end

open Lean in
run_cmd do
  for thm in ["FloatBounds.StdModel.core_cov_polars", "FloatBounds.StdModel.core_corr_polars"] do
    unless (← getEnv).contains thm.toName do
      throwError "no theorem {thm}"
