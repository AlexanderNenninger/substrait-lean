module

public import FloatBounds.Chan

/-!
# DuckDB's `CORR` (#444)

DuckDB computes `CORR` from three separate states, a covariance and two
Welford variances, as `COVAR_POP / (STDDEV_POP_x · STDDEV_POP_y)`
(duckdb-corr). `corr_duck_le` bounds it as `corr_le` bounds the reference's
`C / √(S_xx S_yy)`: `|corr| ≤ 1 + 3E/L + 8u` where the co-moments are within
`E` and both sides at least `L ≥ 8E`. The extra roundings (two divisions by
`n`, two square roots, a product) cost a few `u`, which `E ≥ 64 u L` covers:
`corrErr`'s `447 n u R` with `R ≥ L` is that large.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- One side of DuckDB's `CORR`: `fl √fl(Sh / n)`, for `Sh` within `x S` of
`S ≥ L`, is at least `(1 − 2u)^(3/2)·…`; we keep `√((1 − 2u)(1 − x) S / n)·(1 − 2u)`. -/
theorem StdModel.side_ge {S Sh x n L : ℝ} (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 32) (hx0 : 0 ≤ x)
    (hx8 : x ≤ 1 / 8) (hS : L ≤ S) (hSb : S ≤ 2 ^ 1000) (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hl : (1 - x) * S ≤ Sh) (hu' : Sh ≤ (1 + x) * S) :
    (1 - 2 * u) * √((1 - 2 * u) * (1 - x) * S / n) ≤ M.fl √(M.fl (Sh / n)) ∧
      M.fl √(M.fl (Sh / n)) ≤ 2 ^ 510 := by
  obtain ⟨hu, hu1, ht, -, -⟩ := fpFacts
  have ht' : tiny = (2 : ℝ)⁻¹ ^ 1022 := rfl
  have hmax := two_pow_le_maxFinite
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLt
  have hn0 : 0 < n := by linarith
  have hv1 : (1 - x) * S / n ≤ Sh / n := div_le_div_of_nonneg_right hl hn0.le
  have hlow : (2 : ℝ)⁻¹ ^ 533 ≤ (1 - x) * S / n := by
    rw [le_div_iff₀ hn0]
    have : (2 : ℝ)⁻¹ ^ 533 * n ≤ (2 : ℝ)⁻¹ ^ 533 * 2 ^ 32 := by gcongr
    have : (2 : ℝ)⁻¹ ^ 533 * 2 ^ 32 = (2 : ℝ)⁻¹ ^ 500 / 2 := by norm_num
    nlinarith
  have hv : 0 < Sh / n := lt_of_lt_of_le (by positivity) (le_trans hlow hv1)
  have hvt : tiny ≤ |Sh / n| := by
    rw [abs_of_pos hv]
    have : tiny ≤ (2 : ℝ)⁻¹ ^ 533 := by rw [ht']; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    linarith
  have hvm : |Sh / n| ≤ 2 ^ 1001 := by
    rw [abs_of_pos hv, div_le_iff₀ hn0]
    have : (1 + x) * S ≤ 2 * 2 ^ 1000 := by nlinarith
    nlinarith
  have hr1 := M.rel hvt (le_trans hvm (by unfold maxFinite; norm_num))
  rw [abs_of_pos hv] at hr1
  set w := M.fl (Sh / n)
  have hw1 : (1 - 2 * u) * (Sh / n) ≤ w := by linarith [(abs_le.mp hr1).1]
  have hw2 : w ≤ (1 + 2 * u) * (Sh / n) := by linarith [(abs_le.mp hr1).2]
  have h12 : 0 < 1 - 2 * u := by have : u ≤ 1 / 2 ^ 53 := hu1; linarith
  have hw0 : 0 < w := lt_of_lt_of_le (mul_pos h12 hv) hw1
  have hq : (1 - 2 * u) * (1 - x) * S / n ≤ w := by
    have := mul_le_mul_of_nonneg_left hv1 h12.le
    have e : (1 - 2 * u) * (1 - x) * S / n = (1 - 2 * u) * ((1 - x) * S / n) := by ring
    linarith
  have hs1 : √((1 - 2 * u) * (1 - x) * S / n) ≤ √w := Real.sqrt_le_sqrt hq
  -- `√w` is far from both ends of the doubles
  have hsw : tiny ≤ |√w| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : (2 : ℝ)⁻¹ ^ 534 ≤ w := by
      have : (2 : ℝ)⁻¹ ^ 534 ≤ (1 - 2 * u) * (2 : ℝ)⁻¹ ^ 533 := by
        have : (1 / 2 : ℝ) ≤ 1 - 2 * u := by have : u ≤ 1 / 2 ^ 53 := hu1; linarith
        nlinarith [show (2 : ℝ)⁻¹ ^ 534 = (1 / 2) * (2 : ℝ)⁻¹ ^ 533 by norm_num]
      have := mul_le_mul_of_nonneg_left (le_trans hlow hv1) h12.le
      linarith
    have h2 : √((2 : ℝ)⁻¹ ^ 534) = (2 : ℝ)⁻¹ ^ 267 := by
      rw [show (2 : ℝ)⁻¹ ^ 534 = ((2 : ℝ)⁻¹ ^ 267) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h3 := Real.sqrt_le_sqrt h1
    rw [h2] at h3
    have : tiny ≤ (2 : ℝ)⁻¹ ^ 267 := by
      rw [ht']; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    linarith
  have hwb : w ≤ 2 ^ 1002 := by
    have : (1 + 2 * u) * (Sh / n) ≤ 2 * 2 ^ 1001 := by
      have : (1 + 2 * u) ≤ 2 := by have : u ≤ 1 / 2 ^ 53 := hu1; linarith
      nlinarith [abs_of_pos hv]
    nlinarith
  have hsb : √w ≤ 2 ^ 501 := by
    rw [show (2 : ℝ) ^ 501 = √((2 ^ 501) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr2 := M.rel hsw (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hr2
  constructor
  · have := mul_le_mul_of_nonneg_left hs1 h12.le
    linarith [(abs_le.mp hr2).1]
  · have : (1 + 2 * u) * √w ≤ 2 * 2 ^ 501 := by
      have : (1 + 2 * u) ≤ 2 := by have : u ≤ 1 / 2 ^ 53 := hu1; linarith
      nlinarith [Real.sqrt_nonneg w]
    have : (2 : ℝ) * 2 ^ 501 ≤ 2 ^ 510 := by norm_num
    linarith [(abs_le.mp hr2).2]

/-- The arithmetic of `corr_duck_le`: the roundings cost at most what
`3x` leaves over `(1 + x)/(1 − x)` once `x ≥ 64u`. -/
theorem corr_key {x u : ℝ} (hx0 : 0 ≤ x) (hx8 : x ≤ 1 / 8) (hxu : 64 * u ≤ x) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 53) :
    (1 + x) * (1 + u) + u * u * (1 - 2 * u) * (1 - x)
      ≤ (1 + 3 * x + 5 * u) * (1 - 2 * u) ^ 3 * ((1 - 2 * u) * (1 - x)) := by
  have h4 : 1 - 8 * u ≤ (1 - 2 * u) ^ 4 := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -2 * u by nlinarith) 4
    push_cast at this; linarith
  have hpos : 0 ≤ (1 + 3 * x + 5 * u) * (1 - x) := by nlinarith
  have hR : (1 + 3 * x + 5 * u) * (1 - 8 * u) * (1 - x)
      ≤ (1 + 3 * x + 5 * u) * (1 - 2 * u) ^ 3 * ((1 - 2 * u) * (1 - x)) := by
    have := mul_le_mul_of_nonneg_left h4 hpos
    have e : (1 + 3 * x + 5 * u) * (1 - 2 * u) ^ 3 * ((1 - 2 * u) * (1 - x))
        = (1 + 3 * x + 5 * u) * (1 - x) * (1 - 2 * u) ^ 4 := by ring
    have e2 : (1 + 3 * x + 5 * u) * (1 - 8 * u) * (1 - x)
        = (1 + 3 * x + 5 * u) * (1 - x) * (1 - 8 * u) := by ring
    linarith
  have hL : (1 + x) * (1 + u) + u * u * (1 - 2 * u) * (1 - x) ≤ 1 + x + u + u * x + u * u := by
    have : u * u * (1 - 2 * u) * (1 - x) ≤ u * u := by
      have h1 : 0 ≤ (1 - 2 * u) * (1 - x) := by nlinarith
      have h2 : (1 - 2 * u) * (1 - x) ≤ 1 := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hu0 hu0)
      linarith [show u * u * (1 - 2 * u) * (1 - x) = u * u * ((1 - 2 * u) * (1 - x)) by ring]
    linarith [show (1 + x) * (1 + u) = 1 + x + u + u * x by ring]
  have hx2 : x * x ≤ x / 8 := by nlinarith
  have hux : u * x ≤ u / 8 := by nlinarith
  have huu : u * u ≤ u / 2 ^ 53 := by nlinarith
  have hn1 : 0 ≤ u * x * x := by positivity
  have hn2 : 0 ≤ u * u * x := by positivity
  have hexp : (1 + 3 * x + 5 * u) * (1 - 8 * u) * (1 - x)
      = 1 + 2 * x - 3 * u - 3 * (x * x) - 21 * (u * x) + 24 * (u * x * x) - 40 * (u * u)
        + 40 * (u * u * x) := by ring
  linarith

set_option maxHeartbeats 2000000 in
/-- **`CORR` as DuckDB computes it**, `COVAR_POP / (STDDEV_POP_x · STDDEV_POP_y)`
from separate states (duckdb-corr): with the co-moments within `E` of the
exact ones, both sides at least `L ≥ 8E` and `E ≥ 64 u L` (as `corrErr`'s
`447 n u R` with `R ≥ L` is), `|corr| ≤ 1 + 3E/L + 8u`, the bound of
`corr_le`. -/
theorem StdModel.corr_duck_le {C Sx Sy Ch Sxh Syh E L n : ℝ} (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 32)
    (hCS : C ^ 2 ≤ Sx * Sy) (hC : |Ch - C| ≤ E) (hx : |Sxh - Sx| ≤ E) (hy : |Syh - Sy| ≤ E)
    (hL : 8 * E ≤ L) (hSx : L ≤ Sx) (hSy : L ≤ Sy) (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hbx : Sx ≤ 2 ^ 1000) (hby : Sy ≤ 2 ^ 1000) (hEu : 64 * u * L ≤ E) :
    |M.fl (M.fl (Ch / n) / M.fl (M.fl √(M.fl (Sxh / n)) * M.fl √(M.fl (Syh / n))))|
      ≤ 1 + 3 * E / L + 8 * u := by
  obtain ⟨hu, hu1, ht, -, -⟩ := fpFacts
  have hu1' : u ≤ 1 / 2 ^ 53 := hu1
  have ht' : tiny = (2 : ℝ)⁻¹ ^ 1022 := rfl
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLt
  have hn0 : 0 < n := by linarith
  set x := E / L with hxdef
  have hE0 : 0 ≤ E := le_trans (by positivity) hEu
  have hx0 : 0 ≤ x := by positivity
  have hx8 : x ≤ 1 / 8 := by rw [hxdef, div_le_iff₀ hL0]; linarith
  have hx64 : 64 * u ≤ x := by rw [hxdef, le_div_iff₀ hL0]; linarith
  have hEx : E = x * L := by rw [hxdef]; field_simp
  have hSx0 : 0 < Sx := by linarith
  have hSy0 : 0 < Sy := by linarith
  have hQ0 : 0 < Sx * Sy := by positivity
  set r := √(Sx * Sy) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hQ0
  have hrL : L ≤ r := by
    rw [hrdef, Real.le_sqrt hL0.le hQ0.le]; nlinarith [mul_le_mul hSx hSy hL0.le hSx0.le]
  have hCabs : |C| ≤ r := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hCS
  have hxS : x * L ≤ x * Sx := mul_le_mul_of_nonneg_left hSx hx0
  have hyS : x * L ≤ x * Sy := mul_le_mul_of_nonneg_left hSy hx0
  have hx1 := abs_le.mp hx
  have hy1 := abs_le.mp hy
  obtain ⟨hsx, hsxb⟩ := M.side_ge (Sh := Sxh) hn1 hn hx0 hx8 hSx hbx hLt (by nlinarith [hx1.1, hEx, hxS])
    (by nlinarith [hx1.2, hEx, hxS])
  obtain ⟨hsy, hsyb⟩ := M.side_ge (Sh := Syh) hn1 hn hx0 hx8 hSy hby hLt (by nlinarith [hy1.1, hEx, hyS])
    (by nlinarith [hy1.2, hEx, hyS])
  set fx := M.fl √(M.fl (Sxh / n))
  set fy := M.fl √(M.fl (Syh / n))
  -- the product of the sides: at least `(1 − 2u)³ (1 − x) r / n`
  have h12 : 0 < 1 - 2 * u := by linarith
  set A := (1 - 2 * u) * (1 - x) / n with hAdef
  have hA0 : 0 < A := by rw [hAdef]; apply div_pos (mul_pos h12 (by linarith)) hn0
  have eAx : (1 - 2 * u) * (1 - x) * Sx / n = A * Sx := by rw [hAdef]; ring
  have eAy : (1 - 2 * u) * (1 - x) * Sy / n = A * Sy := by rw [hAdef]; ring
  rw [eAx] at hsx
  rw [eAy] at hsy
  have hroot : √(A * Sx) * √(A * Sy) = A * r := by
    rw [← Real.sqrt_mul (by positivity), show A * Sx * (A * Sy) = A ^ 2 * (Sx * Sy) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hA0.le]
  have hP : (1 - 2 * u) ^ 2 * (A * r) ≤ fx * fy := by
    have := mul_le_mul hsx hsy (by positivity) (le_trans (by positivity) hsx)
    have e : (1 - 2 * u) * √(A * Sx) * ((1 - 2 * u) * √(A * Sy)) = (1 - 2 * u) ^ 2 * (A * r) := by
      rw [← hroot]; ring
    linarith
  have hAr : 0 < A * r := mul_pos hA0 hr0
  have hPpos : 0 < fx * fy := lt_of_lt_of_le (by positivity) hP
  -- `A r` is far above `tiny`
  have hArL : (2 : ℝ)⁻¹ ^ 540 ≤ A * r := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - 2 * u) * (1 - x) := by nlinarith
    have h2 : (2 : ℝ)⁻¹ ^ 500 / 2 ^ 32 ≤ r / n := by
      rw [div_le_div_iff₀ (by positivity) hn0]
      have := mul_le_mul hLt hn (by positivity) (by positivity)
      nlinarith
    have : A * r = (1 - 2 * u) * (1 - x) * (r / n) := by rw [hAdef]; ring
    rw [this]
    have h3 : (2 : ℝ)⁻¹ ^ 540 ≤ (1 / 2) * ((2 : ℝ)⁻¹ ^ 500 / 2 ^ 32) := by norm_num
    nlinarith [div_nonneg hr0.le hn0.le]
  have hPt : tiny ≤ |fx * fy| := by
    rw [abs_of_pos hPpos]
    have : tiny ≤ (1 / 2) * (2 : ℝ)⁻¹ ^ 540 := by rw [ht']; norm_num
    have : (1 / 2 : ℝ) ≤ (1 - 2 * u) ^ 2 := by nlinarith
    nlinarith
  have hPm : |fx * fy| ≤ maxFinite := by
    rw [abs_of_pos hPpos]
    have := mul_le_mul hsxb hsyb (le_of_lt (lt_of_lt_of_le (by positivity) hsy))
      (by positivity)
    have : (2 : ℝ) ^ 510 * 2 ^ 510 ≤ maxFinite := by unfold maxFinite; norm_num
    linarith
  have hr3 := M.rel hPt hPm
  rw [abs_of_pos hPpos] at hr3
  set b := M.fl (fx * fy)
  have hb : (1 - 2 * u) ^ 3 * (A * r) ≤ b := by
    have := mul_le_mul_of_nonneg_left hP h12.le
    nlinarith [(abs_le.mp hr3).1]
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  -- the numerator
  have hCh : |Ch| ≤ (1 + x) * r := by
    have := abs_sub_abs_le_abs_sub Ch C
    have : x * L ≤ x * r := mul_le_mul_of_nonneg_left hrL hx0
    linarith
  have hChn : |Ch / n| ≤ (1 + x) * (r / n) := by
    rw [abs_div, abs_of_pos hn0, mul_div_assoc']
    exact div_le_div_of_nonneg_right hCh hn0.le
  have hChm : |Ch / n| ≤ maxFinite := by
    have : (1 + x) * (r / n) ≤ 2 * r := by
      have : r / n ≤ r := div_le_self hr0.le hn1
      nlinarith
    have : r ≤ 2 ^ 1000 := by
      rw [hrdef, show (2 : ℝ) ^ 1000 = √((2 ^ 1000) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith [mul_le_mul hbx hby hSy0.le (by positivity)])
    have : (2 : ℝ) * 2 ^ 1000 ≤ maxFinite := by unfold maxFinite; norm_num
    linarith
  have ha := M.err _ hChm
  set a := M.fl (Ch / n)
  have hden : 0 < (1 - 2 * u) * (1 - x) := mul_pos h12 (by linarith)
  have hta : tiny ≤ u * (A * r) := by
    have : tiny ≤ (1 / 2 ^ 60) * (2 : ℝ)⁻¹ ^ 540 := by rw [ht']; norm_num
    have : (1 / 2 ^ 60 : ℝ) ≤ u := by rw [u_val]; norm_num
    nlinarith
  have haabs : |a| ≤ (1 + x) * (1 + u) * (r / n) + u * tiny := by
    have := abs_sub_abs_le_abs_sub a (Ch / n)
    nlinarith [abs_nonneg (Ch / n)]
  -- `|a / b| ≤ 1 + 3x + 5u`
  have hq : |a / b| ≤ 1 + 3 * x + 5 * u := by
    rw [abs_div, abs_of_pos hb0, div_le_iff₀ hb0]
    have hAr' : r / n * ((1 - 2 * u) * (1 - x)) = A * r := by rw [hAdef]; ring
    have hut : u * tiny ≤ u * (u * (A * r)) := mul_le_mul_of_nonneg_left hta hu.le
    have key := corr_key hx0 hx8 hx64 hu.le hu1'
    have hrn0 : 0 ≤ r / n := div_nonneg hr0.le hn0.le
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 1 + 3 * x + 5 * u)
    have k2 := mul_le_mul_of_nonneg_left key hrn0
    have e1 : r / n * ((1 + x) * (1 + u) + u * u * (1 - 2 * u) * (1 - x))
        = (1 + x) * (1 + u) * (r / n) + u * u * (r / n * ((1 - 2 * u) * (1 - x))) := by ring
    have e2 : r / n * ((1 + 3 * x + 5 * u) * (1 - 2 * u) ^ 3 * ((1 - 2 * u) * (1 - x)))
        = (1 + 3 * x + 5 * u) * ((1 - 2 * u) ^ 3 * (r / n * ((1 - 2 * u) * (1 - x)))) := by ring
    rw [e1, e2, hAr'] at k2
    have e3 : u * (u * (A * r)) = u * u * (A * r) := by ring
    linarith
  have hqm : |a / b| ≤ maxFinite := by
    have : (2 : ℝ) ≤ maxFinite := le_trans (by norm_num) two_pow_le_maxFinite
    linarith
  have hfin := M.err (a / b) hqm
  have := abs_sub_abs_le_abs_sub (M.fl (a / b)) (a / b)
  have : 3 * E / L = 3 * x := by rw [hxdef]; ring
  rw [this]
  have htu : tiny ≤ 1 / 2 ^ 10 := by rw [ht']; norm_num
  nlinarith [abs_nonneg (a / b)]

set_option maxHeartbeats 4000000 in
/-- **DuckDB's `CORR`** (`corrOf_props` of the reference, for DuckDB's
algorithm): a covariance state `P` and variance states `Pv`, `Pw` over the
pairs' two sides, `COVAR_POP / (STDDEV_POP_x · STDDEV_POP_y)`, is at most
`1 + 3 corrErr / L + 8u` in magnitude, under the hypotheses of `core_corr_k`. -/
theorem StdModel.core_corr_chan (P : Plan) (Pv Pw : VPlan) (hne : P.pairs ≠ [])
    (hN : P.pairs.length ≤ 2 ^ 32) (hB : Bounded (2 ^ 398) P.pairs)
    (hrep : ∀ p ∈ P.pairs, M.fl p.1 = p.1 ∧ M.fl p.2 = p.2)
    (hv : Pv.vals = P.pairs.map Prod.fst) (hw : Pw.vals = P.pairs.map Prod.snd)
    {R L : ℝ}
    (hR : ∀ a ∈ [(P.pairs.map fun p => (|p.1| + tiny) ^ 2).sum,
        (P.pairs.map fun p => (|p.2| + tiny) ^ 2).sum,
        comoment (P.pairs.map fun p => (p.1, p.1))],
      ∀ b ∈ [comoment (P.pairs.map fun p => (p.1, p.1)), comoment (P.pairs.map fun p => (p.2, p.2))],
        √a * √b ≤ R)
    (hL : 8 * corrErr P.pairs.length R ((P.pairs.map fun p => (|p.1| + tiny) ^ 2).sum
      + (P.pairs.map fun p => (|p.2| + tiny) ^ 2).sum) ≤ L)
    (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hSx : L ≤ comoment (P.pairs.map fun p => (p.1, p.1)))
    (hSy : L ≤ comoment (P.pairs.map fun p => (p.2, p.2))) :
    |M.fl (M.fl ((M.run P).c / P.pairs.length) /
        M.fl (M.fl √(M.fl ((M.vEval Pv).2.2 / P.pairs.length))
          * M.fl √(M.fl ((M.vEval Pw).2.2 / P.pairs.length))))|
      ≤ 1 + 3 * corrErr P.pairs.length R ((P.pairs.map fun p => (|p.1| + tiny) ^ 2).sum
        + (P.pairs.map fun p => (|p.2| + tiny) ^ 2).sum) / L + 8 * u := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  set ps := P.pairs with hps
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
  have hEc : |(M.run P).c - comoment ps| ≤ E := by
    have h := M.chanCov_rel P hne hN (fun p h => ⟨le_trans (hB p h).1 (by norm_num),
      le_trans (hB p h).2 (by norm_num)⟩) hrep
    rw [hdx, hdy, ← hps, Real.sqrt_mul hQx0, Real.sqrt_mul hQy0, Real.sqrt_mul hSx0,
      Real.sqrt_mul hQx0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 70 * n * u * (√Qx * √Syy + √Qy * √Sxx) ≤ 140 * n * u * R := by nlinarith
    have a2 : 11 * n * u * (√Sxx * √Syy) ≤ 11 * n * u * R := by nlinarith
    have a3 : 3961 * n ^ 2 * u ^ 2 * (√Qx * √Qy) ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    have : 0 ≤ (n : ℝ) * u * R := by positivity
    linarith
  have hEx : |(M.vEval Pv).2.2 - Sxx| ≤ E := by
    have hne' : Pv.vals ≠ [] := by rw [hv]; simpa using hne
    have h := M.chanVar_rel Pv hne' (by rw [hv]; simpa using hN)
      (fun x h => by rw [hv] at h; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
                     exact le_trans (hB p hp).1 (by norm_num))
      (fun x h => by rw [hv] at h; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact (hrep p hp).1)
    rw [hv, hdx] at h
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [Real.sqrt_mul hQx0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 148 * n * u * (√Qx * √Sxx) ≤ 447 * n * u * R := by nlinarith
    have a2 : 3961 * n ^ 2 * u ^ 2 * Qx ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    linarith
  have hEy : |(M.vEval Pw).2.2 - Syy| ≤ E := by
    have hne' : Pw.vals ≠ [] := by rw [hw]; simpa using hne
    have h := M.chanVar_rel Pw hne' (by rw [hw]; simpa using hN)
      (fun x h => by rw [hw] at h; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
                     exact le_trans (hB p hp).2 (by norm_num))
      (fun x h => by rw [hw] at h; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact (hrep p hp).2)
    rw [hw, hdy] at h
    simp only [List.map_map, Function.comp_def, List.length_map] at h
    rw [Real.sqrt_mul hQy0] at h
    refine le_trans h ?_
    rw [hEdef]; unfold corrErr
    have a1 : 148 * n * u * (√Qy * √Syy) ≤ 447 * n * u * R := by nlinarith
    have a2 : 3961 * n ^ 2 * u ^ 2 * Qy ≤ 11883 * n ^ 2 * u ^ 2 * (Qx + Qy) := by
      have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 := by positivity
      nlinarith
    linarith
  have hEu : 64 * u * L ≤ E := by
    rw [hEdef]; unfold corrErr
    have : 0 ≤ (n : ℝ) ^ 2 * u ^ 2 * (Qx + Qy) := by positivity
    have : 0 ≤ (n : ℝ) ^ 2 * u * tiny := by positivity
    have h1 := mul_le_mul_of_nonneg_left hLR (by positivity : (0 : ℝ) ≤ u)
    have h2 := mul_nonneg (sub_nonneg.mpr hn1) (mul_nonneg hu.le hR0)
    have : 64 * u * L ≤ 447 * n * u * R := by nlinarith
    linarith
  have hbx : Sxx ≤ 2 ^ 1000 := le_trans (le_trans hSxQ hQxb) (by norm_num)
  have hby : Syy ≤ 2 ^ 1000 := le_trans (le_trans hSyQ hQyb) (by norm_num)
  exact M.corr_duck_le hn1 hnN (sq_comoment_le ps) hEc hEx hEy hL hSx hSy hLt hbx hby hEu

end FloatBounds

end
