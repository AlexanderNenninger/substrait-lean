module

public import FloatBounds.Epsilon
public import FloatBounds.CoreKappa
public import FloatBounds.TwoPassRel

/-!
# The corrected two-pass formula on shifted values (#1810)

Snowflake's `VAR_*` of doubles, as sverify writes it, reads its values shifted
by their group's mean (`momentNum_shift` in `core/Sverify/Core/FloatMoments.lean`
keeps the reference's value) and applies the textbook formula to them:
`Σ d² − (Σ d)² / n` on `dᵢ = fl(xᵢ − c)`. That is the corrected two-pass
algorithm of Chan, Golub and LeVeque. Its sums may be added in any tree, or by
Kahan's sum (`StdModel.Summed`): Snowflake's order is not known.

* `comoment_shift`: shifting the values leaves the co-moment `S` alone.
* `comoment_perturb`: moving each value by `eᵢ` moves `S` by at most
  `2 √S √(Σ e²) + Σ e²`.
* `StdModel.textbook_summed`: the formula on doubles `d`, both sums in any
  order, is within `(2n + 6) u D + 5 u |T| √(n D) + 64 n² u² D + 64 n² u · tiny`
  of their co-moment, `D = Σ d²`, `T = Σ d`. The `T` term is of second order
  when the values are centred.
* `StdModel.corrTwoPass_error`: the whole algorithm against the exact `S` of
  the `xᵢ`, for any shift `c`, with `K = |Σ (xᵢ − c)|` (small for the group's
  mean) and `W = Σ (|xᵢ − c| + tiny)²`, which is `S + K²/n` up to the
  underflow terms (`sum_sq_shift`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-! ## Exact algebra -/

/-- A co-moment with a constant side is `0`. -/
theorem comoment_const_right {α : Type*} (qs : List α) (a : α → ℝ) (k : ℝ) :
    comoment (qs.map fun q => (a q, k)) = 0 := by
  rcases eq_or_ne qs [] with rfl | hne
  · simp [comoment]
  have hl : (qs.length : ℝ) ≠ 0 := by simp [hne]
  have hmy : my (qs.map fun q => (a q, k)) = k := by
    simp only [my, sy, List.map_map, Function.comp_def, List.length_map, List.map_const',
      List.sum_replicate, nsmul_eq_mul]
    field_simp
  unfold comoment
  rw [hmy]
  simp [Function.comp_def]

/-- The co-moment is symmetric. -/
theorem comoment_swap {α : Type*} (qs : List α) (a b : α → ℝ) :
    comoment (qs.map fun q => (b q, a q)) = comoment (qs.map fun q => (a q, b q)) := by
  rw [comoment_eq, comoment_eq]
  simp only [sxy, sx, sy, List.map_map, Function.comp_def, List.length_map]
  rw [show (fun q => b q * a q) = fun q => a q * b q from funext fun q => mul_comm _ _]
  ring

/-- **Shifting leaves the co-moment alone**: `S` of `xᵢ − c` is `S` of `xᵢ`. -/
theorem comoment_shift (xs : List ℝ) (c : ℝ) :
    comoment (xs.map fun x => (x - c, x - c)) = comoment (dupL xs) := by
  have e : (xs.map fun x => (x - c, x - c)) = xs.map fun x => (x + (-c), x + (-c)) := by
    simp [sub_eq_add_neg]
  rw [e, comoment_map_add xs (fun x => x) (fun x => x) (fun _ => -c) (fun _ => -c),
    comoment_const_right, comoment_swap xs (fun x => x) (fun _ => -c), comoment_const_right,
    comoment_const_right]
  simp [dupL]

/-- **Moving each value moves `S` by little**: by `eᵢ`, at most
`2 √S √(Σ e²) + Σ e²`, `S` the co-moment of the `aᵢ`. -/
theorem comoment_perturb {α : Type*} (qs : List α) (a e : α → ℝ) :
    |comoment (qs.map fun q => (a q + e q, a q + e q)) - comoment (qs.map fun q => (a q, a q))|
      ≤ 2 * √(comoment (qs.map fun q => (a q, a q))) * √((qs.map fun q => e q ^ 2).sum)
        + (qs.map fun q => e q ^ 2).sum := by
  rw [comoment_map_add, comoment_swap qs a e]
  have h1 := abs_comoment_le_S qs a e
  have ee : comoment (qs.map fun q => (e q, e q)) = comoment (dupL (qs.map e)) := by
    simp [dupL, List.map_map, Function.comp_def]
  have h2 := comoment_dupL_nonneg (qs.map e)
  have h3 := comoment_dupL_le (qs.map e)
  simp only [List.map_map, Function.comp_def] at h3
  rw [← ee] at h2 h3
  have := abs_le.mp h1
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The rounding errors, as arithmetic -/

/-- `4 n t r ≤ D + 4 n³ t²` where `r² = n D`. -/
theorem four_ntr_le {n t r D : ℝ} (hn : 0 < n) (hr2 : r ^ 2 = n * D) :
    4 * n * t * r ≤ D + 4 * n ^ 3 * t ^ 2 := by
  have h := sq_nonneg (r - 2 * n ^ 2 * t)
  have : n * (4 * n * t * r) ≤ n * (D + 4 * n ^ 3 * t ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left this hn

/-- The common smallness facts: `n u ≤ 2⁻²¹`, `n t ≤ 2⁻⁹⁸⁰`. -/
structure TbScale (n u t : ℝ) : Prop where
  hn1 : 1 ≤ n
  hnN : n ≤ 2 ^ 32
  hu : 0 < u
  hu1 : u ≤ 1 / 2 ^ 53
  ht : 0 ≤ t
  ht1 : t ≤ 1 / 2 ^ 1022

theorem TbScale.nu {n u t : ℝ} (S : TbScale n u t) : n * u ≤ 1 / 2 ^ 21 := by
  calc n * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul S.hnN S.hu1 S.hu.le (by norm_num)
    _ = 1 / 2 ^ 21 := by norm_num

theorem TbScale.nt {n u t : ℝ} (S : TbScale n u t) : n * t ≤ 1 / 2 ^ 990 := by
  calc n * t ≤ 2 ^ 32 * (1 / 2 ^ 1022) := mul_le_mul S.hnN S.ht1 S.ht (by norm_num)
    _ = 1 / 2 ^ 990 := by norm_num

/-- The sum of the rounded squares, `A`, against `D = Σ d²`. -/
theorem tb_EA {n u t D Qs A : ℝ} (S : TbScale n u t)
    (hQs : |Qs - D| ≤ u * (D + n * t)) (hA : |A - Qs| ≤ 2 * n * u * (Qs + n * t)) :
    |A - D| ≤ (2 * n + 1) * u * D + 2 * n * u ^ 2 * D + 4 * n ^ 2 * u * t := by
  have hu0 := S.hu.le
  have hn0 : 0 ≤ n := by linarith [S.hn1]
  have hQsle : Qs ≤ (1 + u) * D + n * u * t := by linarith [(abs_le.mp hQs).2]
  have h1 : 2 * n * u * (Qs + n * t) ≤ 2 * n * u * ((1 + u) * D + n * u * t + n * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 2 * n * u * (n * u * t) ≤ n ^ 2 * u * t := by
    have e : 2 * n * u * (n * u * t) = (n ^ 2 * u * t) * (2 * u) := by ring
    rw [e]
    exact mul_le_of_le_one_right (by have := S.ht; positivity) (by linarith [S.hu1])
  have h3 : u * (n * t) ≤ n ^ 2 * u * t := by
    have : n ≤ n ^ 2 := by nlinarith [S.hn1]
    have e : n ^ 2 * u * t = u * (n ^ 2 * t) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this S.ht) hu0
  have htri : |A - D| ≤ |A - Qs| + |Qs - D| := abs_sub_le A Qs D
  have e1 : 2 * n * u * ((1 + u) * D + n * u * t + n * t)
      = 2 * n * u * D + 2 * n * u ^ 2 * D + 2 * n * u * (n * u * t) + 2 * (n ^ 2 * u * t) := by ring
  have e2 : u * (D + n * t) = u * D + u * (n * t) := by ring
  have e3 : (2 * n + 1) * u * D = 2 * n * u * D + u * D := by ring
  linarith

/-- `X = δ (2|T| + δ) / n`, `δ = 2 n u (r + n t)` the error of the sum `T`. -/
theorem tb_X {n u t D r T : ℝ} (S : TbScale n u t)
    (hr2 : r ^ 2 = n * D) (hT : |T| ≤ r) :
    2 * n * u * (r + n * t) * (2 * |T| + 2 * n * u * (r + n * t)) / n
      ≤ 4 * u * |T| * r + u * D + 8 * n ^ 2 * u ^ 2 * D + 2 * n ^ 2 * u * t := by
  have hn0 : 0 < n := by linarith [S.hn1]
  have hu0 := S.hu.le
  have ht := S.ht
  have hnt := S.nt
  have e : 2 * n * u * (r + n * t) * (2 * |T| + 2 * n * u * (r + n * t)) / n
      = 4 * u * |T| * r + u * (4 * n * t * |T|) + 4 * n * u ^ 2 * (r + n * t) ^ 2 := by
    field_simp; ring
  rw [e]
  have h1 : 4 * n * t * |T| ≤ D + 4 * n ^ 3 * t ^ 2 := by
    have := four_ntr_le (t := t) hn0 hr2
    have : 4 * n * t * |T| ≤ 4 * n * t * r := mul_le_mul_of_nonneg_left hT (by positivity)
    linarith
  have h2 : (r + n * t) ^ 2 ≤ 2 * (n * D) + 2 * (n * t) ^ 2 := by
    nlinarith [sq_nonneg (r - n * t)]
  have h4 : 4 * n * u ^ 2 * (r + n * t) ^ 2 ≤ 4 * n * u ^ 2 * (2 * (n * D) + 2 * (n * t) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hP : 0 ≤ n ^ 2 * u * t := by positivity
  have h5 : 8 * n * u ^ 2 * (n * t) ^ 2 ≤ n ^ 2 * u * t := by
    have e2 : 8 * n * u ^ 2 * (n * t) ^ 2 = (n ^ 2 * u * t) * (8 * (n * u) * t) := by ring
    rw [e2]; apply mul_le_of_le_one_right hP
    have : (n * u) * t ≤ (1 / 2 ^ 21) * (1 / 2 ^ 1022) := mul_le_mul S.nu S.ht1 ht (by norm_num)
    have : (1 / 2 ^ 21 : ℝ) * (1 / 2 ^ 1022) ≤ 1 / 8 := by norm_num
    linarith
  have h6 : u * (4 * n ^ 3 * t ^ 2) ≤ n ^ 2 * u * t := by
    have e2 : u * (4 * n ^ 3 * t ^ 2) = (n ^ 2 * u * t) * (4 * (n * t)) := by ring
    rw [e2]; apply mul_le_of_le_one_right hP; linarith
  have h7 : u * (4 * n * t * |T|) ≤ u * (D + 4 * n ^ 3 * t ^ 2) := mul_le_mul_of_nonneg_left h1 hu0
  have e3 : 4 * n * u ^ 2 * (2 * (n * D) + 2 * (n * t) ^ 2)
      = 8 * n ^ 2 * u ^ 2 * D + 8 * n * u ^ 2 * (n * t) ^ 2 := by ring
  have e4 : u * (D + 4 * n ^ 3 * t ^ 2) = u * D + u * (4 * n ^ 3 * t ^ 2) := by ring
  linarith

/-- `F = fl(fl(B · B) / n)` against `T² / n`. -/
theorem tb_EF {n u t D T B G F X : ℝ} (S : TbScale n u t)
    (hBBT : |B * B - T ^ 2| ≤ n * X) (hTn : T ^ 2 / n ≤ D)
    (hG : |G - B * B| ≤ u * (B * B + t)) (hF : |F - G / n| ≤ u * (|G / n| + t)) :
    |F - T ^ 2 / n| ≤ (2 * u + u ^ 2) * (D + X) + 3 * u * t + X := by
  have hn0 : 0 < n := by linarith [S.hn1]
  have hu0 := S.hu.le
  have ht := S.ht
  have hBB0 : 0 ≤ B * B := mul_self_nonneg B
  have hBn : B * B / n ≤ D + X := by
    rw [div_le_iff₀ hn0]
    have := (abs_le.mp hBBT).2
    have := (div_le_iff₀ hn0).mp hTn
    linarith
  have hBn0 : 0 ≤ B * B / n := by positivity
  have h1 : |G / n - B * B / n| ≤ u * (B * B / n) + u * t := by
    rw [← sub_div, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    have : u * t ≤ u * t * n := le_mul_of_one_le_right (by positivity) S.hn1
    have e : (u * (B * B / n) + u * t) * n = u * (B * B) + u * t * n := by field_simp
    rw [e]; linarith
  have h2 : |B * B / n - T ^ 2 / n| ≤ X := by
    rw [← sub_div, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]; linarith
  have hGn : |G / n| ≤ (1 + u) * (B * B / n) + u * t := by
    have h3 := abs_sub_abs_le_abs_sub (G / n) (B * B / n)
    rw [abs_of_nonneg hBn0] at h3
    have e : (1 + u) * (B * B / n) = B * B / n + u * (B * B / n) := by ring
    linarith
  have hFG : |F - G / n| ≤ u * ((1 + u) * (B * B / n) + u * t + t) :=
    le_trans hF (mul_le_mul_of_nonneg_left (by linarith) hu0)
  have hut : u * (u * t) ≤ u * t := by
    have : u * t * u ≤ u * t * 1 := mul_le_mul_of_nonneg_left (by linarith [S.hu1]) (by positivity)
    nlinarith
  have hfin : |F - T ^ 2 / n| ≤ |F - G / n| + |G / n - B * B / n| + |B * B / n - T ^ 2 / n| := by
    have := abs_sub_le F (G / n) (T ^ 2 / n)
    have := abs_sub_le (G / n) (B * B / n) (T ^ 2 / n)
    linarith
  have hk : (2 * u + u ^ 2) * (B * B / n) ≤ (2 * u + u ^ 2) * (D + X) :=
    mul_le_mul_of_nonneg_left hBn (by positivity)
  have e : u * ((1 + u) * (B * B / n) + u * t + t)
      = (u + u ^ 2) * (B * B / n) + u * (u * t) + u * t := by ring
  have e2 : (2 * u + u ^ 2) * (B * B / n) = (u + u ^ 2) * (B * B / n) + u * (B * B / n) := by ring
  linarith

/-- The higher-order terms of `tb_arith`, collected: with `Y = u |T| r`,
`Z = n² u² D`, `P = n² u t`, the errors `ea` of `A` and `ef` of `F` and the
last rounding give `(2n + 6) u D + 6Y + 64Z + 64P`. -/
theorem tb_collect {n u t D Y X ea ef rr : ℝ} (S : TbScale n u t) (hD : 0 ≤ D) (hY0 : 0 ≤ Y)
    (hX0 : 0 ≤ X)
    (hXb : X ≤ 4 * Y + u * D + 8 * (n ^ 2 * u ^ 2 * D) + 2 * (n ^ 2 * u * t))
    (hEA : ea ≤ (2 * n + 1) * u * D + 2 * n * u ^ 2 * D + 4 * n ^ 2 * u * t)
    (hEF : ef ≤ (2 * u + u ^ 2) * (D + X) + 3 * u * t + X)
    (hfin : rr ≤ u * (D + ea + ef + t) + ea + ef) :
    rr ≤ (2 * n + 6) * u * D + 6 * Y + 64 * (n ^ 2 * u ^ 2 * D) + 64 * (n ^ 2 * u * t) := by
  have hu0 := S.hu.le
  have ht := S.ht
  have hu53 := S.hu1
  have hn2 : n ≤ n ^ 2 := by nlinarith [S.hn1]
  have hn21 : (1 : ℝ) ≤ n ^ 2 := by nlinarith [S.hn1]
  set Z := n ^ 2 * u ^ 2 * D with hZdef
  set P := n ^ 2 * u * t with hPdef
  have hZ0 : 0 ≤ Z := by positivity
  have hP0 : 0 ≤ P := by positivity
  have huD : 0 ≤ u * D := by positivity
  have hu2D : u ^ 2 * D ≤ Z := by
    calc u ^ 2 * D = 1 * (u ^ 2 * D) := by ring
      _ ≤ n ^ 2 * (u ^ 2 * D) := mul_le_mul_of_nonneg_right hn21 (by positivity)
      _ = Z := by rw [hZdef]; ring
  have hnu2D : n * u ^ 2 * D ≤ Z := by
    calc n * u ^ 2 * D = n * (u ^ 2 * D) := by ring
      _ ≤ n ^ 2 * (u ^ 2 * D) := mul_le_mul_of_nonneg_right hn2 (by positivity)
      _ = Z := by rw [hZdef]; ring
  have hut : u * t ≤ P := by
    calc u * t = 1 * (u * t) := by ring
      _ ≤ n ^ 2 * (u * t) := mul_le_mul_of_nonneg_right hn21 (by positivity)
      _ = P := by rw [hPdef]; ring
  have e4P : 4 * n ^ 2 * u * t = 4 * P := by rw [hPdef]; ring
  -- `ef ≤ 4uD + 5Y + 12Z + 6P`
  have hEF' : ef ≤ 4 * u * D + 5 * Y + 12 * Z + 6 * P := by
    have hc : 2 * u + u ^ 2 ≤ 3 * u := by
      have : u * u ≤ u * 1 := mul_le_mul_of_nonneg_left (by linarith) hu0
      nlinarith
    have h1 : (2 * u + u ^ 2) * (D + X) ≤ 3 * u * (D + X) :=
      mul_le_mul_of_nonneg_right hc (by linarith)
    have h2 : 3 * u * X ≤ 3 * u * (4 * Y + u * D + 8 * Z + 2 * P) :=
      mul_le_mul_of_nonneg_left hXb (by linarith)
    have h3 : 3 * u * (4 * Y) ≤ Y := by
      rw [show 3 * u * (4 * Y) = (12 * u) * Y by ring]
      exact mul_le_of_le_one_left hY0 (by linarith)
    have h4 : 3 * u * (u * D) = 3 * (u ^ 2 * D) := by ring
    have h5 : 3 * u * (8 * Z) ≤ Z := by
      rw [show 3 * u * (8 * Z) = (24 * u) * Z by ring]
      exact mul_le_of_le_one_left hZ0 (by linarith)
    have h6 : 3 * u * (2 * P) ≤ P := by
      rw [show 3 * u * (2 * P) = (6 * u) * P by ring]
      exact mul_le_of_le_one_left hP0 (by linarith)
    have e1 : 3 * u * (D + X) = 3 * u * D + 3 * u * X := by ring
    have e2 : 3 * u * (4 * Y + u * D + 8 * Z + 2 * P)
        = 3 * u * (4 * Y) + 3 * u * (u * D) + 3 * u * (8 * Z) + 3 * u * (2 * P) := by ring
    linarith only [hEF, h1, h2, h3, h4, h5, h6, e1, e2, hXb, hu2D, hut]
  -- `ea ≤ (2n + 1) u D + 2Z + 4P`
  have hEA' : ea ≤ (2 * n + 1) * u * D + 2 * Z + 4 * P := by
    have : 2 * n * u ^ 2 * D = 2 * (n * u ^ 2 * D) := by ring
    linarith only [hEA, hnu2D, this, e4P]
  -- the last rounding
  have hlast : u * (D + ea + ef + t) ≤ u * D + Y + 8 * Z + 2 * P := by
    have h1 : u * ea ≤ u * ((2 * n + 1) * u * D + 2 * Z + 4 * P) :=
      mul_le_mul_of_nonneg_left hEA' hu0
    have h2 : u * ef ≤ u * (4 * u * D + 5 * Y + 12 * Z + 6 * P) :=
      mul_le_mul_of_nonneg_left hEF' hu0
    have e1 : u * ((2 * n + 1) * u * D + 2 * Z + 4 * P)
        = 2 * (n * u ^ 2 * D) + u ^ 2 * D + 2 * u * Z + 4 * u * P := by ring
    have e2 : u * (4 * u * D + 5 * Y + 12 * Z + 6 * P)
        = 4 * (u ^ 2 * D) + 5 * u * Y + 12 * u * Z + 6 * u * P := by ring
    have k1 : 5 * u * Y ≤ Y := by
      rw [show 5 * u * Y = (5 * u) * Y by ring]
      exact mul_le_of_le_one_left hY0 (by linarith)
    have k2 : 2 * u * Z + 12 * u * Z ≤ Z := by
      rw [show 2 * u * Z + 12 * u * Z = (14 * u) * Z by ring]
      exact mul_le_of_le_one_left hZ0 (by linarith)
    have k3 : 4 * u * P + 6 * u * P ≤ P := by
      rw [show 4 * u * P + 6 * u * P = (10 * u) * P by ring]
      exact mul_le_of_le_one_left hP0 (by linarith)
    have e3 : u * (D + ea + ef + t) = u * D + u * ea + u * ef + u * t := by ring
    linarith only [h1, h2, e1, e2, k1, k2, k3, e3, hnu2D, hu2D, hut]
  have e : (2 * n + 6) * u * D = (2 * n + 1) * u * D + 5 * (u * D) := by ring
  linarith only [hfin, hlast, hEA', hEF', e, hZ0, hP0]

/-- The textbook formula's rounding errors, put together: the bounds of each
step (`A` the sum of the rounded squares `Qs`, `B` the sum of the values `T`,
`G = fl(B · B)`, `F = fl(G / n)`, `R = fl(A − F)`) give
`|R − C| ≤ (2n + 6) u D + 6 u |T| r + 64 n² u² D + 64 n² u t`
for `C = D − T² / n`, `r = √(n D)`. -/
theorem tb_arith {n u t D r T Qs A B G F R : ℝ} (S : TbScale n u t) (hD : 0 ≤ D)
    (hr : 0 ≤ r) (hr2 : r ^ 2 = n * D) (hT : |T| ≤ r)
    (hQs : |Qs - D| ≤ u * (D + n * t))
    (hA : |A - Qs| ≤ 2 * n * u * (Qs + n * t))
    (hB : |B - T| ≤ 2 * n * u * (r + n * t))
    (hG : |G - B * B| ≤ u * (B * B + t))
    (hF : |F - G / n| ≤ u * (|G / n| + t))
    (hR : |R - (A - F)| ≤ u * (|A - F| + t)) :
    |R - (D - T ^ 2 / n)|
      ≤ (2 * n + 6) * u * D + 6 * u * |T| * r + 64 * n ^ 2 * u ^ 2 * D + 64 * n ^ 2 * u * t := by
  have hn0 : 0 < n := by linarith [S.hn1]
  have hu0 := S.hu.le
  have ht := S.ht
  have hTa := abs_nonneg T
  have hT2 : T ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ hTa hT 2
  have hTn : T ^ 2 / n ≤ D := by rw [div_le_iff₀ hn0]; linarith
  have hTn0 : 0 ≤ T ^ 2 / n := by positivity
  have EA := tb_EA S hQs hA
  set δ := 2 * n * u * (r + n * t) with hδ
  have hδ0 : 0 ≤ δ := by have := S.hn1; positivity
  set X := δ * (2 * |T| + δ) / n with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXb := tb_X S hr2 hT
  rw [← hδ, ← hXdef] at hXb
  have hBBT : |B * B - T ^ 2| ≤ n * X := by
    have e : B * B - T ^ 2 = (B - T) * ((B - T) + 2 * T) := by ring
    have h1 : |(B - T) + 2 * T| ≤ δ + 2 * |T| := by
      calc |(B - T) + 2 * T| ≤ |B - T| + |2 * T| := abs_add_le _ _
        _ ≤ δ + 2 * |T| := by rw [abs_mul, abs_two]; linarith
    have e2 : n * X = δ * (2 * |T| + δ) := by rw [hXdef]; field_simp
    rw [e, abs_mul, e2]
    calc |B - T| * |(B - T) + 2 * T| ≤ δ * (δ + 2 * |T|) :=
          mul_le_mul hB h1 (abs_nonneg _) hδ0
      _ = δ * (2 * |T| + δ) := by ring
  have EF := tb_EF S hBBT hTn hG hF
  have hAF : |A - F| ≤ D + |A - D| + |F - T ^ 2 / n| := by
    have := abs_sub_le A D (T ^ 2 / n)
    have := abs_sub_le (T ^ 2 / n) F (T ^ 2 / n)
    have h3 : |A - F| ≤ |A - T ^ 2 / n| + |T ^ 2 / n - F| := abs_sub_le A (T ^ 2 / n) F
    have h4 : |A - T ^ 2 / n| ≤ |A - D| + |D - T ^ 2 / n| := abs_sub_le A D (T ^ 2 / n)
    have h5 : |D - T ^ 2 / n| ≤ D := by rw [abs_le]; constructor <;> linarith
    rw [abs_sub_comm (T ^ 2 / n) F] at h3
    linarith
  have hfin : |R - (D - T ^ 2 / n)| ≤ |R - (A - F)| + |A - D| + |F - T ^ 2 / n| := by
    have h1 := abs_sub_le R (A - F) (D - T ^ 2 / n)
    have h2 : |(A - F) - (D - T ^ 2 / n)| ≤ |A - D| + |F - T ^ 2 / n| := by
      have e : (A - F) - (D - T ^ 2 / n) = (A - D) - (F - T ^ 2 / n) := by ring
      rw [e]; exact abs_sub _ _
    linarith
  have hRb : |R - (A - F)| ≤ u * (D + |A - D| + |F - T ^ 2 / n| + t) :=
    le_trans hR (mul_le_mul_of_nonneg_left (by linarith) hu0)
  have hc := tb_collect (Y := u * |T| * r) (ea := |A - D|) (ef := |F - T ^ 2 / n|)
    (rr := |R - (D - T ^ 2 / n)|) S hD (by positivity) hX0
    (by linarith only [hXb]) EA EF (by linarith only [hfin, hRb])
  linarith only [hc]

/-! ## The textbook formula on doubles, its sums in any order -/

/-- `|Σ x| ≤ Σ |x|`. -/
theorem abs_listSum_le (l : List ℝ) : |l.sum| ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact le_trans (abs_add_le _ _) (by linarith)

/-- `mag` is `Σ |x| + n · tiny`. -/
theorem mag_split (l : List ℝ) : mag l = (l.map abs).sum + l.length * tiny := by
  induction l with
  | nil => simp [mag]
  | cons x l ih =>
    simp only [mag, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Termwise errors `|f x − g x| ≤ c (g x + t)` add up. -/
theorem sum_err {α : Type*} (l : List α) (f g : α → ℝ) {c t : ℝ}
    (h : ∀ x ∈ l, |f x - g x| ≤ c * (g x + t)) :
    |(l.map f).sum - (l.map g).sum| ≤ c * ((l.map g).sum + l.length * t) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    have e : f x + (l.map f).sum - (g x + (l.map g).sum)
        = (f x - g x) + ((l.map f).sum - (l.map g).sum) := by ring
    rw [e]
    have e2 : c * (g x + (l.map g).sum + ((l.length + 1 : ℕ) : ℝ) * t)
        = c * (g x + t) + c * ((l.map g).sum + l.length * t) := by push_cast; ring
    rw [e2]
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

variable (M : StdModel)

/-- **The textbook formula on doubles, its sums in any order the engines
use** (`StdModel.Summed`): `fl(A − fl(fl(B · B) / n))`, `A` a sum of the
rounded squares and `B` a sum of the values, is within
`(2n + 6) u D + 6 u |T| √(n D) + 64 n² u² D + 64 n² u · tiny` of their
co-moment, `D = Σ d²`, `T = Σ d`. -/
theorem StdModel.textbook_summed {ds : List ℝ} (hne : ds ≠ []) (hN : ds.length ≤ 2 ^ 32)
    (hfix : ∀ d ∈ ds, M.fl d = d) (hb : ∀ d ∈ ds, |d| ≤ 2 ^ 400) {A B : ℝ}
    (hA : M.Summed (ds.map fun d => M.fl (d * d)) A) (hB : M.Summed ds B) :
    |M.fl (A - M.fl (M.fl (B * B) / ds.length)) - comoment (dupL ds)|
      ≤ (2 * ds.length + 6) * u * (ds.map (· ^ 2)).sum
        + 6 * u * |ds.sum| * √(ds.length * (ds.map (· ^ 2)).sum)
        + 64 * ds.length ^ 2 * u ^ 2 * (ds.map (· ^ 2)).sum + 64 * ds.length ^ 2 * u * tiny := by
  obtain ⟨hu, hu1, ht, -, hmax⟩ := fpFacts
  have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set n : ℕ := ds.length with hn_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hnN : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have S : TbScale n u tiny := ⟨hn1, hnN, hu, hu1, ht.le, ht1⟩
  have hnu := S.nu
  set D := (ds.map (· ^ 2)).sum with hD_def
  set T := ds.sum with hT_def
  have hD0 : 0 ≤ D := List.sum_nonneg (fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hDb : D ≤ 2 ^ 832 := by
    have h1 : ∀ y ∈ ds.map (· ^ 2), y ≤ (2 : ℝ) ^ 800 := by
      intro y hy; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      have := hb d hd
      calc d ^ 2 = |d| ^ 2 := (sq_abs d).symm
        _ ≤ (2 ^ 400) ^ 2 := pow_le_pow_left₀ (abs_nonneg d) this 2
        _ = 2 ^ 800 := by norm_num
    have := List.sum_le_length_nsmul _ _ h1
    rw [List.length_map, nsmul_eq_mul] at this
    calc D ≤ n * 2 ^ 800 := this
      _ ≤ 2 ^ 32 * 2 ^ 800 := by gcongr
      _ = 2 ^ 832 := by norm_num
  set r := √(n * D) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = n * D := Real.sq_sqrt (by positivity)
  -- `|T| ≤ Σ |d| ≤ r`
  have hPa := sq_abs_sum_le ds
  rw [← hn_def, ← hD_def] at hPa
  have hPa0 : 0 ≤ (ds.map abs).sum := List.sum_nonneg (fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hPr : (ds.map abs).sum ≤ r := by
    rw [hr_def, ← Real.sqrt_sq hPa0]; exact Real.sqrt_le_sqrt hPa
  have hT : |T| ≤ r := le_trans (abs_listSum_le ds) hPr
  have hrb : r ≤ 2 ^ 432 := by
    rw [hr_def, show (2 : ℝ) ^ 432 = √((2 ^ 432) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    calc (n : ℝ) * D ≤ 2 ^ 32 * 2 ^ 832 := mul_le_mul hnN hDb hD0 (by norm_num)
      _ = (2 ^ 432) ^ 2 := by norm_num
  -- the rounded squares
  set qs := ds.map fun d => M.fl (d * d) with hqs
  set Qs := qs.sum with hQs_def
  have hsq : ∀ d ∈ ds, |M.fl (d * d) - d ^ 2| ≤ u * (d ^ 2 + tiny) := by
    intro d hd
    have hdd : |d * d| ≤ maxFinite := by
      rw [abs_mul]
      have := hb d hd
      have : |d| * |d| ≤ 2 ^ 400 * 2 ^ 400 := mul_le_mul this this (abs_nonneg _) (by norm_num)
      have : (2 : ℝ) ^ 400 * 2 ^ 400 ≤ 2 ^ 1023 := by norm_num
      linarith
    have := M.err (d * d) hdd
    rw [abs_mul_self] at this
    rw [show d * d = d ^ 2 by ring] at this ⊢
    exact this
  have hQs : |Qs - D| ≤ u * (D + n * tiny) := by
    have := sum_err ds (fun d => M.fl (d * d)) (fun d => d ^ 2) hsq
    simpa [hQs_def, hqs, hD_def] using this
  have hq0 : ∀ q ∈ qs, 0 ≤ q := by
    intro q hq; obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq; exact M.nonneg _ (mul_self_nonneg d)
  have hQs0 : 0 ≤ Qs := List.sum_nonneg hq0
  have hQsb : Qs ≤ 2 ^ 834 := by
    have := (abs_le.mp hQs).2
    have hnt1 : (n : ℝ) * tiny ≤ 1 := by have := S.nt; linarith
    have : u * (D + n * tiny) ≤ 1 * (D + n * tiny) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have : (2 : ℝ) * 2 ^ 832 + 1 ≤ 2 ^ 834 := by norm_num
    linarith
  have hgam : gamma n ≤ 2 * n * u := gamma_le_two (by linarith)
  have hA' : |A - Qs| ≤ 2 * n * u * (Qs + n * tiny) := by
    have hlen : qs.length = n := by simp [hqs, hn_def]
    have hmag : mag qs = Qs + n * tiny := by
      rw [mag_split, hlen]
      congr 1
      rw [hQs_def]; congr 1
      exact List.map_congr_left (fun q hq => abs_of_nonneg (hq0 q hq)) |>.trans (List.map_id' qs)
    have h := StdModel.Summed.near M hA (fun q hq => by
        obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq; exact M.idem _)
      (by rw [hlen]; exact hnN) (by
        rw [hmag]
        have : (n : ℝ) * tiny ≤ 1 := by have := S.nt; linarith
        have : (2 : ℝ) * (2 ^ 834 + 1) ≤ 2 ^ 1023 := by norm_num
        linarith)
    rw [hmag, hlen] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hgam (by have := S.nt; positivity))
  have hB' : |B - T| ≤ 2 * n * u * (r + n * tiny) := by
    have h := StdModel.Summed.near M hB hfix hnN (by
      rw [mag_split]
      have : (n : ℝ) * tiny ≤ 1 := by have := S.nt; linarith
      have : (2 : ℝ) * (2 ^ 432 + 1) ≤ 2 ^ 1023 := by norm_num
      rw [← hn_def]; linarith)
    rw [mag_split, ← hn_def] at h
    refine le_trans h ?_
    exact mul_le_mul hgam (by linarith) (by positivity) (by positivity)
  -- the products and the quotient
  have hBb : |B| ≤ 2 ^ 433 := by
    have := abs_sub_abs_le_abs_sub B T
    have : 2 * n * u * (r + n * tiny) ≤ 2 ^ 432 := by
      have := S.nt
      have h1 : 2 * n * u ≤ 1 / 2 ^ 20 := by linarith
      have h2 : r + n * tiny ≤ 2 ^ 432 + 1 := by linarith
      have := mul_le_mul h1 h2 (by positivity) (by norm_num)
      have : (1 / 2 ^ 20 : ℝ) * (2 ^ 432 + 1) ≤ 2 ^ 432 := by norm_num
      linarith
    have : (2 : ℝ) ^ 432 + 2 ^ 432 = 2 ^ 433 := by norm_num
    linarith
  have hBB : |B * B| ≤ maxFinite := by
    rw [abs_mul]
    have : |B| * |B| ≤ 2 ^ 433 * 2 ^ 433 := mul_le_mul hBb hBb (abs_nonneg _) (by norm_num)
    have : (2 : ℝ) ^ 433 * 2 ^ 433 ≤ 2 ^ 1023 := by norm_num
    linarith
  have hG := M.err (B * B) hBB
  rw [abs_mul_self] at hG
  set G := M.fl (B * B) with hG_def
  have hGb : |G| ≤ 2 ^ 868 := by
    have := abs_sub_abs_le_abs_sub G (B * B)
    rw [abs_mul_self] at this
    have : B * B ≤ 2 ^ 866 := by
      rw [← abs_mul_self, abs_mul]
      calc |B| * |B| ≤ 2 ^ 433 * 2 ^ 433 := mul_le_mul hBb hBb (abs_nonneg _) (by norm_num)
        _ = 2 ^ 866 := by norm_num
    have : u * (B * B + tiny) ≤ B * B + 1 := by nlinarith [mul_self_nonneg B]
    have : (2 : ℝ) * 2 ^ 866 + 1 ≤ 2 ^ 868 := by norm_num
    linarith
  have hGn : |G / n| ≤ maxFinite := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n)]
    have : |G| / n ≤ |G| := div_le_self (abs_nonneg _) hn1
    have : (2 : ℝ) ^ 868 ≤ 2 ^ 1023 := by norm_num
    linarith
  have hF := M.err (G / n) hGn
  set F := M.fl (G / n) with hF_def
  have hAF : |A - F| ≤ maxFinite := by
    have hAb : |A| ≤ 2 ^ 836 := by
      have := abs_sub_abs_le_abs_sub A Qs
      rw [abs_of_nonneg hQs0] at this
      have : 2 * n * u * (Qs + n * tiny) ≤ Qs + 1 := by
        have := S.nt
        have h1 : 2 * n * u ≤ 1 := by linarith
        have h2 : 2 * n * u * (Qs + n * tiny) ≤ Qs + n * tiny :=
          mul_le_of_le_one_left (by positivity) h1
        linarith
      have : (2 : ℝ) * 2 ^ 834 + 1 ≤ 2 ^ 836 := by norm_num
      linarith
    have hFb : |F| ≤ 2 ^ 1000 := by
      have h1 := abs_sub_abs_le_abs_sub F (G / n)
      have h2 : |G / n| ≤ 2 ^ 868 := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n)]
        exact le_trans (div_le_self (abs_nonneg _) hn1) hGb
      have h3 : u * (|G / n| + tiny) ≤ 1 * (|G / n| + tiny) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have : tiny ≤ 1 := by linarith
      have : (2 : ℝ) * 2 ^ 868 + 1 ≤ 2 ^ 1000 := by norm_num
      linarith
    have := abs_sub A F
    have : (2 : ℝ) ^ 836 + 2 ^ 1000 ≤ 2 ^ 1023 := by norm_num
    linarith
  have hR := M.err (A - F) hAF
  have hC : comoment (dupL ds) = D - T ^ 2 / n := by
    rw [comoment_eq]
    simp [sxy, sx, sy, dupL, List.map_map, Function.comp_def, sq, hD_def, hT_def, hn_def]
  rw [hC]
  have := tb_arith S hD0 hr0 hr2 hT hQs hA' hB' hG hF hR
  convert this using 2

/-- The constants of `corrTwoPass_error`, from `textbook_summed` on the
shifted doubles (`D ≤ (1 + u)² W`, `|T| ≤ K + u ρ`, `√(n D) ≤ (1 + u) ρ`,
`ρ² = n W`) and the shift's own rounding (`2 u W + u² W`). -/
theorem ct_arith {n u t W K ρ D T sD e1 e2 : ℝ} (S : TbScale n u t) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hρ : 0 ≤ ρ) (hρ2 : ρ ^ 2 = n * W) (hDW : D ≤ (1 + u) ^ 2 * W)
    (hT : |T| ≤ K + u * ρ) (hsD : sD ≤ (1 + u) * ρ) (hsD0 : 0 ≤ sD)
    (he1 : e1 ≤ (2 * n + 6) * u * D + 6 * u * |T| * sD + 64 * n ^ 2 * u ^ 2 * D
      + 64 * n ^ 2 * u * t)
    (he2 : e2 ≤ 2 * u * W + u ^ 2 * W) :
    e1 + e2 ≤ (2 * n + 9) * u * W + 7 * u * K * ρ + 128 * n ^ 2 * u ^ 2 * W
      + 64 * n ^ 2 * u * t := by
  have hu0 := S.hu.le
  have hu1 := S.hu1
  have hn1 := S.hn1
  have hn0 : 0 ≤ n := by linarith
  have h1u : (1 + u) ^ 2 ≤ 1 + 3 * u := by
    have : u * u ≤ u * 1 := mul_le_mul_of_nonneg_left (by linarith) hu0
    nlinarith
  have hDW' : D ≤ W + 3 * u * W := by
    have := mul_le_mul_of_nonneg_right h1u hW
    nlinarith
  -- `(2n + 6) u D`
  have k1 : (2 * n + 6) * u * D ≤ (2 * n + 6) * u * W + (6 * n + 18) * (u ^ 2 * W) := by
    have := mul_le_mul_of_nonneg_left hDW' (by positivity : (0 : ℝ) ≤ (2 * n + 6) * u)
    nlinarith
  -- `6 u |T| √(n D)`
  have k2 : 6 * u * |T| * sD ≤ 6 * u * (1 + u) * (K * ρ) + 6 * (1 + u) * (n * (u ^ 2 * W)) := by
    have hTs : |T| * sD ≤ (K + u * ρ) * ((1 + u) * ρ) :=
      mul_le_mul hT hsD hsD0 (by positivity)
    have e : (K + u * ρ) * ((1 + u) * ρ) = (1 + u) * (K * ρ) + (1 + u) * u * ρ ^ 2 := by ring
    rw [e, hρ2] at hTs
    have := mul_le_mul_of_nonneg_left hTs (by positivity : (0 : ℝ) ≤ 6 * u)
    nlinarith
  have k2' : 6 * u * (1 + u) * (K * ρ) ≤ 7 * u * K * ρ := by
    have : 6 * (1 + u) ≤ 7 := by linarith
    have hKρ : 0 ≤ u * (K * ρ) := by positivity
    nlinarith
  -- `64 n² u² D`
  have k3 : 64 * n ^ 2 * u ^ 2 * D ≤ 65 * (n ^ 2 * (u ^ 2 * W)) := by
    have h : D ≤ (1 + 3 * u) * W := by linarith
    have : 64 * (1 + 3 * u) ≤ 65 := by linarith
    have hZ : 0 ≤ n ^ 2 * (u ^ 2 * W) := by positivity
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 64 * n ^ 2 * u ^ 2)
    nlinarith
  -- every `u² W` term below `n² u² W`
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn21 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
  have hZ0 : 0 ≤ u ^ 2 * W := by positivity
  have z1 : (6 * n + 18) * (u ^ 2 * W) ≤ 24 * (n ^ 2 * (u ^ 2 * W)) := by
    have : 6 * n + 18 ≤ 24 * n ^ 2 := by nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right this hZ0) (by rw [mul_assoc])
  have z2 : 6 * (1 + u) * (n * (u ^ 2 * W)) ≤ 7 * (n ^ 2 * (u ^ 2 * W)) := by
    have : 6 * (1 + u) * n ≤ 7 * n ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hZ0
    nlinarith
  have z3 : u ^ 2 * W ≤ n ^ 2 * (u ^ 2 * W) := le_mul_of_one_le_left hZ0 hn21
  have e3 : 128 * n ^ 2 * u ^ 2 * W = 128 * (n ^ 2 * (u ^ 2 * W)) := by ring
  have e4 : (2 * n + 9) * u * W = (2 * n + 6) * u * W + 3 * (u * W) := by ring
  have huW : 0 ≤ u * W := by positivity
  have e5 : 2 * u * W = 2 * (u * W) := by ring
  rw [e3, e4]
  linarith

/-- **The corrected two-pass formula on shifted doubles, its sums in any
order** (#1810): for doubles `xᵢ` and a shift `c` (Snowflake's writer takes
the group's mean), `dᵢ = fl(xᵢ − c)`, `A` any sum the engines use of the
`fl(dᵢ²)` and `B` of the `dᵢ`, `fl(A − fl(fl(B · B) / n))` is within
`(2n + 9) u W + 7 u K √(n W) + 128 n² u² W + 64 n² u · tiny` of the exact
co-moment `S` of the `xᵢ`, where `W = Σ (|xᵢ − c| + tiny)²` and
`K = |Σ (xᵢ − c)|`. Without the underflow terms `W` is `S + K² / n`
(`sum_sq_shift`), and `K` is `n` times the shift's distance to the exact
mean, so for the computed mean the bound is `(2n + 9) u S` to first order. -/
theorem StdModel.corrTwoPass_error {xs : List ℝ} (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32)
    (hb : ∀ x ∈ xs, |x| ≤ 2 ^ 398) {c : ℝ}
    (hc : |c| ≤ 2 ^ 398) {A B : ℝ}
    (hA : M.Summed ((xs.map fun x => M.fl (x - c)).map fun d => M.fl (d * d)) A)
    (hB : M.Summed (xs.map fun x => M.fl (x - c)) B) :
    |M.fl (A - M.fl (M.fl (B * B) / xs.length)) - comoment (dupL xs)|
      ≤ (2 * xs.length + 9) * u * (xs.map fun x => (|x - c| + tiny) ^ 2).sum
        + 7 * u * |(xs.map fun x => x - c).sum|
          * √(xs.length * (xs.map fun x => (|x - c| + tiny) ^ 2).sum)
        + 128 * xs.length ^ 2 * u ^ 2 * (xs.map fun x => (|x - c| + tiny) ^ 2).sum
        + 64 * xs.length ^ 2 * u * tiny := by
  obtain ⟨hu, hu1, ht, -, hmax⟩ := fpFacts
  have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set n : ℕ := xs.length with hn_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hnN : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have S : TbScale n u tiny := ⟨hn1, hnN, hu, hu1, ht.le, ht1⟩
  set ds := xs.map fun x => M.fl (x - c) with hds
  have hlen : ds.length = n := by simp [hds, hn_def]
  have hxc : ∀ x ∈ xs, |x - c| ≤ 2 ^ 399 := by
    intro x hx
    have := abs_sub x c
    have := hb x hx
    have : (2 : ℝ) ^ 398 + 2 ^ 398 = 2 ^ 399 := by norm_num
    linarith
  have hη : ∀ x ∈ xs, |M.fl (x - c) - (x - c)| ≤ u * (|x - c| + tiny) := by
    intro x hx
    have := hxc x hx
    exact M.err _ (by have : (2 : ℝ) ^ 399 ≤ 2 ^ 1023 := by norm_num
                      linarith)
  have hdx : ∀ x ∈ xs, |M.fl (x - c)| ≤ (1 + u) * (|x - c| + tiny) := by
    intro x hx
    have h1 := abs_sub_abs_le_abs_sub (M.fl (x - c)) (x - c)
    have h2 := hη x hx
    nlinarith [abs_nonneg (x - c)]
  have hdb : ∀ d ∈ ds, |d| ≤ 2 ^ 400 := by
    intro d hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    have h1 := hdx x hx
    have h2 := hxc x hx
    have : (1 + u) * (|x - c| + tiny) ≤ (1 + 1 / 2 ^ 53) * (2 ^ 399 + 1 / 2 ^ 1022) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    have : (1 + 1 / 2 ^ 53 : ℝ) * (2 ^ 399 + 1 / 2 ^ 1022) ≤ 2 ^ 400 := by norm_num
    linarith
  have hdfix : ∀ d ∈ ds, M.fl d = d := by
    intro d hd; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd; exact M.idem _
  have hne' : ds ≠ [] := by simpa [hds] using hne
  have tb := M.textbook_summed hne' (by rw [hlen]; exact hN) hdfix hdb hA hB
  rw [hlen] at tb
  -- the names of the bound
  set W := (xs.map fun x => (|x - c| + tiny) ^ 2).sum with hW_def
  set K := |(xs.map fun x => x - c).sum| with hK_def
  set ρ := √(n * W) with hρ_def
  set D := (ds.map (· ^ 2)).sum with hD_def
  set T := ds.sum with hT_def
  have hW0 : 0 ≤ W := List.sum_nonneg (fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = n * W := Real.sq_sqrt (by positivity)
  -- `D ≤ (1 + u)² W`
  have hDW : D ≤ (1 + u) ^ 2 * W := by
    rw [hD_def, hds, List.map_map, hW_def, ← List.sum_map_mul_left]
    apply List.sum_le_sum
    intro x hx
    simp only [Function.comp_apply]
    have h := hdx x hx
    calc M.fl (x - c) ^ 2 = |M.fl (x - c)| ^ 2 := (sq_abs _).symm
      _ ≤ ((1 + u) * (|x - c| + tiny)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (1 + u) ^ 2 * (|x - c| + tiny) ^ 2 := by ring
  -- `Σ (|x − c| + tiny) ≤ ρ`
  have hsumρ : (xs.map fun x => |x - c| + tiny).sum ≤ ρ := by
    have h := sq_abs_sum_le (xs.map fun x => |x - c| + tiny)
    have e1 : ((xs.map fun x => |x - c| + tiny).map abs) = xs.map fun x => |x - c| + tiny := by
      rw [List.map_map]; apply List.map_congr_left; intro x _
      simp only [Function.comp_apply]; exact abs_of_nonneg (by positivity)
    have e2 : ((xs.map fun x => |x - c| + tiny).map (· ^ 2)) = xs.map fun x => (|x - c| + tiny) ^ 2 := by
      rw [List.map_map]; rfl
    rw [e1, e2, List.length_map, ← hn_def, ← hW_def] at h
    have h0 : 0 ≤ (xs.map fun x => |x - c| + tiny).sum := List.sum_nonneg (fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
    rw [hρ_def, ← Real.sqrt_sq h0]; exact Real.sqrt_le_sqrt h
  -- `|T| ≤ K + u ρ`
  have hT : |T| ≤ K + u * ρ := by
    have e : T = (xs.map fun x => x - c).sum + (xs.map fun x => M.fl (x - c) - (x - c)).sum := by
      rw [hT_def, hds, ← List.sum_map_add]; congr 1; apply List.map_congr_left; intro x _; ring
    have h1 := abs_listSum_le (xs.map fun x => M.fl (x - c) - (x - c))
    have h2 : ((xs.map fun x => M.fl (x - c) - (x - c)).map abs).sum
        ≤ (xs.map fun x => u * (|x - c| + tiny)).sum := by
      rw [List.map_map]; apply List.sum_le_sum; intro x hx; exact hη x hx
    rw [List.sum_map_mul_left] at h2
    have h3 : u * (xs.map fun x => |x - c| + tiny).sum ≤ u * ρ :=
      mul_le_mul_of_nonneg_left hsumρ hu.le
    rw [e]
    exact le_trans (abs_add_le _ _) (by rw [← hK_def]; linarith)
  -- `√(n D) ≤ (1 + u) ρ`
  have hsD : √(n * D) ≤ (1 + u) * ρ := by
    have h : (n : ℝ) * D ≤ (1 + u) ^ 2 * (n * W) := by
      have := mul_le_mul_of_nonneg_left hDW (by positivity : (0 : ℝ) ≤ n)
      linarith
    calc √(n * D) ≤ √((1 + u) ^ 2 * (n * W)) := Real.sqrt_le_sqrt h
      _ = (1 + u) * ρ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the shift's own rounding moves `S` by at most `2 u W + u² W`
  set H := (xs.map fun x => (M.fl (x - c) - (x - c)) ^ 2).sum with hH_def
  have hH : H ≤ u ^ 2 * W := by
    rw [hH_def, hW_def, ← List.sum_map_mul_left]
    apply List.sum_le_sum; intro x hx
    have h := hη x hx
    calc (M.fl (x - c) - (x - c)) ^ 2 = |M.fl (x - c) - (x - c)| ^ 2 := (sq_abs _).symm
      _ ≤ (u * (|x - c| + tiny)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = u ^ 2 * (|x - c| + tiny) ^ 2 := by ring
  set Sx := comoment (dupL xs) with hSx_def
  have hSc : comoment (xs.map fun x => (x - c, x - c)) = Sx := comoment_shift xs c
  have hSW : Sx ≤ W := by
    have h := comoment_dupL_le (xs.map fun x => x - c)
    have e : dupL (xs.map fun x => x - c) = xs.map fun x => (x - c, x - c) := by
      simp [dupL, List.map_map, Function.comp_def]
    rw [e, hSc] at h
    refine le_trans h ?_
    rw [List.map_map, hW_def]; apply List.sum_le_sum; intro x _
    simp only [Function.comp_apply]
    have := abs_nonneg (x - c)
    calc (x - c) ^ 2 = |x - c| ^ 2 := (sq_abs _).symm
      _ ≤ (|x - c| + tiny) ^ 2 := pow_le_pow_left₀ this (by linarith) 2
  have hS0 : 0 ≤ Sx := comoment_dupL_nonneg xs
  have hpert : |comoment (dupL ds) - Sx| ≤ 2 * u * W + u ^ 2 * W := by
    have h := comoment_perturb xs (fun x => x - c) (fun x => M.fl (x - c) - (x - c))
    have e : (xs.map fun x => ((x - c) + (M.fl (x - c) - (x - c)),
        (x - c) + (M.fl (x - c) - (x - c)))) = dupL ds := by
      simp only [dupL, hds, List.map_map]; apply List.map_congr_left; intro x _
      simp only [Function.comp_apply]; ring_nf
    rw [e, hSc, ← hH_def] at h
    refine le_trans h ?_
    have h1 : √Sx ≤ √W := Real.sqrt_le_sqrt hSW
    have h2 : √H ≤ u * √W := by
      calc √H ≤ √(u ^ 2 * W) := Real.sqrt_le_sqrt hH
        _ = u * √W := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu.le]
    have h3 : √Sx * √H ≤ √W * (u * √W) :=
      mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h4 : √W * (u * √W) = u * W := by
      rw [mul_left_comm, Real.mul_self_sqrt hW0]
    nlinarith
  -- together
  have htri : |M.fl (A - M.fl (M.fl (B * B) / n)) - Sx|
      ≤ |M.fl (A - M.fl (M.fl (B * B) / n)) - comoment (dupL ds)| + |comoment (dupL ds) - Sx| :=
    abs_sub_le _ _ _
  have hK0 : 0 ≤ K := abs_nonneg _
  have := ct_arith S hW0 hK0 hρ0 hρ2 hDW hT hsD (Real.sqrt_nonneg _) tb hpert
  linarith

end FloatBounds

end
