module

public import FloatBounds.MergeRel
public import FloatBounds.CoreKappa
public import FloatBounds.Tree

/-!
# DuckDB's statistical aggregates meet `StatProps` (#444)

DuckDB computes `VAR_*`, `STDDEV_*` with Welford's update in each thread and
Chan's merge of the threads' states (duckdb-var-stddev), modelled as
`StdModel.vEval` of a `VPlan`. `chanVar_rel` bounds its co-moment. What
`StatProps` (`SubstraitLean/StatProps.lean`) also asks is that the variance
is `≥ 0`, which Welford's update keeps only because rounding is monotone:
the new mean lies between the old one and the value, so `(x − m)` and
`(x − m')` have one sign. The standard model does not say rounding is
monotone; IEEE 754's rounding to nearest is (`StdModel.Mono`).

* `StdModel.vEval_nonneg`: with `Mono` and `Grid`, the co-moment of every
  plan is `≥ 0`;
* `StdModel.core_var_chan`: `fl(M₂ / d)` is `≥ 0` and within `varTol` of
  `S / d`, the property `varOf_props` states of the reference's two-pass
  (`core_var_k`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- What IEEE 754 rounding to nearest does beyond the standard model:
rounding is monotone. -/
structure StdModel.Mono (M : StdModel) : Prop where
  mono : ∀ a b, a ≤ b → M.fl a ≤ M.fl b

theorem eta_pos : 0 < eta := by unfold eta; positivity

theorem u_tiny_eq : u * tiny = eta / 2 := by
  rw [u_val]; unfold tiny eta; norm_num

/-- A multiple of `2⁻¹⁰⁷⁴` below another plus `2⁻¹⁰⁷⁴` is at most it. -/
theorem OnGrid.le_of_lt_add {a b : ℝ} (ha : OnGrid a) (hb : OnGrid b) (h : a < b + eta) :
    a ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have he := eta_pos
  have h1 : ((m : ℝ) - n - 1) * eta < 0 := by nlinarith
  have h2 : (m : ℝ) - n - 1 < 0 := by
    by_contra hc; push_neg at hc; nlinarith
  have h3 : m ≤ n := by
    have : (m : ℝ) < n + 1 := by linarith
    have : m < n + 1 := by exact_mod_cast this
    omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h3) he.le

variable (M : StdModel)

/-- **Welford's new mean lies between the old one and the value**, for a
count `k ≥ 1`: the step `fl(fl(x − m) / (k + 1))` is at most `x − m` in
magnitude, by the grid. -/
theorem StdModel.welford_between (hg : M.Grid) (hmo : M.Mono) {m x : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hmg : OnGrid m) (hxg : OnGrid x) (hmf : M.fl m = m) (hxf : M.fl x = x)
    (hbig : |x - m| ≤ 2 ^ 1000) :
    (m ≤ x → m ≤ M.fl (m + M.fl (M.fl (x - m) / ((k : ℝ) + 1))) ∧
        M.fl (m + M.fl (M.fl (x - m) / ((k : ℝ) + 1))) ≤ x) ∧
      (x ≤ m → x ≤ M.fl (m + M.fl (M.fl (x - m) / ((k : ℝ) + 1))) ∧
        M.fl (m + M.fl (M.fl (x - m) / ((k : ℝ) + 1))) ≤ m) := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hmax : (2 : ℝ) ^ 1000 ≤ maxFinite := two_pow_le_maxFinite
  have hk1 : (2 : ℝ) ≤ (k : ℝ) + 1 := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk; linarith
  have hgxm : OnGrid (x - m) := by rw [sub_eq_add_neg]; exact hxg.add hmg.neg
  have hd := hg.rel (x - m) hgxm (le_trans hbig hmax)
  set d := M.fl (x - m) with hd_def
  set t := d / ((k : ℝ) + 1) with ht_def
  have hdabs : |d| ≤ (1 + u) * |x - m| := by
    have := abs_sub_abs_le_abs_sub d (x - m); nlinarith [abs_nonneg (x - m)]
  have htabs : |t| ≤ |d| / 2 := by
    rw [ht_def, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (k : ℝ) + 1)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hk1
  have htM : |t| ≤ maxFinite := by nlinarith [abs_nonneg (x - m)]
  have hq := M.err t htM
  set q := M.fl t with hq_def
  have hqg : OnGrid q := hg.on_grid t
  have hqabs : |q| ≤ |t| * (1 + u) + u * tiny := by
    have := abs_sub_abs_le_abs_sub q t; nlinarith [abs_nonneg t]
  -- `|q| < |x − m| + η`, so `|q| ≤ |x − m|` on the grid
  have hlt : |q| < |x - m| + eta := by
    rw [u_tiny_eq] at hqabs
    have he := eta_pos
    have : |t| * (1 + u) ≤ |x - m| := by
      have h1 : |t| ≤ (1 + u) * |x - m| / 2 := by linarith
      have h2 : (1 + u) * (1 + u) ≤ 2 := by nlinarith
      nlinarith [abs_nonneg (x - m), abs_nonneg t]
    linarith
  constructor
  · intro hmx
    have hxm0 : 0 ≤ x - m := by linarith
    have hd0 : 0 ≤ d := M.nonneg _ hxm0
    have ht0 : 0 ≤ t := div_nonneg hd0 (by linarith)
    have hq0 : 0 ≤ q := M.nonneg _ ht0
    rw [abs_of_nonneg hq0, abs_of_nonneg hxm0] at hlt
    have hqle : q ≤ x - m := OnGrid.le_of_lt_add hqg hgxm hlt
    constructor
    · have := hmo.mono m (m + q) (by linarith); rwa [hmf] at this
    · have := hmo.mono (m + q) x (by linarith); rwa [hxf] at this
  · intro hxm
    have hxm0 : x - m ≤ 0 := by linarith
    have hd0 : d ≤ 0 := M.nonpos _ hxm0
    have ht0 : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg hd0 (by linarith)
    have hq0 : q ≤ 0 := M.nonpos _ ht0
    rw [abs_of_nonpos hq0, abs_of_nonpos hxm0] at hlt
    have hqle : -q ≤ -(x - m) := OnGrid.le_of_lt_add hqg.neg hgxm.neg hlt
    constructor
    · have := hmo.mono x (m + q) (by linarith); rwa [hxf] at this
    · have := hmo.mono (m + q) m (by linarith); rwa [hmf] at this

/-- The invariant of Welford's states: the count, a mean that is a double
between the values' bounds, a co-moment `≥ 0`. -/
def WNon (M : StdModel) (B : ℝ) (n : ℕ) (s : ℕ × ℝ × ℝ) : Prop :=
  s.1 = n ∧ 0 ≤ s.2.2 ∧ OnGrid s.2.1 ∧ M.fl s.2.1 = s.2.1 ∧ |s.2.1| ≤ B ∧ (n = 0 → s.2.1 = 0)

/-- One step keeps the invariant. -/
theorem StdModel.wStep_non (hg : M.Grid) (hmo : M.Mono) {B : ℝ} (hB : B ≤ 2 ^ 998) {n : ℕ}
    {s : ℕ × ℝ × ℝ} (hs : WNon M B n s) {x : ℝ} (hxg : OnGrid x) (hxf : M.fl x = x)
    (hxB : |x| ≤ B) : WNon M B (n + 1) (M.wStep s x) := by
  obtain ⟨hn, h2, hmg, hmf, hmB, h0⟩ := hs
  obtain ⟨s1, m, S⟩ := s
  simp only at hn h2 hmg hmf hmB h0
  subst hn
  rcases Nat.eq_zero_or_pos s1 with rfl | hk
  · -- the first value: the mean is the value, the co-moment `0`
    have hm0 := h0 rfl
    subst hm0
    simp only [WNon, StdModel.wStep, sub_zero, Nat.cast_zero, zero_add, div_one, hxf, sub_self,
      M.zero, mul_zero]
    refine ⟨rfl, ?_, hxg, hxf, hxB, fun h => absurd h (by omega)⟩
    have := M.nonneg _ h2; simpa using this
  · have hbig : |x - m| ≤ 2 ^ 1000 := by
      have := abs_sub_le_add x m
      have : (2 : ℝ) * 2 ^ 998 ≤ 2 ^ 1000 := by norm_num
      linarith
    obtain ⟨hup, hdown⟩ := M.welford_between hg hmo hk hmg hxg hmf hxf hbig
    set m' := M.fl (m + M.fl (M.fl (x - m) / ((s1 : ℝ) + 1)))
    have hm'g : OnGrid m' := hg.on_grid _
    have hm'f : M.fl m' = m' := M.idem _
    -- the two differences have one sign, so their product is `≥ 0`
    have hprod : 0 ≤ M.fl (M.fl (x - m) * M.fl (x - m')) := by
      rcases le_total m x with hmx | hxm
      · obtain ⟨-, h2'⟩ := hup hmx
        exact M.nonneg _ (mul_nonneg (M.nonneg _ (by linarith)) (M.nonneg _ (by linarith)))
      · obtain ⟨h1', -⟩ := hdown hxm
        exact M.nonneg _ (mul_nonneg_of_nonpos_of_nonpos (M.nonpos _ (by linarith))
          (M.nonpos _ (by linarith)))
    have hm'B : |m'| ≤ B := by
      rcases le_total m x with hmx | hxm
      · obtain ⟨a, b⟩ := hup hmx
        rw [abs_le] at hmB hxB ⊢; constructor <;> linarith
      · obtain ⟨a, b⟩ := hdown hxm
        rw [abs_le] at hmB hxB ⊢; constructor <;> linarith
    refine ⟨rfl, M.nonneg _ (by linarith), hm'g, hm'f, hm'B, fun h => absurd h (by omega)⟩

theorem StdModel.foldl_wStep_non (hg : M.Grid) (hmo : M.Mono) {B : ℝ} (hB : B ≤ 2 ^ 998) :
    ∀ (xs : List ℝ) {n : ℕ} {s : ℕ × ℝ × ℝ}, WNon M B n s →
      (∀ x ∈ xs, OnGrid x ∧ M.fl x = x ∧ |x| ≤ B) →
      WNon M B (n + xs.length) (xs.foldl M.wStep s)
  | [], _, _, hs, _ => by simpa using hs
  | x :: xs, n, s, hs, hx => by
    obtain ⟨hxg, hxf, hxB⟩ := hx x (by simp)
    have := StdModel.foldl_wStep_non hg hmo hB xs (M.wStep_non hg hmo hB hs hxg hxf hxB)
      (fun y hy => hx y (by simp [hy]))
    simp only [List.foldl_cons, List.length_cons]
    rwa [show n + (xs.length + 1) = n + 1 + xs.length by omega]

/-- **Every plan's co-moment is `≥ 0`.** -/
theorem StdModel.vEval_nonneg (hg : M.Grid) (hmo : M.Mono) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : B ≤ 2 ^ 998) :
    ∀ p : VPlan, (∀ x ∈ p.vals, OnGrid x ∧ M.fl x = x ∧ |x| ≤ B) → 0 ≤ (M.vEval p).2.2
  | .leaf xs, hx => by
    have h0 : WNon M B 0 (0, 0, 0) :=
      ⟨rfl, le_rfl, ⟨0, by simp⟩, M.zero, by simpa using hB0, fun _ => rfl⟩
    simp only [StdModel.vEval, StdModel.wState]
    exact (M.foldl_wStep_non hg hmo hB xs h0 (fun x h => hx x (by simpa [VPlan.vals] using h))).2.1
  | .merge t s, hx => by
    have ht := StdModel.vEval_nonneg hg hmo hB0 hB t (fun x h => hx x (by simp [VPlan.vals, h]))
    have hs := StdModel.vEval_nonneg hg hmo hB0 hB s (fun x h => hx x (by simp [VPlan.vals, h]))
    simp only [StdModel.vEval, StdModel.dMerge]
    split
    · exact hs
    split
    · exact ht
    dsimp only
    apply M.nonneg
    refine add_nonneg (M.nonneg _ (by linarith)) (M.nonneg _ (div_nonneg ?_ (by positivity)))
    refine M.nonneg _ (mul_nonneg (M.nonneg _ (mul_nonneg (M.nonneg _ ?_) (by positivity)))
      (by positivity))
    exact mul_self_nonneg _

/-- **DuckDB's `VAR_*`** (`varOf_props` of the reference, for DuckDB's
algorithm): `fl(M₂ / d)` is `≥ 0` and within `varTol` of `S / d`, for every
`r ≥ √(Q' S)`. -/
theorem StdModel.core_var_chan (hg : M.Grid) (hmo : M.Mono) (p : VPlan) (hne : p.vals ≠ [])
    (hN : p.vals.length ≤ 2 ^ 32) (hB : ∀ x ∈ p.vals, |x| ≤ 2 ^ 398)
    (hx : ∀ x ∈ p.vals, OnGrid x ∧ M.fl x = x) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ p.vals.length)
    {r : ℝ} (hr : √((p.vals.map fun x => (|x| + tiny) ^ 2).sum) * √(comoment (dupL p.vals)) ≤ r) :
    0 ≤ M.fl ((M.vEval p).2.2 / d) ∧
      |M.fl ((M.vEval p).2.2 / d) - comoment (dupL p.vals) / d|
        ≤ varTol p.vals.length d r (p.vals.map fun x => (|x| + tiny) ^ 2).sum := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  set n : ℕ := p.vals.length with hn_def
  set Q := (p.vals.map fun x => (|x| + tiny) ^ 2).sum with hQ_def
  set S := comoment (dupL p.vals) with hS_def
  obtain ⟨hS0, hSQ, hQbig⟩ := SQ_facts (qs := p.vals) (fun x => x) hN hB
  have hdup : (p.vals.map fun x => (x, x)) = dupL p.vals := rfl
  rw [hdup] at hS0 hSQ
  have hQ0 : 0 ≤ Q := le_trans hS0 hSQ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hnN : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  -- the co-moment's error
  have hE := M.chanVar_rel p hne hN (fun x h => le_trans (hB x h) (by norm_num))
    (fun x h => (hx x h).2)
  rw [Real.sqrt_mul hQ0] at hE
  set R := √Q * √S with hR_def
  have hR0 : 0 ≤ R := by positivity
  have hRr : R ≤ r := hr
  have hsS : √S ≤ √Q := Real.sqrt_le_sqrt hSQ
  have hSR : S ≤ R := by
    have : √S * √S = S := Real.mul_self_sqrt hS0
    have := mul_le_mul_of_nonneg_right hsS (Real.sqrt_nonneg S)
    linarith
  have hRQ : R ≤ Q := by
    have : √Q * √Q = Q := Real.mul_self_sqrt hQ0
    have := mul_le_mul_of_nonneg_left hsS (Real.sqrt_nonneg Q)
    linarith
  set E := 148 * n * u * R + 3961 * n ^ 2 * u ^ 2 * Q + 793 * n * u * tiny with hE_def
  have hE0 : 0 ≤ E := by positivity
  -- far from overflow
  have hbig : R + E + n * tiny ≤ 2 ^ 999 := by
    have hnu : (n : ℝ) * u ≤ 1 / 2 ^ 21 := by
      calc (n : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul hnN hu1 hu.le (by norm_num)
        _ = 1 / 2 ^ 21 := by norm_num
    have htiny : tiny ≤ 1 := by unfold tiny; exact pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : 148 * n * u * R ≤ R := by nlinarith
    have h2 : 3961 * n ^ 2 * u ^ 2 * Q ≤ Q := by nlinarith
    have h3 : 793 * n * u * tiny ≤ 1 := by nlinarith
    have h4 : (n : ℝ) * tiny ≤ 2 ^ 32 := by nlinarith
    have : (2 : ℝ) ^ 830 * 3 + 1 + 2 ^ 32 ≤ 2 ^ 999 := by norm_num
    nlinarith
  have hdiv := M.div_kappa (C := S) (Ch := (M.vEval p).2.2) (E := E) (rs := R) (n := n) (d := d)
    hE (by rw [abs_of_nonneg hS0]; exact hSR) hE0 hR0 hn1 hd' hdn' hbig
  have hv0 : 0 ≤ (M.vEval p).2.2 :=
    M.vEval_nonneg hg hmo (B := 2 ^ 398) (by positivity) (by norm_num) p
      (fun x h => ⟨(hx x h).1, (hx x h).2, hB x h⟩)
  refine ⟨M.nonneg _ (div_nonneg hv0 (by linarith)), le_trans hdiv ?_⟩
  unfold varTol
  apply div_le_div_of_nonneg_right _ (by linarith)
  have hr0 : 0 ≤ r := le_trans hR0 hRr
  have hu3 : 3 * u ≤ 1 / 2 ^ 50 := by
    calc 3 * u ≤ 3 * (1 / 2 ^ 53) := by linarith
      _ ≤ 1 / 2 ^ 50 := by norm_num
  have a1 : 148 * n * u * R ≤ 148 * n * u * r := by gcongr
  have a2 : 3 * u * R ≤ 3 * n * u * r := by nlinarith
  have hnut : 0 ≤ (n : ℝ) * u * tiny := by positivity
  have a3 : (n : ℝ) * u * tiny ≤ n ^ 2 * u * tiny := by nlinarith
  have hEu : 3 * u * E ≤ 1 / 2 ^ 50 * E := mul_le_mul_of_nonneg_right hu3 hE0
  nlinarith

end FloatBounds

end
