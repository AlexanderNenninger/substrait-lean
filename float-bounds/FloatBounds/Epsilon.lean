module

public import FloatBounds.Kahan

/-!
# The `epsilon` of a contract (#444)

`substrait-check --contract` reports, per output column that is a double
`SUM` or `AVG`, how far an engine's result may be from one the reference
allows (`"epsilon"`, `SubstraitLean/Epsilon.lean`). This file proves those
bounds, for every summation order the engine profiles allow (`sum_order`):

| behaviour | algorithm | here |
|---|---|---|
| `SEQUENTIAL`, `ANY`, `PAIRWISE` | a tree of additions in any order (`FloatSums`) | `TreeSum.seq`, `TreeSum.split` |
| `SCALED_CONSTANT` | DuckDB's constant run, one `fl(k · x)` | `TreeSum.const` |
| `COMPENSATED` | Kahan's sum (Polars, in memory, by groups) | `Rnd.kahan` |

`StdModel.Summed` is all of them. Its results meet the sequential sum's
bound (`Summed.near`), so:

* `epsilon_sum`, `epsilon_avg` (`"abs"`): two results of `n ≤ N ≤ 2³²` doubles,
  decoded from codes of magnitude at most `Bs ≤ 2¹⁴⁷⁴` (scaled by `2¹⁰⁷⁴`), are
  within `2 · sumTolScaled N Bs` (`2 · avgTolScaled N Bs` for the means) of
  each other, scaled. The checker reports that number as a double, rounded
  up (`unscale`).
* `epsilon_sum_rel`, `epsilon_avg_rel` (`"rel"`): for values of one sign, the
  two results are within `2γ/(1 − γ)` of each other relative to either,
  `γ = γ n` for a sum and `γ (n + 2)` for a mean whose exact value is at
  least `tiny` in magnitude. These need IEEE's exact underflow of sums
  (`StdModel.Grid`), which the standard model leaves out.

Each takes the values as doubles: fixed by rounding, and for `rel` multiples
of `2⁻¹⁰⁷⁴`. That an engine's order is one of the table's is what its
characterization records (duckdb-sum-double, polars-sum-float,
polars-sum-float-streaming); Polars's `Float32` sums, in single precision,
are not covered.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

variable (M : StdModel)

/-- The doubles a `SUM` of `xs` gives under the `sum_order` behaviours the
engine profiles allow: a tree sum (`SEQUENTIAL`, `ANY`, `PAIRWISE`,
`SCALED_CONSTANT`) or Kahan's compensated sum of a permutation
(`COMPENSATED`). -/
def StdModel.Summed (xs : List ℝ) (s : ℝ) : Prop :=
  M.TreeSum xs s ∨ ∃ ws, ws.Perm xs ∧ s = M.toRnd.kahan ws

theorem gridRnd_mag (hg : M.Grid) (l : List ℝ) : (M.gridRnd hg).mag l = (l.map abs).sum := by
  simp [Rnd.mag, StdModel.gridRnd]

theorem mul_u_lt {m : ℕ} (hm : (m : ℝ) ≤ 2 ^ 34) : (m : ℝ) * u < 1 := by
  have hu := fpFacts.u_le
  have hu0 := u_pos
  have : (m : ℝ) * u ≤ 2 ^ 34 * (1 / 2 ^ 53) := mul_le_mul hm hu hu0.le (by norm_num)
  have : (2 : ℝ) ^ 34 * (1 / 2 ^ 53) < 1 := by norm_num
  linarith

theorem nu_lt {n : ℕ} (hn : (n : ℝ) ≤ 2 ^ 32) : ((2 * n : ℕ) : ℝ) * u < 1 := by
  have := Rnd.nu_small hn
  have := u_pos
  push_cast; nlinarith

/-- **Every order the engines use** is within `γ n · mag xs` of the exact sum. -/
theorem StdModel.Summed.near {xs : List ℝ} {s : ℝ} (h : M.Summed xs s)
    (hfix : ∀ x ∈ xs, M.fl x = x) (hn : (xs.length : ℝ) ≤ 2 ^ 32)
    (hov : 2 * mag xs ≤ maxFinite) : |s - xs.sum| ≤ gamma xs.length * mag xs := by
  have h2 := nu_lt hn
  have hu := u_pos
  have hn1 : (xs.length : ℝ) * u < 1 := by push_cast at h2; nlinarith
  rcases h with h | ⟨ws, hp, rfl⟩
  · have g := gamma_lt_one h2
    have := mag_nonneg xs
    exact h.error M hn1 (by nlinarith)
  · have := Rnd.kahan_near (R := M.toRnd) (xs := ws)
      (fun x hx => ⟨trivial, hfix x (hp.subset hx)⟩) (by rwa [hp.length_eq])
      (by rw [M.toRnd.mag_perm hp]; exact hov)
    exact (this.perm hp)

/-- **Every order the engines use, without the underflow term**: within
`γ n · Σ |xᵢ|` of the exact sum, where sums underflow exactly (`Grid`). -/
theorem StdModel.Summed.near_grid (hg : M.Grid) {xs : List ℝ} {s : ℝ} (h : M.Summed xs s)
    (hfix : ∀ x ∈ xs, M.fl x = x) (hgrid : ∀ x ∈ xs, OnGrid x)
    (hn : (xs.length : ℝ) ≤ 2 ^ 32) (hov : 2 * (xs.map abs).sum ≤ maxFinite) :
    |s - xs.sum| ≤ gamma xs.length * (xs.map abs).sum := by
  have h2 := nu_lt hn
  have hu := u_pos
  have hn1 : (xs.length : ℝ) * u < 1 := by push_cast at h2; nlinarith
  rcases h with h | ⟨ws, hp, rfl⟩
  · have g := gamma_lt_one h2
    have : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
    exact h.grid_error M hg hgrid hn1 (by nlinarith)
  · have := Rnd.kahan_near (R := M.gridRnd hg) (xs := ws)
      (fun x hx => ⟨hgrid x (hp.subset hx), hfix x (hp.subset hx)⟩) (by rwa [hp.length_eq])
      (by rw [gridRnd_mag, (hp.map abs).sum_eq]; exact hov)
    have := this.perm hp
    unfold Rnd.Near at this
    rwa [gridRnd_mag] at this

/-! ## Absolute: the codes' tolerances -/

/-- What the hypotheses on the codes give: the doubles are at most
`(1 + 2u) B` in magnitude, far from overflow, and within `2nuB` of the
codes' sum. -/
theorem decoded_facts {ps : List (ℝ × ℝ)} (hd : Decoded ps) {N Bs : ℕ} (hN : ps.length ≤ N)
    (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474) (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    mag (ps.map Prod.fst) ≤ ps.length * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) ∧
      2 * mag (ps.map Prod.fst) ≤ maxFinite ∧
      |(ps.map Prod.fst).sum - (ps.map Prod.snd).sum| ≤ 2 * ps.length * u * (Bs / 2 ^ 1074) := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  have hu' := u_val
  set B : ℝ := Bs / 2 ^ 1074 with hBdef
  have hB : ∀ p ∈ ps, |p.2| ≤ B := by
    intro p hp; rw [hBdef, le_div_iff₀ (by positivity)]; exact hb p hp
  have hB0 : 0 ≤ B := by positivity
  have hB400 : B ≤ 2 ^ 400 := by
    rw [hBdef, div_le_iff₀ (by positivity)]
    linarith [show (2 : ℝ) ^ 400 * 2 ^ 1074 = 2 ^ 1474 by norm_num]
  have hB' : ∀ x ∈ ps.map Prod.fst, |x| ≤ (1 + 2 * u) * B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have := hd p hp
    have := abs_sub_abs_le_abs_sub p.1 p.2
    have := hB p hp
    nlinarith [abs_nonneg p.2]
  have hmag := mag_le_of_bound hB'
  simp only [List.length_map] at hmag
  refine ⟨hmag, ?_, ?_⟩
  · have hl : (ps.length : ℝ) ≤ 2 ^ 32 := by
      have : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
      have : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN32
      linarith
    have h1 : (1 + 2 * u) * B + tiny ≤ 2 ^ 402 := by
      have : tiny ≤ 1 := by unfold tiny; norm_num
      have : 2 * u ≤ 1 := by rw [hu']; norm_num
      nlinarith
    have h2 : (ps.length : ℝ) * ((1 + 2 * u) * B + tiny) ≤ 2 ^ 32 * 2 ^ 402 :=
      mul_le_mul hl h1 (by positivity) (by norm_num)
    linarith [two_pow_le_maxFinite]
  · have h2 := abs_sum_map_sub_le Prod.fst Prod.snd (fun _ => (1 : ℝ)) (2 * u * B) ps (by
      intro p hp
      have h1 := hd p hp
      have h2 := hB p hp
      have : 2 * u * |p.2| ≤ 2 * u * B := by gcongr
      simpa using le_trans h1 this)
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at h2
    linarith

/-- **A `SUM` the engines give, against the codes**: within
`sumTolScaled N Bs / 2¹⁰⁷⁴` of the exact sum of the codes' values, as the
reference's sequential sum is (`core_sum`). -/
theorem StdModel.core_summed_sum {ps : List (ℝ × ℝ)} (hd : Decoded ps)
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s : ℝ} (hs : M.Summed (ps.map Prod.fst) s)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |s - (ps.map Prod.snd).sum| ≤ sumTolScaled N Bs / 2 ^ 1074 := by
  obtain ⟨hmag, hov, hdec⟩ := decoded_facts hd hN hN32 hBs hb
  have hl : ((ps.map Prod.fst).length : ℝ) ≤ 2 ^ 32 := by
    simp only [List.length_map]
    have : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN32
    linarith
  have hnear := hs.near M (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hfix p hp) hl hov
  simp only [List.length_map] at hnear
  have hg := gamma_nonneg (n := ps.length) (mul_u_lt (by simp at hl; linarith))
  have h1 := mul_le_mul_of_nonneg_left hmag hg
  have htol := sumTol_le (n := ps.length) (Bs := Bs) hN hN32
  calc _ = |(s - (ps.map Prod.fst).sum) + ((ps.map Prod.fst).sum - (ps.map Prod.snd).sum)| := by
        ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **`"abs"` of a `SUM`**: two results the engines' orders give for the same
doubles are within `2 · sumTolScaled N Bs / 2¹⁰⁷⁴`. -/
theorem StdModel.epsilon_sum {ps : List (ℝ × ℝ)} (hd : Decoded ps)
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s₁ s₂ : ℝ} (h₁ : M.Summed (ps.map Prod.fst) s₁)
    (h₂ : M.Summed (ps.map Prod.fst) s₂)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |s₁ - s₂| ≤ 2 * sumTolScaled N Bs / 2 ^ 1074 := by
  have a := M.core_summed_sum hd hfix h₁ hN hN32 hBs hb
  have b := M.core_summed_sum hd hfix h₂ hN hN32 hBs hb
  calc _ = |(s₁ - (ps.map Prod.snd).sum) - (s₂ - (ps.map Prod.snd).sum)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-- **An `AVG` the engines give, against the codes**: within
`avgTolScaled N Bs / 2¹⁰⁷⁴` of the exact mean of the codes' values. -/
theorem StdModel.core_summed_avg {ps : List (ℝ × ℝ)} (hd : Decoded ps) (hne : ps ≠ [])
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s : ℝ} (hs : M.Summed (ps.map Prod.fst) s)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |M.fl (s / ps.length) - (ps.map Prod.snd).sum / ps.length| ≤ avgTolScaled N Bs / 2 ^ 1074 := by
  obtain ⟨hu, -, ht, -, -⟩ := fpFacts
  obtain ⟨hmag, hov, hdec⟩ := decoded_facts hd hN hN32 hBs hb
  have hlN : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (N : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN32
  have hl : ((ps.map Prod.fst).length : ℝ) ≤ 2 ^ 32 := by simp only [List.length_map]; linarith
  have hnear := hs.near M (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact hfix p hp) hl hov
  simp only [List.length_map] at hnear
  have hl0 : (0 : ℝ) < ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn2 : ((ps.length + 2 : ℕ) : ℝ) * u < 1 :=
    mul_u_lt (by simp at hl; push_cast; linarith)
  have hn0 : (ps.length : ℝ) * u < 1 := mul_u_lt (by simp at hl; linarith)
  have g0 := gamma_nonneg hn0
  have g1 := gamma_lt_one (m := ps.length) (nu_lt (by simpa using hl))
  have hmag0 := mag_nonneg (ps.map Prod.fst)
  have hdiv := M.div_error (s := (ps.map Prod.fst).sum) (s' := s) (A := mag (ps.map Prod.fst))
    (j := ps.length) (n := ps.length) (List.length_pos_iff.mpr hne) (by simpa using hnear)
    (abs_sum_le_mag _) (by simpa using length_mul_tiny_le_mag (ps.map Prod.fst)) hn2
    (by nlinarith)
  have g2 := gamma_nonneg hn2
  have e1 : gamma (ps.length + 2) * mag (ps.map Prod.fst) / ps.length
      ≤ gamma (ps.length + 2) * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) := by
    rw [div_le_iff₀ hl0]
    have := mul_le_mul_of_nonneg_left hmag g2
    linarith [show gamma (ps.length + 2) * (ps.length * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny))
      = gamma (ps.length + 2) * ((1 + 2 * u) * (Bs / 2 ^ 1074) + tiny) * ps.length by ring]
  have e2 : |(ps.map Prod.fst).sum / ps.length - (ps.map Prod.snd).sum / ps.length|
      ≤ 2 * u * (Bs / 2 ^ 1074) := by
    rw [← sub_div, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; linarith
  have htol := avgTol_le (n := ps.length) (Bs := Bs) hN hN32
  calc _ = |(M.fl (s / ps.length) - (ps.map Prod.fst).sum / ps.length)
        + ((ps.map Prod.fst).sum / ps.length - (ps.map Prod.snd).sum / ps.length)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **`"abs"` of an `AVG`**: two means the engines' orders give for the same
doubles are within `2 · avgTolScaled N Bs / 2¹⁰⁷⁴`. -/
theorem StdModel.epsilon_avg {ps : List (ℝ × ℝ)} (hd : Decoded ps) (hne : ps ≠ [])
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s₁ s₂ : ℝ} (h₁ : M.Summed (ps.map Prod.fst) s₁)
    (h₂ : M.Summed (ps.map Prod.fst) s₂)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |M.fl (s₁ / ps.length) - M.fl (s₂ / ps.length)| ≤ 2 * avgTolScaled N Bs / 2 ^ 1074 := by
  have a := M.core_summed_avg hd hne hfix h₁ hN hN32 hBs hb
  have b := M.core_summed_avg hd hne hfix h₂ hN hN32 hBs hb
  set q := (ps.map Prod.snd).sum / ps.length
  calc _ = |(M.fl (s₁ / ps.length) - q) - (M.fl (s₂ / ps.length) - q)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-! ## Against the reference's correctly rounded sum (D25)

The reference's `SUM` of doubles is the exact sum of the values rounded once
(`floatSumCR`, `SubstraitLean/FloatExact.lean`), and its `AVG` the exact mean
rounded once (`floatAvgCR`). The core proves, on integers, that this value is
within `u` of the exact one relatively (`FloatCode.ofExact_rel`); here that is
the hypothesis `hr`. An engine's result is then within its order's bound of
the exact sum (`core_summed_sum`) plus `u` of it. -/

/-- The codes' values add up to at most `N · Bs / 2¹⁰⁷⁴` in magnitude. -/
theorem abs_snd_sum_le {ps : List (ℝ × ℝ)} {N Bs : ℕ} (hN : ps.length ≤ N)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |(ps.map Prod.snd).sum| ≤ N * (Bs / 2 ^ 1074) := by
  have hB : ∀ x ∈ (ps.map Prod.snd).map abs, x ≤ Bs / 2 ^ 1074 := by
    intro x hx
    simp only [List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [le_div_iff₀ (by positivity)]; exact hb p hp
  have h1 := Rnd.abs_sum_le_absSum (ps.map Prod.snd)
  have h2 := List.sum_le_length_nsmul _ _ hB
  simp only [List.length_map, nsmul_eq_mul] at h2
  have h3 : (ps.length : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : 0 ≤ (Bs : ℝ) / 2 ^ 1074 := by positivity
  nlinarith

/-- **`"abs"` of a `SUM` against the reference (D25)**: a result an engine's
order gives is within `sumTolScaled N Bs / 2¹⁰⁷⁴ + u · N · Bs / 2¹⁰⁷⁴` of any
`r` within `u` of the exact sum, relatively, which the correctly rounded sum
is (`FloatCode.ofExact_rel`). -/
theorem StdModel.epsilon_sum_cr {ps : List (ℝ × ℝ)} (hd : Decoded ps)
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s r : ℝ} (hs : M.Summed (ps.map Prod.fst) s)
    (hr : |r - (ps.map Prod.snd).sum| ≤ u * |(ps.map Prod.snd).sum|)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |s - r| ≤ sumTolScaled N Bs / 2 ^ 1074 + u * (N * (Bs / 2 ^ 1074)) := by
  have a := M.core_summed_sum hd hfix hs hN hN32 hBs hb
  have hz := abs_snd_sum_le hN hb
  have hz' := mul_le_mul_of_nonneg_left hz u_pos.le
  calc |s - r| = |(s - (ps.map Prod.snd).sum) - (r - (ps.map Prod.snd).sum)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-- **`"abs"` of an `AVG` against the reference (D25)**: a mean an engine's
order gives is within `avgTolScaled N Bs / 2¹⁰⁷⁴ + u · Bs / 2¹⁰⁷⁴` of any `r`
within `u` of the exact mean, relatively, which `floatAvgCR` is. -/
theorem StdModel.epsilon_avg_cr {ps : List (ℝ × ℝ)} (hd : Decoded ps) (hne : ps ≠ [])
    (hfix : ∀ p ∈ ps, M.fl p.1 = p.1) {s r : ℝ} (hs : M.Summed (ps.map Prod.fst) s)
    (hr : |r - (ps.map Prod.snd).sum / ps.length| ≤ u * |(ps.map Prod.snd).sum / ps.length|)
    {N Bs : ℕ} (hN : ps.length ≤ N) (hN32 : N ≤ 2 ^ 32) (hBs : (Bs : ℝ) ≤ 2 ^ 1474)
    (hb : ∀ p ∈ ps, |p.2| * 2 ^ 1074 ≤ Bs) :
    |M.fl (s / ps.length) - r| ≤ avgTolScaled N Bs / 2 ^ 1074 + u * (Bs / 2 ^ 1074) := by
  have a := M.core_summed_avg hd hne hfix hs hN hN32 hBs hb
  have hz := abs_snd_sum_le (N := ps.length) le_rfl hb
  have hl0 : (0 : ℝ) < ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hq : |(ps.map Prod.snd).sum / ps.length| ≤ Bs / 2 ^ 1074 := by
    rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; linarith
  have hq' := mul_le_mul_of_nonneg_left hq u_pos.le
  set q := (ps.map Prod.snd).sum / ps.length
  calc _ = |(M.fl (s / ps.length) - q) - (r - q)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-! ## Relative: values of one sign -/

theorem absSum_nonneg : ∀ {xs : List ℝ}, (∀ x ∈ xs, 0 ≤ x) → (xs.map abs).sum = xs.sum
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [abs_of_nonneg (h x (by simp)), absSum_nonneg (fun y hy => h y (by simp [hy]))]

theorem absSum_nonpos : ∀ {xs : List ℝ}, (∀ x ∈ xs, x ≤ 0) → (xs.map abs).sum = -xs.sum
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [abs_of_nonpos (h x (by simp)), absSum_nonpos (fun y hy => h y (by simp [hy]))]; ring

theorem absSum_of_one_sign {xs : List ℝ} (h : (∀ x ∈ xs, 0 ≤ x) ∨ (∀ x ∈ xs, x ≤ 0)) :
    (xs.map abs).sum = |xs.sum| := by
  have h0 : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
  rcases h with h | h
  · rw [absSum_nonneg h, abs_of_nonneg (List.sum_nonneg h)]
  · have e := absSum_nonpos h
    rw [e, abs_of_nonpos (by linarith)]

/-- Two values within `γ |S|` of `S`, `γ < 1`, are within `2γ/(1 − γ)` of
each other, relative to either. -/
theorem rel_of_near {a b S g : ℝ} (hg0 : 0 ≤ g) (hg : g < 1) (ha : |a - S| ≤ g * |S|)
    (hb : |b - S| ≤ g * |S|) : |a - b| ≤ 2 * g / (1 - g) * |b| := by
  have hS : (1 - g) * |S| ≤ |b| := by
    have := abs_sub_abs_le_abs_sub S b
    rw [abs_sub_comm] at hb
    nlinarith
  have hab : |a - b| ≤ 2 * g * |S| := by
    calc _ = |(a - S) - (b - S)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ _ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 2 * g)
  nlinarith

/-- **`"rel"` of a `SUM`**: for doubles of one sign, two results the engines'
orders give are within `2γ/(1 − γ)` of each other, relative to either,
`γ = γ n` (Higham, §4.2, without the underflow term). -/
theorem StdModel.epsilon_sum_rel (hg : M.Grid) {xs : List ℝ}
    (hfix : ∀ x ∈ xs, M.fl x = x) (hgrid : ∀ x ∈ xs, OnGrid x)
    (hsign : (∀ x ∈ xs, 0 ≤ x) ∨ (∀ x ∈ xs, x ≤ 0))
    (hn : (xs.length : ℝ) ≤ 2 ^ 32) (hov : 2 * (xs.map abs).sum ≤ maxFinite)
    {s₁ s₂ : ℝ} (h₁ : M.Summed xs s₁) (h₂ : M.Summed xs s₂) :
    |s₁ - s₂| ≤ 2 * gamma xs.length / (1 - gamma xs.length) * |s₂| := by
  have a := h₁.near_grid M hg hfix hgrid hn hov
  have b := h₂.near_grid M hg hfix hgrid hn hov
  rw [absSum_of_one_sign hsign] at a b
  have hn1 : (xs.length : ℝ) * u < 1 := mul_u_lt (by linarith)
  exact rel_of_near (gamma_nonneg hn1) (gamma_lt_one (nu_lt hn)) a b

/-- **`"rel"` of an `AVG`**: for doubles of one sign whose exact mean is at
least `tiny` in magnitude, two means the engines' orders give are within
`2γ/(1 − γ)` of each other, relative to either, `γ = γ (n + 2)`. -/
theorem StdModel.epsilon_avg_rel (hg : M.Grid) {xs : List ℝ} (hne : xs ≠ [])
    (hfix : ∀ x ∈ xs, M.fl x = x) (hgrid : ∀ x ∈ xs, OnGrid x)
    (hsign : (∀ x ∈ xs, 0 ≤ x) ∨ (∀ x ∈ xs, x ≤ 0))
    (htiny : tiny ≤ |xs.sum / xs.length|)
    (hn : (xs.length : ℝ) ≤ 2 ^ 32) (hov : 2 * (xs.map abs).sum ≤ maxFinite)
    {s₁ s₂ : ℝ} (h₁ : M.Summed xs s₁) (h₂ : M.Summed xs s₂) :
    |M.fl (s₁ / xs.length) - M.fl (s₂ / xs.length)|
      ≤ 2 * gamma (xs.length + 2) / (1 - gamma (xs.length + 2)) * |M.fl (s₂ / xs.length)| := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hl0 : (0 : ℝ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  set n := xs.length
  have hn2 : ((n + 2 : ℕ) : ℝ) * u < 1 := mul_u_lt (by push_cast; linarith)
  have hn1 : ((n + 1 : ℕ) : ℝ) * u < 1 := mul_u_lt (by push_cast; linarith)
  have hn0 : (n : ℝ) * u < 1 := mul_u_lt (by linarith)
  have g0 := gamma_nonneg hn0
  have g1 := gamma_nonneg hn1
  have s1 := gamma_succ hn1
  have s0 := gamma_succ (j := n + 1) (by push_cast at hn2 ⊢; linarith)
  have hn2' : ((2 * (n + 2) : ℕ) : ℝ) * u < 1 := mul_u_lt (by push_cast; linarith)
  have g2 := gamma_lt_one hn2'
  have g20 := gamma_nonneg hn2
  set q := xs.sum / n
  -- each mean within `γ (n + 2) |q|` of the exact one
  have mean : ∀ {s : ℝ}, M.Summed xs s → |M.fl (s / n) - q| ≤ gamma (n + 2) * |q| := by
    intro s h
    have e := h.near_grid M hg hfix hgrid hn hov
    rw [absSum_of_one_sign hsign] at e
    have ez : |s / n - q| ≤ gamma n * |q| := by
      rw [show q = xs.sum / n from rfl, ← sub_div, abs_div, abs_of_pos hl0, abs_div,
        abs_of_pos hl0, mul_div_assoc']
      gcongr
    have hz : |s / n| ≤ (1 + gamma n) * |q| := by
      have := abs_sub_abs_le_abs_sub (s / n) q; nlinarith
    have hzM : |s / n| ≤ maxFinite := by
      have : |q| ≤ (xs.map abs).sum := by
        rw [absSum_of_one_sign hsign, show q = xs.sum / n from rfl, abs_div, abs_of_pos hl0]
        exact div_le_self (abs_nonneg _) (by exact_mod_cast List.length_pos_iff.mpr hne)
      have := gamma_lt_one (nu_lt hn)
      nlinarith [abs_nonneg q]
    have hr := M.err (s / n) hzM
    have hq0 := abs_nonneg q
    calc _ = |(M.fl (s / n) - s / n) + (s / n - q)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ u * ((1 + gamma n) * |q| + |q|) + gamma n * |q| := by
          have := mul_le_mul_of_nonneg_left (add_le_add hz htiny) hu.le
          linarith
      _ = ((1 + gamma n) * (1 + u) - 1 + u) * |q| := by ring
      _ ≤ ((1 + gamma (n + 1)) * (1 + u) - 1) * |q| := by gcongr; nlinarith
      _ ≤ gamma (n + 2) * |q| := by gcongr; linarith
  exact rel_of_near g20 g2 (mean h₁) (mean h₂)

end FloatBounds

end

/-! The theorems the core's engine rows name (`floatBoundsTheorems` in
`SubstraitLean/EngineTables.lean`) are these. -/
open Lean in
run_cmd do
  for thm in ["FloatBounds.StdModel.epsilon_sum", "FloatBounds.StdModel.epsilon_avg",
      "FloatBounds.StdModel.epsilon_sum_rel", "FloatBounds.StdModel.epsilon_avg_rel",
      "FloatBounds.StdModel.epsilon_sum_cr", "FloatBounds.StdModel.epsilon_avg_cr",
      "FloatBounds.StdModel.TreeSum.sign", "FloatBounds.StdModel.TreeSum.avg_sign"] do
    unless (← getEnv).contains thm.toName do
      throwError "no theorem {thm}"
