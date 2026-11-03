module

public import FloatBounds.Variance
public import FloatBounds.Core

/-!
# The statistical aggregates the core trusted before the first-order bounds (#85)

`SubstraitLean/StatProps.lean` now states the bounds of `CoreKappa.lean`,
which scale with the spread of the values. The bounds below, in
`B = max |xᵢ|`, remain true and are what `CoreKappa.lean` builds on.

`SubstraitLean/StatProps.lean` states the generic properties of `VAR_*`,
`STDDEV_*`, `COVAR_*` and `CORR`, and three trusted facts that Lean's own
results have them (`varOf_props`, `covOf_props`, `corrOf_props`). This file
proves those facts for the standard model, over the reals, for the
algorithm Lean computes (two-pass, `twoPass_error`) on the doubles
`FloatCode.toFloat` decodes (`Decoded`):

* `core_var`: the variance, `fl(Ĉ / d)`, is `≥ 0` and within
  `E / d + 12 n u B² / d` of `C / d`, with `E = 128 n² u B²`;
* `core_stddev`: its rounded square root is within `(1 ± u)` of `√(V ± τ)`,
  squared so the core needs no square roots;
* `core_cov`: the covariance, within the same bound;
* `core_corr`: `|corr| ≤ 1 + 3E/L + 8u` when both sides' co-moments are at
  least `L ≥ 8E`.

`128 n² u B²` covers the two-pass bound `64 n² u B'²` for the decoded values
(`B' = (1 + 2u) B`) and the decoding itself (`comoment_decoded`). It also
covers Welford with Chan's merge (`plan_good`) and the textbook formula, so
the properties hold for DuckDB's results too.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- Doubles `(x', y')` and the values `(x, y)` they decode, each within `δ`. -/
def Near (δ : ℝ) (qs : List ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ δ ∧ |q.1.2 - q.2.2| ≤ δ

theorem abs_mx_sub_le {δ : ℝ} {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (h : Near δ qs) (hδ : 0 ≤ δ) :
    |mx (qs.map (·.1)) - mx (qs.map (·.2))| ≤ δ ∧ |my (qs.map (·.1)) - my (qs.map (·.2))| ≤ δ := by
  rcases Nat.eq_zero_or_pos qs.length with h0 | h0
  · simp [mx, my, h0, hδ]
  have hl : (0 : ℝ) < qs.length := by exact_mod_cast h0
  have key : ∀ f g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ, (∀ q ∈ qs, |f q - g q| ≤ δ) →
      |(qs.map f).sum / qs.length - (qs.map g).sum / qs.length| ≤ δ := by
    intro f g hfg
    rw [← sub_div, abs_div, abs_of_pos hl, div_le_iff₀ hl]
    have := abs_sum_map_sub_le f g (fun _ => (1 : ℝ)) δ qs (fun q hq => by simpa using hfg q hq)
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at this
    linarith
  constructor
  · have := key (fun q => q.1.1) (fun q => q.2.1) (fun q hq => (h q hq).1)
    simpa [mx, sx, List.map_map, Function.comp_def] using this
  · have := key (fun q => q.1.2) (fun q => q.2.2) (fun q hq => (h q hq).2)
    simpa [my, sy, List.map_map, Function.comp_def] using this

/-- **Decoding moves the co-moment by at most `12 n B δ`**, for values within
`B` and doubles within `δ ≤ B` of them. -/
theorem comoment_decoded {δ B : ℝ} {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (h : Near δ qs)
    (hB : ∀ q ∈ qs, |q.2.1| ≤ B ∧ |q.2.2| ≤ B) (hδ : 0 ≤ δ) (hδB : δ ≤ B) :
    |comoment (qs.map (·.1)) - comoment (qs.map (·.2))| ≤ 12 * qs.length * B * δ := by
  have hB0 : 0 ≤ B := le_trans hδ hδB
  obtain ⟨hmx, hmy⟩ := abs_mx_sub_le h hδ
  have hb2 : Bounded B (qs.map (·.2)) := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hB q hq
  have bx := abs_mx_le hb2 hB0
  have bY := abs_my_le hb2 hB0
  unfold comoment
  simp only [List.map_map]
  have := abs_sum_map_sub_le
    (fun q => (q.1.1 - mx (qs.map (·.1))) * (q.1.2 - my (qs.map (·.1))))
    (fun q => (q.2.1 - mx (qs.map (·.2))) * (q.2.2 - my (qs.map (·.2))))
    (fun _ => (1 : ℝ)) (12 * B * δ) qs (by
      intro q hq
      obtain ⟨h1, h2⟩ := h q hq
      obtain ⟨b1, b2⟩ := hB q hq
      have e1 : |(q.1.1 - mx (qs.map (·.1))) - (q.2.1 - mx (qs.map (·.2)))| ≤ 2 * δ := by
        have : (q.1.1 - mx (qs.map (·.1))) - (q.2.1 - mx (qs.map (·.2)))
            = (q.1.1 - q.2.1) - (mx (qs.map (·.1)) - mx (qs.map (·.2))) := by ring
        rw [this]; have := abs_sub (q.1.1 - q.2.1) (mx (qs.map (·.1)) - mx (qs.map (·.2)))
        linarith
      have e2 : |(q.1.2 - my (qs.map (·.1))) - (q.2.2 - my (qs.map (·.2)))| ≤ 2 * δ := by
        have : (q.1.2 - my (qs.map (·.1))) - (q.2.2 - my (qs.map (·.2)))
            = (q.1.2 - q.2.2) - (my (qs.map (·.1)) - my (qs.map (·.2))) := by ring
        rw [this]; have := abs_sub (q.1.2 - q.2.2) (my (qs.map (·.1)) - my (qs.map (·.2)))
        linarith
      have a1 : |q.2.1 - mx (qs.map (·.2))| ≤ 2 * B := by
        have := abs_sub q.2.1 (mx (qs.map (·.2))); linarith
      have a2 : |q.2.2 - my (qs.map (·.2))| ≤ 2 * B := by
        have := abs_sub q.2.2 (my (qs.map (·.2))); linarith
      have := abs_mul_sub_le e1 e2 a1 a2
      have : 2 * δ * (2 * B + 2 * δ) + 2 * B * (2 * δ) ≤ 12 * B * δ := by nlinarith
      simp only [mul_one]
      linarith)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at this
  simp only [Function.comp_def]
  linarith

variable (M : StdModel)

/-- Values within `B ≤ 2³⁹⁹`, decoded within `2u|x|`: `(x', x)` pairs as the
co-moment needs them. -/
noncomputable def dup (ps : List (ℝ × ℝ)) : List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ps.map fun p => ((p.1, p.1), (p.2, p.2))

/-- **The co-moment Lean computes, against the exact one**, for decoded
pairs: within `128 n² u B²`. -/
theorem StdModel.decoded_twoPass {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) {B : ℝ} (hB0 : (2 : ℝ)⁻¹ ^ 500 ≤ B) (hB1 : B ≤ 2 ^ 399)
    (hB : ∀ q ∈ qs, |q.2.1| ≤ B ∧ |q.2.2| ≤ B)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|) :
    |M.twoPass (qs.map (·.1)) - comoment (qs.map (·.2))| ≤ 128 * qs.length ^ 2 * u * B ^ 2 := by
  have hu := u_pos
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB0
  set B' := (1 + 2 * u) * B with hB'
  have hB'1 : B ≤ B' := by rw [hB']; nlinarith
  have S : Scale qs.length B' :=
    ⟨hN, le_trans hB0 hB'1, by rw [hB']; nlinarith [show (2 : ℝ) ^ 400 = 2 * 2 ^ 399 by norm_num]⟩
  have hb' : Bounded B' (qs.map (·.1)) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2⟩ := hd q hq
    obtain ⟨b1, b2⟩ := hB q hq
    constructor
    · have := abs_sub_abs_le_abs_sub q.1.1 q.2.1
      have : 2 * u * |q.2.1| ≤ 2 * u * B := by gcongr
      rw [hB']; linarith
    · have := abs_sub_abs_le_abs_sub q.1.2 q.2.2
      have : 2 * u * |q.2.2| ≤ 2 * u * B := by gcongr
      rw [hB']; linarith
  have h1 := M.twoPass_error S (ps := qs.map (·.1)) (by simpa using hne) (by simp) hb'
  simp only [List.length_map] at h1
  have hnear : Near (2 * u * B) qs := fun q hq =>
    ⟨le_trans (hd q hq).1 (by gcongr; exact (hB q hq).1),
     le_trans (hd q hq).2 (by gcongr; exact (hB q hq).2)⟩
  have h2 := comoment_decoded hnear hB (by positivity) (by nlinarith)
  have hn1 : (1 : ℝ) ≤ qs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hB'2 : B' ^ 2 ≤ (65 / 64) * B ^ 2 := by
    rw [hB']
    have : (1 + 2 * u) ^ 2 ≤ 65 / 64 := by nlinarith
    nlinarith [sq_nonneg B]
  have hw : 0 ≤ u * B ^ 2 := by positivity
  have e1 : 64 * (qs.length : ℝ) ^ 2 * u * B' ^ 2 ≤ 65 * qs.length ^ 2 * u * B ^ 2 := by
    have := mul_le_mul_of_nonneg_left hB'2 (by positivity : (0 : ℝ) ≤ 64 * qs.length ^ 2 * u)
    nlinarith
  have e2 : 12 * (qs.length : ℝ) * B * (2 * u * B) ≤ 24 * qs.length ^ 2 * u * B ^ 2 := by
    have : (qs.length : ℝ) ≤ qs.length ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hw
    nlinarith
  calc _ = |(M.twoPass (qs.map (·.1)) - comoment (qs.map (·.1)))
        + (comoment (qs.map (·.1)) - comoment (qs.map (·.2)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 64 * (qs.length : ℝ) ^ 2 * u * B' ^ 2 + 12 * qs.length * B * (2 * u * B) :=
      add_le_add h1 h2
    _ ≤ _ := by nlinarith

theorem StdModel.twoPass_dup_nonneg (ps : List (ℝ × ℝ)) :
    0 ≤ M.twoPass (ps.map fun p => (p.1, p.1)) := by
  have hm : M.mean ((ps.map fun p => (p.1, p.1)).map Prod.snd)
      = M.mean ((ps.map fun p => (p.1, p.1)).map Prod.fst) := by
    simp [List.map_map, Function.comp_def]
  unfold StdModel.twoPass
  rw [hm]
  refine M.sumFrom_nonneg le_rfl ?_
  intro x hx
  simp only [List.map_map, List.mem_map, Function.comp_def] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact M.nonneg _ (mul_self_nonneg _)

/-- **`VAR_*` the core trusts** (`varOf_props`): `fl(Ĉ / d)` is `≥ 0` and
within `E / d + 12 n u B² / d` of `C / d`. -/
theorem StdModel.core_var {ps : List (ℝ × ℝ)} (hne : ps ≠ []) (hN : ps.length ≤ 2 ^ 32)
    {B : ℝ} (hB0 : (2 : ℝ)⁻¹ ^ 500 ≤ B) (hB1 : B ≤ 2 ^ 399) (hB : ∀ p ∈ ps, |p.2| ≤ B)
    (hd : ∀ p ∈ ps, |p.1 - p.2| ≤ 2 * u * |p.2|) {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ ps.length) :
    0 ≤ M.fl (M.twoPass (ps.map fun p => (p.1, p.1)) / d) ∧
      |M.fl (M.twoPass (ps.map fun p => (p.1, p.1)) / d)
          - comoment (ps.map fun p => (p.2, p.2)) / d|
        ≤ 128 * ps.length ^ 2 * u * B ^ 2 / d + 12 * ps.length * u * B ^ 2 / d := by
  have hu := u_pos
  have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB0
  have h := M.decoded_twoPass (qs := dup ps) (by simpa [dup] using hne) (by simpa [dup] using hN)
    hB0 hB1 (by intro q hq; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨hB p hp, hB p hp⟩)
    (by intro q hq; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨hd p hp, hd p hp⟩)
  simp only [dup, List.map_map, Function.comp_def, List.length_map] at h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hn1 : (1 : ℝ) ≤ ps.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hNr : (ps.length : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  refine ⟨M.nonneg _ (div_nonneg (M.twoPass_dup_nonneg ps) (by positivity)), ?_⟩
  have hb2 : Bounded B (ps.map fun p => (p.2, p.2)) := by
    intro q hq; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact ⟨hB p hp, hB p hp⟩
  have hC := abs_comoment_le hb2 hBp.le
  simp only [List.length_map] at hC
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hE : 128 * (ps.length : ℝ) ^ 2 * u * B ^ 2 ≤ 4 * ps.length * B ^ 2 := by
    have : (ps.length : ℝ) * u ≤ 2 ^ 32 / 2 ^ 53 := by
      calc (ps.length : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
        _ = _ := by ring
    have hB2 : 0 ≤ (ps.length : ℝ) * B ^ 2 := by positivity
    nlinarith
  have ht : (d : ℝ) * tiny ≤ 4 * ps.length * B ^ 2 := by
    have h1 : tiny ≤ (2 : ℝ)⁻¹ ^ 22 * B ^ 2 := by
      have := mul_le_mul hB0 hB0 (by positivity) hBp.le
      have : tiny = (2 : ℝ)⁻¹ ^ 22 * ((2 : ℝ)⁻¹ ^ 500 * (2 : ℝ)⁻¹ ^ 500) := by unfold tiny; norm_num
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 22 by positivity]
    have hdn' : (d : ℝ) ≤ ps.length := by exact_mod_cast hdn
    have h2 := mul_le_mul hdn' h1 tiny_pos.le (by positivity)
    have : (ps.length : ℝ) * ((2 : ℝ)⁻¹ ^ 22 * B ^ 2) ≤ 4 * ps.length * B ^ 2 := by
      have : (0 : ℝ) ≤ ps.length * B ^ 2 := by positivity
      nlinarith
    linarith
  have hbig : 2 * (4 * (ps.length : ℝ) * B ^ 2) ≤ 2 ^ 1000 := by
    have : B ^ 2 ≤ 2 ^ 798 := by
      calc B ^ 2 ≤ (2 ^ 399) ^ 2 := by gcongr
        _ = 2 ^ 798 := by norm_num
    nlinarith
  have := M.covar_error h hC hE ht hd' hbig
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **`STDDEV_*` the core trusts** (`varOf_props`): the rounded square root
`σ` of a variance `v ≥ 0` within `τ` of `V` satisfies, squared,
`(σ − u·tiny)² ≤ (1 + u)² (V + τ)` (where `σ ≥ u·tiny`) and
`(1 − u)² (V − τ) ≤ (σ + u·tiny)²`. -/
theorem StdModel.core_stddev {v V τ : ℝ} (hv : 0 ≤ v) (h : |v - V| ≤ τ)
    (hbig : V + τ ≤ 2 ^ 1000) :
    0 ≤ M.fl √v ∧ (M.fl √v ≤ u * tiny ∨ (M.fl √v - u * tiny) ^ 2 ≤ (1 + u) ^ 2 * (V + τ)) ∧
      (1 - u) ^ 2 * (V - τ) ≤ (M.fl √v + u * tiny) ^ 2 := by
  have hu := u_pos
  have hu1 : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have ht := tiny_pos
  have hs := Real.sqrt_nonneg v
  have hsv : √v ^ 2 = v := Real.sq_sqrt hv
  have h1 := abs_le.mp h
  have hsb : √v ≤ maxFinite := by
    have : √v ≤ v + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hmax : (2 : ℝ) ^ 1023 ≤ maxFinite := by unfold maxFinite; norm_num
    linarith [h1.2]
  have he := abs_le.mp (M.err (√v) (by rw [abs_of_nonneg hs]; exact hsb))
  rw [abs_of_nonneg hs] at he
  refine ⟨M.nonneg _ hs, ?_, ?_⟩
  · rcases le_or_gt (M.fl √v) (u * tiny) with hl | hl
    · exact .inl hl
    · right
      have h2 : M.fl √v - u * tiny ≤ (1 + u) * √v := by linarith [he.2]
      have h3 : 0 ≤ M.fl √v - u * tiny := by linarith
      have h4 : (1 + u) ^ 2 * v ≤ (1 + u) ^ 2 * (V + τ) := by gcongr; linarith
      calc (M.fl √v - u * tiny) ^ 2 ≤ ((1 + u) * √v) ^ 2 := by gcongr
        _ = (1 + u) ^ 2 * v := by rw [mul_pow, hsv]
        _ ≤ _ := h4
  · have h2 : (1 - u) * √v ≤ M.fl √v + u * tiny := by linarith [he.1]
    have h3 : 0 ≤ (1 - u) * √v := mul_nonneg (by linarith) hs
    calc (1 - u) ^ 2 * (V - τ) ≤ (1 - u) ^ 2 * v := by gcongr; linarith
      _ = ((1 - u) * √v) ^ 2 := by rw [mul_pow, hsv]
      _ ≤ _ := by gcongr

/-- **`COVAR_*` the core trusts** (`covOf_props`): `fl(Ĉ / d)` within
`E / d + 12 n u B² / d` of `C / d`. -/
theorem StdModel.core_cov {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) {B : ℝ} (hB0 : (2 : ℝ)⁻¹ ^ 500 ≤ B) (hB1 : B ≤ 2 ^ 399)
    (hB : ∀ q ∈ qs, |q.2.1| ≤ B ∧ |q.2.2| ≤ B)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|)
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ qs.length) :
    |M.fl (M.twoPass (qs.map (·.1)) / d) - comoment (qs.map (·.2)) / d|
      ≤ 128 * qs.length ^ 2 * u * B ^ 2 / d + 12 * qs.length * u * B ^ 2 / d := by
  have hu := u_pos
  have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB0
  have h := M.decoded_twoPass hne hN hB0 hB1 hB hd
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hNr : (qs.length : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hb2 : Bounded B (qs.map (·.2)) := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hB q hq
  have hC := abs_comoment_le hb2 hBp.le
  simp only [List.length_map] at hC
  have hu' : u ≤ 1 / 2 ^ 53 := by unfold u; norm_num
  have hE : 128 * (qs.length : ℝ) ^ 2 * u * B ^ 2 ≤ 4 * qs.length * B ^ 2 := by
    have : (qs.length : ℝ) * u ≤ 2 ^ 32 / 2 ^ 53 := by
      calc (qs.length : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
        _ = _ := by ring
    have hB2 : 0 ≤ (qs.length : ℝ) * B ^ 2 := by positivity
    nlinarith
  have ht : (d : ℝ) * tiny ≤ 4 * qs.length * B ^ 2 := by
    have h1 : tiny ≤ (2 : ℝ)⁻¹ ^ 22 * B ^ 2 := by
      have := mul_le_mul hB0 hB0 (by positivity) hBp.le
      have : tiny = (2 : ℝ)⁻¹ ^ 22 * ((2 : ℝ)⁻¹ ^ 500 * (2 : ℝ)⁻¹ ^ 500) := by unfold tiny; norm_num
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 22 by positivity]
    have hdn' : (d : ℝ) ≤ qs.length := by exact_mod_cast hdn
    have h2 := mul_le_mul hdn' h1 tiny_pos.le (by positivity)
    have : (qs.length : ℝ) * ((2 : ℝ)⁻¹ ^ 22 * B ^ 2) ≤ 4 * qs.length * B ^ 2 := by
      have : (0 : ℝ) ≤ qs.length * B ^ 2 := by positivity
      nlinarith
    linarith
  have hbig : 2 * (4 * (qs.length : ℝ) * B ^ 2) ≤ 2 ^ 1000 := by
    have : B ^ 2 ≤ 2 ^ 798 := by
      calc B ^ 2 ≤ (2 ^ 399) ^ 2 := by gcongr
        _ = 2 ^ 798 := by norm_num
    nlinarith
  have := M.covar_error h hC hE ht hd' hbig
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **`CORR` the core trusts** (`corrOf_props`): with `E = 128 n² u B²` and
both sides' exact co-moments at least `L ≥ 8E`, `L ≥ 2⁻⁵⁰⁰`, and their
product at most `2¹⁰⁰⁰`, `|Ĉ / fl(√fl(Ŝx Ŝy))| ≤ 1 + 3E/L + 8u`. -/
theorem StdModel.core_corr {qs : List ((ℝ × ℝ) × (ℝ × ℝ))} (hne : qs ≠ [])
    (hN : qs.length ≤ 2 ^ 32) {B : ℝ} (hB0 : (2 : ℝ)⁻¹ ^ 500 ≤ B) (hB1 : B ≤ 2 ^ 399)
    (hB : ∀ q ∈ qs, |q.2.1| ≤ B ∧ |q.2.2| ≤ B)
    (hd : ∀ q ∈ qs, |q.1.1 - q.2.1| ≤ 2 * u * |q.2.1| ∧ |q.1.2 - q.2.2| ≤ 2 * u * |q.2.2|)
    {L : ℝ} (hL : 8 * (128 * qs.length ^ 2 * u * B ^ 2) ≤ L) (hLt : (2 : ℝ)⁻¹ ^ 500 ≤ L)
    (hSx : L ≤ comoment (qs.map fun q => (q.2.1, q.2.1)))
    (hSy : L ≤ comoment (qs.map fun q => (q.2.2, q.2.2)))
    (hbig : comoment (qs.map fun q => (q.2.1, q.2.1)) * comoment (qs.map fun q => (q.2.2, q.2.2))
      ≤ 2 ^ 1000) :
    |M.fl (M.twoPass (qs.map (·.1)) /
        M.fl √(M.fl (M.twoPass (qs.map fun q => (q.1.1, q.1.1))
          * M.twoPass (qs.map fun q => (q.1.2, q.1.2)))))|
      ≤ 1 + 3 * (128 * qs.length ^ 2 * u * B ^ 2) / L + 8 * u := by
  have hu := u_pos
  have hc := M.decoded_twoPass hne hN hB0 hB1 hB hd
  have hx := M.decoded_twoPass (qs := qs.map fun q => ((q.1.1, q.1.1), (q.2.1, q.2.1)))
    (by simpa using hne) (by simpa using hN) hB0 hB1
    (by intro q hq; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hB r hr).1, (hB r hr).1⟩)
    (by intro q hq; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hd r hr).1, (hd r hr).1⟩)
  have hy := M.decoded_twoPass (qs := qs.map fun q => ((q.1.2, q.1.2), (q.2.2, q.2.2)))
    (by simpa using hne) (by simpa using hN) hB0 hB1
    (by intro q hq; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hB r hr).2, (hB r hr).2⟩)
    (by intro q hq; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq; exact ⟨(hd r hr).2, (hd r hr).2⟩)
  simp only [List.map_map, Function.comp_def, List.length_map] at hx hy
  have hCS := sq_comoment_le (qs.map (·.2))
  simp only [List.map_map, Function.comp_def] at hCS
  exact M.corr_le hCS hc hx hy hL (by positivity) hSx hSy hLt hbig

end FloatBounds

end
