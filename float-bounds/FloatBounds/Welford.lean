module

public import FloatBounds.Moments

/-!
# Welford's algorithm and Chan's merge (DuckDB's `VARIANCE` and `COVAR`)

DuckDB computes `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` from a state
`(n, x̄, ȳ, C)`: one pair at a time by Welford's update, and states of
different threads by Chan's merge (`StdModel.welfordStep`, `StdModel.chan`,
in DuckDB's order of operations; `VARIANCE` is the case `y = x`).
`StdModel.Plan` is any tree of such steps and merges.

`StdModel.plan_good`: the state of a plan over `n` pairs, all within `B`,
has means within `8 · n · u · B` and a co-moment within `64 · n² · u · B²`
of the exact ones (`Good`). The proof is by induction on the plan, with the
invariant `Good` closed under both a step (`welfordStep_good`) and a merge
(`chan_good`).
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- A running state: the count, the two means, and the co-moment. -/
structure WState where
  n : ℕ
  mx : ℝ
  my : ℝ
  c : ℝ

/-- The state of no pairs. -/
def WState.empty : WState := ⟨0, 0, 0, 0⟩

variable (M : StdModel)

/-- **Welford's update**, as DuckDB's `CovarOperation` makes it:
`dx = x − x̄`, `x̄' = x̄ + dx / n`, the same for `y`, and
`C' = C + dx · (y − ȳ')`. -/
noncomputable def StdModel.welfordStep (s : WState) (p : ℝ × ℝ) : WState :=
  let k : ℝ := s.n + 1
  let dx := M.fl (p.1 - s.mx)
  let mx' := M.fl (s.mx + M.fl (dx / k))
  let dy := M.fl (p.2 - s.my)
  let my' := M.fl (s.my + M.fl (dy / k))
  ⟨s.n + 1, mx', my', M.fl (s.c + M.fl (dx * M.fl (p.2 - my')))⟩

/-- **Chan's merge** of a source state `s` into a target `t`, as DuckDB's
`Combine` makes it: `x̄ = (n_s·x̄_s + n_t·x̄_t) / n` and
`C = C_s + C_t + Δx · Δy · n_s · n_t / n`, with `Δ = t − s`. -/
noncomputable def StdModel.chan (t s : WState) : WState :=
  if t.n = 0 then s else if s.n = 0 then t else
    let n : ℝ := t.n + s.n
    ⟨t.n + s.n,
      M.fl (M.fl (M.fl (s.n * s.mx) + M.fl (t.n * t.mx)) / n),
      M.fl (M.fl (M.fl (s.n * s.my) + M.fl (t.n * t.my)) / n),
      M.fl (M.fl (s.c + t.c)
        + M.fl (M.fl (M.fl (M.fl (M.fl (t.mx - s.mx) * M.fl (t.my - s.my)) * s.n) * t.n) / n))⟩

/-- A plan: Welford's update over a list, from the empty state, or a merge
of two plans. -/
inductive Plan where
  | seq (ps : List (ℝ × ℝ))
  | merge (t s : Plan)

/-- The pairs a plan aggregates. -/
def Plan.pairs : Plan → List (ℝ × ℝ)
  | .seq ps => ps
  | .merge t s => t.pairs ++ s.pairs

/-- The state a plan computes. -/
noncomputable def StdModel.run : Plan → WState
  | .seq ps => ps.foldl M.welfordStep .empty
  | .merge t s => M.chan (StdModel.run t) (StdModel.run s)

/-- `s` is the state of `ps`, within the bounds of the invariant. -/
def Good (B : ℝ) (s : WState) (ps : List (ℝ × ℝ)) : Prop :=
  s.n = ps.length ∧ |s.mx - mx ps| ≤ 8 * s.n * u * B ∧ |s.my - my ps| ≤ 8 * s.n * u * B ∧
    |s.c - comoment ps| ≤ 64 * s.n ^ 2 * u * B ^ 2

theorem good_empty (B : ℝ) : Good B .empty [] := by
  simp [Good, WState.empty, mx, my, comoment, sx, sy]

/-- A rounding with `|z| ≤ Z`: within `u · (Z + tiny)`. -/
theorem StdModel.r {z Z : ℝ} (h : |z| ≤ Z) (hZ : Z ≤ 2 ^ 1000) :
    |M.fl z - z| ≤ u * (Z + tiny) := by
  have := M.err z (le_trans h (le_trans hZ two_pow_le_maxFinite))
  have hu := u_pos
  calc _ ≤ u * (|z| + tiny) := this
    _ ≤ _ := by gcongr

/-- `|a'b' − ab|` from the errors of `a'` and `b'`. -/
theorem abs_mul_sub_le {a a' b b' ea eb A B' : ℝ} (ha : |a' - a| ≤ ea) (hb : |b' - b| ≤ eb)
    (hA : |a| ≤ A) (hB : |b| ≤ B') :
    |a' * b' - a * b| ≤ ea * (B' + eb) + A * eb := by
  have hb' : |b'| ≤ B' + eb := by have := abs_sub_abs_le_abs_sub b' b; linarith
  have h1 : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
  rw [h1]
  calc _ ≤ |(a' - a) * b'| + |a * (b' - b)| := abs_add_le _ _
    _ = |a' - a| * |b'| + |a| * |b' - b| := by rw [abs_mul, abs_mul]
    _ ≤ ea * (B' + eb) + A * eb := by
      gcongr
      · exact le_trans (abs_nonneg _) ha
      · exact le_trans (abs_nonneg _) hA

section
variable {N : ℕ} {B : ℝ} (S : Scale N B)
include S

/-- The facts about the scale the steps below use, as linear facts about
the products that appear in them. -/
theorem Scale.facts {k : ℕ} (hk : k ≤ N) :
    0 < u ∧ 0 < B ∧ (k : ℝ) * u * B ≤ B / 2 ^ 21 ∧ u * ((k : ℝ) * u * B) ≤ u * B / 2 ^ 21 ∧
      u * B ≤ B / 2 ^ 53 ∧ tiny ≤ B / 2 ^ 64 ∧ u * tiny ≤ u * B / 2 ^ 64 ∧
      tiny ≤ B ^ 2 / 2 ^ 22 ∧ (k : ℝ) ≤ 2 ^ 32 ∧ B ≤ 2 ^ 400 ∧ B ^ 2 ≤ 2 ^ 800 := by
  have hu := u_pos
  have hB := S.B_pos
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hku : (k : ℝ) * u ≤ 1 / 2 ^ 21 := by
    have := S.nu_le; have : (k : ℝ) * u ≤ N * u := by gcongr
    norm_num at *; linarith
  have h1 : (k : ℝ) * u * B ≤ B / 2 ^ 21 := by
    have := mul_le_mul_of_nonneg_right hku hB.le; linarith
  have htB : tiny ≤ B / 2 ^ 64 := by
    have := S.tiny_le_B
    have : (2 : ℝ)⁻¹ ^ 500 * B ≤ B / 2 ^ 64 := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ)⁻¹ ^ 500 * 2 ^ 64 ≤ 1 := by norm_num
      nlinarith
    linarith
  refine ⟨hu, hB, h1, ?_, ?_, htB, ?_, ?_, le_trans hkN S.n_le', S.B_le, S.B2_le⟩
  · have := mul_le_mul_of_nonneg_left h1 hu.le; linarith
  · have : u = 1 / 2 ^ 53 := by unfold u; norm_num
    rw [this]; ring_nf; rfl
  · have := mul_le_mul_of_nonneg_left htB hu.le; linarith
  · have := S.tiny_le_B2; norm_num at this ⊢; linarith

/-- **The mean in Welford's update**: from a mean within `8 k u B`, the new
mean is within `8 (k + 1) u B`, and `dx` within `(8k + 3) u B`. -/
theorem StdModel.mean_step {k : ℕ} (hk : k + 1 ≤ N) {m mh x : ℝ}
    (hm : |m| ≤ B) (hx : |x| ≤ B) (hmh : |mh - m| ≤ 8 * k * u * B) :
    |M.fl (x - mh) - (x - m)| ≤ (8 * k + 3) * u * B ∧
      |M.fl (mh + M.fl (M.fl (x - mh) / (k + 1))) - (m + (x - m) / (k + 1))|
        ≤ 8 * (k + 1) * u * B := by
  obtain ⟨hu, hB, F1, F2, F4, htB, F3, -, hk32, hB4, -⟩ := S.facts (k := k) (by omega)
  have huB : 0 ≤ u * B := by positivity
  have hkuB : 0 ≤ (k : ℝ) * u * B := by positivity
  have hK : (1 : ℝ) ≤ k + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hK0 : (0 : ℝ) < k + 1 := by linarith
  have small : 8 * k * u * B + tiny ≤ B / 4 := by linarith
  -- `d = x − mh`, rounded
  have hxmh : |x - mh| ≤ 2 * B + 8 * k * u * B := by
    have : x - mh = (x - m) - (mh - m) := by ring
    rw [this]
    have := abs_sub (x - m) (mh - m); have := abs_sub x m; linarith
  set d := M.fl (x - mh)
  have r1 : |d - (x - mh)| ≤ 9 / 4 * u * B := by
    have := M.r (z := x - mh) hxmh (by linarith)
    linarith
  have hd : |d| ≤ 5 / 2 * B := by
    have := abs_sub_abs_le_abs_sub d (x - mh)
    linarith
  refine ⟨?_, ?_⟩
  · have : d - (x - m) = (d - (x - mh)) - (mh - m) := by ring
    rw [this]
    have := abs_sub (d - (x - mh)) (mh - m)
    linarith
  -- `q = d / (k + 1)`, rounded
  have hdK : |d / (k + 1)| ≤ 5 / 2 * B := by
    rw [abs_div, abs_of_pos hK0]
    exact le_trans (div_le_self (abs_nonneg _) hK) hd
  set q := M.fl (d / (k + 1))
  have r2 : |q - d / (k + 1)| ≤ 3 * u * B := by
    have := M.r hdK (by linarith)
    linarith
  -- the decomposition of the new mean's error
  have hdec : mh + q - (m + (x - m) / (k + 1))
      = (mh - m) * (1 - 1 / (k + 1)) + (d - (x - mh)) / (k + 1) + (q - d / (k + 1)) := by
    field_simp; ring
  have hcoef : |(mh - m) * (1 - 1 / (k + 1))| ≤ |mh - m| := by
    rw [abs_mul]
    have h1 : 0 ≤ 1 - 1 / ((k : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one hK0]; exact hK
    have h2 : 1 - 1 / ((k : ℝ) + 1) ≤ 1 := by
      have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    rw [abs_of_nonneg h1]
    exact mul_le_of_le_one_right (abs_nonneg _) h2
  have hr1K : |(d - (x - mh)) / (k + 1)| ≤ 9 / 4 * u * B := by
    rw [abs_div, abs_of_pos hK0]
    exact le_trans (div_le_self (abs_nonneg _) hK) r1
  have hz : |mh + q - (m + (x - m) / (k + 1))| ≤ 8 * k * u * B + 21 / 4 * u * B := by
    rw [hdec]
    have := abs_add_le ((mh - m) * (1 - 1 / (k + 1)) + (d - (x - mh)) / (k + 1))
      (q - d / (k + 1))
    have := abs_add_le ((mh - m) * (1 - 1 / (k + 1))) ((d - (x - mh)) / (k + 1))
    linarith
  have hm' : |m + (x - m) / (k + 1)| ≤ B := by
    have : m + (x - m) / (k + 1) = m * (1 - 1 / (k + 1)) + x * (1 / (k + 1)) := by
      field_simp; ring
    rw [this]
    have h1 : 0 ≤ 1 - 1 / ((k : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one hK0]; exact hK
    have h2 : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    calc _ ≤ |m * (1 - 1 / (k + 1))| + |x * (1 / (k + 1))| := abs_add_le _ _
      _ = |m| * (1 - 1 / (k + 1)) + |x| * (1 / (k + 1)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
      _ ≤ B * (1 - 1 / (k + 1)) + B * (1 / (k + 1)) := by gcongr
      _ = B := by ring
  have hmq : |mh + q| ≤ 5 / 4 * B := by
    have := abs_sub_abs_le_abs_sub (mh + q) (m + (x - m) / (k + 1))
    linarith
  have r3 := M.r hmq (by linarith)
  have := abs_add_le (M.fl (mh + q) - (mh + q)) (mh + q - (m + (x - m) / (k + 1)))
  have e : M.fl (mh + q) - (m + (x - m) / (k + 1))
      = (M.fl (mh + q) - (mh + q)) + (mh + q - (m + (x - m) / (k + 1))) := by ring
  rw [e]
  linarith

/-- **Welford's update keeps the invariant.** -/
theorem StdModel.welfordStep_good {s : WState} {ps : List (ℝ × ℝ)} {p : ℝ × ℝ}
    (hg : Good B s ps) (hb : Bounded B (ps ++ [p])) (hN : ps.length + 1 ≤ N) :
    Good B (M.welfordStep s p) (ps ++ [p]) := by
  obtain ⟨hn, hmx, hmy, hc⟩ := hg
  obtain ⟨hbp, hbx⟩ := Bounded.append.mp hb
  have hp := hbx p (by simp)
  obtain ⟨hu, hB, F1, F2, F4, htB, F3, htB2, hk32, hB4, hB2⟩ := S.facts (k := ps.length + 1) hN
  have hB0 := hB.le
  have mxb := abs_mx_le hbp hB0
  have myb := abs_my_le hbp hB0
  rw [hn] at hmx hmy hc
  obtain ⟨hdx, hmx'⟩ := M.mean_step S hN mxb hp.1 hmx
  obtain ⟨-, hmy'⟩ := M.mean_step S hN myb hp.2 hmy
  have my'b := abs_my_le hb hB0
  have cb := abs_comoment_le hb hB0
  rw [← my_snoc] at hmy'
  rw [← mx_snoc] at hmx'
  simp only [List.length_append, List.length_singleton] at cb
  push_cast at F1 F2 cb hk32 ⊢
  set k : ℝ := (ps.length : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have huB : 0 ≤ u * B := by positivity
  have huB2 : 0 ≤ u * B ^ 2 := by positivity
  -- the scale-`B²` facts
  have G1 : (k + 1) * u * B ^ 2 ≤ B ^ 2 / 2 ^ 21 := by
    have := mul_le_mul_of_nonneg_right F1 hB0; linarith
  have G3 : u * tiny ≤ u * B ^ 2 / 2 ^ 22 := by
    have := mul_le_mul_of_nonneg_left htB2 hu.le; linarith
  have hkuB2 : 0 ≤ k * (u * B ^ 2) := mul_nonneg hk0 huB2
  have G5 : k * u * B ^ 2 ≤ B ^ 2 / 2 ^ 21 := by linarith
  -- `y − ȳ'`, rounded
  set my' := M.fl (s.my + M.fl (M.fl (p.2 - s.my) / (k + 1)))
  have hz2 : |p.2 - my'| ≤ 2 * B + 8 * (k + 1) * u * B := by
    have : p.2 - my' = (p.2 - my (ps ++ [p])) - (my' - my (ps ++ [p])) := by ring
    rw [this]
    have := abs_sub (p.2 - my (ps ++ [p])) (my' - my (ps ++ [p]))
    have := abs_sub p.2 (my (ps ++ [p]))
    linarith [hp.2]
  have he := M.r hz2 (by linarith)
  have hE : |M.fl (p.2 - my') - (p.2 - my (ps ++ [p]))| ≤ (8 * (k + 1) + 3) * u * B := by
    have : M.fl (p.2 - my') - (p.2 - my (ps ++ [p]))
        = (M.fl (p.2 - my') - (p.2 - my')) - (my' - my (ps ++ [p])) := by ring
    rw [this]
    have := abs_sub (M.fl (p.2 - my') - (p.2 - my')) (my' - my (ps ++ [p]))
    linarith
  have hD : |M.fl (p.1 - s.mx) - (p.1 - mx ps)| ≤ (8 * (k + 1) + 3) * u * B := by
    linarith
  have hDb : |p.1 - mx ps| ≤ 2 * B := by have := abs_sub p.1 (mx ps); linarith [hp.1]
  have hEb : |p.2 - my (ps ++ [p])| ≤ 2 * B := by
    have := abs_sub p.2 (my (ps ++ [p])); linarith [hp.2]
  -- the product
  have e_small : (8 * (k + 1) + 3) * u * B ≤ B / 2 ^ 17 := by linarith
  have hP := abs_mul_sub_le hD hE hDb hEb
  have hP' : |M.fl (p.1 - s.mx) * M.fl (p.2 - my') - (p.1 - mx ps) * (p.2 - my (ps ++ [p]))|
      ≤ (4 + 1 / 2 ^ 16) * B * ((8 * (k + 1) + 3) * u * B) := by
    have : (8 * (k + 1) + 3) * u * B * (2 * B + (8 * (k + 1) + 3) * u * B)
        ≤ (8 * (k + 1) + 3) * u * B * (2 * B + B / 2 ^ 17) := by gcongr
    have : 0 ≤ B * ((8 * (k + 1) + 3) * u * B) := by positivity
    linarith
  have hPz : |(p.1 - mx ps) * (p.2 - my (ps ++ [p]))| ≤ 4 * B ^ 2 := by
    rw [abs_mul]
    have := mul_le_mul hDb hEb (abs_nonneg _) (by positivity)
    linarith
  have hP'z : |M.fl (p.1 - s.mx) * M.fl (p.2 - my')| ≤ 5 * B ^ 2 := by
    have := abs_sub_abs_le_abs_sub (M.fl (p.1 - s.mx) * M.fl (p.2 - my'))
      ((p.1 - mx ps) * (p.2 - my (ps ++ [p])))
    have := mul_le_mul_of_nonneg_left e_small hB0
    linarith
  have hPr := M.r hP'z (by linarith)
  set P := M.fl (M.fl (p.1 - s.mx) * M.fl (p.2 - my'))
  have hPe : |P - (p.1 - mx ps) * (p.2 - my (ps ++ [p]))| ≤ (33 * (k + 1) + 18) * (u * B ^ 2) := by
    have : P - (p.1 - mx ps) * (p.2 - my (ps ++ [p]))
        = (P - M.fl (p.1 - s.mx) * M.fl (p.2 - my'))
          + (M.fl (p.1 - s.mx) * M.fl (p.2 - my') - (p.1 - mx ps) * (p.2 - my (ps ++ [p]))) := by
      ring
    rw [this]
    have := abs_add_le (P - M.fl (p.1 - s.mx) * M.fl (p.2 - my'))
      (M.fl (p.1 - s.mx) * M.fl (p.2 - my') - (p.1 - mx ps) * (p.2 - my (ps ++ [p])))
    linarith
  -- the sum
  have hsum : |s.c + P - comoment (ps ++ [p])|
      ≤ 64 * k ^ 2 * u * B ^ 2 + (33 * (k + 1) + 18) * (u * B ^ 2) := by
    rw [comoment_snoc]
    have : s.c + P - (comoment ps + (p.1 - mx ps) * (p.2 - my (ps ++ [p])))
        = (s.c - comoment ps) + (P - (p.1 - mx ps) * (p.2 - my (ps ++ [p]))) := by ring
    rw [this]
    have := abs_add_le (s.c - comoment ps) (P - (p.1 - mx ps) * (p.2 - my (ps ++ [p])))
    linarith
  have hk2 : k * (k * u * B ^ 2) ≤ k * (B ^ 2 / 2 ^ 21) := mul_le_mul_of_nonneg_left G5 hk0
  have hsz : |s.c + P| ≤ 5 * (k + 1) * B ^ 2 := by
    have := abs_sub_abs_le_abs_sub (s.c + P) (comoment (ps ++ [p]))
    have : 0 ≤ k * B ^ 2 := by positivity
    linarith
  have hKB : (k + 1) * B ^ 2 ≤ 2 ^ 32 * 2 ^ 800 := mul_le_mul hk32 hB2 (by positivity) (by positivity)
  have hsr := M.r hsz (by linarith)
  refine ⟨by simp [StdModel.welfordStep, hn], ?_, ?_, ?_⟩
  · simpa [StdModel.welfordStep, hn] using hmx'
  · simpa [StdModel.welfordStep, hn] using hmy'
  · simp only [StdModel.welfordStep, hn]
    push_cast
    have : M.fl (s.c + P) - comoment (ps ++ [p])
        = (M.fl (s.c + P) - (s.c + P)) + (s.c + P - comoment (ps ++ [p])) := by ring
    rw [this]
    have := abs_add_le (M.fl (s.c + P) - (s.c + P)) (s.c + P - comoment (ps ++ [p]))
    linarith

/-- A mean scaled by its count `c`, rounded: `c · m` within `8 c² u B + 2 c u B`. -/
theorem StdModel.chan_scaled {a b : ℕ} (hN : a + b ≤ N) {c m Mm : ℝ} (hc : 1 ≤ c)
    (hcn : c ≤ (a : ℝ) + b) (hMm : |Mm| ≤ B) (hm : |m - Mm| ≤ 8 * c * u * B) :
    |M.fl (c * m) - c * Mm| ≤ 8 * c ^ 2 * u * B + 2 * c * u * B := by
  obtain ⟨hu, hB, F1, F2, F4, htB, F3, -, hk32, hB4, -⟩ := S.facts hN
  push_cast at F1 F2 hk32
  have hB0 := hB.le
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hz : |c * m - c * Mm| ≤ 8 * c ^ 2 * u * B := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    calc _ ≤ c * (8 * c * u * B) := by gcongr
      _ = _ := by ring
  have hcu : c * u * B ≤ B / 2 ^ 21 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcn hu.le) hB0
    linarith
  have hz' : |c * m| ≤ c * B + 8 * c ^ 2 * u * B := by
    have := abs_sub_abs_le_abs_sub (c * m) (c * Mm)
    simp only [abs_mul, abs_of_nonneg hc0] at this ⊢
    have := mul_le_mul_of_nonneg_left hMm hc0
    linarith
  have hcc : c * (c * u * B) ≤ c * (B / 2 ^ 21) := mul_le_mul_of_nonneg_left hcu hc0
  have hcB : c * B ≤ 2 ^ 32 * 2 ^ 400 := mul_le_mul (by linarith) hB4 hB0 (by positivity)
  have hr := M.r hz' (by linarith)
  have hcuB0 : 0 ≤ c * u * B := by positivity
  have hcuB : u * B ≤ c * u * B := by
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ u * B); linarith
  have : M.fl (c * m) - c * Mm = (M.fl (c * m) - c * m) + (c * m - c * Mm) := by ring
  rw [this]
  have := abs_add_le (M.fl (c * m) - c * m) (c * m - c * Mm)
  have : u * (8 * c ^ 2 * u * B) ≤ 8 * c * (u * B / 2 ^ 21) := by
    have := mul_le_mul_of_nonneg_left hcu (by positivity : (0 : ℝ) ≤ 8 * c * u)
    linarith
  linarith

/-- **The mean in Chan's merge**: `(b·m_s + a·m_t) / (a + b)` from means
within `8 a u B` and `8 b u B` is within `8 (a + b) u B`. -/
theorem StdModel.chan_mean {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : a + b ≤ N)
    {mt ms Mp Mq : ℝ} (hMp : |Mp| ≤ B) (hMq : |Mq| ≤ B)
    (ht : |mt - Mp| ≤ 8 * a * u * B) (hs : |ms - Mq| ≤ 8 * b * u * B) :
    |M.fl (M.fl (M.fl (b * ms) + M.fl (a * mt)) / ((a : ℝ) + b))
        - (b * Mq + a * Mp) / ((a : ℝ) + b)| ≤ 8 * ((a : ℝ) + b) * u * B := by
  obtain ⟨hu, hB, F1, F2, F4, htB, F3, -, hk32, hB4, -⟩ := S.facts hN
  push_cast at F1 F2 hk32
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hn0 : (0 : ℝ) < a + b := by linarith
  have hab : ((a : ℝ) + b) / 2 ≤ a * b := by
    have := mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'); linarith
  have hBn : B ≤ ((a : ℝ) + b) * B := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ a + b by linarith) hB.le; linarith
  have hnuB : 0 ≤ ((a : ℝ) + b) * u * B := by positivity
  have huB : 0 ≤ u * B := by positivity
  have hB0 := hB.le
  -- `b · m_s` and `a · m_t`, rounded
  have hA1 := M.chan_scaled S hN hb' (by linarith) hMq hs
  have hA2 := M.chan_scaled S hN ha' (by linarith) hMp ht
  set A1 := M.fl (b * ms)
  set A2 := M.fl (a * mt)
  -- their sum, rounded
  have hsum : |A1 + A2 - (b * Mq + a * Mp)|
      ≤ 8 * ((a : ℝ) ^ 2 + b ^ 2) * u * B + 2 * ((a : ℝ) + b) * u * B := by
    have : A1 + A2 - (b * Mq + a * Mp) = (A1 - b * Mq) + (A2 - a * Mp) := by ring
    rw [this]
    have := abs_add_le (A1 - b * Mq) (A2 - a * Mp)
    linarith
  have hzab : |(b : ℝ) * Mq + a * Mp| ≤ (a + b) * B := by
    have := abs_add_le ((b : ℝ) * Mq) (a * Mp)
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ a)] at this
    have := mul_le_mul_of_nonneg_left hMq (by linarith : (0 : ℝ) ≤ b)
    have := mul_le_mul_of_nonneg_left hMp (by linarith : (0 : ℝ) ≤ a)
    linarith
  have hsq : ((a : ℝ) ^ 2 + b ^ 2) * u * B ≤ (a + b) * (B / 2 ^ 21) := by
    have : ((a : ℝ) ^ 2 + b ^ 2) ≤ (a + b) * (a + b) := by nlinarith
    have := mul_le_mul_of_nonneg_right this huB
    have := mul_le_mul_of_nonneg_left F1 hn0.le
    linarith
  have hA : |A1 + A2| ≤ (a + b) * B + (a + b) * B / 2 ^ 17 := by
    have := abs_sub_abs_le_abs_sub (A1 + A2) (b * Mq + a * Mp)
    linarith
  have hnB : ((a : ℝ) + b) * B ≤ 2 ^ 32 * 2 ^ 400 := mul_le_mul hk32 hB4 hB0 (by positivity)
  have hr := M.r hA (by linarith)
  set A := M.fl (A1 + A2)
  have hAe : |A - (b * Mq + a * Mp)|
      ≤ 8 * ((a : ℝ) ^ 2 + b ^ 2) * u * B + 4 * ((a : ℝ) + b) * u * B := by
    have : A - (b * Mq + a * Mp) = (A - (A1 + A2)) + (A1 + A2 - (b * Mq + a * Mp)) := by ring
    rw [this]
    have := abs_add_le (A - (A1 + A2)) (A1 + A2 - (b * Mq + a * Mp))
    have : u * B ≤ ((a : ℝ) + b) * u * B := by
      have := mul_le_mul_of_nonneg_left hBn hu.le; linarith
    linarith
  -- the division by the count, rounded
  have hdiv : |A / (a + b) - (b * Mq + a * Mp) / (a + b)|
      ≤ (8 * ((a : ℝ) + b) - 2) * u * B := by
    rw [← sub_div, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    have : (0 : ℝ) ≤ (16 * a * b - 6 * (a + b)) * (u * B) := by
      apply mul_nonneg _ huB; linarith
    linarith
  have hAn : |A / (a + b)| ≤ 5 / 4 * B := by
    have := abs_sub_abs_le_abs_sub (A / (a + b)) ((b * Mq + a * Mp) / (a + b))
    have : |((b : ℝ) * Mq + a * Mp) / (a + b)| ≤ B := by
      rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]; linarith
    linarith
  have hr2 := M.r hAn (by linarith)
  have : M.fl (A / (a + b)) - (b * Mq + a * Mp) / (a + b)
      = (M.fl (A / (a + b)) - A / (a + b)) + (A / (a + b) - (b * Mq + a * Mp) / (a + b)) := by
    ring
  rw [this]
  have := abs_add_le (M.fl (A / (a + b)) - A / (a + b))
    (A / (a + b) - (b * Mq + a * Mp) / (a + b))
  linarith

/-- A difference of two means, rounded: within `(8 n + 3) u B`. -/
theorem StdModel.diff_error {n : ℕ} (hN : n ≤ N) {mt ms Mp Mq : ℝ} (hMp : |Mp| ≤ B)
    (hMq : |Mq| ≤ B) (he : |(mt - ms) - (Mp - Mq)| ≤ 8 * n * u * B) :
    |M.fl (mt - ms) - (Mp - Mq)| ≤ (8 * n + 3) * u * B := by
  obtain ⟨hu, hB, F1, F2, F4, htB, F3, -, hk32, hB4, -⟩ := S.facts hN
  have hz : |mt - ms| ≤ 2 * B + 8 * n * u * B := by
    have := abs_sub_abs_le_abs_sub (mt - ms) (Mp - Mq)
    have := abs_sub Mp Mq
    linarith
  have hr := M.r hz (by linarith)
  have : M.fl (mt - ms) - (Mp - Mq) = (M.fl (mt - ms) - (mt - ms)) + ((mt - ms) - (Mp - Mq)) := by
    ring
  rw [this]
  have := abs_add_le (M.fl (mt - ms) - (mt - ms)) ((mt - ms) - (Mp - Mq))
  have : 0 ≤ u * B := by positivity
  linarith

/-- The product of two differences of means, rounded. -/
theorem StdModel.prod_error {n : ℕ} (hN : n ≤ N) {X X' Y Y' : ℝ}
    (hX : |X| ≤ 2 * B) (hY : |Y| ≤ 2 * B)
    (hdx : |X' - X| ≤ (8 * n + 3) * u * B) (hdy : |Y' - Y| ≤ (8 * n + 3) * u * B) :
    |M.fl (X' * Y') - X * Y| ≤ (33 * n + 18) * (u * B ^ 2) := by
  obtain ⟨hu, hB, F1, -, F4, -, -, htB2, -, hB4, hB2⟩ := S.facts hN
  have hB0 := hB.le
  set e := (8 * (n : ℝ) + 3) * u * B
  have e_small : e ≤ B / 2 ^ 17 := by simp only [e]; linarith only [F1, F4, hB0]
  have hBe : B * e = (8 * n + 3) * (u * B ^ 2) := by simp only [e]; ring
  have hP := abs_mul_sub_le hdx hdy hX hY
  have he0 : 0 ≤ e := by positivity
  have hP' : |X' * Y' - X * Y| ≤ (4 + 1 / 2 ^ 16) * (B * e) := by
    have h1 : e * (2 * B + e) ≤ e * (2 * B + B / 2 ^ 17) := by gcongr
    have h2 : 0 ≤ B * e := by positivity
    linarith only [hP, h1, h2]
  have hPz : |X * Y| ≤ 4 * B ^ 2 := by
    rw [abs_mul]; have := mul_le_mul hX hY (abs_nonneg _) (by positivity); linarith only [this]
  have hBeB : B * e ≤ B ^ 2 / 2 ^ 17 := by
    have := mul_le_mul_of_nonneg_left e_small hB0; linarith only [this]
  have hP'z : |X' * Y'| ≤ 5 * B ^ 2 := by
    have := abs_sub_abs_le_abs_sub (X' * Y') (X * Y)
    linarith only [this, hP', hPz, hBeB, sq_nonneg B]
  have hr := M.r hP'z (by linarith only [hB2])
  have hsplit : M.fl (X' * Y') - X * Y = (M.fl (X' * Y') - X' * Y') + (X' * Y' - X * Y) := by
    ring
  rw [hsplit]
  have hadd := abs_add_le (M.fl (X' * Y') - X' * Y') (X' * Y' - X * Y)
  have G3 : u * tiny ≤ u * B ^ 2 / 2 ^ 22 := by
    have := mul_le_mul_of_nonneg_left htB2 hu.le; linarith only [this]
  have h3 : 0 ≤ (n : ℝ) * (u * B ^ 2) := by positivity
  have h4 : 0 ≤ u * B ^ 2 := by positivity
  rw [hBe] at hP'
  linarith only [hr, hP', G3, h3, h4, hadd]

end

/-- A rounded product by a count `c ≥ 1`. -/
theorem StdModel.round_count {P D e Dm c : ℝ} (h : |P - D| ≤ e) (hD : |D| ≤ Dm)
    (he : e ≤ Dm / 4) (ht : tiny ≤ Dm) (hc : 1 ≤ c) (hbig : 3 * c * Dm ≤ 2 ^ 1000) :
    |M.fl (P * c) - D * c| ≤ c * e + 3 * u * (c * Dm) := by
  have hu := u_pos
  have hc0 : 0 ≤ c := by linarith
  have hDm : 0 ≤ Dm := le_trans (abs_nonneg _) hD
  have h1 : |P * c - D * c| ≤ c * e := by
    rw [← sub_mul, abs_mul, abs_of_nonneg hc0, mul_comm]; gcongr
  have h2 : |D * c| ≤ c * Dm := by
    rw [abs_mul, abs_of_nonneg hc0, mul_comm]; gcongr
  have hcDm : Dm ≤ c * Dm := by nlinarith
  have hce : c * e ≤ c * (Dm / 4) := by gcongr
  have hPc : |P * c| ≤ 3 * c * Dm := by
    have := abs_sub_abs_le_abs_sub (P * c) (D * c); linarith
  have := M.round_near h1 (le_trans hPc (le_trans hbig two_pow_le_maxFinite))
  have hz : u * (|D * c| + c * e + tiny) ≤ u * (3 * (c * Dm)) := by
    gcongr; linarith
  linarith

/-- A rounded division by a count `n ≥ 1`. -/
theorem StdModel.round_div {P D e Dm n : ℝ} (h : |P - D| ≤ e) (hD : |D| ≤ Dm)
    (he : e ≤ Dm) (ht : n * tiny ≤ Dm) (hn : 1 ≤ n) (hbig : 2 * Dm ≤ 2 ^ 1000) :
    |M.fl (P / n) - D / n| ≤ e / n + 3 * u * Dm / n := by
  have hu := u_pos
  have hn0 : 0 < n := by linarith
  have hDm : 0 ≤ Dm := le_trans (abs_nonneg _) hD
  have h1 : |P / n - D / n| ≤ e / n := by
    rw [← sub_div, abs_div, abs_of_pos hn0]; gcongr
  have h2 : |D / n| ≤ Dm / n := by rw [abs_div, abs_of_pos hn0]; gcongr
  have hDn : Dm / n ≤ Dm := div_le_self hDm hn
  have hen : e / n ≤ Dm / n := by gcongr
  have htn : tiny ≤ Dm / n := by rw [le_div_iff₀ hn0]; linarith
  have hPn : |P / n| ≤ 2 * Dm := by
    have := abs_sub_abs_le_abs_sub (P / n) (D / n); linarith
  have := M.round_near h1 (le_trans hPn (le_trans hbig two_pow_le_maxFinite))
  have hz : u * (|D / n| + e / n + tiny) ≤ u * (3 * (Dm / n)) := by
    gcongr; linarith
  have : u * (3 * (Dm / n)) = 3 * u * Dm / n := by ring
  linarith

section
variable {N : ℕ} {B : ℝ} (S : Scale N B)
include S

set_option maxHeartbeats 1000000 in
/-- **The co-moment in Chan's merge.** -/
theorem StdModel.chan_comoment {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hN : a + b ≤ N)
    {mtx msx mty msy Mpx Mqx Mpy Mqy ct cs Cp Cq : ℝ}
    (hpx : |Mpx| ≤ B) (hqx : |Mqx| ≤ B) (hpy : |Mpy| ≤ B) (hqy : |Mqy| ≤ B)
    (htx : |mtx - Mpx| ≤ 8 * a * u * B) (hsx : |msx - Mqx| ≤ 8 * b * u * B)
    (hty : |mty - Mpy| ≤ 8 * a * u * B) (hsy : |msy - Mqy| ≤ 8 * b * u * B)
    (hCp : |Cp| ≤ 4 * a * B ^ 2) (hCq : |Cq| ≤ 4 * b * B ^ 2)
    (hct : |ct - Cp| ≤ 64 * (a : ℝ) ^ 2 * u * B ^ 2) (hcs : |cs - Cq| ≤ 64 * (b : ℝ) ^ 2 * u * B ^ 2)
    (hC : |Cq + Cp + (Mpx - Mqx) * (Mpy - Mqy) * b * a / ((a : ℝ) + b)| ≤ 4 * ((a : ℝ) + b) * B ^ 2) :
    |M.fl (M.fl (cs + ct)
        + M.fl (M.fl (M.fl (M.fl (M.fl (mtx - msx) * M.fl (mty - msy)) * b) * a) / ((a : ℝ) + b)))
      - (Cq + Cp + (Mpx - Mqx) * (Mpy - Mqy) * b * a / ((a : ℝ) + b))|
      ≤ 64 * ((a : ℝ) + b) ^ 2 * u * B ^ 2 := by
  obtain ⟨hu, hB, F1, -, F4, -, -, htB2, hk32, -, hB2⟩ := S.facts hN
  push_cast at F1 hk32
  have hB0 := hB.le
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hab : ((a : ℝ) + b) / 2 ≤ a * b := by
    have := mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hb'); linarith
  have hw0 : 0 ≤ u * B ^ 2 := by positivity
  have G1 : ((a : ℝ) + b) * (u * B ^ 2) ≤ B ^ 2 / 2 ^ 21 := by
    have := mul_le_mul_of_nonneg_right F1 hB0; linarith only [this]
  have hB2' : 0 ≤ B ^ 2 := sq_nonneg B
  have htB2' : tiny ≤ B ^ 2 := by linarith only [htB2, hB2']
  have huB2 : u * B ^ 2 ≤ B ^ 2 / 2 ^ 53 := by
    have := mul_le_mul_of_nonneg_right F4 hB0; linarith only [this]
  -- the differences of the means, and their product
  have hdx := M.diff_error S hN hpx hqx (by
    have : (mtx - msx) - (Mpx - Mqx) = (mtx - Mpx) - (msx - Mqx) := by ring
    rw [this]; have := abs_sub (mtx - Mpx) (msx - Mqx); push_cast; linarith)
  have hdy := M.diff_error S hN hpy hqy (by
    have : (mty - msy) - (Mpy - Mqy) = (mty - Mpy) - (msy - Mqy) := by ring
    rw [this]; have := abs_sub (mty - Mpy) (msy - Mqy); push_cast; linarith)
  have hDx : |Mpx - Mqx| ≤ 2 * B := by have := abs_sub Mpx Mqx; linarith
  have hDy : |Mpy - Mqy| ≤ 2 * B := by have := abs_sub Mpy Mqy; linarith
  have hP1 := M.prod_error S hN hDx hDy hdx hdy
  push_cast at hP1
  set D := (Mpx - Mqx) * (Mpy - Mqy)
  set n : ℝ := (a : ℝ) + b with hn
  set w := u * B ^ 2 with hw
  have hn2 : 2 ≤ n := by linarith only [ha', hb', hn]
  have habn : (a : ℝ) * b ≤ n * n := by nlinarith
  have hsqn : (a : ℝ) ^ 2 + b ^ 2 ≤ n * n := by nlinarith
  have hnG : n * (n * w) ≤ n * (B ^ 2 / 2 ^ 21) := mul_le_mul_of_nonneg_left G1 (by linarith)
  clear_value n w
  have hD : |D| ≤ 4 * B ^ 2 := by
    simp only [D]; rw [abs_mul]
    have := mul_le_mul hDx hDy (abs_nonneg _) (by positivity); linarith only [this]
  -- times the source's count, then the target's
  have hnw : (33 * n + 18) * w ≤ 4 * B ^ 2 / 4 := by linarith only [G1, huB2, hB2']
  have hbB : (b : ℝ) * B ^ 2 ≤ 2 ^ 32 * 2 ^ 800 :=
    mul_le_mul (by linarith) hB2 (by positivity) (by positivity)
  have hP2 := M.round_count hP1 hD hnw (by linarith only [htB2', hB2']) hb' (by linarith only [hbB])
  have hDb : |D * b| ≤ b * (4 * B ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b), mul_comm]; gcongr
  have he2 : (b : ℝ) * ((33 * n + 18) * w) + 3 * u * (b * (4 * B ^ 2))
      ≤ b * (4 * B ^ 2) / 4 := by
    have h1 : (b : ℝ) * ((33 * n + 18) * w) ≤ b * (B ^ 2 / 2 ^ 15) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith only [G1, huB2, hB2']
    have h2 : 3 * u * (b * (4 * B ^ 2)) ≤ b * (12 * (B ^ 2 / 2 ^ 53)) := by
      have := mul_le_mul_of_nonneg_left huB2 (by linarith : (0 : ℝ) ≤ 12 * b)
      rw [hw] at this; linarith only [this]
    have h3 : 0 ≤ (b : ℝ) * B ^ 2 := by positivity
    linarith only [h1, h2, h3]
  have habB : (a : ℝ) * (b * (4 * B ^ 2)) ≤ 2 ^ 32 * (2 ^ 32 * (4 * 2 ^ 800)) :=
    mul_le_mul (by linarith) (mul_le_mul (by linarith) (by linarith) (by positivity)
      (by positivity)) (by positivity) (by positivity)
  have htb : tiny ≤ b * (4 * B ^ 2) := by
    have := mul_le_mul_of_nonneg_right hb' (by positivity : (0 : ℝ) ≤ 4 * B ^ 2)
    linarith only [this, htB2', hB2']
  have hP3 := M.round_count hP2 hDb he2 htb ha' (by linarith only [habB])
  -- divided by the count
  have hDba : |D * b * a| ≤ a * (b * (4 * B ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a), mul_comm]; gcongr
  set e3 := (a : ℝ) * ((b : ℝ) * ((33 * n + 18) * w) + 3 * u * (b * (4 * B ^ 2)))
    + 3 * u * (a * (b * (4 * B ^ 2)))
  have he3 : e3 = a * b * ((33 * n + 42) * w) := by simp only [e3]; rw [hw]; ring
  have he3' : e3 ≤ a * (b * (4 * B ^ 2)) := by
    rw [he3]
    have : (33 * n + 42) * w ≤ 4 * B ^ 2 := by linarith only [G1, huB2, hB2']
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ a * b)
    linarith only [this]
  have hnt : n * tiny ≤ a * (b * (4 * B ^ 2)) := by
    have : n * tiny ≤ n * B ^ 2 := by gcongr
    have : n * B ^ 2 ≤ 2 * (a * b) * B ^ 2 := by
      have := mul_le_mul_of_nonneg_right hab hB2'; linarith only [this]
    linarith only [‹n * tiny ≤ _›, this, hB2', mul_nonneg (by positivity : (0 : ℝ) ≤ a * b) hB2']
  have hP4 := M.round_div hP3 hDba he3' hnt (by linarith only [hn2]) (by linarith only [habB])
  have hP4' : e3 / n + 3 * u * (a * (b * (4 * B ^ 2))) / n ≤ 60 * (a * b * w) := by
    rw [he3, ← add_div, div_le_iff₀ (by linarith only [hn2])]
    have h0 : 0 ≤ (a : ℝ) * b * w := by positivity
    have h1 : 0 ≤ (27 * n - 54) * (a * b * w) := mul_nonneg (by linarith only [hn2]) h0
    have h2 : 3 * u * (a * (b * (4 * B ^ 2))) = 12 * (a * b * w) := by rw [hw]; ring
    rw [h2]; linarith only [h1]
  -- the two co-moments, added, and the final addition
  have hcsum : |(cs + ct) - (Cq + Cp)| ≤ 64 * ((a : ℝ) ^ 2 + b ^ 2) * w := by
    have : (cs + ct) - (Cq + Cp) = (cs - Cq) + (ct - Cp) := by ring
    rw [this]
    have := abs_add_le (cs - Cq) (ct - Cp)
    rw [hw]; linarith only [this, hcs, hct]
  have hCqp : |Cq + Cp| ≤ 4 * n * B ^ 2 := by
    have := abs_add_le Cq Cp; rw [hn]; linarith only [this, hCp, hCq]
  have hsq : 64 * ((a : ℝ) ^ 2 + b ^ 2) * w ≤ 4 * n * B ^ 2 / 4 := by
    have h1 := mul_le_mul_of_nonneg_right hsqn hw0
    have h2 : 0 ≤ n * B ^ 2 := by positivity
    linarith only [h1, hnG, h2]
  have hnt1 : tiny ≤ 4 * n * B ^ 2 := by
    have : B ^ 2 ≤ n * B ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n by linarith) hB2'; linarith
    linarith only [this, htB2', hB2']
  have hnB : n * B ^ 2 ≤ 2 ^ 32 * 2 ^ 800 := mul_le_mul hk32 hB2 hB2' (by positivity)
  have hcs' := M.round_count (c := 1) (by simpa using hcsum) (by simpa using hCqp)
    (by simpa using hsq) hnt1 le_rfl (by linarith only [hnB])
  simp only [mul_one, one_mul] at hcs'
  set Cs := M.fl (cs + ct)
  set P4 := M.fl (M.fl (M.fl (M.fl (M.fl (mtx - msx) * M.fl (mty - msy)) * b) * a) / n)
  have hfe : |(Cs + P4) - (Cq + Cp + D * b * a / n)|
      ≤ 64 * ((a : ℝ) ^ 2 + b ^ 2) * w + 3 * u * (4 * n * B ^ 2) + 60 * (a * b * w) := by
    have : (Cs + P4) - (Cq + Cp + D * b * a / n) = (Cs - (Cq + Cp)) + (P4 - D * b * a / n) := by
      ring
    rw [this]
    have := abs_add_le (Cs - (Cq + Cp)) (P4 - D * b * a / n)
    linarith only [this, hcs', hP4, hP4']
  have h12 : 3 * u * (4 * n * B ^ 2) = 12 * (n * w) := by rw [hw]; ring
  have hnab : n * w ≤ 2 * (a * b * w) := by
    have := mul_le_mul_of_nonneg_right hab hw0; linarith only [this]
  have hfe' : 64 * ((a : ℝ) ^ 2 + b ^ 2) * w + 3 * u * (4 * n * B ^ 2) + 60 * (a * b * w)
      ≤ 4 * n * B ^ 2 / 4 := by
    have h1 := mul_le_mul_of_nonneg_right habn hw0
    have h2 := mul_le_mul_of_nonneg_right hsqn hw0
    have h3 : 0 ≤ n * B ^ 2 := by positivity
    have h4 : n * w ≤ B ^ 2 / 2 ^ 21 := G1
    have h5 : B ^ 2 ≤ n * B ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n by linarith) hB2'; linarith
    rw [h12]; linarith only [h1, h2, h3, hnG, h4, h5]
  have hfin := M.round_count (c := 1) (by simpa using hfe) (by simpa using hC)
    (by simpa using hfe') hnt1 le_rfl (by linarith only [hnB])
  simp only [mul_one, one_mul] at hfin
  have : 64 * n ^ 2 * u * B ^ 2 = 64 * ((a : ℝ) ^ 2 + b ^ 2) * w + 128 * (a * b * w) := by
    rw [hw, hn]; ring
  rw [this]
  have h0 : 0 ≤ (a : ℝ) * b * w := by positivity
  linarith only [hfin, h12, hnab, h0]

/-- **Chan's merge keeps the invariant.** -/
theorem StdModel.chan_good {t s : WState} {ps qs : List (ℝ × ℝ)}
    (ht : Good B t ps) (hs : Good B s qs) (hb : Bounded B (ps ++ qs))
    (hN : ps.length + qs.length ≤ N) : Good B (M.chan t s) (ps ++ qs) := by
  obtain ⟨htn, htx, hty, htc⟩ := ht
  obtain ⟨hsn, hsx, hsy, hsc⟩ := hs
  by_cases h0 : t.n = 0
  · have : ps = [] := List.length_eq_zero_iff.mp (htn ▸ h0)
    subst this
    rw [StdModel.chan, ite_eq_left h0, List.nil_append]
    exact ⟨hsn, hsx, hsy, hsc⟩
  by_cases h1 : s.n = 0
  · have : qs = [] := List.length_eq_zero_iff.mp (hsn ▸ h1)
    subst this
    rw [StdModel.chan, ite_eq_right h0, ite_eq_left h1, List.append_nil]
    exact ⟨htn, htx, hty, htc⟩
  have hp : ps ≠ [] := by intro h; simp [h] at htn; exact h0 htn
  have hq : qs ≠ [] := by intro h; simp [h] at hsn; exact h1 hsn
  obtain ⟨hbp, hbq⟩ := Bounded.append.mp hb
  have hB0 := S.B_pos.le
  have ha : 1 ≤ ps.length := List.length_pos_iff.mpr hp
  have hb1 : 1 ≤ qs.length := List.length_pos_iff.mpr hq
  rw [htn] at htx hty htc
  rw [hsn] at hsx hsy hsc
  rw [StdModel.chan, ite_eq_right h0, ite_eq_right h1]
  refine ⟨by simp [htn, hsn], ?_, ?_, ?_⟩ <;> simp only [htn, hsn]
  · rw [mx_append hp hq]; push_cast
    exact M.chan_mean S ha hb1 hN (abs_mx_le hbp hB0) (abs_mx_le hbq hB0) htx hsx
  · rw [my_append hp hq]; push_cast
    exact M.chan_mean S ha hb1 hN (abs_my_le hbp hB0) (abs_my_le hbq hB0) hty hsy
  · rw [comoment_append hp hq]; push_cast
    have hC := abs_comoment_le hb hB0
    rw [comoment_append hp hq] at hC
    simp only [List.length_append] at hC; push_cast at hC
    exact M.chan_comoment S ha hb1 hN (abs_mx_le hbp hB0) (abs_mx_le hbq hB0)
      (abs_my_le hbp hB0) (abs_my_le hbq hB0) htx hsx hty hsy (abs_comoment_le hbp hB0)
      (abs_comoment_le hbq hB0) htc hsc hC

/-- Welford's update over a list keeps the invariant. -/
theorem StdModel.welford_good (ps : List (ℝ × ℝ)) (hb : Bounded B ps) (hN : ps.length ≤ N) :
    Good B (ps.foldl M.welfordStep .empty) ps := by
  induction ps using List.reverseRecOn with
  | nil => exact good_empty B
  | append_singleton ps p ih =>
    simp only [List.length_append, List.length_singleton] at hN
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact M.welfordStep_good S (ih (Bounded.append.mp hb).1 (by omega)) hb hN

/-- **Any plan of Welford updates and Chan merges keeps the invariant.** -/
theorem StdModel.plan_good (P : Plan) (hb : Bounded B P.pairs) (hN : P.pairs.length ≤ N) :
    Good B (M.run P) P.pairs := by
  induction P with
  | seq ps => exact M.welford_good S ps hb hN
  | merge t s iht ihs =>
    simp only [Plan.pairs, List.length_append] at hb hN
    obtain ⟨hbt, hbs⟩ := Bounded.append.mp hb
    exact M.chan_good S (iht hbt (by omega)) (ihs hbs (by omega)) hb hN

end

end FloatBounds

end
