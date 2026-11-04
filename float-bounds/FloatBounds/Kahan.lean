module

public import FloatBounds.Tree

/-!
# Kahan's compensated sum (#444, `COMPENSATED`)

Polars's in-memory engine sums a group's doubles with Kahan's compensated sum
(`KahanSum::add_assign` in `polars-utils`, polars-sum-float): from
`(s, c) = (0, 0)`, each value `x` takes

    y = fl(x − c),  t = fl(s + y),  c = fl(fl(t − s) − y),  s = t,

and the result is `s`. It is no tree of additions (duckdb-kahan-sum has a
result outside every tree sum), so `TreeSum` does not cover it.

`Rnd.kahan_near`: for `n ≤ 2³²` values that are doubles, the result is within
`γ n · Σ (|xᵢ| + τ)` of the exact sum, the bound of a tree sum, for every
`Rnd`. So the absolute bound (`τ = tiny`) and, without the underflow term,
the relative one for values of one sign hold of it as of a tree sum.

Kahan's own bound is `(2u + O(n u²)) · Σ |xᵢ|` (Higham, §4.3, after Knuth),
far below `γ n` for large `n`; this proof is cruder: each step after the
second adds at most `2u · |x| + 3u · τ + 14 u² · A` to the error of `s − c`,
`A` the magnitude so far, and the last step `u · |S| + …`. The first step is
exact and the second rounds no `y`, which keeps three values within `γ 3`.
-/

@[expose] public section

namespace FloatBounds

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b); rwa [abs_neg, ← sub_eq_add_neg] at this

namespace Rnd

variable (R : Rnd)

/-- One step of Kahan's compensated sum: the running sum and the
compensation `(s, c)` take the value `x`. -/
noncomputable def kstep (p : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  (R.fl (p.1 + R.fl (x - p.2)), R.fl (R.fl (R.fl (p.1 + R.fl (x - p.2)) - p.1) - R.fl (x - p.2)))

/-- Kahan's compensated sum of `xs` in list order, from `(0, 0)`: the
running sum at the end. -/
noncomputable def kahan (xs : List ℝ) : ℝ := (xs.foldl R.kstep (0, 0)).1

variable {R}

theorem G_sub {a b : ℝ} (ha : R.G a) (hb : R.G b) : R.G (a - b) := by
  rw [sub_eq_add_neg]; exact R.G_add _ _ ha (R.G_neg _ hb)

/-- The middle steps: the compensation stays within `4u · A'`, and `s − c`
moves from the exact sum by at most `Ey + u(|x| + τ) + uτ + 10u² · A'`, where
`Ey` bounds the rounding of `x − c` and `A' = A + |x| + τ`. -/
theorem kstep_mid {s c S A x Ey : ℝ} (hs : R.G s) (hc : R.G c) (hx : R.G x)
    (hA : 0 ≤ A) (hS : |S| ≤ A) (hcA : |c| ≤ 4 * u * A) (hF : |s - c - S| ≤ 6 * u * A)
    (hEy : |R.fl (x - c) - (x - c)| ≤ Ey) (hEy' : Ey ≤ u * (|x| + |c| + R.τ))
    (hov : 2 * (A + |x| + R.τ) ≤ maxFinite) :
    |(R.kstep (s, c) x).2| ≤ 4 * u * (A + |x| + R.τ) ∧
    |(R.kstep (s, c) x).1 - (R.kstep (s, c) x).2 - (S + x)|
      ≤ |s - c - S| + Ey + u * (|x| + R.τ) + u * R.τ + 10 * u ^ 2 * (A + |x| + R.τ) := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hτ := R.τ_nonneg
  have hX := abs_nonneg x
  have hc0 := abs_nonneg c
  have hu1 : u ≤ 1 / 100 := le_trans hu' (by norm_num)
  generalize hXd : |x| = X at *
  generalize hτd : R.τ = τ at *
  have hA' : 0 ≤ A + X + τ := by linarith
  generalize hA'd : A + X + τ = A' at *
  have hk : R.kstep (s, c) x = (R.fl (s + R.fl (x - c)),
      R.fl (R.fl (R.fl (s + R.fl (x - c)) - s) - R.fl (x - c))) := rfl
  rw [hk]; dsimp only
  generalize hy : R.fl (x - c) = y at *
  have hGy : R.G y := hy ▸ R.G_fl _ (G_sub hx hc)
  generalize ht : R.fl (s + y) = t
  have hGt : R.G t := ht ▸ R.G_fl _ (R.G_add _ _ hs hGy)
  generalize hd : R.fl (t - s) = d
  have hGd : R.G d := hd ▸ R.G_fl _ (G_sub hGt hs)
  -- products used below
  have hA0 := hA
  have eA1 : u * A' = u * A + u * X + u * τ := by rw [← hA'd]; ring
  have eA2 : u ^ 2 * A' = u ^ 2 * A + u ^ 2 * X + u ^ 2 * τ := by rw [← hA'd]; ring
  have n1 : 0 ≤ u * X := by positivity
  have n2 : 0 ≤ u * τ := by positivity
  have n3 : 0 ≤ u * A := by positivity
  have n4 : 0 ≤ u ^ 2 * X := by positivity
  have n5 : 0 ≤ u ^ 2 * τ := by positivity
  have n6 : 0 ≤ u ^ 2 * A := by positivity
  have pA : u ^ 2 * A ≤ u ^ 2 * A' := by linarith
  have pu : u * (u ^ 2 * A') ≤ 1 / 100 * (u ^ 2 * A') :=
    mul_le_mul_of_nonneg_right hu1 (by positivity)
  have pu' : u * (u * A') ≤ 1 / 100 * (u * A') :=
    mul_le_mul_of_nonneg_right hu1 (by positivity)
  have p3 : u * (u ^ 2 * A) ≤ 1 / 100 * (u ^ 2 * A') :=
    le_trans (mul_le_mul_of_nonneg_left pA hu.le) pu
  have huA0 : u * A ≤ 1 / 100 * A := mul_le_mul_of_nonneg_right hu1 hA
  have huX : u * X ≤ 1 / 100 * X := mul_le_mul_of_nonneg_right hu1 hX
  have huτ : u * τ ≤ 1 / 100 * τ := mul_le_mul_of_nonneg_right hu1 hτ
  have hu2A : u * (u * A) ≤ 1 / 100 * (u * A) := mul_le_mul_of_nonneg_right hu1 n3
  -- `y`
  have hEy0 : 0 ≤ Ey := le_trans (abs_nonneg _) hEy
  have hEy2 : Ey ≤ u * (X + τ) + 4 * u ^ 2 * A := by
    have := mul_le_mul_of_nonneg_left hcA hu.le; linarith
  have hyb : |y| ≤ X + |c| + Ey := by
    have := abs_sub_abs_le_abs_sub y (x - c)
    have := abs_sub_le_add x c
    linarith
  -- `t`
  have hsy : |s + y| ≤ A + X + 6 * u * A + Ey := by
    have e : s + y = (S + x) + (s - c - S) + (y - (x - c)) := by ring
    rw [e]
    have := abs_add_le ((S + x) + (s - c - S)) (y - (x - c))
    have := abs_add_le (S + x) (s - c - S)
    have := abs_add_le S x
    linarith
  have hsyM : |s + y| ≤ maxFinite := by linarith
  have het := R.err (s + y) (R.G_add _ _ hs hGy) hsyM
  rw [ht, hτd] at het
  have het2 : |t - (s + y)| ≤ u * A' + 7 * u ^ 2 * A' := by
    have h1 := mul_le_mul_of_nonneg_left hsy hu.le
    have h2 := mul_le_mul_of_nonneg_left hEy2 hu.le
    linarith
  -- `d`
  have htsb : |t - s| ≤ |y| + |t - (s + y)| := by
    have e : t - s = y + (t - (s + y)) := by ring
    rw [e]; exact abs_add_le _ _
  have htsM : |t - s| ≤ maxFinite := by linarith
  have hed := R.err (t - s) (G_sub hGt hs) htsM
  rw [hd, hτd] at hed
  have hed2 : |d - (t - s)| ≤ u * (X + τ) + 7 * u ^ 2 * A' := by
    have h1 := mul_le_mul_of_nonneg_left htsb hu.le
    have h2 := mul_le_mul_of_nonneg_left hyb hu.le
    have h3 := mul_le_mul_of_nonneg_left hEy2 hu.le
    have h4 := mul_le_mul_of_nonneg_left het2 hu.le
    have h5 := mul_le_mul_of_nonneg_left hcA hu.le
    linarith
  -- `c'`
  have hdy : |d - y| ≤ |t - (s + y)| + |d - (t - s)| := by
    have e : d - y = (t - (s + y)) + (d - (t - s)) := by ring
    rw [e]; exact abs_add_le _ _
  have hdyM : |d - y| ≤ maxFinite := by linarith
  have hec := R.err (d - y) (G_sub hGd hGy) hdyM
  rw [hτd] at hec
  have hec2 : |R.fl (d - y) - (d - y)| ≤ u * τ + 3 * u ^ 2 * A' := by
    have h1 := mul_le_mul_of_nonneg_left hdy hu.le
    have h2 := mul_le_mul_of_nonneg_left het2 hu.le
    have h3 := mul_le_mul_of_nonneg_left hed2 hu.le
    linarith
  constructor
  · have e : R.fl (d - y) = (t - (s + y)) + (d - (t - s)) + (R.fl (d - y) - (d - y)) := by ring
    rw [e]
    have := abs_add_le ((t - (s + y)) + (d - (t - s))) (R.fl (d - y) - (d - y))
    have := abs_add_le (t - (s + y)) (d - (t - s))
    linarith
  · have e : t - R.fl (d - y) - (S + x) = (s - c - S) + (y - (x - c)) - (d - (t - s))
        - (R.fl (d - y) - (d - y)) := by ring
    rw [e]
    have := abs_sub_le_add ((s - c - S) + (y - (x - c)) - (d - (t - s))) (R.fl (d - y) - (d - y))
    have := abs_sub_le_add ((s - c - S) + (y - (x - c))) (d - (t - s))
    have := abs_add_le (s - c - S) (y - (x - c))
    linarith

/-- The last step: the result moves from the exact sum by at most
`Ey + u(|S + x| + τ) + 8u² · A'`. -/
theorem kstep_last {s c S A x Ey : ℝ} (hs : R.G s) (hc : R.G c) (hx : R.G x)
    (hA : 0 ≤ A) (hS : |S| ≤ A) (hcA : |c| ≤ 4 * u * A) (hF : |s - c - S| ≤ 6 * u * A)
    (hEy : |R.fl (x - c) - (x - c)| ≤ Ey) (hEy' : Ey ≤ u * (|x| + |c| + R.τ))
    (hov : 2 * (A + |x| + R.τ) ≤ maxFinite) :
    |(R.kstep (s, c) x).1 - (S + x)|
      ≤ |s - c - S| + Ey + u * (|S + x| + R.τ) + 8 * u ^ 2 * (A + |x| + R.τ) := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hτ := R.τ_nonneg
  have hX := abs_nonneg x
  have hc0 := abs_nonneg c
  have hu1 : u ≤ 1 / 100 := le_trans hu' (by norm_num)
  have hSx : |S + x| ≤ A + |x| := by have := abs_add_le S x; linarith
  generalize hXd : |x| = X at *
  generalize hτd : R.τ = τ at *
  have hA' : 0 ≤ A + X + τ := by linarith
  generalize hA'd : A + X + τ = A' at *
  have hk : (R.kstep (s, c) x).1 = R.fl (s + R.fl (x - c)) := rfl
  rw [hk]
  generalize hy : R.fl (x - c) = y at *
  have hGy : R.G y := hy ▸ R.G_fl _ (G_sub hx hc)
  have eA2 : u ^ 2 * A' = u ^ 2 * A + u ^ 2 * X + u ^ 2 * τ := by rw [← hA'd]; ring
  have n4 : 0 ≤ u ^ 2 * X := by positivity
  have n5 : 0 ≤ u ^ 2 * τ := by positivity
  have n6 : 0 ≤ u ^ 2 * A := by positivity
  have p3 : u * (u ^ 2 * A) ≤ 1 / 100 * (u ^ 2 * A') :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hu.le)
      (mul_le_mul_of_nonneg_right hu1 (by positivity))
  have huA0 : u * A ≤ 1 / 100 * A := mul_le_mul_of_nonneg_right hu1 hA
  have huX : u * X ≤ 1 / 100 * X := mul_le_mul_of_nonneg_right hu1 hX
  have huτ : u * τ ≤ 1 / 100 * τ := mul_le_mul_of_nonneg_right hu1 hτ
  have hu2A : u * (u * A) ≤ 1 / 100 * (u * A) :=
    mul_le_mul_of_nonneg_right hu1 (by positivity)
  have hEy0 : 0 ≤ Ey := le_trans (abs_nonneg _) hEy
  have hEy2 : Ey ≤ u * (X + τ) + 4 * u ^ 2 * A := by
    have := mul_le_mul_of_nonneg_left hcA hu.le; linarith
  have hsy : |s + y| ≤ |S + x| + 6 * u * A + Ey := by
    have e : s + y = (S + x) + (s - c - S) + (y - (x - c)) := by ring
    rw [e]
    have := abs_add_le ((S + x) + (s - c - S)) (y - (x - c))
    have := abs_add_le (S + x) (s - c - S)
    linarith
  have hsyM : |s + y| ≤ maxFinite := by linarith
  have het := R.err (s + y) (R.G_add _ _ hs hGy) hsyM
  rw [hτd] at het
  have h1 := mul_le_mul_of_nonneg_left hsy hu.le
  have h2 := mul_le_mul_of_nonneg_left hEy2 hu.le
  have e : R.fl (s + y) - (S + x) = (s - c - S) + (y - (x - c)) + (R.fl (s + y) - (s + y)) := by
    ring
  rw [e]
  have := abs_add_le ((s - c - S) + (y - (x - c))) (R.fl (s + y) - (s + y))
  have := abs_add_le (s - c - S) (y - (x - c))
  linarith

theorem mag_eq' (xs : List ℝ) : R.mag xs = (xs.map abs).sum + xs.length * R.τ := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [mag_cons, ih, List.map_cons, List.sum_cons, List.length_cons]; push_cast; ring

theorem abs_sum_le_absSum (xs : List ℝ) : |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.sum_cons, List.map_cons]; have := abs_add_le x xs.sum; linarith

/-- The middle steps, folded: from a state whose compensation is within
`4u · A` and whose `s − c` is within `W` of the exact sum `S` of the values
so far `ps`, the steps over `mid` add at most
`2u · Σ |mid| + 3u · |mid| · τ + 14 |mid| u² · A'` to `W`. -/
theorem kfold_mid (mid : List ℝ) :
    ∀ (ps : List ℝ) (p : ℝ × ℝ) (W : ℝ), (∀ x ∈ mid, R.G x) → R.G p.1 → R.G p.2 →
      |p.2| ≤ 4 * u * R.mag ps → |p.1 - p.2 - ps.sum| ≤ W →
      W ≤ 2 * u * (ps.map abs).sum + 3 * u * ps.length * R.τ
        + 14 * ps.length * u ^ 2 * R.mag ps →
      14 * ((ps.length + mid.length : ℕ) : ℝ) * u ≤ 1 →
      2 * R.mag (ps ++ mid) ≤ maxFinite →
      R.G (mid.foldl R.kstep p).1 ∧ R.G (mid.foldl R.kstep p).2 ∧
      |(mid.foldl R.kstep p).2| ≤ 4 * u * R.mag (ps ++ mid) ∧
      |(mid.foldl R.kstep p).1 - (mid.foldl R.kstep p).2 - (ps ++ mid).sum|
        ≤ W + 2 * u * (mid.map abs).sum + 3 * u * mid.length * R.τ
          + 14 * mid.length * u ^ 2 * R.mag (ps ++ mid) := by
  induction mid with
  | nil =>
    intro ps p W _ h1 h2 h3 h4 _ _ _
    simp only [List.foldl_nil, List.append_nil, List.map_nil, List.sum_nil, List.length_nil]
    refine ⟨h1, h2, h3, by simpa using h4⟩
  | cons x mid ih =>
    intro ps p W hG h1 h2 h3 h4 hW hn hov
    obtain ⟨hu, hu', -, -, -⟩ := fpFacts
    have hτ := R.τ_nonneg
    have hA := R.mag_nonneg ps
    have hX := abs_nonneg x
    have hx : R.G x := hG x (by simp)
    have hmag : R.mag (ps ++ x :: mid) = R.mag ps + |x| + R.τ + R.mag mid := by
      rw [R.mag_append, mag_cons]; ring
    have hmid := R.mag_nonneg mid
    have hS : |ps.sum| ≤ R.mag ps := R.abs_sum_le_mag ps
    have hk : 14 * (ps.length : ℝ) * u ≤ 1 := by
      simp only [List.length_cons] at hn; push_cast at hn
      have : (0 : ℝ) ≤ 14 * ((mid.length : ℝ) + 1) * u := by positivity
      linarith
    have hP := mag_eq' (R := R) ps
    have hPn : 0 ≤ (ps.map abs).sum := List.sum_nonneg (by simp)
    have hW6 : W ≤ 6 * u * R.mag ps := by
      have a : 14 * ps.length * u ^ 2 * R.mag ps ≤ u * R.mag ps := by
        have := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ u * R.mag ps)
        linarith
      have b : 2 * u * (ps.map abs).sum + 3 * u * ps.length * R.τ ≤ 3 * u * R.mag ps := by
        rw [hP]; have : 0 ≤ u * (ps.map abs).sum := by positivity
        linarith
      have : 0 ≤ u * R.mag ps := by positivity
      linarith
    have hF : |p.1 - p.2 - ps.sum| ≤ 6 * u * R.mag ps := le_trans h4 hW6
    have hov1 : 2 * (R.mag ps + |x| + R.τ) ≤ maxFinite := by
      rw [hmag] at hov; linarith
    have hxc : |x - p.2| ≤ maxFinite := by
      have := abs_sub_le_add x p.2
      have : 4 * u * R.mag ps ≤ R.mag ps := by
        have : u ≤ 1 / 4 := le_trans hu' (by norm_num)
        nlinarith
      linarith
    have hEy := R.err (x - p.2) (G_sub hx h2) hxc
    have hEy' : u * (|x - p.2| + R.τ) ≤ u * (|x| + |p.2| + R.τ) := by
      have := abs_sub_le_add x p.2
      gcongr
    have step := kstep_mid (S := ps.sum) h1 h2 hx hA hS h3 hF hEy hEy' hov1
    -- the next state
    have hq1 : R.G (R.kstep p x).1 := R.G_fl _ (R.G_add _ _ h1 (R.G_fl _ (G_sub hx h2)))
    have hq2 : R.G (R.kstep p x).2 :=
      R.G_fl _ (G_sub (R.G_fl _ (G_sub hq1 h1)) (R.G_fl _ (G_sub hx h2)))
    rw [List.foldl_cons]
    generalize R.kstep p x = q at step hq1 hq2 ⊢
    have hmx : R.mag (ps ++ [x]) = R.mag ps + |x| + R.τ := by
      rw [R.mag_append]; simp; ring
    have hEyb : u * (|x - p.2| + R.τ) ≤ u * (|x| + R.τ) + 4 * u ^ 2 * R.mag ps := by
      have := mul_le_mul_of_nonneg_left h3 hu.le
      linarith
    have hq4 : |q.1 - q.2 - (ps ++ [x]).sum|
        ≤ W + 2 * u * |x| + 3 * u * R.τ + 14 * u ^ 2 * R.mag (ps ++ [x]) := by
      rw [List.sum_append, List.sum_singleton, hmx]
      have : 0 ≤ u ^ 2 * (|x| + R.τ) := by positivity
      have := step.2
      linarith
    have hq3 : |q.2| ≤ 4 * u * R.mag (ps ++ [x]) := by rw [hmx]; exact step.1
    have hW'b : W + 2 * u * |x| + 3 * u * R.τ + 14 * u ^ 2 * R.mag (ps ++ [x])
        ≤ 2 * u * ((ps ++ [x]).map abs).sum + 3 * u * (ps ++ [x]).length * R.τ
          + 14 * (ps ++ [x]).length * u ^ 2 * R.mag (ps ++ [x]) := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, List.length_append, List.length_cons, List.length_nil]
      push_cast
      have : 14 * ps.length * u ^ 2 * R.mag ps ≤ 14 * ps.length * u ^ 2 * R.mag (ps ++ [x]) := by
        rw [hmx]; gcongr; linarith
      linarith
    have := ih (ps ++ [x]) q _ (fun y hy => hG y (by simp [hy])) hq1 hq2 hq3 hq4 hW'b
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hn ⊢
          push_cast at hn ⊢; linarith)
      (by simpa using hov)
    simp only [List.append_assoc, List.singleton_append] at this
    refine ⟨this.1, this.2.1, this.2.2.1, le_trans this.2.2.2 ?_⟩
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    have hm2 : R.mag (ps ++ [x]) ≤ R.mag (ps ++ x :: mid) := by rw [hmx, hmag]; linarith
    have : 14 * u ^ 2 * R.mag (ps ++ [x]) ≤ 14 * u ^ 2 * R.mag (ps ++ x :: mid) := by gcongr
    linarith

/-- The first step is exact: a double added to `(0, 0)`. -/
theorem kstep_zero {x : ℝ} (hx : R.fl x = x) : R.kstep (0, 0) x = (x, 0) := by
  simp [kstep, hx, R.zero]

theorem gamma_ge {n : ℕ} (hn : (n : ℝ) * u < 1) : n * u ≤ gamma n := by
  have hu := u_pos
  unfold gamma
  rw [le_div_iff₀ (by linarith)]
  have : 0 ≤ (n : ℝ) * u := by positivity
  nlinarith

theorem nu_small {n : ℕ} (hn : (n : ℝ) ≤ 2 ^ 32) : 14 * (n : ℝ) * u ≤ 1 := by
  have hu := fpFacts.u_le
  have hu0 := u_pos
  have : (n : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := mul_le_mul hn hu hu0.le (by norm_num)
  have : (2 : ℝ) ^ 32 * (1 / 2 ^ 53) ≤ 1 / 14 := by norm_num
  linarith

/-- The arithmetic of the last step: what the steps add up to is within
`γ n · (P + n τ)`. -/
theorem kahan_final {n : ℕ} {P τ E : ℝ} (hn3 : 3 ≤ n) (hn : (n : ℝ) ≤ 2 ^ 32) (hP : 0 ≤ P)
    (hτ : 0 ≤ τ)
    (hE : E ≤ (n - 1) * u * P + (3 * n - 5) * u * τ + 14 * n * u ^ 2 * (P + n * τ)) :
    E ≤ gamma n * (P + n * τ) := by
  have hu := u_pos
  have hu' := fpFacts.u_le
  have hnu := nu_small hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlt : (n : ℝ) * u < 1 := by linarith
  have hg := gamma_ge hlt
  have a1 : 14 * n * u * (u * P) ≤ 1 * (u * P) :=
    mul_le_mul_of_nonneg_right hnu (by positivity)
  have h14 : 14 * u ≤ 1 / 2 := by
    have : (14 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 := by norm_num
    linarith
  have a2 : (3 * (n : ℝ) - 5) + 14 * n ^ 2 * u ≤ n ^ 2 := by
    have : 14 * u * (n : ℝ) ^ 2 ≤ 1 / 2 * n ^ 2 := mul_le_mul_of_nonneg_right h14 (by positivity)
    nlinarith [sq_nonneg ((n : ℝ) - 3)]
  have a3 := mul_le_mul_of_nonneg_right a2 (by positivity : 0 ≤ u * τ)
  have hPn : 0 ≤ P + n * τ := by positivity
  have := mul_le_mul_of_nonneg_right hg hPn
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Kahan's compensated sum** of `n ≤ 2³²` doubles is within
`γ n · Σ (|xᵢ| + τ)` of the exact sum. -/
theorem kahan_near {xs : List ℝ} (hx : ∀ x ∈ xs, R.G x ∧ R.fl x = x)
    (hn : (xs.length : ℝ) ≤ 2 ^ 32) (hov : 2 * R.mag xs ≤ maxFinite) :
    R.Near xs (R.kahan xs) := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hτ := R.τ_nonneg
  have hu1 : u ≤ 1 / 100 := le_trans hu' (by norm_num)
  rcases xs with _ | ⟨x1, _ | ⟨x2, rest⟩⟩
  · simp [Near, kahan]
  · have h1 := (hx x1 (by simp)).2
    simp only [Near, kahan, List.foldl_cons, List.foldl_nil, kstep_zero h1, List.sum_cons,
      List.sum_nil, add_zero, sub_self, abs_zero]
    exact mul_nonneg (gamma_nonneg (by simp at hn ⊢; nlinarith)) (R.mag_nonneg _)
  obtain ⟨hG1, hf1⟩ := hx x1 (by simp)
  obtain ⟨hG2, hf2⟩ := hx x2 (by simp)
  have hX1 := abs_nonneg x1
  have hX2 := abs_nonneg x2
  have hA1 : R.mag [x1] = |x1| + R.τ := by simp
  have hA2 : R.mag [x1, x2] = |x1| + |x2| + 2 * R.τ := by simp; ring
  have hEy0 : |R.fl (x2 - (0 : ℝ × ℝ).2) - (x2 - (0 : ℝ × ℝ).2)| ≤ 0 := by simp [hf2]
  have hS1 : |x1| ≤ |x1| + R.τ := by linarith
  have hc0 : |(0 : ℝ)| ≤ 4 * u * (|x1| + R.τ) := by simp; positivity
  have hF0 : |x1 - 0 - x1| ≤ 6 * u * (|x1| + R.τ) := by simp; positivity
  have hEy0' : (0 : ℝ) ≤ u * (|x2| + |(0 : ℝ)| + R.τ) := by positivity
  have hmagxs := mag_eq' (R := R) (x1 :: x2 :: rest)
  rcases List.eq_nil_or_concat rest with rfl | ⟨mid, xn, rfl⟩
  · -- two values
    have hov2 : 2 * (|x1| + R.τ + |x2| + R.τ) ≤ maxFinite := by
      have := hov; simp at this; linarith
    have hl := kstep_last (S := x1) (A := |x1| + R.τ) (s := x1) (c := 0) hG1 R.G_zero hG2
      (by positivity) hS1 hc0 hF0 (by simpa using hEy0) hEy0' (by linarith)
    have hg : 2 * u ≤ gamma 2 := by
      have := gamma_ge (n := 2) (by push_cast; linarith); push_cast at this; linarith
    have key : |(R.kstep (x1, 0) x2).1 - (x1 + x2)| ≤ gamma 2 * (|x1| + |x2| + 2 * R.τ) := by
      have hS := abs_add_le x1 x2
      have h0 : |x1 - 0 - x1| = 0 := by simp
      have hP : 0 ≤ |x1| + |x2| + 2 * R.τ := by positivity
      have a := mul_le_mul_of_nonneg_right hg hP
      have b := mul_le_mul_of_nonneg_right hu1 (by positivity : 0 ≤ u * (|x1| + |x2| + 2 * R.τ))
      have c := mul_le_mul_of_nonneg_left hS hu.le
      have d : 0 ≤ u * R.τ := by positivity
      have d1 : 0 ≤ u * |x1| := by positivity
      have d2 : 0 ≤ u * |x2| := by positivity
      rw [h0] at hl
      linarith
    simpa [Near, kahan, kstep_zero hf1, hA2] using key
  -- three values or more: `x1`, `x2`, the middle `mid` and the last `xn`
  simp only [List.concat_eq_append] at hx hn hov hmagxs ⊢
  set n := (x1 :: x2 :: (mid ++ [xn])).length with hn_def
  have hnm : n = mid.length + 3 := by simp [n]
  have hGm : ∀ x ∈ mid, R.G x := fun x h => (hx x (by simp [h])).1
  obtain ⟨hGn, hfn⟩ := hx xn (by simp)
  have hXn := abs_nonneg xn
  -- the state after two steps
  have hov2 : 2 * (|x1| + R.τ + |x2| + R.τ) ≤ maxFinite := by
    have : R.mag [x1, x2] ≤ R.mag (x1 :: x2 :: (mid ++ [xn])) := by
      have e : x1 :: x2 :: (mid ++ [xn]) = [x1, x2] ++ (mid ++ [xn]) := rfl
      rw [e, R.mag_append]; linarith [R.mag_nonneg (mid ++ [xn])]
    rw [hA2] at this; linarith
  have st2 := kstep_mid (S := x1) (A := |x1| + R.τ) (s := x1) (c := 0) hG1 R.G_zero hG2
    (by positivity) hS1 hc0 hF0 (by simpa using hEy0) hEy0' (by linarith)
  have hq1 : R.G (R.kstep (x1, 0) x2).1 :=
    R.G_fl _ (R.G_add _ _ hG1 (R.G_fl _ (G_sub hG2 R.G_zero)))
  have hq2 : R.G (R.kstep (x1, 0) x2).2 :=
    R.G_fl _ (G_sub (R.G_fl _ (G_sub hq1 hG1)) (R.G_fl _ (G_sub hG2 R.G_zero)))
  generalize hqd : R.kstep (x1, 0) x2 = q at st2 hq1 hq2
  simp only [sub_zero, sub_self, abs_zero, add_zero, zero_add] at st2
  have hlen : (n : ℝ) = mid.length + 3 := by rw [hnm]; push_cast; ring
  have hnr : (n : ℝ) ≤ 2 ^ 32 := hn
  -- the middle steps
  have fold := kfold_mid mid [x1, x2] q (u * (|x2| + R.τ) + u * R.τ + 10 * u ^ 2 * R.mag [x1, x2])
    hGm hq1 hq2 (by rw [hA2]; linarith [st2.1]) (by
      simp only [List.sum_cons, List.sum_nil, add_zero, hA2]
      have := st2.2; linarith)
    (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil, hA2]
      push_cast
      have : 0 ≤ u ^ 2 * (|x1| + |x2| + 2 * R.τ) := by positivity
      have : 0 ≤ u * |x1| := by positivity
      have : 0 ≤ u * |x2| := by positivity
      have : 0 ≤ u * R.τ := by positivity
      linarith)
    (by
      have := nu_small hnr
      rw [hlen] at this
      simp only [List.length_cons, List.length_nil]; push_cast; linarith)
    (by
      have e : x1 :: x2 :: (mid ++ [xn]) = [x1, x2] ++ mid ++ [xn] := by simp
      rw [e, R.mag_append (([x1, x2] ++ mid))] at hov
      have := R.mag_nonneg [xn]
      linarith)
  obtain ⟨hr1, hr2, hr3, hr4⟩ := fold
  generalize hrd : mid.foldl R.kstep q = r at hr1 hr2 hr3 hr4
  set Am := R.mag ([x1, x2] ++ mid) with hAm
  have hAm0 : 0 ≤ Am := R.mag_nonneg _
  have hPm := mag_eq' (R := R) ([x1, x2] ++ mid)
  rw [← hAm] at hPm
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, List.length_append, List.length_cons, List.length_nil] at hPm
  push_cast at hPm
  have hPmid : 0 ≤ (mid.map abs).sum := List.sum_nonneg (by simp)
  have hA2m : R.mag [x1, x2] ≤ Am := by
    rw [hAm, R.mag_append]; linarith [R.mag_nonneg mid]
  -- `s − c` is within `6u · Am`
  have hk : 14 * ((mid.length : ℝ) + 2) * u ≤ 1 := by
    have := nu_small hnr; rw [hlen] at this; linarith only [this, hu]
  have hW : |r.1 - r.2 - ([x1, x2] ++ mid).sum|
      ≤ u * |x2| + 2 * u * R.τ + 2 * u * (mid.map abs).sum + 3 * u * mid.length * R.τ
        + 14 * ((mid.length : ℝ) + 2) * u ^ 2 * Am := by
    have : 10 * u ^ 2 * R.mag [x1, x2] ≤ 14 * u ^ 2 * Am := by
      have h0 : 0 ≤ u ^ 2 * Am := by positivity
      have h1 := mul_le_mul_of_nonneg_left hA2m (sq_nonneg u)
      linarith only [h0, h1]
    have : 14 * (mid.length : ℝ) * u ^ 2 * Am + 14 * u ^ 2 * Am
        ≤ 14 * ((mid.length : ℝ) + 2) * u ^ 2 * Am := by
      have h0 : 0 ≤ u ^ 2 * Am := by positivity
      linarith only [h0]
    linarith
  have hF6 : |r.1 - r.2 - ([x1, x2] ++ mid).sum| ≤ 6 * u * Am := by
    have : 14 * ((mid.length : ℝ) + 2) * u * (u * Am) ≤ 1 * (u * Am) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    have : 0 ≤ u * |x1| := by positivity
    have : 0 ≤ u * R.τ := by positivity
    have : 0 ≤ u * (mid.map abs).sum := by positivity
    have : u * Am = u * (|x1| + |x2| + (mid.map abs).sum) + u * (((mid.length : ℝ) + 2) * R.τ) := by
      rw [hPm]; ring
    nlinarith
  -- the last step
  have hSm : |([x1, x2] ++ mid).sum| ≤ Am := R.abs_sum_le_mag _
  have hmagn : R.mag (x1 :: x2 :: (mid ++ [xn])) = Am + |xn| + R.τ := by
    have e : x1 :: x2 :: (mid ++ [xn]) = ([x1, x2] ++ mid) ++ [xn] := by simp
    rw [e, R.mag_append, ← hAm]; simp; ring
  have hovn : 2 * (Am + |xn| + R.τ) ≤ maxFinite := by rw [← hmagn]; exact hov
  have hxc : |xn - r.2| ≤ maxFinite := by
    have := abs_sub_le_add xn r.2
    have : 4 * u * Am ≤ Am := by nlinarith
    linarith
  have hEy := R.err (xn - r.2) (G_sub hGn hr2) hxc
  have hEy' : u * (|xn - r.2| + R.τ) ≤ u * (|xn| + |r.2| + R.τ) := by
    have := abs_sub_le_add xn r.2; gcongr
  have last := kstep_last hr1 hr2 hGn hAm0 hSm hr3 hF6 hEy hEy' hovn
  have hK : R.kahan (x1 :: x2 :: (mid ++ [xn])) = (R.kstep r xn).1 := by
    rw [← hrd, ← hqd]
    simp only [kahan, List.foldl_cons, kstep_zero hf1, List.foldl_append, List.foldl_nil]
  -- adding it up
  unfold Near
  rw [hK, hmagxs]
  have hsum : (x1 :: x2 :: (mid ++ [xn])).sum = ([x1, x2] ++ mid).sum + xn := by simp; ring
  rw [hsum]
  have hPn : ((x1 :: x2 :: (mid ++ [xn])).map abs).sum
      = |x1| + |x2| + (mid.map abs).sum + |xn| := by simp; ring
  rw [hPn]
  have hSn : |([x1, x2] ++ mid).sum + xn| ≤ |x1| + |x2| + (mid.map abs).sum + |xn| := by
    have := abs_sum_le_absSum (([x1, x2] ++ mid) ++ [xn])
    have e1 : (([x1, x2] ++ mid) ++ [xn]).sum = ([x1, x2] ++ mid).sum + xn := by simp; ring
    have e2 : ((([x1, x2] ++ mid) ++ [xn]).map abs).sum
        = |x1| + |x2| + (mid.map abs).sum + |xn| := by simp; ring
    rw [e1, e2] at this; exact this
  have hEyb : u * (|xn - r.2| + R.τ) ≤ u * (|xn| + R.τ) + 4 * u ^ 2 * Am := by
    have := mul_le_mul_of_nonneg_left hr3 hu.le; linarith
  have hQ : |x2| + 2 * (mid.map abs).sum + |xn|
      ≤ ((n : ℝ) - 2) * (|x1| + |x2| + (mid.map abs).sum + |xn|) := by
    rcases eq_or_ne mid [] with rfl | hne
    · simp at hlen; rw [hlen]; simp; linarith
    · have : (1 : ℝ) ≤ mid.length := by exact_mod_cast List.length_pos_iff.mpr hne
      rw [hlen]
      have : 0 ≤ |x1| + |x2| + (mid.map abs).sum + |xn| := by positivity
      nlinarith
  have hlen' : ((x1 :: x2 :: (mid ++ [xn])).length : ℝ) = n := rfl
  rw [hlen']
  apply kahan_final (by omega) hnr (by positivity) hτ
  have hu2 : 0 ≤ u ^ 2 := by positivity
  have hAmn : Am ≤ |x1| + |x2| + (mid.map abs).sum + |xn| + n * R.τ := by
    rw [hPm, hlen]; nlinarith
  have hAn : Am + |xn| + R.τ = |x1| + |x2| + (mid.map abs).sum + |xn| + n * R.τ := by
    rw [hPm, hlen]; ring
  have := mul_le_mul_of_nonneg_left hAmn hu2
  have hQu := mul_le_mul_of_nonneg_left hQ hu.le
  have hSnu := mul_le_mul_of_nonneg_left hSn hu.le
  rw [hlen] at hQu ⊢
  rw [hAn] at last
  have : 0 ≤ u ^ 2 * (|x1| + |x2| + (mid.map abs).sum + |xn| + n * R.τ) := by positivity
  rw [hlen] at this
  nlinarith

end Rnd

end FloatBounds

end
