module

public import FloatBounds.TwoPass

/-!
# Two-pass, relative to the variance (#85)

The two-pass variance is accurate relative to the variance itself, not only
to `Σx²`: the error of the mean, `ε`, adds `n ε²` to the sum of squared
deviations, because the deviations from the exact mean sum to `0`
(`sum_sq_shift`). So

  `|Ŝ − S| ≤ 8 n u S + 80 n² u² Σx² + 8 n² u · tiny`

(`twoPass_var_rel`), with `S = Σ (xᵢ − x̄)²`: first order in `u` relative to
`S`, and only second order in `Σx²`. This is better than the first-order
behaviour of Welford's algorithm, `n u √(S Σx²)`.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

/-- `Σ (f x − c)² = Σ f x² − 2 c Σ f x + n c²`. -/
theorem sum_sq_sub (xs : List ℝ) (f : ℝ → ℝ) (c : ℝ) :
    (xs.map fun x => (f x - c) ^ 2).sum
      = (xs.map fun x => f x ^ 2).sum - 2 * c * (xs.map f).sum + xs.length * c ^ 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- The squared deviations from `x̄ + ε`: `S + n ε²`. -/
theorem sum_sq_shift (xs : List ℝ) (hne : xs ≠ []) (ε : ℝ) :
    (xs.map fun x => (x - (xs.sum / xs.length + ε)) ^ 2).sum
      = (xs.map fun x => (x - xs.sum / xs.length) ^ 2).sum + xs.length * ε ^ 2 := by
  have hl : (xs.length : ℝ) ≠ 0 := by simp [hne]
  have h1 := sum_sq_sub xs (fun x => x) (xs.sum / xs.length + ε)
  have h2 := sum_sq_sub xs (fun x => x) (xs.sum / xs.length)
  simp only [List.map_id'] at h1 h2
  rw [h1, h2]
  field_simp
  ring

/-- `(Σ|x|)² ≤ n Σx²`. -/
theorem sq_abs_sum_le (xs : List ℝ) : (xs.map abs).sum ^ 2 ≤ xs.length * (xs.map (· ^ 2)).sum := by
  rcases eq_or_ne xs [] with rfl | hne
  · simp
  have hl : (0 : ℝ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have h := sum_sq_sub xs abs ((xs.map abs).sum / xs.length)
  have h0 : 0 ≤ (xs.map fun x => (|x| - (xs.map abs).sum / xs.length) ^ 2).sum :=
    List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  simp only [sq_abs] at h
  rw [h] at h0
  have : (xs.map fun x => x ^ 2).sum = (xs.map (· ^ 2)).sum := rfl
  rw [this] at h0
  field_simp at h0
  nlinarith

variable (M : StdModel)

/-- A rounded square of a rounded value: `fl(fl(z)²)` within `5u z² + 3u·tiny`. -/
theorem StdModel.sq_step {z : ℝ} (hz : |z| ≤ 2 ^ 450) :
    |M.fl (M.fl z * M.fl z) - z ^ 2| ≤ 5 * u * z ^ 2 + 3 * u * tiny := by
  obtain ⟨hu, hu', ht, -, hmax⟩ := fpFacts
  have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set a := |z|
  have ha : 0 ≤ a := abs_nonneg z
  have hz2 : z ^ 2 = a ^ 2 := (sq_abs z).symm
  have e1 := M.err z (by linarith)
  set d := M.fl z
  have hd : |d| ≤ a + u * (a + tiny) := by have := abs_sub_abs_le_abs_sub d z; linarith
  -- `d² − z² = (d − z)(d + z)`
  have hdz : |d * d - z ^ 2| ≤ u * (a + tiny) * (2 * a + u * (a + tiny)) := by
    have : d * d - z ^ 2 = (d - z) * (d + z) := by ring
    rw [this, abs_mul]
    have h2 : |d + z| ≤ 2 * a + u * (a + tiny) := by
      have := abs_add_le d z; linarith
    exact mul_le_mul e1 h2 (abs_nonneg _) (by positivity)
  have hat : a * tiny ≤ (a ^ 2 + tiny ^ 2) / 2 := by nlinarith [sq_nonneg (a - tiny)]
  have ht2 : tiny ^ 2 ≤ tiny := by nlinarith
  have hsmall : u * (a + tiny) * (2 * a + u * (a + tiny)) ≤ 3.01 * u * a ^ 2 + 1.01 * u * tiny := by
    have hu2 : u * u ≤ u / 2 ^ 53 := by nlinarith
    nlinarith [mul_nonneg hu.le (sq_nonneg a), mul_nonneg hu.le ht.le, mul_nonneg hu.le ha,
      mul_nonneg (mul_nonneg hu.le hu.le) (sq_nonneg (a + tiny))]
  have hdd : |d * d| ≤ 2 ^ 1000 := by
    have : |d * d| ≤ z ^ 2 + (3.01 * u * a ^ 2 + 1.01 * u * tiny) := by
      have := abs_sub_abs_le_abs_sub (d * d) (z ^ 2)
      rw [abs_of_nonneg (sq_nonneg z)] at this; linarith
    have : a ^ 2 ≤ 2 ^ 900 := by
      calc a ^ 2 ≤ (2 ^ 450) ^ 2 := by gcongr
        _ = 2 ^ 900 := by norm_num
    nlinarith
  have e2 := M.err (d * d) (by linarith)
  have hddv : |d * d| ≤ (1 + 3.01 * u) * a ^ 2 + 1.01 * u * tiny := by
    have h1 := abs_sub_abs_le_abs_sub (d * d) (z ^ 2)
    have h2 := le_trans hdz hsmall
    rw [abs_of_nonneg (sq_nonneg z)] at h1
    rw [hz2] at h1 h2
    linarith
  calc |M.fl (d * d) - z ^ 2| = |(M.fl (d * d) - d * d) + (d * d - z ^ 2)| := by ring_nf
    _ ≤ |M.fl (d * d) - d * d| + |d * d - z ^ 2| := abs_add_le _ _
    _ ≤ u * (|d * d| + tiny) + (3.01 * u * a ^ 2 + 1.01 * u * tiny) := by linarith
    _ ≤ 5 * u * z ^ 2 + 3 * u * tiny := by
      rw [hz2]
      have : u * (|d * d| + tiny) ≤ u * ((1 + 3.01 * u) * a ^ 2 + 1.01 * u * tiny + tiny) := by
        gcongr
      nlinarith [mul_nonneg (mul_nonneg hu.le hu.le) (sq_nonneg a), mul_nonneg (mul_nonneg hu.le hu.le) ht.le]

/-- `n ε² ≤ 72 n² u² Q + 72 n³ u² t²` from `|ε| ≤ 6 u (A + n t)`, `A² ≤ n Q`. -/
theorem eps_sq_bound {n A Q ε t : ℝ} (hn : 0 ≤ n) (_hA : 0 ≤ A) (_ht : 0 ≤ t) (hAQ : A ^ 2 ≤ n * Q)
    (hε : |ε| ≤ 6 * u * (A + n * t)) :
    n * ε ^ 2 ≤ 72 * n ^ 2 * u ^ 2 * Q + 72 * n ^ 3 * u ^ 2 * t ^ 2 := by
  have hu := u_pos
  have h1 : ε ^ 2 ≤ (6 * u * (A + n * t)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hε 2
  have h2 : (A + n * t) ^ 2 ≤ 2 * (A ^ 2 + (n * t) ^ 2) := by
    nlinarith [sq_nonneg (A - n * t)]
  have h3 : (6 * u * (A + n * t)) ^ 2 ≤ 36 * u ^ 2 * (2 * (n * Q + (n * t) ^ 2)) := by
    have : (6 * u * (A + n * t)) ^ 2 = 36 * u ^ 2 * (A + n * t) ^ 2 := by ring
    rw [this]
    have h4 : (A + n * t) ^ 2 ≤ 2 * (n * Q + (n * t) ^ 2) := by linarith
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have := mul_le_mul_of_nonneg_left (le_trans h1 h3) hn
  have e : n * (36 * u ^ 2 * (2 * (n * Q + (n * t) ^ 2)))
      = 72 * n ^ 2 * u ^ 2 * Q + 72 * n ^ 3 * u ^ 2 * t ^ 2 := by ring
  linarith

/-- The arithmetic at the end of `twoPass_var_rel`. -/
theorem twoPass_assemble {n S Q E P g t X : ℝ} (hn1 : 1 ≤ n) (hnu : n * u ≤ 1 / 2 ^ 21)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2 ^ 1022) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hE2 : E ≤ 72 * n ^ 2 * u ^ 2 * Q + 72 * n ^ 3 * u ^ 2 * t ^ 2) (hg0 : 0 ≤ g)
    (hg : g ≤ 2 * n * u) (hP0 : 0 ≤ P) (hP : P ≤ (1 + 5 * u) * (S + E) + 3 * n * u * t)
    (hX : |X - S| ≤ g * (P + n * t) + (5 * u * (S + E) + 3 * n * u * t) + E) :
    |X - S| ≤ 8 * n * u * S + 80 * n ^ 2 * u ^ 2 * Q + 8 * n ^ 2 * u * t := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hn0 : 0 ≤ n := by linarith
  have hnu0 : 0 ≤ n * u := by positivity
  have h1 : g * (P + n * t) ≤ 2 * n * u * ((1 + 5 * u) * (S + E) + 3 * n * u * t + n * t) :=
    mul_le_mul hg (by linarith) (by positivity) (by positivity)
  -- products as atoms
  have a1 : n * u * u * (S + E) ≤ 1 / 2 ^ 53 * (n * u * (S + E)) := by
    have := mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ n * u * (S + E)); linarith
  have a2 : u * (S + E) ≤ n * u * (S + E) := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ u * (S + E)); linarith
  have a3 : n * u * E ≤ 1 / 2 ^ 21 * E := mul_le_mul_of_nonneg_right hnu hE
  have a4 : n * u * (n * u * t) ≤ 1 / 2 ^ 21 * (n * u * t) :=
    mul_le_mul_of_nonneg_right hnu (by positivity)
  have a5 : n * u * t ≤ n * (n * u * t) := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ n * u * t); linarith
  have a6 : n * u * E * u ≤ 1 / 2 ^ 21 * E := by
    have : n * u * E * u ≤ n * u * E := by
      have := mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ n * u * E); nlinarith
    linarith
  have a7 : u * E ≤ n * u * E := by
    have := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ u * E); linarith
  have hnut : n * u * t ≤ 1 / 2 ^ 1000 := by
    have := mul_le_mul hnu ht1 ht (by norm_num); nlinarith
  have a8 : 72 * n ^ 3 * u ^ 2 * t ^ 2 ≤ n * (n * u * t) / 2 := by
    have e : 72 * n ^ 3 * u ^ 2 * t ^ 2 = 72 * (n * (n * u * t)) * (n * u * t) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hnut (by positivity : 0 ≤ 72 * (n * (n * u * t)))
    have : 0 ≤ n * (n * u * t) := by positivity
    linarith
  have a9 : 0 ≤ n * u * S := by positivity
  have a10 : 0 ≤ n ^ 2 * u ^ 2 * Q := by positivity
  have e1 : 2 * n * u * ((1 + 5 * u) * (S + E) + 3 * n * u * t + n * t)
      = 2 * (n * u * (S + E)) + 10 * (n * u * u * (S + E)) + 6 * (n * u * (n * u * t))
        + 2 * (n * (n * u * t)) := by ring
  have e2 : n * u * (S + E) = n * u * S + n * u * E := by ring
  have a11 : 0 ≤ n * (n * u * t) := by positivity
  have a12 : 0 ≤ n * u * t := by positivity
  have a13 : 0 ≤ n * u * E := by positivity
  have e3 : n ^ 2 * u * t = n * (n * u * t) := by ring
  have hX' := le_trans hX (by linarith : g * (P + n * t) + (5 * u * (S + E) + 3 * n * u * t) + E
    ≤ 2 * n * u * ((1 + 5 * u) * (S + E) + 3 * n * u * t + n * t)
      + (5 * u * (S + E) + 3 * n * u * t) + E)
  rw [e1, e2] at hX'
  linarith

set_option maxHeartbeats 1000000 in
/-- **Two-pass, relative to the variance**: for `n ≤ 2³²` values at most
`2³⁹⁹`, `|Ŝ − S| ≤ 8 n u S + 80 n² u² Σx² + 8 n² u · tiny`. -/
theorem StdModel.twoPass_var_rel {xs : List ℝ} (hne : xs ≠ []) (hN : xs.length ≤ 2 ^ 32)
    (hB : ∀ x ∈ xs, |x| ≤ 2 ^ 399) :
    |M.twoPass (xs.map fun x => (x, x)) - (xs.map fun x => (x - xs.sum / xs.length) ^ 2).sum|
      ≤ 8 * xs.length * u * (xs.map fun x => (x - xs.sum / xs.length) ^ 2).sum
        + 80 * xs.length ^ 2 * u ^ 2 * (xs.map (· ^ 2)).sum + 8 * xs.length ^ 2 * u * tiny := by
  obtain ⟨hu, hu', ht, -, hmax⟩ := fpFacts
  have ht1 : tiny ≤ 1 / 2 ^ 1022 := by unfold tiny; norm_num
  set n : ℕ := xs.length with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast List.length_pos_iff.mpr hne
  have hn0 : (0 : ℝ) < n := by linarith
  have hN' : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hN
  have hnu : (n : ℝ) * u ≤ 1 / 2 ^ 21 := by
    calc (n : ℝ) * u ≤ 2 ^ 32 * (1 / 2 ^ 53) := by gcongr
      _ = 1 / 2 ^ 21 := by norm_num
  set S := (xs.map fun x => (x - xs.sum / n) ^ 2).sum with hS
  set Q := (xs.map (· ^ 2)).sum with hQ
  set A := (xs.map abs).sum with hA
  have hS0 : 0 ≤ S := List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hQ0 : 0 ≤ Q := List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  have hAQ : A ^ 2 ≤ n * Q := sq_abs_sum_le xs
  have hA0 : 0 ≤ A := List.sum_nonneg (fun y hy => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; positivity)
  -- the computed mean, and its error `ε`
  have hmag : mag xs = A + n * tiny := by
    simp only [mag, hA, hn]
    induction xs with
    | nil => simp
    | cons x xs ih => simp; ring
  have hAb : A ≤ n * 2 ^ 399 := by
    have := abs_sum_le_of_bound (B := 2 ^ 399) (xs := xs.map abs) (by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; rw [abs_abs]; exact hB x hx)
    simp only [List.length_map] at this
    rw [abs_of_nonneg hA0] at this; exact this
  have hn2u : ((n + 2 : ℕ) : ℝ) * u ≤ 1 / 2 := by push_cast; nlinarith
  have hg := gamma_le_two hn2u
  have hgn := gamma_le_two (k := n) (by nlinarith)
  have hov : (1 + gamma n) * mag xs ≤ maxFinite := by
    rw [hmag]
    have : 1 + gamma n ≤ 2 := by nlinarith
    have : A + n * tiny ≤ 2 ^ 32 * 2 ^ 399 + 2 ^ 32 := by nlinarith
    nlinarith [gamma_nonneg (n := n) (by nlinarith)]
  have havg := M.avg_error hne (by push_cast; nlinarith) hov
  set mh := M.fl (M.sum xs / n)
  set m := xs.sum / n
  set ε := mh - m with hε
  have hε1 : |ε| ≤ 6 * u * (A + n * tiny) := by
    rw [hmag] at havg
    rw [hε]
    calc _ ≤ gamma (n + 2) * (A + n * tiny) / n := havg
      _ ≤ 2 * ((n + 2 : ℕ) : ℝ) * u * (A + n * tiny) / n := by gcongr
      _ ≤ 6 * u * (A + n * tiny) := by
        rw [div_le_iff₀ hn0]; push_cast
        have : 0 ≤ u * (A + n * tiny) := by positivity
        nlinarith
  have hε2 : (n : ℝ) * ε ^ 2 ≤ 72 * n ^ 2 * u ^ 2 * Q + 72 * n ^ 3 * u ^ 2 * tiny ^ 2 :=
    eps_sq_bound hn0.le hA0 ht.le hAQ hε1
  -- the deviations from the computed mean, squared and rounded
  have hfst : (xs.map fun x => (x, x)).map Prod.fst = xs := by
    simp [List.map_map, Function.comp_def]
  have hsnd : (xs.map fun x => (x, x)).map Prod.snd = xs := by
    simp [List.map_map, Function.comp_def]
  have htp : M.twoPass (xs.map fun x => (x, x))
      = M.sum (xs.map fun x => M.fl (M.fl (x - mh) * M.fl (x - mh))) := by
    unfold StdModel.twoPass StdModel.mean
    rw [hfst, hsnd]
    simp [List.map_map, Function.comp_def, mh]
    rfl
  rw [htp]
  have hmh : |mh| ≤ 2 ^ 400 := by
    have hm : |m| ≤ 2 ^ 399 := by
      have := abs_sum_le_of_bound hB
      simp only [m]; rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]; linarith
    have : |ε| ≤ 2 ^ 399 := by
      have : 6 * u * (A + n * tiny) ≤ 2 ^ 399 := by
        have h1 : A + n * tiny ≤ 2 ^ 32 * 2 ^ 399 + 2 ^ 32 := by nlinarith
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 6 * u)
        have h3 : 6 * u * (2 ^ 32 * 2 ^ 399 + 2 ^ 32) ≤ 2 ^ 399 := by
          calc 6 * u * (2 ^ 32 * 2 ^ 399 + 2 ^ 32) ≤ 6 * (1 / 2 ^ 53) * (2 ^ 32 * 2 ^ 399 + 2 ^ 32) := by
                gcongr
            _ ≤ 2 ^ 399 := by norm_num
        linarith
      linarith
    have e : mh = m + ε := by simp only [hε]; ring
    rw [e]; exact le_trans (abs_add_le _ _) (by linarith)
  have hz : ∀ x ∈ xs, |x - mh| ≤ 2 ^ 450 := by
    intro x hx
    have := abs_sub x mh
    linarith [hB x hx]
  have hstep : ∀ x ∈ xs, |M.fl (M.fl (x - mh) * M.fl (x - mh)) - (x - mh) ^ 2|
      ≤ 5 * u * (x - mh) ^ 2 + 3 * u * tiny := fun x hx => M.sq_step (hz x hx)
  have hshift := sum_sq_shift xs hne ε
  have hmε : m + ε = mh := by simp only [hε]; ring
  simp only [← hn] at hshift
  rw [show xs.sum / n + ε = mh from hmε] at hshift
  set Z := (xs.map fun x => (x - mh) ^ 2).sum with hZ
  -- the sum of the rounded squares, against `Z = S + n ε²`
  set P := xs.map fun x => M.fl (M.fl (x - mh) * M.fl (x - mh))
  have hPZ : |P.sum - Z| ≤ 5 * u * Z + 3 * n * u * tiny := by
    have := abs_sum_map_sub_le (fun x => M.fl (M.fl (x - mh) * M.fl (x - mh)))
      (fun x => (x - mh) ^ 2) (fun x => 5 * u * (x - mh) ^ 2 + 3 * u * tiny) 1 xs
      (fun x hx => by simpa using hstep x hx)
    simp only [one_mul] at this
    have e : (xs.map fun x => 5 * u * (x - mh) ^ 2 + 3 * u * tiny).sum = 5 * u * Z + 3 * n * u * tiny := by
      have key : ∀ L : List ℝ, (L.map fun x => 5 * u * (x - mh) ^ 2 + 3 * u * tiny).sum
          = 5 * u * (L.map fun x => (x - mh) ^ 2).sum + 3 * L.length * u * tiny := by
        intro L
        induction L with
        | nil => simp
        | cons x L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring
      rw [key, hZ, hn]
    linarith
  have hP0 : ∀ y ∈ P, 0 ≤ y := by
    intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy; exact M.nonneg _ (mul_self_nonneg _)
  have hmagP : mag P = P.sum + n * tiny := by
    have : ∀ L : List ℝ, (∀ y ∈ L, 0 ≤ y) → mag L = L.sum + L.length * tiny := by
      intro L hL
      induction L with
      | nil => simp
      | cons y L ih =>
        simp only [mag_cons, List.sum_cons, List.length_cons]
        rw [abs_of_nonneg (hL y (by simp)), ih (fun z hz => hL z (by simp [hz]))]; push_cast; ring
    rw [this P hP0]; simp [P, hn]
  have hZb : Z ≤ 2 ^ 32 * 2 ^ 900 := by
    have := abs_sum_le_of_bound (B := 2 ^ 900) (xs := xs.map fun x => (x - mh) ^ 2) (by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      rw [abs_of_nonneg (sq_nonneg _)]
      calc (x - mh) ^ 2 = |x - mh| ^ 2 := (sq_abs _).symm
        _ ≤ (2 ^ 450) ^ 2 := by gcongr; exact hz x hx
        _ = 2 ^ 900 := by norm_num)
    simp only [List.length_map] at this
    rw [← hn] at this
    have h1 := le_abs_self Z
    have h2 := mul_le_mul_of_nonneg_right hN' (by norm_num : (0 : ℝ) ≤ 2 ^ 900)
    linarith
  have hPlen : P.length = n := by simp [P, hn]
  have hsum := M.sum_error (xs := P) (by rw [hPlen]; nlinarith) (by
    rw [hPlen, hmagP]
    have : P.sum ≤ 2 * 2 ^ 932 := by
      have := (abs_le.mp hPZ).2
      have : 5 * u * Z ≤ Z := by nlinarith
      have : 3 * n * u * tiny ≤ 1 := by nlinarith
      nlinarith
    have h1 : 1 + gamma n ≤ 2 := by nlinarith
    have h2 : P.sum + n * tiny ≤ 2 ^ 934 := by
      have : (n : ℝ) * tiny ≤ 1 := by nlinarith
      linarith
    have h3 : 0 ≤ P.sum + n * tiny := by have := List.sum_nonneg hP0; positivity
    have := mul_le_mul h1 h2 h3 (by norm_num)
    linarith)
  rw [hPlen, hmagP] at hsum
  -- assemble
  have hZS : Z = S + n * ε ^ 2 := hshift
  have hPs : P.sum ≤ (1 + 5 * u) * Z + 3 * n * u * tiny := by linarith [(abs_le.mp hPZ).2]
  have hΔ : |M.sum P - S| ≤ gamma n * (P.sum + n * tiny) + (5 * u * Z + 3 * n * u * tiny) + n * ε ^ 2 := by
    have : M.sum P - S = (M.sum P - P.sum) + (P.sum - Z) + (Z - S) := by ring
    rw [this]
    have h1 := abs_add_le (M.sum P - P.sum + (P.sum - Z)) (Z - S)
    have h2 := abs_add_le (M.sum P - P.sum) (P.sum - Z)
    have h3 : |Z - S| = n * ε ^ 2 := by rw [hZS]; ring_nf; exact abs_of_nonneg (by positivity)
    linarith
  have hg' : gamma n ≤ 2 * n * u := hgn
  have hnε0 : 0 ≤ (n : ℝ) * ε ^ 2 := by positivity
  rw [hZS] at hΔ hPs
  exact twoPass_assemble hn1 hnu ht.le ht1 hS0 hQ0 hnε0 hε2
    (gamma_nonneg (n := n) (by nlinarith)) hg' (List.sum_nonneg hP0) hPs hΔ

end FloatBounds

end
