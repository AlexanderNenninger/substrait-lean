module

public import FloatBounds.Sum

/-!
# The trusted link to native doubles (#85, stage 2)

`NativeLink` states what is assumed of Lean's `Float`: its arithmetic rounds
as one `StdModel` does, and an operation whose exact result does not overflow
gives a finite double. This is IEEE 754 binary64 with round to nearest, the
rounding C's `double` does and Lean's `Float` compiles to. Like
`Impl.Faithful` in `SubstraitLean/Guards.lean`, it is a hypothesis, never an
axiom: a theorem that needs it takes a `NativeLink` argument.

Since Lean 4.35, `Float`'s operations have a logical model in the kernel
(`Init/Data/Float/Model`) besides the compiled C code, so this link could be
proved from that model; Lean has no lemmas about the model yet.

`Float.toReal` reads a double's value from its bits, the decoding
`FloatCode.ofFloat` in `core/Sverify/Core/Float.lean` uses: a code's magnitude is
`|x| · 2¹⁰⁷⁴`.

`exp` is trusted to one ulp: the platform's `libm` (#582).

`native_sum_error` is the bound of `sum_error` for a fold of native doubles,
`xs.foldl (· + ·) 0`, which is `floatSum` in `SubstraitLean/Aggregate.lean`
on codes; `native_avg_error` adds `AVG`'s division by the count.
-/

@[expose] public section

namespace FloatBounds

/-- The value of a finite double, from its bits; `0` for `±∞` and NaN. -/
noncomputable def _root_.Float.toReal (f : Float) : ℝ :=
  let bits : ℕ := f.toBits.toNat
  let e : ℕ := (bits / 2 ^ 52) % 2 ^ 11
  let m : ℕ := bits % 2 ^ 52
  let mag : ℕ := if e = 0 then m else (2 ^ 52 + m) * 2 ^ (e - 1)
  if e = 2047 then 0 else (if bits / 2 ^ 63 = 1 then -1 else 1) * mag * (2 : ℝ)⁻¹ ^ 1074

/-- **The trusted link**: native doubles round as `model` does, and an
operation whose exact result is at most `maxFinite` gives a finite double.
Counts up to `2⁵³` convert exactly. -/
structure NativeLink where
  model : StdModel
  add : ∀ a b : Float, a.isFinite → b.isFinite → |a.toReal + b.toReal| ≤ maxFinite →
    (a + b).isFinite ∧ (a + b).toReal = model.fl (a.toReal + b.toReal)
  sub : ∀ a b : Float, a.isFinite → b.isFinite → |a.toReal - b.toReal| ≤ maxFinite →
    (a - b).isFinite ∧ (a - b).toReal = model.fl (a.toReal - b.toReal)
  mul : ∀ a b : Float, a.isFinite → b.isFinite → |a.toReal * b.toReal| ≤ maxFinite →
    (a * b).isFinite ∧ (a * b).toReal = model.fl (a.toReal * b.toReal)
  div : ∀ a b : Float, a.isFinite → b.isFinite → b.toReal ≠ 0 →
    |a.toReal / b.toReal| ≤ maxFinite →
    (a / b).isFinite ∧ (a / b).toReal = model.fl (a.toReal / b.toReal)
  sqrt : ∀ a : Float, a.isFinite → 0 ≤ a.toReal →
    a.sqrt.isFinite ∧ a.sqrt.toReal = model.fl (Real.sqrt a.toReal)
  /-- `exp` is the platform's `libm`, which IEEE 754 does not require to
  round correctly: within one ulp, `2u (|z| + tiny)`, of the exact value
  (glibc's manual states 1 ulp; macOS measured 0.502, duckdb-ulp-libm and
  polars-ulp-libm), and finite where that value is. -/
  exp : ∀ a : Float, a.isFinite → Real.exp a.toReal ≤ maxFinite →
    a.exp.isFinite ∧ |a.exp.toReal - Real.exp a.toReal| ≤ 2 * u * (Real.exp a.toReal + tiny)
  ofNat_exact : ∀ n : ℕ, n ≤ 2 ^ 53 → (Float.ofNat n).isFinite ∧ (Float.ofNat n).toReal = n
  zero_exact : (0 : Float).isFinite ∧ (0 : Float).toReal = 0

/-- A native fold of doubles is the model's rounded sum of their values,
as long as no partial sum overflows. -/
theorem NativeLink.foldl_add (L : NativeLink) (xs : List Float) (hfin : ∀ x ∈ xs, x.isFinite)
    (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag (xs.map Float.toReal) ≤ maxFinite) :
    (xs.foldl (· + ·) 0).isFinite ∧
      (xs.foldl (· + ·) 0).toReal = L.model.sum (xs.map Float.toReal) := by
  induction xs using List.reverseRecOn with
  | nil => simpa [StdModel.sum, StdModel.sumFrom] using L.zero_exact
  | append_singleton ys y ih =>
    obtain ⟨hu, -, ht, -, -⟩ := fpFacts
    simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
      List.map_nil, mag_append, mag_cons, mag_nil] at hn hov
    push_cast at hn hov
    have hys : (ys.length : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn
    have hn' : ((ys.length + 1 : ℕ) : ℝ) * u < 1 := by push_cast; exact hn
    have gys := gamma_nonneg hys
    have gmono := gamma_mono (Nat.le_succ ys.length) hn'
    have hmy := mag_nonneg (ys.map Float.toReal)
    have hy := abs_nonneg y.toReal
    have hovys : (1 + gamma ys.length) * mag (ys.map Float.toReal) ≤ maxFinite := by
      calc _ ≤ (1 + gamma (ys.length + 1)) * (mag (ys.map Float.toReal) + (|y.toReal| + tiny + 0)) := by
            exact mul_le_mul (by linarith) (by linarith) hmy (by linarith)
        _ ≤ maxFinite := hov
    obtain ⟨hf, he⟩ := ih (fun x hx => hfin x (by simp [hx])) hys (by simpa using hovys)
    have hs := L.model.abs_sum_le (xs := ys.map Float.toReal) (by simpa using hys)
      (by simpa using hovys)
    simp only [List.length_map] at hs
    have hz : |(ys.foldl (· + ·) 0).toReal + y.toReal| ≤ maxFinite := by
      rw [he]
      calc _ ≤ |L.model.sum (ys.map Float.toReal)| + |y.toReal| := abs_add_le _ _
        _ ≤ (1 + gamma (ys.length + 1)) * (mag (ys.map Float.toReal) + (|y.toReal| + tiny + 0)) := by
            nlinarith
        _ ≤ maxFinite := hov
    obtain ⟨hf', he'⟩ := L.add _ y hf (hfin y (by simp)) hz
    refine ⟨by simpa using hf', ?_⟩
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, he', he]
    simp [StdModel.sum, StdModel.sumFrom, List.foldl_append, StdModel.add]

/-- **`SUM` of native doubles**: within `γ n · mag xs` of the exact sum. -/
theorem NativeLink.native_sum_error (L : NativeLink) (xs : List Float) (hfin : ∀ x ∈ xs, x.isFinite)
    (hn : (xs.length : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag (xs.map Float.toReal) ≤ maxFinite) :
    |(xs.foldl (· + ·) 0).toReal - (xs.map Float.toReal).sum|
      ≤ gamma xs.length * mag (xs.map Float.toReal) := by
  rw [(L.foldl_add xs hfin hn hov).2]
  simpa using L.model.sum_error (xs := xs.map Float.toReal) (by simpa using hn) (by simpa using hov)

/-- **`AVG` of native doubles**: the native sum divided by the native count,
within `γ (n + 2) · mag xs / n` of the exact mean. -/
theorem NativeLink.native_avg_error (L : NativeLink) (xs : List Float) (hne : xs ≠ [])
    (hfin : ∀ x ∈ xs, x.isFinite) (hn : ((xs.length + 2 : ℕ) : ℝ) * u < 1)
    (hov : (1 + gamma xs.length) * mag (xs.map Float.toReal) ≤ maxFinite) :
    |(xs.foldl (· + ·) 0 / Float.ofNat xs.length).toReal
        - (xs.map Float.toReal).sum / xs.length|
      ≤ gamma (xs.length + 2) * mag (xs.map Float.toReal) / xs.length := by
  have hu := u_pos
  have hn0 : (xs.length : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; linarith) hn
  have hl : xs.length ≤ 2 ^ 53 := by
    by_contra h
    have : (2 : ℝ) ^ 53 < xs.length := by exact_mod_cast not_le.mp h
    have : (2 : ℝ) ^ 53 * u = 1 := by rw [u_val]; norm_num
    nlinarith
  obtain ⟨hcf, hc⟩ := L.ofNat_exact xs.length hl
  obtain ⟨hsf, hs⟩ := L.foldl_add xs hfin hn0 hov
  have hlen : (0 : ℝ) < xs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hsum := L.model.abs_sum_le (xs := xs.map Float.toReal) (by simpa using hn0)
    (by simpa using hov)
  simp only [List.length_map] at hsum
  have hz : |(xs.foldl (· + ·) 0).toReal / (Float.ofNat xs.length).toReal| ≤ maxFinite := by
    rw [hs, hc, abs_div, abs_of_pos hlen]
    calc _ ≤ |L.model.sum (xs.map Float.toReal)| :=
          div_le_self (abs_nonneg _) (by exact_mod_cast List.length_pos_iff.mpr hne)
      _ ≤ _ := le_trans hsum hov
  rw [(L.div _ _ hsf hcf (by rw [hc]; exact hlen.ne') hz).2, hs, hc]
  simpa using L.model.avg_error (xs := xs.map Float.toReal) (by simpa using hne)
    (by simpa using hn) (by simpa using hov)

end FloatBounds

end
