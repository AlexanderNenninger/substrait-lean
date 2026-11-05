module

public import FloatBounds.Kahan
public import FloatBounds.Link
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# One double operation, from the bounds on its inputs (#582)

The checker bounds a double `a + b`, `a − b`, `a · b`, `a / b` and `exp a`
from intervals of its inputs (`floatArith` in `SubstraitLean/Safety.lean`),
and so rules out an overflow to `±∞` where the bounds do. The core trusts
one fact per operation, on scaled codes (a double `x` is `x · 2¹⁰⁷⁴`); this
file proves them for native doubles (`NativeLink`), with the doubles
decoded from codes within `2u` of the codes' values `A`, `B`, as `Decoded`
says:

* `core_add`, `core_sub`: where `|A| + |B| ≤ 2¹⁰²³`, the result is finite and
  within `(|A| + |B|) / 2⁵¹ + u · tiny` of `A ± B`;
* `core_mul`: where `|A B| ≤ 2¹⁰²³`, finite and within `|A B| / 2⁵⁰ + u · tiny`;
* `core_div`: where `B ≠ 0` and `|A / B| ≤ 2¹⁰²³`, finite and within
  `|A / B| / 2⁵⁰ + u · tiny`;
* `core_exp`: where `A ≤ 709`, `exp` is finite (`709 < 1023 · ln 2`), by
  `NativeLink.exp`.

Scaled by `2¹⁰⁷⁴`, `u · tiny` is `1/2`.
-/

@[expose] public section

set_option exponentiation.threshold 2100

namespace FloatBounds

namespace NativeLink

theorem decoded_le {a : Float} {A : ℝ} (hA : |a.toReal - A| ≤ 2 * u * |A|) :
    |a.toReal| ≤ (1 + 2 * u) * |A| := by
  have := abs_sub_abs_le_abs_sub a.toReal A; nlinarith [abs_nonneg A]

theorem two_pow_1023_le : (2 : ℝ) ^ 1023 * (1 + 1 / 2 ^ 40) ≤ maxFinite := by
  unfold maxFinite
  have h : (1 + 1 / 2 ^ 40 : ℝ) ≤ 2 - (2 : ℝ)⁻¹ ^ 52 := by norm_num
  rw [mul_comm ((2 : ℝ) ^ 1023)]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- **`+`**: finite, within `(|A| + |B|) / 2⁵¹ + u · tiny` of `A + B`. -/
theorem core_add (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite) {A B : ℝ}
    (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (h : |A| + |B| ≤ 2 ^ 1023) :
    (a + b).isFinite ∧ |(a + b).toReal - (A + B)| ≤ (|A| + |B|) / 2 ^ 51 + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have h1 := decoded_le hA
  have h2 := decoded_le hB
  have hS : |a.toReal + b.toReal| ≤ (1 + 2 * u) * (|A| + |B|) := by
    have := abs_add_le a.toReal b.toReal; linarith
  have hM : |a.toReal + b.toReal| ≤ maxFinite := by
    have h2u : 1 + 2 * u ≤ 1 + 1 / 2 ^ 40 := by
      linarith [show (2 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 40 by norm_num]
    have := mul_le_mul h2u h (by positivity) (by norm_num)
    have := two_pow_1023_le
    linarith
  obtain ⟨hf, he⟩ := L.add a b ha hb hM
  refine ⟨hf, ?_⟩
  rw [he]
  have hr := L.model.err _ hM
  have hd : |(a.toReal + b.toReal) - (A + B)| ≤ 2 * u * (|A| + |B|) := by
    calc _ = |(a.toReal - A) + (b.toReal - B)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  have hu4 : 4 * u ≤ 1 / 2 ^ 51 := by linarith [show (4 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 51 by norm_num]
  have hu2 : u * (2 * u) ≤ u * (1 / 2 ^ 51) :=
    mul_le_mul_of_nonneg_left (by linarith [show (2 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 51 by norm_num])
      hu.le
  have hAB : 0 ≤ |A| + |B| := by positivity
  calc _ = |(L.model.fl (a.toReal + b.toReal) - (a.toReal + b.toReal))
        + ((a.toReal + b.toReal) - (A + B))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ u * ((1 + 2 * u) * (|A| + |B|) + tiny) + 2 * u * (|A| + |B|) := by
        have := mul_le_mul_of_nonneg_left hS hu.le
        linarith
    _ = (3 * u + 2 * u * u) * (|A| + |B|) + u * tiny := by ring
    _ ≤ (|A| + |B|) / 2 ^ 51 + u * tiny := by
        have : 3 * u + 2 * u * u ≤ 1 / 2 ^ 51 := by nlinarith
        have := mul_le_mul_of_nonneg_right this hAB
        linarith [show (|A| + |B|) / 2 ^ 51 = 1 / 2 ^ 51 * (|A| + |B|) by ring]

/-- **`−`**: as `+`. -/
theorem core_sub (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite) {A B : ℝ}
    (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (h : |A| + |B| ≤ 2 ^ 1023) :
    (a - b).isFinite ∧ |(a - b).toReal - (A - B)| ≤ (|A| + |B|) / 2 ^ 51 + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have h1 := decoded_le hA
  have h2 := decoded_le hB
  have hS : |a.toReal - b.toReal| ≤ (1 + 2 * u) * (|A| + |B|) := by
    have := abs_sub_le_add a.toReal b.toReal; linarith
  have hM : |a.toReal - b.toReal| ≤ maxFinite := by
    have h2u : 1 + 2 * u ≤ 1 + 1 / 2 ^ 40 := by
      linarith [show (2 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 40 by norm_num]
    have := mul_le_mul h2u h (by positivity) (by norm_num)
    have := two_pow_1023_le
    linarith
  obtain ⟨hf, he⟩ := L.sub a b ha hb hM
  refine ⟨hf, ?_⟩
  rw [he]
  have hr := L.model.err _ hM
  have hd : |(a.toReal - b.toReal) - (A - B)| ≤ 2 * u * (|A| + |B|) := by
    calc _ = |(a.toReal - A) - (b.toReal - B)| := by ring_nf
      _ ≤ _ := abs_sub_le_add _ _
      _ ≤ _ := by linarith
  have hAB : 0 ≤ |A| + |B| := by positivity
  calc _ = |(L.model.fl (a.toReal - b.toReal) - (a.toReal - b.toReal))
        + ((a.toReal - b.toReal) - (A - B))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ u * ((1 + 2 * u) * (|A| + |B|) + tiny) + 2 * u * (|A| + |B|) := by
        have := mul_le_mul_of_nonneg_left hS hu.le
        linarith
    _ = (3 * u + 2 * u * u) * (|A| + |B|) + u * tiny := by ring
    _ ≤ (|A| + |B|) / 2 ^ 51 + u * tiny := by
        have : 3 * u + 2 * u * u ≤ 1 / 2 ^ 51 := by nlinarith
        have := mul_le_mul_of_nonneg_right this hAB
        linarith [show (|A| + |B|) / 2 ^ 51 = 1 / 2 ^ 51 * (|A| + |B|) by ring]

/-- **`×`**: finite, within `|A B| / 2⁵⁰ + u · tiny` of `A B`. -/
theorem core_mul (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite) {A B : ℝ}
    (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (h : |A * B| ≤ 2 ^ 1023) :
    (a * b).isFinite ∧ |(a * b).toReal - A * B| ≤ |A * B| / 2 ^ 50 + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hP : 0 ≤ |A * B| := abs_nonneg _
  -- the product of the decoded doubles: within `(4u + 4u²) |A B|`
  have hd : |a.toReal * b.toReal - A * B| ≤ (4 * u + 4 * u * u) * |A * B| := by
    have e : a.toReal * b.toReal - A * B
        = (a.toReal - A) * B + A * (b.toReal - B) + (a.toReal - A) * (b.toReal - B) := by ring
    rw [e, abs_mul A B]
    have p1 : |(a.toReal - A) * B| ≤ 2 * u * |A| * |B| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
    have p2 : |A * (b.toReal - B)| ≤ |A| * (2 * u * |B|) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
    have p3 : |(a.toReal - A) * (b.toReal - B)| ≤ (2 * u * |A|) * (2 * u * |B|) := by
      rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have := abs_add_le ((a.toReal - A) * B + A * (b.toReal - B)) ((a.toReal - A) * (b.toReal - B))
    have := abs_add_le ((a.toReal - A) * B) (A * (b.toReal - B))
    nlinarith
  have hsmall : 4 * u + 4 * u * u ≤ 1 / 2 ^ 40 := by nlinarith
  have hS : |a.toReal * b.toReal| ≤ (1 + 1 / 2 ^ 40) * |A * B| := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (A * B)
    nlinarith
  have hM : |a.toReal * b.toReal| ≤ maxFinite := by
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 40)
    have := two_pow_1023_le
    linarith
  obtain ⟨hf, he⟩ := L.mul a b ha hb hM
  refine ⟨hf, ?_⟩
  rw [he]
  have hr := L.model.err _ hM
  calc _ = |(L.model.fl (a.toReal * b.toReal) - a.toReal * b.toReal)
        + (a.toReal * b.toReal - A * B)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ u * ((1 + 1 / 2 ^ 40) * |A * B| + tiny) + (4 * u + 4 * u * u) * |A * B| := by
        have := mul_le_mul_of_nonneg_left hS hu.le
        linarith
    _ = (u * (1 + 1 / 2 ^ 40) + 4 * u + 4 * u * u) * |A * B| + u * tiny := by ring
    _ ≤ |A * B| / 2 ^ 50 + u * tiny := by
        have : u * (1 + 1 / 2 ^ 40) + 4 * u + 4 * u * u ≤ 1 / 2 ^ 50 := by nlinarith
        have := mul_le_mul_of_nonneg_right this hP
        linarith [show |A * B| / 2 ^ 50 = 1 / 2 ^ 50 * |A * B| by ring]

/-- **`/`**: where `B ≠ 0`, finite, within `|A / B| / 2⁵⁰ + u · tiny` of `A / B`. -/
theorem core_div (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite) {A B : ℝ}
    (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|) (hB0 : B ≠ 0)
    (h : |A / B| ≤ 2 ^ 1023) :
    (a / b).isFinite ∧ |(a / b).toReal - A / B| ≤ |A / B| / 2 ^ 50 + u * tiny := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hBp : 0 < |B| := abs_pos.mpr hB0
  -- the decoded divisor keeps its sign and is at least `(1 − 2u) |B|`
  have hb' : (1 - 2 * u) * |B| ≤ |b.toReal| := by
    have := abs_sub_abs_le_abs_sub B b.toReal
    rw [abs_sub_comm] at this; nlinarith
  have hbp : 0 < |b.toReal| := lt_of_lt_of_le (by nlinarith) hb'
  have hb0 : b.toReal ≠ 0 := abs_pos.mp hbp
  set q := A / B
  have hq : A = q * B := by rw [div_mul_cancel₀ _ hB0]
  have hQ : 0 ≤ |q| := abs_nonneg _
  -- `a' / b' − q = ((a' − A) − q (b' − B)) / b'`
  have hd : |a.toReal / b.toReal - q| ≤ (4 * u / (1 - 2 * u)) * |q| := by
    have e : a.toReal / b.toReal - q = ((a.toReal - A) - q * (b.toReal - B)) / b.toReal := by
      field_simp; rw [hq]; ring
    rw [e, abs_div, div_le_iff₀ hbp]
    have h1 : |(a.toReal - A) - q * (b.toReal - B)| ≤ 2 * u * |A| + |q| * (2 * u * |B|) := by
      have := abs_sub_le_add (a.toReal - A) (q * (b.toReal - B))
      rw [abs_mul] at this
      have := mul_le_mul_of_nonneg_left hB hQ
      linarith
    have hAq : |A| = |q| * |B| := by rw [hq, abs_mul]
    rw [hAq] at h1
    have h2u : 0 < 1 - 2 * u := by nlinarith
    calc _ ≤ 2 * u * (|q| * |B|) + |q| * (2 * u * |B|) := h1
      _ = (4 * u / (1 - 2 * u)) * |q| * ((1 - 2 * u) * |B|) := by field_simp; ring
      _ ≤ _ := by gcongr
  have hc : 4 * u / (1 - 2 * u) ≤ 1 / 2 ^ 50 - 2 * u := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hS : |a.toReal / b.toReal| ≤ (1 + 1 / 2 ^ 50) * |q| := by
    have := abs_sub_abs_le_abs_sub (a.toReal / b.toReal) q
    have := mul_le_mul_of_nonneg_right hc hQ
    nlinarith
  have hM : |a.toReal / b.toReal| ≤ maxFinite := by
    have := two_pow_1023_le
    have := mul_le_mul (by norm_num : (1 + 1 / 2 ^ 50 : ℝ) ≤ 1 + 1 / 2 ^ 40) h hQ (by norm_num)
    linarith
  obtain ⟨hf, he⟩ := L.div a b ha hb hb0 hM
  refine ⟨hf, ?_⟩
  rw [he]
  have hr := L.model.err _ hM
  calc _ = |(L.model.fl (a.toReal / b.toReal) - a.toReal / b.toReal)
        + (a.toReal / b.toReal - q)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ u * ((1 + 1 / 2 ^ 50) * |q| + tiny) + (1 / 2 ^ 50 - 2 * u) * |q| := by
        have := mul_le_mul_of_nonneg_left hS hu.le
        have := mul_le_mul_of_nonneg_right hc hQ
        linarith
    _ ≤ |q| / 2 ^ 50 + u * tiny := by
        have : u * (1 + 1 / 2 ^ 50) ≤ 2 * u := by nlinarith
        have := mul_le_mul_of_nonneg_right this hQ
        nlinarith

/-! ### Signs (#441)

Rounding keeps the sign (`StdModel.nonneg`): under the guards of `core_add`,
`core_mul` and `core_div`, a sum or product of non-negative doubles, and a
quotient of one by a positive one, is non-negative. The core states these as
`FloatCode.add_nonneg`, `mul_nonneg` and `div_nonneg`. -/

/-- **`+`** of non-negative doubles is non-negative. -/
theorem core_add_nonneg (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite)
    {A B : ℝ} (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (h : |A| + |B| ≤ 2 ^ 1023) (ha0 : 0 ≤ a.toReal) (hb0 : 0 ≤ b.toReal) :
    0 ≤ (a + b).toReal := by
  obtain ⟨-, hu', -, -, -⟩ := fpFacts
  have h1 := decoded_le hA
  have h2 := decoded_le hB
  have hS : |a.toReal + b.toReal| ≤ (1 + 2 * u) * (|A| + |B|) := by
    have := abs_add_le a.toReal b.toReal; linarith
  have hM : |a.toReal + b.toReal| ≤ maxFinite := by
    have h2u : 1 + 2 * u ≤ 1 + 1 / 2 ^ 40 := by
      linarith [show (2 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 ^ 40 by norm_num]
    have := mul_le_mul h2u h (by positivity) (by norm_num)
    have := two_pow_1023_le
    linarith
  obtain ⟨-, he⟩ := L.add a b ha hb hM
  rw [he]
  exact L.model.nonneg _ (add_nonneg ha0 hb0)

/-- **`*`** of non-negative doubles is non-negative. -/
theorem core_mul_nonneg (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite)
    {A B : ℝ} (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (h : |A * B| ≤ 2 ^ 1023) (ha0 : 0 ≤ a.toReal) (hb0 : 0 ≤ b.toReal) :
    0 ≤ (a * b).toReal := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hP : 0 ≤ |A * B| := abs_nonneg _
  -- the product of the decoded doubles: within `(4u + 4u²) |A B|`
  have hd : |a.toReal * b.toReal - A * B| ≤ (4 * u + 4 * u * u) * |A * B| := by
    have e : a.toReal * b.toReal - A * B
        = (a.toReal - A) * B + A * (b.toReal - B) + (a.toReal - A) * (b.toReal - B) := by ring
    rw [e, abs_mul A B]
    have p1 : |(a.toReal - A) * B| ≤ 2 * u * |A| * |B| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
    have p2 : |A * (b.toReal - B)| ≤ |A| * (2 * u * |B|) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
    have p3 : |(a.toReal - A) * (b.toReal - B)| ≤ (2 * u * |A|) * (2 * u * |B|) := by
      rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have := abs_add_le ((a.toReal - A) * B + A * (b.toReal - B)) ((a.toReal - A) * (b.toReal - B))
    have := abs_add_le ((a.toReal - A) * B) (A * (b.toReal - B))
    nlinarith
  have hsmall : 4 * u + 4 * u * u ≤ 1 / 2 ^ 40 := by nlinarith
  have hS : |a.toReal * b.toReal| ≤ (1 + 1 / 2 ^ 40) * |A * B| := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (A * B)
    nlinarith
  have hM : |a.toReal * b.toReal| ≤ maxFinite := by
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 40)
    have := two_pow_1023_le
    linarith
  obtain ⟨-, he⟩ := L.mul a b ha hb hM
  rw [he]
  exact L.model.nonneg _ (mul_nonneg ha0 hb0)

/-- **`/`** of a non-negative double by a positive one is non-negative. -/
theorem core_div_nonneg (L : NativeLink) {a b : Float} (ha : a.isFinite) (hb : b.isFinite)
    {A B : ℝ} (hA : |a.toReal - A| ≤ 2 * u * |A|) (hB : |b.toReal - B| ≤ 2 * u * |B|)
    (hB0 : B ≠ 0) (h : |A / B| ≤ 2 ^ 1023) (ha0 : 0 ≤ a.toReal) (hbn : 0 ≤ b.toReal) :
    0 ≤ (a / b).toReal := by
  obtain ⟨hu, hu', ht, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have hBp : 0 < |B| := abs_pos.mpr hB0
  -- the decoded divisor keeps its sign and is at least `(1 − 2u) |B|`
  have hb' : (1 - 2 * u) * |B| ≤ |b.toReal| := by
    have := abs_sub_abs_le_abs_sub B b.toReal
    rw [abs_sub_comm] at this; nlinarith
  have hbp : 0 < |b.toReal| := lt_of_lt_of_le (by nlinarith) hb'
  have hb0 : b.toReal ≠ 0 := abs_pos.mp hbp
  set q := A / B
  have hq : A = q * B := by rw [div_mul_cancel₀ _ hB0]
  have hQ : 0 ≤ |q| := abs_nonneg _
  -- `a' / b' − q = ((a' − A) − q (b' − B)) / b'`
  have hd : |a.toReal / b.toReal - q| ≤ (4 * u / (1 - 2 * u)) * |q| := by
    have e : a.toReal / b.toReal - q = ((a.toReal - A) - q * (b.toReal - B)) / b.toReal := by
      field_simp; rw [hq]; ring
    rw [e, abs_div, div_le_iff₀ hbp]
    have h1 : |(a.toReal - A) - q * (b.toReal - B)| ≤ 2 * u * |A| + |q| * (2 * u * |B|) := by
      have := abs_sub_le_add (a.toReal - A) (q * (b.toReal - B))
      rw [abs_mul] at this
      have := mul_le_mul_of_nonneg_left hB hQ
      linarith
    have hAq : |A| = |q| * |B| := by rw [hq, abs_mul]
    rw [hAq] at h1
    have h2u : 0 < 1 - 2 * u := by nlinarith
    calc _ ≤ 2 * u * (|q| * |B|) + |q| * (2 * u * |B|) := h1
      _ = (4 * u / (1 - 2 * u)) * |q| * ((1 - 2 * u) * |B|) := by field_simp; ring
      _ ≤ _ := by gcongr
  have hc : 4 * u / (1 - 2 * u) ≤ 1 / 2 ^ 50 - 2 * u := by
    rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have hS : |a.toReal / b.toReal| ≤ (1 + 1 / 2 ^ 50) * |q| := by
    have := abs_sub_abs_le_abs_sub (a.toReal / b.toReal) q
    have := mul_le_mul_of_nonneg_right hc hQ
    nlinarith
  have hM : |a.toReal / b.toReal| ≤ maxFinite := by
    have := two_pow_1023_le
    have := mul_le_mul (by norm_num : (1 + 1 / 2 ^ 50 : ℝ) ≤ 1 + 1 / 2 ^ 40) h hQ (by norm_num)
    linarith
  obtain ⟨-, he⟩ := L.div a b ha hb hb0 hM
  rw [he]
  exact L.model.nonneg _ (div_nonneg ha0 hbn)

theorem exp_le_two_pow : Real.exp (709 + 1 / 2 ^ 30) ≤ 2 ^ 1023 := by
  have hlog : (709 : ℝ) + 1 / 2 ^ 30 ≤ 1023 * Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  calc Real.exp (709 + 1 / 2 ^ 30) ≤ Real.exp (1023 * Real.log 2) := Real.exp_le_exp.mpr hlog
    _ = 2 ^ 1023 := by
      rw [show (1023 : ℝ) * Real.log 2 = Real.log (2 ^ 1023) by
        rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]

/-- **`exp`**: where `A ≤ 709`, `exp` of the decoded double is finite
(`709 < 1023 · ln 2`). -/
theorem core_exp (L : NativeLink) {a : Float} (ha : a.isFinite) {A : ℝ} (hA : |a.toReal - A| ≤ 2 * u * |A|)
    (h : A ≤ 709) : a.exp.isFinite := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hu1 : u ≤ 1 / 2 ^ 53 := hu'
  have ha' : a.toReal ≤ 709 + 1 / 2 ^ 30 := by
    have := le_abs_self (a.toReal - A)
    rcases le_total 0 A with h0 | h0
    · rw [abs_of_nonneg h0] at hA
      have : 2 * u * A ≤ 2 * (1 / 2 ^ 53) * 709 := by
        apply mul_le_mul (by linarith) h h0 (by norm_num)
      have : (2 : ℝ) * (1 / 2 ^ 53) * 709 ≤ 1 / 2 ^ 30 := by norm_num
      linarith
    · rw [abs_of_nonpos h0] at hA; nlinarith
  have hexp : Real.exp a.toReal ≤ maxFinite := by
    have h1 : Real.exp a.toReal ≤ Real.exp (709 + 1 / 2 ^ 30) := Real.exp_le_exp.mpr ha'
    have := exp_le_two_pow
    have := two_pow_1023_le
    have : (0 : ℝ) ≤ 2 ^ 1023 * (1 / 2 ^ 40) := by positivity
    linarith
  exact (L.exp a ha hexp).1

end NativeLink

end FloatBounds

end
