module

public import FloatBounds.Epsilon

/-!
# `ε` through double arithmetic (#568)

`epsilon_by_engine` (`SubstraitLean/Epsilon.lean`) carries each column's
error, how far an engine's value may be from the reference's, through the
double arithmetic between the aggregates and the output. The reference
rounds the exact result `z = f(a, b)` of its inputs once, `fl z`; the engine
computes from its own inputs `a'`, `b'`, within `εa`, `εb` of the
reference's. Forward mode (#568): the exact results differ by at most `Δ`, a
bound on the derivative over the inputs' ranges plus the remainder, and the
two roundings add the rest (`StdModel.transfer`).

With `|a| ≤ ma`, `|b| ≤ mb` and, for `/`, `|b| ≥ lb > 0` with `b` the same on
both sides:

| operation | `Δ` | `|z| ≤` | rule |
|---|---|---|---|
| `a + b`, `a − b` | `εa + εb` | `ma + mb` | `rule_add`, `rule_sub` |
| `a · b` | `ma εb + mb εa + εa εb` | `ma mb` | `rule_mul` |
| `a / b` | `εa / lb` | `ma / lb` | `rule_div` |

each giving `Δ (1 + u) + 2u (F + tiny)`, `F` the bound on `|z|`, where the
engine's operation is correctly rounded (IEEE 754: `+ − × /` on DuckDB and
Polars, the characterization's round 5). Polars divides by a literal as
`fl(a' · fl(1/b))` (polars-scalar-divisor), two roundings:
`rule_div_recip`, `Δ (1 + u)² + (3u + u²) F + (u (1 + u)(ma + εa) + 2u) tiny`.

Each rule assumes the exact results do not overflow, `F + Δ ≤ maxFinite`.
Elementary functions (`exp`, `log`, `sin`, …) are the platform's `libm`,
which IEEE 754 does not require to round correctly; they have no rule here.
-/

@[expose] public section

namespace FloatBounds

variable (M : StdModel)

/-- **The transfer rule.** The engine's `e` is within `ρ (|z'| + tiny)` of the
exact result `z'` of its inputs; the reference gives `fl z`. Where the exact
results are within `Δ` and `|z| ≤ F`: `|e − fl z| ≤ Δ (1 + ρ) + (ρ + u)(F + tiny)`. -/
theorem StdModel.transfer {z z' e Δ F ρ : ℝ} (hρ : 0 ≤ ρ) (hΔ : |z' - z| ≤ Δ) (hF : |z| ≤ F)
    (hzM : |z| ≤ maxFinite) (he : |e - z'| ≤ ρ * (|z'| + tiny)) :
    |e - M.fl z| ≤ Δ * (1 + ρ) + (ρ + u) * (F + tiny) := by
  have hr := M.err z hzM
  have hz' : |z'| ≤ F + Δ := by have := abs_sub_abs_le_abs_sub z' z; linarith
  have hu := u_pos
  calc |e - M.fl z| = |((e - z') + (z' - z)) - (M.fl z - z)| := by ring_nf
    _ ≤ |e - z'| + |z' - z| + |M.fl z - z| := by
        have := abs_sub_le_add ((e - z') + (z' - z)) (M.fl z - z)
        have := abs_add_le (e - z') (z' - z); linarith
    _ ≤ ρ * (F + Δ + tiny) + Δ + u * (F + tiny) := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right hz' tiny) hρ
        have := mul_le_mul_of_nonneg_left (add_le_add_right hF tiny) hu.le
        linarith
    _ = Δ * (1 + ρ) + (ρ + u) * (F + tiny) := by ring

/-- The rule for a correctly rounded operation of the engine, `ρ = u`. -/
theorem StdModel.transfer_ieee {z z' Δ F : ℝ} (hΔ : |z' - z| ≤ Δ) (hF : |z| ≤ F)
    (hov : F + Δ ≤ maxFinite) :
    |M.fl z' - M.fl z| ≤ Δ * (1 + u) + 2 * u * (F + tiny) := by
  have h0 : 0 ≤ Δ := le_trans (abs_nonneg _) hΔ
  have hz' : |z'| ≤ maxFinite := by have := abs_sub_abs_le_abs_sub z' z; linarith
  have := M.transfer u_pos.le hΔ hF (by linarith) (M.err z' hz')
  linarith

theorem add_delta {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb) :
    |(a' + b') - (a + b)| ≤ εa + εb ∧ |a + b| ≤ ma + mb := by
  constructor
  · calc _ = |(a' - a) + (b' - b)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add ha hb
  · exact le_trans (abs_add_le a b) (add_le_add hma hmb)

theorem sub_delta {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb) :
    |(a' - b') - (a - b)| ≤ εa + εb ∧ |a - b| ≤ ma + mb := by
  constructor
  · calc _ = |(a' - a) - (b' - b)| := by ring_nf
      _ ≤ _ := abs_sub_le_add _ _
      _ ≤ _ := add_le_add ha hb
  · exact le_trans (abs_sub_le_add a b) (add_le_add hma hmb)

theorem mul_delta {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb) :
    |a' * b' - a * b| ≤ ma * εb + mb * εa + εa * εb ∧ |a * b| ≤ ma * mb := by
  have hεa : 0 ≤ εa := le_trans (abs_nonneg _) ha
  have hεb : 0 ≤ εb := le_trans (abs_nonneg _) hb
  constructor
  · calc _ = |a * (b' - b) + b * (a' - a) + (a' - a) * (b' - b)| := by ring_nf
      _ ≤ |a * (b' - b)| + |b * (a' - a)| + |(a' - a) * (b' - b)| := by
          have := abs_add_le (a * (b' - b) + b * (a' - a)) ((a' - a) * (b' - b))
          have := abs_add_le (a * (b' - b)) (b * (a' - a)); linarith
      _ = |a| * |b' - b| + |b| * |a' - a| + |a' - a| * |b' - b| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ _ := by
          have := le_trans (abs_nonneg _) hma
          have := le_trans (abs_nonneg _) hmb
          gcongr
  · rw [abs_mul]; exact mul_le_mul hma hmb (abs_nonneg _) (le_trans (abs_nonneg _) hma)

theorem div_delta {a a' b εa ma lb : ℝ} (hlb : 0 < lb) (hb : lb ≤ |b|) (ha : |a' - a| ≤ εa)
    (hma : |a| ≤ ma) : |a' / b - a / b| ≤ εa / lb ∧ |a / b| ≤ ma / lb := by
  have hb0 : 0 < |b| := lt_of_lt_of_le hlb hb
  have hεa : 0 ≤ εa := le_trans (abs_nonneg _) ha
  constructor
  · rw [← sub_div, abs_div]
    exact div_le_div₀ hεa ha hlb hb
  · rw [abs_div]
    exact div_le_div₀ (le_trans (abs_nonneg _) hma) hma hlb hb

/-- **`+`**: `(εa + εb)(1 + u) + 2u (ma + mb + tiny)`. -/
theorem StdModel.rule_add {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb) (hov : ma + mb + (εa + εb) ≤ maxFinite) :
    |M.fl (a' + b') - M.fl (a + b)| ≤ (εa + εb) * (1 + u) + 2 * u * (ma + mb + tiny) := by
  obtain ⟨h1, h2⟩ := add_delta ha hb hma hmb
  have := M.transfer_ieee h1 h2 hov
  linarith

/-- **`−`**: as `+`. -/
theorem StdModel.rule_sub {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb) (hov : ma + mb + (εa + εb) ≤ maxFinite) :
    |M.fl (a' - b') - M.fl (a - b)| ≤ (εa + εb) * (1 + u) + 2 * u * (ma + mb + tiny) := by
  obtain ⟨h1, h2⟩ := sub_delta ha hb hma hmb
  have := M.transfer_ieee h1 h2 hov
  linarith

/-- **`×`**: `(ma εb + mb εa + εa εb)(1 + u) + 2u (ma mb + tiny)`. -/
theorem StdModel.rule_mul {a b a' b' εa εb ma mb : ℝ} (ha : |a' - a| ≤ εa) (hb : |b' - b| ≤ εb)
    (hma : |a| ≤ ma) (hmb : |b| ≤ mb)
    (hov : ma * mb + (ma * εb + mb * εa + εa * εb) ≤ maxFinite) :
    |M.fl (a' * b') - M.fl (a * b)|
      ≤ (ma * εb + mb * εa + εa * εb) * (1 + u) + 2 * u * (ma * mb + tiny) := by
  obtain ⟨h1, h2⟩ := mul_delta ha hb hma hmb
  exact M.transfer_ieee h1 h2 hov

/-- **`/`** by the same divisor on both sides, `|b| ≥ lb > 0`:
`(εa / lb)(1 + u) + 2u (ma / lb + tiny)`. -/
theorem StdModel.rule_div {a a' b εa ma lb : ℝ} (hlb : 0 < lb) (hb : lb ≤ |b|)
    (ha : |a' - a| ≤ εa) (hma : |a| ≤ ma) (hov : ma / lb + εa / lb ≤ maxFinite) :
    |M.fl (a' / b) - M.fl (a / b)| ≤ εa / lb * (1 + u) + 2 * u * (ma / lb + tiny) := by
  obtain ⟨h1, h2⟩ := div_delta hlb hb ha hma
  exact M.transfer_ieee h1 h2 hov

/-- Polars's quotient by a literal, `fl(a · fl(1/b))`, against the exact
`a / b`. -/
theorem StdModel.recip_mul_error {a b : ℝ} (h1 : |1 / b| ≤ maxFinite)
    (h2 : |a * M.fl (1 / b)| ≤ maxFinite) :
    |M.fl (a * M.fl (1 / b)) - a / b| ≤ (2 * u + u ^ 2) * |a / b| + (u * (1 + u) * |a| + u) * tiny := by
  have hu := u_pos
  have ht := tiny_pos
  have hr := M.err (1 / b) h1
  set r := M.fl (1 / b)
  have hab : a / b = a * (1 / b) := by ring
  have e1 : |a * r - a / b| ≤ u * |a / b| + u * |a| * tiny := by
    rw [hab, ← mul_sub, abs_mul]
    have := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    rw [abs_mul] at *
    nlinarith [abs_nonneg a, abs_nonneg (1 / b)]
  have e2 := M.err (a * r) h2
  have har : |a * r| ≤ |a / b| + (u * |a / b| + u * |a| * tiny) := by
    have := abs_sub_abs_le_abs_sub (a * r) (a / b); linarith
  have hab0 := abs_nonneg (a / b)
  have ha0 := abs_nonneg a
  calc _ = |(M.fl (a * r) - a * r) + (a * r - a / b)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ u * (|a / b| + (u * |a / b| + u * |a| * tiny) + tiny) + (u * |a / b| + u * |a| * tiny) := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right har tiny) hu.le
        linarith
    _ = _ := by ring

/-- **Polars's `/` by a literal** `b`, `|b| ≥ lb > 0`, against the
reference's `fl(a / b)`:
`(εa / lb)(1 + u)² + (3u + u²)(ma / lb) + (u (1 + u)(ma + εa) + 2u) tiny`. -/
theorem StdModel.rule_div_recip {a a' b εa ma lb : ℝ} (hlb : 0 < lb) (hb : lb ≤ |b|)
    (ha : |a' - a| ≤ εa) (hma : |a| ≤ ma) (hab : |a / b| ≤ maxFinite)
    (h1 : |1 / b| ≤ maxFinite) (h2 : |a' * M.fl (1 / b)| ≤ maxFinite) :
    |M.fl (a' * M.fl (1 / b)) - M.fl (a / b)|
      ≤ εa / lb * (1 + u) ^ 2 + (3 * u + u ^ 2) * (ma / lb)
        + (u * (1 + u) * (ma + εa) + 2 * u) * tiny := by
  have hu := u_pos
  have ht := tiny_pos
  obtain ⟨d1, d2⟩ := div_delta hlb hb ha hma
  have e := M.recip_mul_error h1 h2
  have r := M.err (a / b) hab
  have ha' : |a'| ≤ ma + εa := by have := abs_sub_abs_le_abs_sub a' a; linarith
  have hq : |a' / b| ≤ ma / lb + εa / lb := by
    have := abs_sub_abs_le_abs_sub (a' / b) (a / b); linarith
  have hεa : 0 ≤ εa / lb := le_trans (abs_nonneg _) d1
  have hm0 : 0 ≤ ma / lb := le_trans (abs_nonneg _) d2
  have p1 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * u + u ^ 2)
  have p2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha' (by positivity : (0 : ℝ) ≤ u * (1 + u))) ht.le
  have p3 := mul_le_mul_of_nonneg_left d2 hu.le
  calc _ = |(M.fl (a' * M.fl (1 / b)) - a' / b) + (a' / b - a / b) - (M.fl (a / b) - a / b)| := by
        ring_nf
    _ ≤ |M.fl (a' * M.fl (1 / b)) - a' / b| + |a' / b - a / b| + |M.fl (a / b) - a / b| := by
        have := abs_sub_le_add ((M.fl (a' * M.fl (1 / b)) - a' / b) + (a' / b - a / b))
          (M.fl (a / b) - a / b)
        have := abs_add_le (M.fl (a' * M.fl (1 / b)) - a' / b) (a' / b - a / b); linarith
    _ ≤ _ := by nlinarith

end FloatBounds

end
