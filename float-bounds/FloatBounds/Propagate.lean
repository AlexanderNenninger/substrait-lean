module

public import FloatBounds.Epsilon
public import FloatBounds.Arith

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
`exp` is the platform's `libm` on both sides, trusted to one ulp
(`NativeLink.exp`): `rule_exp`, from `|exp x − exp y| ≤ exp M · |x − y|`. The
other elementary functions (`log`, `sin`, …) have no rule here.
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

/-- `|exp x − exp y| ≤ exp M · |x − y|` for `x, y ≤ M`. -/
theorem abs_exp_sub_exp_le {x y M : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this hy hx (by linarith)
  have h1 : 1 - (x - y) ≤ Real.exp (-(x - y)) := by
    have := Real.add_one_le_exp (-(x - y)); linarith
  have e : Real.exp x - Real.exp y = Real.exp x * (1 - Real.exp (-(x - y))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have hpos : 0 ≤ Real.exp x - Real.exp y := by
    have := Real.exp_le_exp.mpr hxy; linarith
  rw [abs_of_nonneg hpos, abs_of_nonneg (by linarith), e]
  have := Real.exp_le_exp.mpr hx
  have := Real.exp_pos x
  nlinarith

/-- **`exp`**, the platform's `libm` on both sides (one ulp, `NativeLink.exp`):
where `a ≤ ha` and the engine's input is within `εa`,
`εa · exp (ha + εa) · (1 + 2u) + 4u (exp ha + tiny)`. -/
theorem rule_exp {a a' εa ha r e : ℝ} (hεa : |a' - a| ≤ εa) (hha : a ≤ ha)
    (hr : |r - Real.exp a| ≤ 2 * u * (Real.exp a + tiny))
    (he : |e - Real.exp a'| ≤ 2 * u * (Real.exp a' + tiny)) :
    |e - r| ≤ εa * Real.exp (ha + εa) * (1 + 2 * u) + 4 * u * (Real.exp ha + tiny) := by
  have hu := u_pos
  have h0 : 0 ≤ εa := le_trans (abs_nonneg _) hεa
  have ha' : a' ≤ ha + εa := by have := le_abs_self (a' - a); linarith
  have hd : |Real.exp a' - Real.exp a| ≤ εa * Real.exp (ha + εa) := by
    have := abs_exp_sub_exp_le ha' (show a ≤ ha + εa by linarith)
    have := mul_le_mul_of_nonneg_left hεa (Real.exp_pos (ha + εa)).le
    linarith
  have hEa : Real.exp a ≤ Real.exp ha := Real.exp_le_exp.mpr hha
  have hEa' : Real.exp a' ≤ Real.exp ha + εa * Real.exp (ha + εa) := by
    have := le_abs_self (Real.exp a' - Real.exp a); linarith
  calc |e - r| = |(e - Real.exp a') + (Real.exp a' - Real.exp a) - (r - Real.exp a)| := by ring_nf
    _ ≤ |e - Real.exp a'| + |Real.exp a' - Real.exp a| + |r - Real.exp a| := by
        have := abs_sub_le_add ((e - Real.exp a') + (Real.exp a' - Real.exp a)) (r - Real.exp a)
        have := abs_add_le (e - Real.exp a') (Real.exp a' - Real.exp a); linarith
    _ ≤ 2 * u * (Real.exp ha + εa * Real.exp (ha + εa) + tiny) + εa * Real.exp (ha + εa)
        + 2 * u * (Real.exp ha + tiny) := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right hEa' tiny) (by positivity : (0 : ℝ) ≤ 2 * u)
        have := mul_le_mul_of_nonneg_left (add_le_add_right hEa tiny) (by positivity : (0 : ℝ) ≤ 2 * u)
        linarith
    _ = _ := by ring

/-! ## Exact and step functions (#568)

`abs` and negation are exact on both engines and 1-Lipschitz. `FLOOR`,
`CEIL`, `ROUND` and casts to integers are steps: the engine's input within
`εa` of the reference's may cross a step, so their results are within
`εa + c₁ + c₂` where each lies in `[x − c₁, x + c₂]` (`FLOOR` 1, `CEIL` 1,
`ROUND` 1, truncation toward zero 2). `sqrt` is correctly rounded on both
engines (`NativeLink.sqrt`). -/

/-- **`abs`**: `||a'| − |a|| ≤ εa`. -/
theorem rule_abs {a a' εa : ℝ} (h : |a' - a| ≤ εa) : abs (abs a' - abs a) ≤ εa :=
  le_trans (abs_abs_sub_abs_le_abs_sub a' a) h

/-- **A step function** whose value lies in `[x − c₁, x + c₂]`: within
`εa + c₁ + c₂`. -/
theorem rule_step {f : ℝ → ℝ} {c₁ c₂ : ℝ} (hf : ∀ x, x - c₁ ≤ f x ∧ f x ≤ x + c₂)
    {a a' εa : ℝ} (h : |a' - a| ≤ εa) : |f a' - f a| ≤ εa + (c₁ + c₂) := by
  have h1 := hf a; have h2 := hf a'
  have := abs_le.mp h
  rw [abs_le]; constructor <;> linarith

theorem floor_step (x : ℝ) : x - 1 ≤ (⌊x⌋ : ℝ) ∧ (⌊x⌋ : ℝ) ≤ x + 0 :=
  ⟨by have := Int.sub_one_lt_floor x; linarith, by have := Int.floor_le x; linarith⟩

theorem ceil_step (x : ℝ) : x - 0 ≤ (⌈x⌉ : ℝ) ∧ (⌈x⌉ : ℝ) ≤ x + 1 :=
  ⟨by have := Int.le_ceil x; linarith, by have := Int.ceil_lt_add_one x; linarith⟩

/-- **`FLOOR`**: within `εa + 1`. -/
theorem rule_floor {a a' εa : ℝ} (h : |a' - a| ≤ εa) : |(⌊a'⌋ : ℝ) - ⌊a⌋| ≤ εa + 1 := by
  have := rule_step (f := fun x => (⌊x⌋ : ℝ)) floor_step h; simpa using this

/-- **`CEIL`**: within `εa + 1`. -/
theorem rule_ceil {a a' εa : ℝ} (h : |a' - a| ≤ εa) : |(⌈a'⌉ : ℝ) - ⌈a⌉| ≤ εa + 1 := by
  have := rule_step (f := fun x => (⌈x⌉ : ℝ)) ceil_step h; simpa using this

/-- **`ROUND`**, any rounding to an integer within `1/2` (half away from zero
as SQL rounds): within `εa + 1`. -/
theorem rule_round {r : ℝ → ℝ} (hr : ∀ x, |r x - x| ≤ 1 / 2) {a a' εa : ℝ}
    (h : |a' - a| ≤ εa) : |r a' - r a| ≤ εa + 1 := by
  have := rule_step (f := r) (c₁ := 1 / 2) (c₂ := 1 / 2)
    (fun x => by have := abs_le.mp (hr x); constructor <;> linarith) h
  linarith

/-- **A cast to an integer by truncation toward zero**: within `εa + 2`. -/
theorem rule_trunc {t : ℝ → ℝ} (ht : ∀ x, |t x - x| ≤ 1) {a a' εa : ℝ}
    (h : |a' - a| ≤ εa) : |t a' - t a| ≤ εa + 2 := by
  have := rule_step (f := t) (c₁ := 1) (c₂ := 1)
    (fun x => by have := abs_le.mp (ht x); constructor <;> linarith) h
  linarith

/-- `√` is `1/2`-Hölder (`abs_sqrt_sub_sqrt_le`, `Variance.lean`), and
`|√x − √y| ≤ |x − y| / s` where `√x + √y ≥ s > 0`. -/
theorem abs_sqrt_sub_sqrt_le_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 < s)
    (hsum : s ≤ √x + √y) : |√x - √y| ≤ |x - y| / s := by
  have e : (√x - √y) * (√x + √y) = x - y := by
    have := Real.sq_sqrt hx; have := Real.sq_sqrt hy; ring_nf; linarith
  rw [le_div_iff₀ hs]
  calc |√x - √y| * s ≤ |√x - √y| * (√x + √y) := by gcongr
    _ = |x - y| := by
      rw [← e, abs_mul, abs_of_nonneg (show 0 ≤ √x + √y by positivity)]

/-- **`sqrt`**, correctly rounded on both sides: inputs `a, a' ≥ 0` within `εa`
whose square roots differ by at most `Δ` (`√εa`, or `εa / s`), with `a ≤ ha`:
`Δ (1 + u) + 2u (√ha + tiny)`. -/
theorem StdModel.rule_sqrt (M : StdModel) {a a' ha Δ : ℝ} (ha0 : 0 ≤ a) (hha : a ≤ ha)
    (hΔ : |√a' - √a| ≤ Δ) (hov : √ha + Δ ≤ maxFinite) :
    |M.fl (√a') - M.fl (√a)| ≤ Δ * (1 + u) + 2 * u * (√ha + tiny) := by
  have hF : |√a| ≤ √ha := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_sqrt hha
  exact M.transfer_ieee hΔ hF hov

/-- **A comparison's threshold** (#568): where `a ≤ ha`, `lb ≤ b` and the
ranges widened by `ε` do not meet, `a < b` on both sides. -/
theorem rule_threshold {a a' b b' ha lb εa εb : ℝ} (hεa : |a' - a| ≤ εa) (hεb : |b' - b| ≤ εb)
    (hha : a ≤ ha) (hlb : lb ≤ b) (h : ha + εa < lb - εb) : a < b ∧ a' < b' := by
  have := abs_le.mp hεa; have := abs_le.mp hεb
  constructor <;> linarith

end FloatBounds

end
