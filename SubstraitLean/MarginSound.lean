import SubstraitLean.MarginCheck
import SubstraitLean.SumBound
import SubstraitLean.FloatArith
import SubstraitLean.Partition

/-!
# The margin check is sound, in codes (#929)

`marginCount` (`MarginCheck.lean`) writes, per group, the test
`|fl(v − t)| > fl(cₙ · fl(A + n · 2⁻¹⁰²²))`, `cₙ = (8n + 16) · 2⁻⁵³`, in the
core's doubles. This module proves it sound against `Rel.AllowedP`'s sums:
when the check passes on one engine sum `v₁` of a group, with `A` the
engine's `SUM(ABS(x))`, every sum `SumOrder` allows (`v₂`, the sink's) and the
reference's `floatSumCR` lie on one side of `t`, strictly.

The proof follows `StdModel.check_sound` (`float-bounds`), in integers: the
values in units of `2⁻¹⁰⁷⁴` (`scaled`), the rounding of each operation from
`ofExact_rel` and `ofExactDiv_err` (relative `2⁻⁵³`, plus `2⁻¹⁰⁷⁵` below the
normal range), and each sum's distance from the exact sum from `SumBound`
(D35). It loses a factor of two where `check_sound` keeps `γₙ`: with
`T = Σ|xᵢ| + n · 2⁻¹⁰²²`, each sum is within `2(n + 1) · T · 2⁻⁵³` of the
exact sum, and the check's margin is at least `(8n + 16) · T / 2 · 2⁻⁵³`
less its roundings, which leaves `4 · T · 2⁻⁵³` to spare.
-/

namespace Substrait

open FloatCode

set_option exponentiation.threshold 3200

/-! ## Codes of exact constants -/

theorem scaled_neg (c : Int) : scaled (-c) = -scaled c := by
  unfold scaled
  by_cases h : c = 0
  · subst h; rfl
  · rw [Int.natAbs_neg]; split <;> split <;> omega

theorem IsFin.neg' {c : Int} (h : IsFin c) : IsFin (-c) := by
  have := posInf_eq; have := negInf_eq
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem isFin_posCode {m : Nat} (h : m ≤ maxMag) : IsFin (posCode m) := by
  have := posInf_eq; have := negInf_eq
  rw [posCode_of_le h]
  constructor <;> split <;> omega

/-- Codes order finite doubles as their values, strictly where the values
differ. -/
theorem lt_of_scaled_lt {c d : Int} (h : scaled c < scaled d) : c < d := by
  apply Classical.byContradiction; intro h'
  have := scaled_mono (Int.not_lt.1 h'); omega

/-- An integer of at most `2⁵³` converts exactly. -/
theorem ofInt_nat {n : Nat} (h : n ≤ 2 ^ 53) :
    IsFin (ofInt n) ∧ scaled (ofInt n) = n * 2 ^ 1074 := by
  rw [ofInt_exact (by simpa using h), scaled_exactCode]
  refine ⟨?_, rfl⟩
  by_cases h0 : n = 0
  · subst h0
    have e : exactCode ((0 : Nat) : Int) = 0 := by simp [exactCode, FloatFormat.exactCode]
    have := posInf_eq; have := negInf_eq; rw [e]; exact ⟨by omega, by omega⟩
  · have hm : n * 2 ^ 1074 ≤ maxMag := by
      rw [maxMag_def]
      calc n * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1074 := Nat.mul_le_mul_right _ h
        _ ≤ (2 ^ 53 - 1) * 2 ^ 2045 := by omega
    have e : exactCode (n : Int) = posCode (n * 2 ^ 1074) := by
      rw [posCode_of_le hm]
      simp only [exactCode, FloatFormat.exactCode, fp64_scale, Int.natAbs_natCast]
      have h1 : ¬ (n : Int) = 0 := by omega
      have h2 : ¬ (n : Int) < 0 := by omega
      have h3 : ¬ n * 2 ^ 1074 = 0 := by exact Nat.mul_ne_zero h0 (by omega)
      simp only [h1, h2, h3, ↓reduceIte]
    rw [e]; exact isFin_posCode hm

/-! ## One rounding, relative `2⁻⁵³` -/

theorem add_rel {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a + scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (fadd a b) ∧ 2 ^ 53 * (scaled (fadd a b) - (scaled a + scaled b)).natAbs ≤
      (scaled a + scaled b).natAbs := by
  rw [fadd_fin ha hb]; exact ofExact_rel h

theorem sub_rel {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a - scaled b).natAbs ≤ 2 ^ 2097) :
    IsFin (fsub a b) ∧ 2 ^ 53 * (scaled (fsub a b) - (scaled a - scaled b)).natAbs ≤
      (scaled a - scaled b).natAbs := by
  rw [fsub_fin ha hb]; exact ofExact_rel h

theorem mul_rel {a b : Int} (ha : IsFin a) (hb : IsFin b)
    (h : (scaled a).natAbs * (scaled b).natAbs ≤ 2 ^ 3171) :
    IsFin (fmul a b) ∧
      2 ^ 53 * (2 ^ 1074 * scaled (fmul a b) - scaled a * scaled b).natAbs ≤
        (scaled a).natAbs * (scaled b).natAbs + 2 ^ 1074 * 2 ^ 52 := by
  have hv : (scaled a * scaled b).natAbs = (scaled a).natAbs * (scaled b).natAbs :=
    Int.natAbs_mul _ _
  have hn : 0 < unitK := Nat.two_pow_pos _
  rw [fmul_fin ha hb]
  have hf := ofExactDiv_fin (v := scaled a * scaled b) hn (by
    rw [hv]; refine Nat.le_trans h (Nat.le_of_eq ?_); unfold unitK; rw [← Nat.pow_add])
  refine ⟨hf, ?_⟩
  have he := ofExactDiv_err hn hf
  rw [hv] at he
  have hk : ((unitK : Nat) : Int) = 2 ^ 1074 := Int.natCast_pow 2 1074
  rw [hk] at he
  generalize (2 ^ 1074 * scaled (ofExactDiv (scaled a * scaled b) unitK) -
    scaled a * scaled b).natAbs = E at he ⊢
  rw [show unitK = 2 ^ 1074 from rfl] at he
  generalize (scaled a).natAbs * (scaled b).natAbs = P at he ⊢
  have := Nat.max_le.2 ⟨Nat.le_add_right P (2 ^ 1074 * 2 ^ 52), Nat.le_add_left (2 ^ 1074 * 2 ^ 52) P⟩
  omega

/-! ## A group's sums -/

/-- `|x|` of a double's code, as `Expr.fabs` computes it. -/
def absCode (c : Int) : Int := if c < 0 then -c else c

theorem absCode_fin {c : Int} (h : IsFin c) : IsFin (absCode c) := by
  unfold absCode; split
  · exact IsFin.neg' h
  · exact h

theorem scaled_absCode (c : Int) : scaled (absCode c) = (scaled c).natAbs := by
  unfold absCode
  split
  · rename_i h; rw [scaled_neg]
    have : scaled c ≤ 0 := by unfold scaled; split <;> omega
    omega
  · rename_i h
    have : 0 ≤ scaled c := by unfold scaled; split <;> omega
    omega

theorem natAbs_exactSum_le (cs : List Int) :
    (exactSum (cs.map .float)).natAbs ≤ scaledAbsSum (cs.map .float) := by
  induction cs with
  | nil => simp [exactSum, scaledAbsSum]
  | cons c cs ih =>
    simp only [List.map_cons, exactSum, scaledAbsSum, exact]
    have := Int.natAbs_add_le (scaled c) (exactSum (cs.map .float))
    omega

theorem scaledAbsSum_abs (cs : List Int) :
    scaledAbsSum ((cs.map absCode).map .float) = scaledAbsSum (cs.map .float) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, scaledAbsSum, scaled_absCode, Int.natAbs_natCast]
    simp only [List.map_map] at ih ⊢
    rw [ih]

theorem exactSum_abs (cs : List Int) :
    exactSum ((cs.map absCode).map .float) = scaledAbsSum (cs.map .float) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, exactSum, scaledAbsSum, exact, scaled_absCode]
    simp only [List.map_map] at ih ⊢
    rw [ih]; push_cast; rfl

/-- **A sum `SumOrder` allows is near the exact sum**: on `1 ≤ n ≤ 2³²`
finite doubles whose `T = Σ|xᵢ| + n · 2⁻¹⁰²²` stays below half the largest
double, every behaviour's sum is finite and within `2(n + 1) · T · 2⁻⁵³` of
the exact sum. `EXACT` by `ofExact_rel`; every other behaviour by `SumBound`
(D35), whose `γₙ + u` this takes as `2(n + 1) · 2⁻⁵³`. -/
theorem SumOrder.near {b : Behaviour} {cs : List Int} {v : Int}
    (h : SumOrder b (cs.map .float) v) (hf : ∀ c ∈ cs, IsFin c) (hn : cs.length ≤ 2 ^ 32)
    (hov : 2 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag) :
    IsFin v ∧ (scaled v - exactSum (cs.map .float)).natAbs * 2 ^ 53 ≤
      2 * (cs.length * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52)) +
        2 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) := by
  have hS := natAbs_exactSum_le cs
  generalize hB : scaledAbsSum (cs.map .float) = B at hS hov ⊢
  generalize hT : B + cs.length * 2 ^ 52 = T at hov ⊢
  by_cases hb : b = "EXACT"
  · simp only [SumOrder, hb, ↓reduceIte] at h
    rw [h, floatSumCR, nonFinite_of_fin hf, Option.getD_none]
    have hmax : maxMag ≤ 2 ^ 2098 := by rw [maxMag_def]; omega
    obtain ⟨hfin, he⟩ := ofExact_rel (S := exactSum (cs.map .float)) (by omega)
    refine ⟨hfin, ?_⟩
    have : cs.length * T ≥ 0 := Nat.zero_le _
    omega
  · simp only [SumOrder, hb, ↓reduceIte] at h
    have hlen : (cs.map Value.float).length = cs.length := List.length_map _
    obtain ⟨hfin, hineq⟩ := h.1
      (fun x hx => by
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hx
        injection e with e; subst e; exact hf _ hy)
      (by rw [hlen]; omega)
      (by rw [hlen, hB]; omega)
    rw [hlen, hB, hT] at hineq
    refine ⟨hfin, ?_⟩
    generalize (scaled v - exactSum (cs.map .float)).natAbs = e at hineq ⊢
    generalize cs.length = n at hineq hn ⊢
    clear hov hS hB hT hfin hf h
    have hk : 2 ^ 52 ≤ 2 ^ 53 - n := by omega
    have h1 : e * (2 ^ 53 * 2 ^ 52) ≤ e * (2 ^ 53 * (2 ^ 53 - n)) :=
      Nat.mul_le_mul_left e (Nat.mul_le_mul_left _ hk)
    have h2 : (n * 2 ^ 53 + (2 ^ 53 - n)) * T ≤ (n * 2 ^ 53 + 2 ^ 53) * T :=
      Nat.mul_le_mul_right T (Nat.add_le_add_left (Nat.sub_le _ _) _)
    have h3 : (n * 2 ^ 53 + 2 ^ 53) * T = 2 ^ 53 * (n * T) + 2 ^ 53 * T := by
      rw [Nat.add_mul, Nat.mul_comm n, Nat.mul_assoc]
    have h4 : e * (2 ^ 53 * 2 ^ 52) = e * 2 ^ 53 * 2 ^ 52 := by rw [Nat.mul_assoc]
    have h5 := Nat.le_trans h1 (Nat.le_trans hineq h2)
    rw [h3, h4] at h5
    have h6 : 2 ^ 53 * (n * T) + 2 ^ 53 * T = (2 * (n * T) + 2 * T) * 2 ^ 52 := by
      grind
    rw [h6] at h5
    exact Nat.le_of_mul_le_mul_right h5 (Nat.two_pow_pos 52)

/-! ## Roundings as integer bounds -/

theorem add_le {a b : Int} (ha : IsFin a) (hb : IsFin b) (h0 : 0 ≤ scaled a + scaled b)
    (h : scaled a + scaled b ≤ 2 ^ 2097) :
    IsFin (fadd a b) ∧ (2 ^ 53 - 1) * (scaled a + scaled b) ≤ 2 ^ 53 * scaled (fadd a b) ∧
      2 ^ 53 * scaled (fadd a b) ≤ (2 ^ 53 + 1) * (scaled a + scaled b) := by
  obtain ⟨hf, he⟩ := add_rel ha hb (by omega)
  refine ⟨hf, ?_⟩
  generalize scaled a + scaled b = S at h0 h he
  generalize scaled (fadd a b) = r at he
  omega

theorem mul_le {a b : Int} (ha : IsFin a) (hb : IsFin b) (h0a : 0 ≤ scaled a) (h0b : 0 ≤ scaled b)
    (h : scaled a * scaled b ≤ 2 ^ 3171) :
    IsFin (fmul a b) ∧
      (2 ^ 53 - 1) * (scaled a * scaled b) - 2 ^ 1126 ≤ 2 ^ 53 * (2 ^ 1074 * scaled (fmul a b)) ∧
      2 ^ 53 * (2 ^ 1074 * scaled (fmul a b)) ≤ (2 ^ 53 + 1) * (scaled a * scaled b) + 2 ^ 1126 := by
  have hP : 0 ≤ scaled a * scaled b := Int.mul_nonneg h0a h0b
  obtain ⟨hf, he⟩ := mul_rel ha hb (by rw [← Int.natAbs_mul]; omega)
  refine ⟨hf, ?_⟩
  rw [← Int.natAbs_mul] at he
  generalize scaled a * scaled b = P at hP h he
  generalize scaled (fmul a b) = r at he
  omega

/-! ## The check -/

/-- The margin `marginCount` computes for a group of `n` values whose
`SUM(ABS(x))` is `a`: `fl(cₙ · fl(a + n · 2⁻¹⁰²²))`, divided by `n` first for
an `AVG`, with `cₙ = fl(fl(fl(8 · n) + c₀) · 2⁻⁵³)`. -/
def marginCode (avg : Bool) (n : Nat) (a : Int) : Int :=
  let n' := ofInt n
  let c := fmul (fadd (fmul marginEight n') (marginC0 avg)) marginUlp
  let p := fadd a (fmul n' marginTiny)
  fmul c (if avg then fdiv p n' else p)

/-- The check passes on a group whose sum is `v`: the margin is below
`|fl(v − t)|`, as `marginCount`'s `pass` compares. -/
def marginPass (avg : Bool) (n : Nat) (a v t : Int) : Prop :=
  marginCode avg n a < fsub v t ∨ marginCode avg n a < -(fsub v t)

theorem posCode_const {m : Nat} (h : m ≤ 2 ^ 1080) : IsFin (posCode m) ∧ scaled (posCode m) = m := by
  have hm := maxMag_def
  exact ⟨isFin_posCode (by omega), by rw [scaled_posCode (by omega)]⟩

theorem marginEight_eq : IsFin marginEight ∧ scaled marginEight = 8 * 2 ^ 1074 :=
  posCode_const (by omega)

theorem marginC0_eq (avg : Bool) :
    IsFin (marginC0 avg) ∧ scaled (marginC0 avg) = marginConst avg * 2 ^ 1074 :=
  posCode_const (by cases avg <;> simp [marginConst] <;> omega)

theorem marginUlp_eq : IsFin marginUlp ∧ scaled marginUlp = 2 ^ 1021 := posCode_const (by omega)

theorem marginTiny_eq : IsFin marginTiny ∧ scaled marginTiny = 2 ^ 52 := posCode_const (by omega)

/-- `scaled m ≤ |scaled d|` when the check passes. -/
theorem pass_le {m d : Int} (h : m < d ∨ m < -d) : scaled m ≤ (scaled d).natAbs := by
  rcases h with h | h
  · have := scaled_mono (Int.le_of_lt h); omega
  · have := scaled_mono (Int.le_of_lt h); rw [scaled_neg] at this; omega

/-- **The check of a `SUM`, in codes**: a group of `1 ≤ n ≤ 2³²` values with
`T = Σ|xᵢ| + n · 2⁻¹⁰²²` at most a quarter of the largest double, whose
engine `SUM(ABS(x))` `a` is near `Σ|xᵢ|` (`SumOrder.near`), and whose engine
sum `v` passes the check, has `|v − t| > 4(n + 1) · T · 2⁻⁵³`: twice the
distance `SumOrder.near` allows any sum from the exact one. -/
theorem check_sum {v t a : Int} {n B : Nat} (hv : IsFin v) (ht : IsFin t) (ha : IsFin a)
    (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 32) (hov : 4 * (B + n * 2 ^ 52) ≤ maxMag)
    (hA : (scaled a - B).natAbs * 2 ^ 53 ≤ 2 * (n * (B + n * 2 ^ 52)) + 2 * (B + n * 2 ^ 52))
    (hpass : marginPass false n a v t) :
    4 * (n * (B + n * 2 ^ 52)) + 4 * (B + n * 2 ^ 52) < (scaled v - scaled t).natAbs * 2 ^ 53 := by
  have hm := maxMag_def
  generalize hT : B + n * 2 ^ 52 = T at hov hA ⊢
  have hnT : n * T ≤ 2 ^ 32 * T := Nat.mul_le_mul_right T hn
  have hWi : ((n * T : Nat) : Int) = (n : Int) * (T : Int) := by push_cast; rfl
  generalize hW : n * T = W at hA hnT hWi ⊢
  obtain ⟨fN, sN⟩ := ofInt_nat (n := n) (by omega)
  obtain ⟨f8, s8⟩ := marginEight_eq
  obtain ⟨f16, s16⟩ := marginC0_eq false
  obtain ⟨fU, sU⟩ := marginUlp_eq
  obtain ⟨fT, sT⟩ := marginTiny_eq
  simp only [marginConst, Bool.false_eq_true, ↓reduceIte] at s16
  simp only [marginPass, marginCode, Bool.false_eq_true, ↓reduceIte] at hpass
  generalize hc1 : fmul marginEight (ofInt n) = c1 at hpass
  generalize hc2 : fadd c1 (marginC0 false) = c2 at hpass
  generalize hc3 : fmul c2 marginUlp = c3 at hpass
  generalize hq : fmul (ofInt n) marginTiny = q at hpass
  generalize hp : fadd a q = p at hpass
  generalize hmc : fmul c3 p = m at hpass
  generalize hd : fsub v t = d at hpass
  have hmd := pass_le hpass
  -- `c₁ = fl(8 · n)`, `c₂ = fl(c₁ + 16)`, `c₃ = fl(c₂ · 2⁻⁵³)`.
  obtain ⟨f1, l1, u1⟩ := mul_le f8 fN (by omega) (by omega) (by rw [s8, sN]; omega)
  rw [hc1, s8, sN] at l1 u1; rw [hc1] at f1
  obtain ⟨f2, l2, u2⟩ := add_le f1 f16 (by omega) (by omega)
  rw [hc2] at f2 l2 u2
  obtain ⟨f3, l3, u3⟩ := mul_le f2 fU (by omega) (by omega) (by rw [sU]; omega)
  rw [hc3, sU] at l3 u3; rw [hc3] at f3
  have hc3lo : (8 * (n : Int) + 16) * (2 ^ 1021 * (2 ^ 53 - 4)) ≤ 2 ^ 53 * scaled c3 := by omega
  have hc3hi : scaled c3 ≤ 2 ^ 1060 := by omega
  clear l1 u1 l2 u2 l3 u3
  -- `q = fl(n · 2⁻¹⁰²²)`, `p = fl(a + q)`: `p ≥ T / 2`.
  obtain ⟨fq, lq, uq⟩ := mul_le fN fT (by omega) (by omega) (by rw [sN, sT]; omega)
  rw [hq, sN, sT] at lq uq; rw [hq] at fq
  obtain ⟨fp, lp, up⟩ := add_le ha fq (by omega) (by omega)
  rw [hp] at fp lp up
  have hP2 : (T : Int) ≤ 2 * scaled p := by omega
  have hP3 : 0 ≤ scaled p ∧ scaled p ≤ 2 ^ 2097 := by omega
  clear lq uq lp up
  -- `m = fl(c₃ · p)`.
  have hcp : scaled c3 * scaled p ≤ 2 ^ 3171 := by
    have := Int.mul_le_mul hc3hi hP3.2 hP3.1 (by omega)
    omega
  obtain ⟨fm, lm, -⟩ := mul_le f3 fp (by omega) hP3.1 hcp
  rw [hmc] at lm
  have hQ : 8 * (2 ^ 1021 * (2 ^ 53 - 4)) * ((n : Int) * scaled p) +
      16 * (2 ^ 1021 * (2 ^ 53 - 4)) * scaled p ≤ 2 ^ 53 * (scaled c3 * scaled p) := by
    have := Int.mul_le_mul_of_nonneg_right hc3lo hP3.1
    have e1 : (8 * (n : Int) + 16) * (2 ^ 1021 * (2 ^ 53 - 4)) * scaled p =
        8 * (2 ^ 1021 * (2 ^ 53 - 4)) * ((n : Int) * scaled p) +
          16 * (2 ^ 1021 * (2 ^ 53 - 4)) * scaled p := by grind
    have e2 : 2 ^ 53 * scaled c3 * scaled p = 2 ^ 53 * (scaled c3 * scaled p) := Int.mul_assoc _ _ _
    omega
  have hNP : (n : Int) * T ≤ 2 * ((n : Int) * scaled p) := by
    have := Int.mul_le_mul_of_nonneg_left hP2 (Int.natCast_nonneg n)
    have e : (n : Int) * (2 * scaled p) = 2 * ((n : Int) * scaled p) := by grind
    omega
  generalize scaled c3 * scaled p = Q at hQ lm
  generalize (n : Int) * scaled p = NP at hQ hNP
  -- `d = fl(v − t)`.
  by_cases hbig : (scaled v - scaled t).natAbs ≤ 2 ^ 2097
  · obtain ⟨-, hd'⟩ := sub_rel hv ht hbig
    rw [hd] at hd'
    omega
  · omega

/-- **The margin check of a `SUM`, end to end, in codes** (#929): on a group
of `1 ≤ n ≤ 2³²` finite doubles with `Σ|xᵢ| + n · 2⁻¹⁰²²` at most a quarter of
the largest double, if the check passes on one sum `v₁` an engine's
`sum_order` allows, with `a` the engine's `SUM(ABS(x))`, then every sum `v₂`
any `sum_order` allows and the reference's `floatSumCR` lie strictly on one
side of `t`. The codes compare as the values do, so a filter comparing `v₂`
with `t` keeps the group exactly when the reference's does. -/
theorem margin_sum {b₁ b₂ bA : Behaviour} {cs : List Int} {v₁ v₂ a t : Int}
    (hf : ∀ c ∈ cs, IsFin c) (hne : cs ≠ []) (hn : cs.length ≤ 2 ^ 32)
    (hov : 4 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag)
    (h₁ : SumOrder b₁ (cs.map .float) v₁) (h₂ : SumOrder b₂ (cs.map .float) v₂)
    (hA : SumOrder bA ((cs.map absCode).map .float) a) (ht : IsFin t)
    (hpass : marginPass false cs.length a v₁ t) :
    (t < v₂ ∧ t < floatSumCR (cs.map .float)) ∨ (v₂ < t ∧ floatSumCR (cs.map .float) < t) := by
  have hn1 : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  have hov2 : 2 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag := by omega
  have hr : SumOrder "EXACT" (cs.map .float) (floatSumCR (cs.map .float)) := by simp [SumOrder]
  obtain ⟨f1, e1⟩ := SumOrder.near h₁ hf hn hov2
  obtain ⟨-, e2⟩ := SumOrder.near h₂ hf hn hov2
  obtain ⟨-, er⟩ := SumOrder.near hr hf hn hov2
  have hfa : ∀ c ∈ cs.map absCode, IsFin c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact absCode_fin (hf x hx)
  have hla : (cs.map absCode).length = cs.length := List.length_map _
  obtain ⟨fa, ea⟩ := SumOrder.near hA hfa (by rw [hla]; exact hn)
    (by rw [hla, scaledAbsSum_abs]; exact hov2)
  rw [hla, scaledAbsSum_abs, exactSum_abs] at ea
  have hX := check_sum f1 ht fa hn1 hn hov ea hpass
  generalize scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 = T at e1 e2 er hX
  generalize cs.length * T = W at e1 e2 er hX
  have key : (scaled t < scaled v₂ ∧ scaled t < scaled (floatSumCR (cs.map .float))) ∨
      (scaled v₂ < scaled t ∧ scaled (floatSumCR (cs.map .float)) < scaled t) := by omega
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact .inl ⟨lt_of_scaled_lt k1, lt_of_scaled_lt k2⟩
  · exact .inr ⟨lt_of_scaled_lt k1, lt_of_scaled_lt k2⟩

/-! ## `AVG` -/

/-- Dividing by a count `1 ≤ n ≤ 2⁵³`, rounded once: `n · y` within
`2⁻⁵³ (|a| + n · 2⁻¹⁰²²)` of `a`. -/
theorem div_n {a : Int} {n : Nat} (ha : IsFin a) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 53)
    (h : (scaled a).natAbs ≤ 2 ^ 2097) :
    IsFin (fdiv a (ofInt n)) ∧
      2 ^ 53 * ((n : Int) * scaled (fdiv a (ofInt n)) - scaled a).natAbs ≤
        (scaled a).natAbs + n * 2 ^ 52 := by
  obtain ⟨fN, sN⟩ := ofInt_nat hn
  have hb0 : scaled (ofInt n) ≠ 0 := by rw [sN]; omega
  have hbn : (scaled (ofInt n)).natAbs = n * 2 ^ 1074 := by rw [sN]; omega
  have hsz : (scaled a).natAbs * 2 ^ 1074 ≤ 2 ^ 2097 * (n * 2 ^ 1074) := by
    have h1 := Nat.mul_le_mul_right (2 ^ 1074) h
    have h2 : 2 ^ 2097 * 2 ^ 1074 ≤ 2 ^ 2097 * (n * 2 ^ 1074) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hn1)
    exact Nat.le_trans h1 h2
  obtain ⟨hf, he⟩ := div_parts ha fN hb0 (by rw [hbn]; exact hsz)
  refine ⟨hf, ?_⟩
  rw [hbn, sN] at he
  have e : scaled (fdiv a (ofInt n)) * ((n : Int) * 2 ^ 1074) - scaled a * 2 ^ 1074 =
      ((n : Int) * scaled (fdiv a (ofInt n)) - scaled a) * 2 ^ 1074 := by grind
  rw [e, Int.natAbs_mul] at he
  have hm := Nat.max_le.2 ⟨Nat.le_add_right ((scaled a).natAbs * 2 ^ 1074) (n * 2 ^ 1074 * 2 ^ 52),
    Nat.le_add_left (n * 2 ^ 1074 * 2 ^ 52) ((scaled a).natAbs * 2 ^ 1074)⟩
  have e2 : (scaled a).natAbs * 2 ^ 1074 + n * 2 ^ 1074 * 2 ^ 52 =
      ((scaled a).natAbs + n * 2 ^ 52) * 2 ^ 1074 := by grind
  have e3 : 2 ^ 53 * (((n : Int) * scaled (fdiv a (ofInt n)) - scaled a).natAbs *
      (2 ^ 1074 : Int).natAbs) = 2 ^ 53 * ((n : Int) * scaled (fdiv a (ofInt n)) - scaled a).natAbs *
        2 ^ 1074 := by rw [show (2 ^ 1074 : Int).natAbs = 2 ^ 1074 from rfl, Nat.mul_assoc]
  rw [e3] at he
  have h4 := Nat.le_trans he hm
  rw [e2] at h4
  exact Nat.le_of_mul_le_mul_right h4 (Nat.two_pow_pos _)

theorem natAbs_tri (x y z : Int) : (x - z).natAbs ≤ (x - y).natAbs + (y - z).natAbs := by
  have := Int.natAbs_add_le (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by omega] at this

/-- The arithmetic of `AvgOrder.near`: a sum near the exact sum, divided and
rounded once more. -/
theorem avg_near_arith {T W B n : Nat} {x z S : Int} (hnT : W ≤ 2 ^ 32 * T)
    (es : (x - S).natAbs * 2 ^ 53 ≤ 2 * W + 2 * T) (hS : S.natAbs ≤ B)
    (ev : 2 ^ 53 * (z - x).natAbs ≤ x.natAbs + n * 2 ^ 52)
    (hT : B + n * 2 ^ 52 = T) : (z - S).natAbs * 2 ^ 53 ≤ 2 * W + 4 * T := by
  have h1 := natAbs_tri x S 0
  have h2 := natAbs_tri z x S
  simp only [Int.sub_zero] at h1
  generalize (x - S).natAbs = a at es h1 h2
  generalize (z - x).natAbs = b at ev h2
  generalize (z - S).natAbs = c at h2 ⊢
  have haT : a ≤ T := by
    have : a * 2 ^ 53 ≤ T * 2 ^ 53 := by clear ev h1 h2 hS hT; omega
    exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
  have h3 : c * 2 ^ 53 ≤ b * 2 ^ 53 + a * 2 ^ 53 := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ h2
  rw [Nat.mul_comm] at ev
  obtain ⟨C, hC⟩ : ∃ C, c * 2 ^ 53 = C := ⟨_, rfl⟩
  obtain ⟨Bb, hB⟩ : ∃ Bb, b * 2 ^ 53 = Bb := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, a * 2 ^ 53 = A := ⟨_, rfl⟩
  rw [hC, hB, hA] at h3; rw [hC]; rw [hB] at ev; rw [hA] at es
  clear h2 hnT hC hB hA
  omega

/-- **A mean `AvgOrder` allows is near the exact mean**: `n` times it is
within `(2(n + 1) + 2) · T · 2⁻⁵³` of the exact sum, on the conditions of
`SumOrder.near`. `EXACT` rounds the exact mean once; every other behaviour
divides a sum `SumOrder.near` bounds, rounding once more. -/
theorem AvgOrder.near {b : Behaviour} {cs : List Int} {v : Int}
    (h : AvgOrder b (cs.map .float) v) (hf : ∀ c ∈ cs, IsFin c) (hn1 : 1 ≤ cs.length)
    (hn : cs.length ≤ 2 ^ 32)
    (hov : 4 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag) :
    IsFin v ∧ ((cs.length : Int) * scaled v - exactSum (cs.map .float)).natAbs * 2 ^ 53 ≤
      2 * (cs.length * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52)) +
        4 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) := by
  have hS := natAbs_exactSum_le cs
  have hnT : cs.length * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤
      2 ^ 32 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) := Nat.mul_le_mul_right _ hn
  have hmax : maxMag ≤ 2 ^ 2098 := by rw [maxMag_def]; omega
  by_cases hb : b = "EXACT"
  · simp only [AvgOrder, hb, ↓reduceIte] at h
    rw [h, floatAvgCR, nonFinite_of_fin hf, Option.getD_none, List.length_map]
    have hfin := ofExactDiv_fin (v := exactSum (cs.map .float)) (n := cs.length) (by omega)
      (Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega)))
    have he := ofExactDiv_err (by omega) hfin
    refine ⟨hfin, ?_⟩
    have := Nat.max_le.2 ⟨Nat.le_add_right (exactSum (cs.map .float)).natAbs (cs.length * 2 ^ 52),
      Nat.le_add_left (cs.length * 2 ^ 52) (exactSum (cs.map .float)).natAbs⟩
    omega
  · simp only [AvgOrder, hb, ↓reduceIte] at h
    obtain ⟨s, hs, rfl⟩ := h
    obtain ⟨fs, es⟩ := SumOrder.near hs hf hn (by omega)
    rw [List.length_map]
    generalize hT : scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 = T at es hnT hov ⊢
    generalize cs.length * T = W at es hnT ⊢
    have hsz : (scaled s).natAbs ≤ 2 ^ 2097 := by
      have h1 := natAbs_tri (scaled s) (exactSum (cs.map .float)) 0
      simp only [Int.sub_zero] at h1
      have : (scaled s - exactSum (cs.map .float)).natAbs ≤ T := by
        have : (scaled s - exactSum (cs.map .float)).natAbs * 2 ^ 53 ≤ T * 2 ^ 53 := by
          clear h1 hS hT hf hs fs; omega
        exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
      clear es hnT hf hs fs; omega
    obtain ⟨fv, ev⟩ := div_n fs hn1 (by omega) hsz
    exact ⟨fv, avg_near_arith hnT es hS ev hT⟩

/-- The arithmetic of `check_avg`, with the products as atoms. -/
theorem avg_final {n c Y P M D X Wi Ti : Int} (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 32)
    (a1 : n * ((2 ^ 53 - 1) * (c * Y) - 2 ^ 1126) ≤ n * (2 ^ 53 * (2 ^ 1074 * M)))
    (a2 : c * ((2 ^ 53 - 1) * P - n * 2 ^ 52) ≤ c * (2 ^ 53 * (n * Y)))
    (a3 : (8 * n + 32) * (2 ^ 1021 * (2 ^ 53 - 4)) * P ≤ 2 ^ 53 * c * P)
    (a4 : n * c ≤ n * 2 ^ 1060) (a5 : n * Ti ≤ n * (2 * P)) (a6 : n * M ≤ n * D)
    (a7 : n * (2 ^ 53 * D) ≤ n * ((2 ^ 53 + 1) * X)) (hP2 : Ti ≤ 2 * P)
    (hWi : Wi = n * Ti) (hWT : Wi ≤ 2 ^ 32 * Ti) (hTn : n * 2 ^ 52 ≤ Ti) :
    4 * Wi + 8 * Ti < n * X * 2 ^ 53 := by
  -- Monomials as atoms.
  have e1 : n * ((2 ^ 53 - 1) * (c * Y) - 2 ^ 1126) = (2 ^ 53 - 1) * (n * c * Y) - 2 ^ 1126 * n := by grind
  have e2 : n * (2 ^ 53 * (2 ^ 1074 * M)) = 2 ^ 1127 * (n * M) := by grind
  have e3 : c * ((2 ^ 53 - 1) * P - n * 2 ^ 52) = (2 ^ 53 - 1) * (c * P) - 2 ^ 52 * (n * c) := by grind
  have e4 : c * (2 ^ 53 * (n * Y)) = 2 ^ 53 * (n * c * Y) := by grind
  have e5 : (8 * n + 32) * (2 ^ 1021 * (2 ^ 53 - 4)) * P =
      8 * (2 ^ 1021 * (2 ^ 53 - 4)) * (n * P) + 32 * (2 ^ 1021 * (2 ^ 53 - 4)) * P := by grind
  have e6 : 2 ^ 53 * c * P = 2 ^ 53 * (c * P) := by grind
  have e7 : n * (2 * P) = 2 * (n * P) := by grind
  have e8 : n * (2 ^ 53 * D) = 2 ^ 53 * (n * D) := by grind
  have e9 : n * ((2 ^ 53 + 1) * X) = (2 ^ 53 + 1) * (n * X) := by grind
  have e10 : n * X * 2 ^ 53 = 2 ^ 53 * (n * X) := by grind
  rw [e1, e2] at a1; rw [e3, e4] at a2; rw [e5, e6] at a3; rw [e7, ← hWi] at a5; rw [e8, e9] at a7
  rw [e10]
  obtain ⟨NCY, h1⟩ : ∃ z, n * c * Y = z := ⟨_, rfl⟩
  obtain ⟨NM, h2⟩ : ∃ z, n * M = z := ⟨_, rfl⟩
  obtain ⟨CP, h3⟩ : ∃ z, c * P = z := ⟨_, rfl⟩
  obtain ⟨NC, h4⟩ : ∃ z, n * c = z := ⟨_, rfl⟩
  obtain ⟨NP, h5⟩ : ∃ z, n * P = z := ⟨_, rfl⟩
  obtain ⟨ND, h6⟩ : ∃ z, n * D = z := ⟨_, rfl⟩
  obtain ⟨NX, h7⟩ : ∃ z, n * X = z := ⟨_, rfl⟩
  rw [h1, h2] at a1; rw [h3, h1, h4] at a2; rw [h5, h3] at a3; rw [h4] at a4; rw [h5] at a5
  rw [h2, h6] at a6; rw [h6, h7] at a7; rw [h7]
  clear h1 h2 h3 h4 h5 h6 h7 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hWi
  -- `2⁵³ · c · P ≥ 4 C W + 16 C T`.
  have s1 : 4 * (2 ^ 1021 * (2 ^ 53 - 4)) * Wi + 16 * (2 ^ 1021 * (2 ^ 53 - 4)) * Ti ≤ 2 ^ 53 * CP := by
    omega
  -- `2¹⁰⁶ · n · c · y ≥ (2⁵³ − 1)(4 C W + 16 C T) − 2¹¹⁶⁵ n`.
  have s2 : (2 ^ 53 - 1) * (4 * (2 ^ 1021 * (2 ^ 53 - 4)) * Wi + 16 * (2 ^ 1021 * (2 ^ 53 - 4)) * Ti) -
      2 ^ 1165 * n ≤ 2 ^ 106 * NCY := by
    clear a1 a5 a6 a7 a3 hP2 hWT
    omega
  -- `n · m`.
  have s3 : (2 ^ 53 - 1) * ((2 ^ 53 - 1) * (4 * (2 ^ 1021 * (2 ^ 53 - 4)) * Wi +
      16 * (2 ^ 1021 * (2 ^ 53 - 4)) * Ti) - 2 ^ 1165 * n) - 2 ^ 1232 * n ≤ 2 ^ 1233 * NM := by
    clear a2 a4 a5 a6 a7 a3 hP2 hWT s1
    omega
  clear a1 a2 a3 a4 a5 s1 s2
  omega

/-- **The check of an `AVG`, in codes**: as `check_sum`, for a group whose
engine mean `v` passes the check with `c₀ = 32` and the margin divided by
`n`: `n · |v − t| > (4(n + 1) + 4) · T · 2⁻⁵³`, twice the distance
`AvgOrder.near` allows `n` times any mean from the exact sum. -/
theorem check_avg {v t a : Int} {n B : Nat} (hv : IsFin v) (ht : IsFin t) (ha : IsFin a)
    (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 32) (hov : 4 * (B + n * 2 ^ 52) ≤ maxMag)
    (hA : (scaled a - B).natAbs * 2 ^ 53 ≤ 2 * (n * (B + n * 2 ^ 52)) + 2 * (B + n * 2 ^ 52))
    (hpass : marginPass true n a v t) :
    4 * (n * (B + n * 2 ^ 52)) + 8 * (B + n * 2 ^ 52) <
      ((n : Int) * (scaled v - scaled t)).natAbs * 2 ^ 53 := by
  have hm := maxMag_def
  generalize hT : B + n * 2 ^ 52 = T at hov hA ⊢
  have hnT : n * T ≤ 2 ^ 32 * T := Nat.mul_le_mul_right T hn
  have hWi : ((n * T : Nat) : Int) = (n : Int) * (T : Int) := by push_cast; rfl
  generalize hW : n * T = W at hA hnT hWi ⊢
  obtain ⟨fN, sN⟩ := ofInt_nat (n := n) (by omega)
  obtain ⟨f8, s8⟩ := marginEight_eq
  obtain ⟨f32, s32⟩ := marginC0_eq true
  obtain ⟨fU, sU⟩ := marginUlp_eq
  obtain ⟨fT, sT⟩ := marginTiny_eq
  simp only [marginConst, ↓reduceIte] at s32
  simp only [marginPass, marginCode, ↓reduceIte] at hpass
  generalize hc1 : fmul marginEight (ofInt n) = c1 at hpass
  generalize hc2 : fadd c1 (marginC0 true) = c2 at hpass
  generalize hc3 : fmul c2 marginUlp = c3 at hpass
  generalize hq : fmul (ofInt n) marginTiny = q at hpass
  generalize hp : fadd a q = p at hpass
  generalize hy : fdiv p (ofInt n) = y at hpass
  generalize hmc : fmul c3 y = m at hpass
  generalize hd : fsub v t = d at hpass
  have hmd := pass_le hpass
  -- `cₙ`, with `c₀ = 32`.
  obtain ⟨f1, l1, u1⟩ := mul_le f8 fN (by omega) (by omega) (by rw [s8, sN]; omega)
  rw [hc1, s8, sN] at l1 u1; rw [hc1] at f1
  obtain ⟨f2, l2, u2⟩ := add_le f1 f32 (by omega) (by omega)
  rw [hc2] at f2 l2 u2
  obtain ⟨f3, l3, u3⟩ := mul_le f2 fU (by omega) (by omega) (by rw [sU]; omega)
  rw [hc3, sU] at l3 u3; rw [hc3] at f3
  have hc3lo : (8 * (n : Int) + 32) * (2 ^ 1021 * (2 ^ 53 - 4)) ≤ 2 ^ 53 * scaled c3 := by omega
  have hc3hi : scaled c3 ≤ 2 ^ 1060 := by omega
  clear l1 u1 l2 u2 l3 u3
  -- `p = fl(a + fl(n · 2⁻¹⁰²²))`, as for a `SUM`.
  obtain ⟨fq, lq, uq⟩ := mul_le fN fT (by omega) (by omega) (by rw [sN, sT]; omega)
  rw [hq, sN, sT] at lq uq; rw [hq] at fq
  obtain ⟨fp, lp, up⟩ := add_le ha fq (by omega) (by omega)
  rw [hp] at fp lp up
  have hP2 : (T : Int) ≤ 2 * scaled p := by omega
  have hP3 : 0 ≤ scaled p ∧ scaled p ≤ 2 ^ 2097 := by omega
  clear lq uq lp up
  -- `y = fl(p / n)`: `n · y` near `p`, and `0 ≤ y ≤ 2²⁰⁹⁸`.
  obtain ⟨fy, ey⟩ := div_n fp hn1 (by omega) (by omega)
  rw [hy] at fy ey
  have hNY : (2 ^ 53 - 1) * scaled p - n * 2 ^ 52 ≤ 2 ^ 53 * ((n : Int) * scaled y) := by omega
  have hNY2 : (n : Int) * scaled y ≤ 2 ^ 2098 := by omega
  have hy0 : 0 ≤ scaled y := by
    apply Classical.byContradiction; intro h
    have : (n : Int) * scaled y ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) (by omega)
    omega
  have hy1 : scaled y ≤ 2 ^ 2098 := by
    have : scaled y ≤ (n : Int) * scaled y := by
      have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ n by omega) hy0
      rwa [Int.one_mul] at this
    omega
  clear ey
  -- `m = fl(cₙ · y)`.
  have hcy : scaled c3 * scaled y ≤ 2 ^ 3171 := by
    have := Int.mul_le_mul hc3hi hy1 hy0 (by omega)
    omega
  obtain ⟨-, lm, -⟩ := mul_le f3 fy (by omega) hy0 hcy
  rw [hmc] at lm
  have hc30 : 0 ≤ scaled c3 := by omega
  -- Times `n`, as integers.
  have nn : (0 : Int) ≤ n := Int.natCast_nonneg n
  have a1 := Int.mul_le_mul_of_nonneg_left lm nn
  have a2 := Int.mul_le_mul_of_nonneg_left hNY hc30
  have a3 := Int.mul_le_mul_of_nonneg_right hc3lo hP3.1
  have a4 := Int.mul_le_mul_of_nonneg_left hc3hi nn
  have a5 := Int.mul_le_mul_of_nonneg_left hP2 nn
  have a6 := Int.mul_le_mul_of_nonneg_left hmd nn
  -- `d = fl(v − t)`.
  by_cases hbig : (scaled v - scaled t).natAbs ≤ 2 ^ 2097
  · obtain ⟨-, hd'⟩ := sub_rel hv ht hbig
    rw [hd] at hd'
    have hX : 2 ^ 53 * ((scaled d).natAbs : Int) ≤ (2 ^ 53 + 1) * (scaled v - scaled t).natAbs := by
      omega
    have a7 := Int.mul_le_mul_of_nonneg_left hX nn
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have hTn : (n : Int) * 2 ^ 52 ≤ T := by omega
    have hWT : (W : Int) ≤ 2 ^ 32 * T := by omega
    suffices h : 4 * (W : Int) + 8 * T < (n : Int) * ((scaled v - scaled t).natAbs : Int) * 2 ^ 53 by
      exact_mod_cast h
    exact avg_final (by omega) (by omega) a1 a2 a3 a4 a5 a6 a7 hP2 hWi hWT hTn
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    have : (scaled v - scaled t).natAbs ≤ n * (scaled v - scaled t).natAbs :=
      Nat.le_mul_of_pos_left _ hn1
    omega

/-- **The margin check of an `AVG`, end to end, in codes** (#929): as
`margin_sum`, for means: if the check of an `AVG` passes on one mean `v₁` an
engine's `sum_order` allows, every mean `v₂` any `sum_order` allows and the
reference's `floatAvgCR` lie strictly on one side of `t`. -/
theorem margin_avg {b₁ b₂ bA : Behaviour} {cs : List Int} {v₁ v₂ a t : Int}
    (hf : ∀ c ∈ cs, IsFin c) (hne : cs ≠ []) (hn : cs.length ≤ 2 ^ 32)
    (hov : 4 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag)
    (h₁ : AvgOrder b₁ (cs.map .float) v₁) (h₂ : AvgOrder b₂ (cs.map .float) v₂)
    (hA : SumOrder bA ((cs.map absCode).map .float) a) (ht : IsFin t)
    (hpass : marginPass true cs.length a v₁ t) :
    (t < v₂ ∧ t < floatAvgCR (cs.map .float)) ∨ (v₂ < t ∧ floatAvgCR (cs.map .float) < t) := by
  have hn1 : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  have hov2 : 2 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤ maxMag := by omega
  have hr : AvgOrder "EXACT" (cs.map .float) (floatAvgCR (cs.map .float)) := by simp [AvgOrder]
  obtain ⟨f1, e1⟩ := AvgOrder.near h₁ hf hn1 hn hov
  obtain ⟨-, e2⟩ := AvgOrder.near h₂ hf hn1 hn hov
  obtain ⟨-, er⟩ := AvgOrder.near hr hf hn1 hn hov
  have hfa : ∀ c ∈ cs.map absCode, IsFin c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact absCode_fin (hf x hx)
  have hla : (cs.map absCode).length = cs.length := List.length_map _
  obtain ⟨fa, ea⟩ := SumOrder.near hA hfa (by rw [hla]; exact hn)
    (by rw [hla, scaledAbsSum_abs]; exact hov2)
  rw [hla, scaledAbsSum_abs, exactSum_abs] at ea
  have hX := check_avg f1 ht fa hn1 hn hov ea hpass
  rw [Int.mul_sub] at hX
  generalize scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 = T at e1 e2 er hX
  generalize cs.length * T = W at e1 e2 er hX
  generalize exactSum (cs.map .float) = S at e1 e2 er
  have hn0 : (0 : Int) ≤ cs.length := Int.natCast_nonneg _
  generalize (cs.length : Int) = n at e1 e2 er hX hn0
  obtain ⟨A1, h1⟩ : ∃ z, n * scaled v₁ = z := ⟨_, rfl⟩
  obtain ⟨A2, h2⟩ : ∃ z, n * scaled v₂ = z := ⟨_, rfl⟩
  obtain ⟨AR, h3⟩ : ∃ z, n * scaled (floatAvgCR (cs.map .float)) = z := ⟨_, rfl⟩
  obtain ⟨AT, h4⟩ : ∃ z, n * scaled t = z := ⟨_, rfl⟩
  rw [h1] at e1; rw [h2] at e2; rw [h3] at er; rw [h1, h4] at hX
  have key : (AT < A2 ∧ AT < AR) ∨ (A2 < AT ∧ AR < AT) := by
    clear h1 h2 h3 h4 hf hne hov hov2 hr hfa hla f1 fa ea hpass h₁ h₂ hA; omega
  rw [← h2, ← h3, ← h4] at key
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact .inl ⟨lt_of_scaled_lt (Int.lt_of_mul_lt_mul_left k1 hn0),
      lt_of_scaled_lt (Int.lt_of_mul_lt_mul_left k2 hn0)⟩
  · exact .inr ⟨lt_of_scaled_lt (Int.lt_of_mul_lt_mul_left k1 hn0),
      lt_of_scaled_lt (Int.lt_of_mul_lt_mul_left k2 hn0)⟩

/-! ## The range of an engine's double `AVG` (D35) -/

/-- `N` values in `[lo, hi]` keep `AvgOrder.near`'s conditions. -/
def avgSafe (N : Nat) (lo hi : Int) : Bool := 4 * (N * (rangeMag lo hi + 2 ^ 52)) ≤ maxMag

/-- The least an engine's `AVG` of values in `[lo, hi]` may be. -/
def avgLo (lo hi : Int) : Int := lo - (rangeMag lo hi + 2 ^ 52 : Nat)

/-- The most an engine's `AVG` of values in `[lo, hi]` may be. -/
def avgHi (lo hi : Int) : Int := hi + (rangeMag lo hi + 2 ^ 52 : Nat)

/-- **The range of an engine's double `AVG`** (D35), for the abstract domain
(#925): under every `sum_order` behaviour, the mean of `1 ≤ n ≤ N ≤ 2³²`
finite doubles in `[lo, hi]` is finite and in `[avgLo lo hi, avgHi lo hi]`
whenever `avgSafe` holds. The range is crude, as `SumOrder.bound`'s is. -/
theorem AvgOrder.bound {b : Behaviour} {cs : List Int} {c : Int} {N : Nat} {lo hi : Int}
    (h : AvgOrder b (cs.map .float) c) (hne : cs ≠ []) (hN : cs.length ≤ N)
    (h32 : N ≤ 2 ^ 32) (hr : ∀ x ∈ cs, IsFin x ∧ lo ≤ scaled x ∧ scaled x ≤ hi)
    (hsafe : avgSafe N lo hi = true) :
    IsFin c ∧ avgLo lo hi ≤ scaled c ∧ scaled c ≤ avgHi lo hi := by
  have hb' : ∀ x ∈ cs, lo ≤ scaled x ∧ scaled x ≤ hi := fun x hx => (hr x hx).2
  have hA := scaledAbsSum_le hb'
  have hsafe' := of_decide_eq_true hsafe
  have hn1 : 1 ≤ cs.length := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons => simp
  have hR : scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 ≤
      cs.length * (rangeMag lo hi + 2 ^ 52) := by rw [Nat.mul_add]; omega
  have hRN : cs.length * (rangeMag lo hi + 2 ^ 52) ≤ N * (rangeMag lo hi + 2 ^ 52) :=
    Nat.mul_le_mul_right _ hN
  obtain ⟨hf, he⟩ := AvgOrder.near h (fun x hx => (hr x hx).1) hn1 (by omega) (by omega)
  refine ⟨hf, ?_⟩
  have ⟨s1, s2⟩ := exactSum_bounds hb'
  have hnT : cs.length * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) ≤
      2 ^ 32 * (scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52) := Nat.mul_le_mul_right _ (by omega)
  generalize scaledAbsSum (cs.map .float) + cs.length * 2 ^ 52 = T at he hnT hR
  generalize cs.length * T = W at he hnT
  have hd : ((cs.length : Int) * scaled c - exactSum (cs.map .float)).natAbs ≤ T := by
    have : ((cs.length : Int) * scaled c - exactSum (cs.map .float)).natAbs * 2 ^ 53 ≤ T * 2 ^ 53 := by
      clear hRN hR s1 s2 hsafe' hsafe hA; omega
    exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
  have hn0 : (0 : Int) < cs.length := by omega
  have hRi : ((cs.length * (rangeMag lo hi + 2 ^ 52) : Nat) : Int) =
      (cs.length : Int) * ((rangeMag lo hi + 2 ^ 52 : Nat) : Int) := Int.natCast_mul _ _
  have el : (cs.length : Int) * avgLo lo hi =
      cs.length * lo - (cs.length : Int) * ((rangeMag lo hi + 2 ^ 52 : Nat) : Int) := by
    unfold avgLo; rw [Int.mul_sub]
  have eh : (cs.length : Int) * avgHi lo hi =
      cs.length * hi + (cs.length : Int) * ((rangeMag lo hi + 2 ^ 52 : Nat) : Int) := by
    unfold avgHi; rw [Int.mul_add]
  have k1 : (cs.length : Int) * avgLo lo hi ≤ (cs.length : Int) * scaled c := by
    rw [el]; clear hRN hsafe' hsafe hA hnT he; omega
  have k2 : (cs.length : Int) * scaled c ≤ (cs.length : Int) * avgHi lo hi := by
    rw [eh]; clear hRN hsafe' hsafe hA hnT he; omega
  exact ⟨Int.le_of_mul_le_mul_left k1 hn0, Int.le_of_mul_le_mul_left k2 hn0⟩

/-! ## The check's columns, row by row -/

/-- On a group's row, the check's margin column is `marginCode`. -/
theorem marginExpr_eval {row : Row} {s : Nat} {avg : Bool} {n : Nat} {a : Int}
    (hn : row.getD (s + 1) .null = .int n) (ha : row.getD (s + 2) .null = .float a) :
    (marginExpr s avg).eval row = .float (marginCode avg n a) := by
  cases avg <;> simp only [marginExpr, marginCode, Expr.eval, hn, ha, Bool.false_eq_true,
    ↓reduceIte] <;> rfl

/-- On a group's row, the check's `v − t` column is `fsub v t`. -/
theorem marginDiff_eval {row : Row} {s : Nat} {t : Expr} {v tc : Int}
    (hv : row.getD s .null = .float v) (ht : t.eval row = .float tc) :
    (marginDiff s t).eval row = .float (fsub v tc) := by
  simp only [marginDiff, Expr.eval, hv, ht]; rfl

/-- **A group the check does not flag passes it**: on a row of `k` columns
with `n ≥ 1` values, `v − t` and the margin appended, a flag that is not true
means the margin is below `|fl(v − t)|` and `n ≤ 2³²`. -/
theorem marginFlag_eval {row : Row} {k s : Nat} {n : Nat} {d m : Int} (hk : row.length = k)
    (hs : s + 1 < k) (hn : row.getD (s + 1) .null = .int n) (hn1 : 1 ≤ n)
    (h : ((marginFlag k s).eval (row ++ [.float d, .float m])).isTrue = false) :
    (m < d ∨ m < -d) ∧ n ≤ 2 ^ 32 := by
  have g1 : (row ++ [Value.float d, .float m]).getD (s + 1) .null = .int n := by
    rw [List.getD_eq_getElem?_getD] at hn ⊢
    rw [List.getElem?_append_left (by omega)]; exact hn
  have g2 : (row ++ [Value.float d, .float m]).getD k .null = .float d := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp [hk]
  have g3 : (row ++ [Value.float d, .float m]).getD (k + 1) .null = .float m := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp [hk]
  simp only [marginFlag, Expr.eval, g1, g2, g3] at h
  change (or3 (and3 (.bool !(decide ((n : Int) < 1))) (UnFn.apply .not (or3 (.bool (decide (m < d)))
    (.bool (decide (m < neg d)))))) (.bool (decide ((2 : Int) ^ 32 < n)))).isTrue = false at h
  have h0 : decide ((n : Int) < 1) = false := by simp; omega
  rw [h0] at h
  generalize hb1 : decide (m < d) = b1 at h
  generalize hb2 : decide (m < neg d) = b2 at h
  generalize hb3 : decide ((2 : Int) ^ 32 < n) = b3 at h
  have hk : (b1 || b2) = true ∧ b3 = false := by
    revert h; cases b1 <;> cases b2 <;> cases b3 <;> decide
  obtain ⟨k1, k2⟩ := hk
  subst hb1 hb2 hb3
  simp only [Bool.or_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at k1 k2
  exact ⟨k1, by omega⟩

/-- **The check's verdict on a group's row** (#929): on an aggregate's row
whose column `s` holds the group's sum or mean `v`, `s + 1` its count `n ≥ 1`
and `s + 2` its `SUM(ABS(x))` `a`, the row `marginCount` projects is not
flagged only if the group passes the check (`marginPass`) and `n ≤ 2³²`: the
premises `margin_sum` and `margin_avg` take. -/
theorem margin_row {row : Row} {k s : Nat} {t : Expr} {v a tc : Int} {n : Nat} {avg : Bool}
    (hk : row.length = k) (hs : s + 2 < k) (hv : row.getD s .null = .float v)
    (hn : row.getD (s + 1) .null = .int n) (ha : row.getD (s + 2) .null = .float a)
    (ht : t.eval row = .float tc) (hn1 : 1 ≤ n)
    (h : ((marginFlag k s).eval
      (row ++ [(marginDiff s t).eval row, (marginExpr s avg).eval row])).isTrue = false) :
    marginPass avg n a v tc ∧ n ≤ 2 ^ 32 := by
  rw [marginDiff_eval hv ht, marginExpr_eval hn ha] at h
  exact marginFlag_eval hk (by omega) hn hn1 h

end Substrait
