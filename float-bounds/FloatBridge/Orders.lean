import FloatBridge.Sums
import FloatBounds.Kahan
import Sverify.Analysis.MarginSound

/-!
# Kahan's sum and constant runs are the standard model's (#1196, part 3)

The core states an engine's double `SUM` under `COMPENSATED` (Kahan's sum,
duckdb-kahan-sum) and `SCALED_CONSTANT` (a constant run added as one product,
duckdb-sum-double) by `SumOrder`'s bound alone: `SumBound`, and exactness on
small integers. The core writes the two algorithms on codes (`kahanSum`,
`FloatSumsK`, `core/Sverify/Core/SumBound.lean`); this module proves that they
meet `SumOrder`:

* `FloatSumsK.treeSum`: a sum with constant runs is a `StdModel.TreeSum`, whose
  `const` node is the product `fl(k · x)`; `TreeSum.error` bounds it.
* `kahanSum_model`: Kahan's sum on codes is `Rnd.kahan` over the reals under
  the core's rounding, step by step, while every rounded value stays below the
  largest double. `Rnd.kfold_mid`, applied to each prefix, keeps the state
  within `kstep_args`' bounds, so none overflows; `Rnd.kahan_near` bounds the
  result.
* The canonical clause of `SumBound` by `KahanSums.canonV` and
  `FloatSumsK.canonV`, and exactness on small integers by
  `KahanSums.int_exact` and `FloatSumsK.int_exact`, both on codes.

Kahan's compensation and its `x − c` may be `-0.0`, which IEEE arithmetic reads
as `0` (`sv`): `Num` and `rv` track those values. The running sum stays a
finite code whose sign is its value's (`Neg`), as a `FloatSums` sum does.
-/

set_option exponentiation.threshold 2200

namespace FloatBridge

open FloatBounds Substrait FloatCode

/-! ## Codes IEEE arithmetic reads as numbers -/

/-- A finite code, or `-0.0`. -/
def Num (c : Int) : Prop := IsFin c ∨ c = negZero

theorem IsFin.num {c : Int} (h : IsFin c) : Num c := .inl h

/-- What IEEE arithmetic reads a code as: `-0.0` as `0`. -/
noncomputable def rv (c : Int) : ℝ := (sv c : ℝ) / 2 ^ 1074

theorem rv_of_fin {c : Int} (h : IsFin c) : rv c = val c := by simp [rv, val, h.sv_eq]

theorem Num.parts {c : Int} (h : Num c) :
    isNanCode c = false ∧ FloatCode.isInfCode c = false ∧ c ≠ posInf ∧ c ≠ negInf := by
  rcases h with h | rfl
  · exact ⟨h.not_nan, h.not_inf, h.ne.2.2.1, h.ne.2.2.2.1⟩
  · have := posInf_eq; have := negInf_eq; have := nan_eq; have := negZero_eq'; have := negNan_eq'
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [isNanCode, FloatCode.isInfCode] <;> omega

theorem sv_negZero : sv negZero = 0 := by simp [FloatCode.sv]

theorem negI_num {b : Int} (hb : Num b) : Num (negI b) ∧ sv (negI b) = -sv b := by
  rcases hb with hb | rfl
  · obtain ⟨-, -, hs⟩ := hb.negI_parts
    refine ⟨?_, by rw [hs, hb.sv_eq]⟩
    have := posInf_eq; have := negInf_eq; have := negZero_eq'
    obtain ⟨h1, h2⟩ := hb
    unfold negI
    split
    · exact .inr rfl
    · split
      · exact .inl ⟨by omega, by omega⟩
      · exact .inl ⟨by omega, by omega⟩
  · have h0 : negI negZero = 0 := by have := negZero_eq'; simp [negI]
    rw [h0, sv_negZero]
    exact ⟨.inl ⟨by have := negInf_eq; omega, by have := posInf_eq; omega⟩, by simp [FloatCode.sv, scaled]⟩

theorem zeroOf_num (b : Bool) : Num (zeroOf b) ∧ sv (zeroOf b) = 0 := by
  cases b
  · exact ⟨.inl ⟨by have := negInf_eq; simp [zeroOf]; omega, by have := posInf_eq; simp [zeroOf]; omega⟩,
      by simp [zeroOf, FloatCode.sv, scaled]⟩
  · exact ⟨.inr rfl, by simp [zeroOf, sv_negZero]⟩

/-- **An addition of numbers**: below the largest double, the sum rounds the
exact one, `-0.0` read as `0`. -/
theorem fadd_num {a b : Int} (ha : Num a) (hb : Num b) (hg : (sv a + sv b).natAbs ≤ maxMag) :
    Num (fadd a b) ∧ sv (fadd a b) = scaled (ofExact (sv a + sv b)) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha.parts
  obtain ⟨b1, b2, -, -⟩ := hb.parts
  unfold fadd addI
  simp only [a1, b1, a3, a4, b2, Bool.or_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h0
    obtain ⟨hn, hs⟩ := zeroOf_num (decide (a < 0) && decide (b < 0))
    refine ⟨hn, ?_⟩
    rw [hs, h0, show ofExact 0 = 0 from ofExactDiv_zero 1]; simp [scaled]
  · rename_i h0
    have hr := (ofExact_good hg).2.2 h0
    have e : rnd (sv a + sv b) 1 = ofExact (sv a + sv b) := by
      unfold rnd; simp only [ofExact] at hr; simp [hr, ofExact]
    rw [e]
    exact ⟨.inl (ofExact_good hg).1, (ofExact_good hg).1.sv_eq⟩

/-- **An addition to a finite code of its sign** is `ofExact` of the exact
sum: finite and `Neg`, even where the other operand is `-0.0`. -/
theorem fadd_neg {a b : Int} (ha : IsFin a) (hna : Neg a) (hb : Num b)
    (hg : (scaled a + sv b).natAbs ≤ maxMag) : fadd a b = ofExact (scaled a + sv b) := by
  obtain ⟨b1, b2, -, -⟩ := hb.parts
  unfold fadd addI
  simp only [ha.not_nan, b1, ha.ne.2.2.1, ha.ne.2.2.2.1, b2, ha.sv_eq, Bool.or_false,
    Bool.false_eq_true, ite_false]
  split
  · rename_i h0
    have hab : ¬ (a < 0 ∧ b < 0) := by
      rintro ⟨h1, h2⟩
      have := hna h1
      rcases hb with hb | rfl
      · have := scaled_nonpos h2; rw [hb.sv_eq] at h0; omega
      · rw [sv_negZero] at h0; omega
    have : (decide (a < 0) && decide (b < 0)) = false := by
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hab
    rw [this, h0]; exact (ofExactDiv_zero 1).symm
  · rename_i h0
    unfold rnd
    have := (ofExact_good hg).2.2 h0
    simp only [ofExact] at this
    simp [this, ofExact]

/-! ## Against the model -/

theorem rv_add (a b : Int) : rv a + rv b = ((sv a + sv b : Int) : ℝ) / 2 ^ 1074 := by
  simp only [rv]; push_cast; ring

/-- **A step on numbers is the model's**. -/
theorem fadd_model_num {a b : Int} (ha : Num a) (hb : Num b) (h : |rv a + rv b| ≤ maxFinite) :
    Num (fadd a b) ∧ rv (fadd a b) = model.fl (rv a + rv b) := by
  rw [rv_add] at h ⊢
  have hg := natAbs_le_of_abs h
  obtain ⟨hn, hs⟩ := fadd_num ha hb hg
  refine ⟨hn, ?_⟩
  rw [model_fl_grid hg, rv, hs, val]

/-- **A step from a finite code of its sign is the model's**, and keeps it
finite and of its sign. -/
theorem fadd_model_neg {a b : Int} (ha : IsFin a) (hna : Neg a) (hb : Num b)
    (h : |val a + rv b| ≤ maxFinite) :
    IsFin (fadd a b) ∧ Neg (fadd a b) ∧ val (fadd a b) = model.fl (val a + rv b) := by
  rw [← rv_of_fin ha, rv_add] at h ⊢
  have hg := natAbs_le_of_abs h
  rw [ha.sv_eq] at hg ⊢
  rw [fadd_neg ha hna hb hg, model_fl_grid hg]
  exact ⟨(ofExact_good hg).1, (ofExact_good hg).2.1, rfl⟩

theorem fsub_eq (a b : Int) : fsub a b = fadd a (negI b) := rfl

theorem rv_negI {b : Int} (hb : Num b) : rv (negI b) = -rv b := by
  simp only [rv, (negI_num hb).2]; push_cast; ring

theorem fsub_model_num {a b : Int} (ha : Num a) (hb : Num b) (h : |rv a - rv b| ≤ maxFinite) :
    Num (fsub a b) ∧ rv (fsub a b) = model.fl (rv a - rv b) := by
  rw [fsub_eq, sub_eq_add_neg, ← rv_negI hb] at *
  exact fadd_model_num ha (negI_num hb).1 h

theorem fsub_model_neg {a b : Int} (ha : IsFin a) (hna : Neg a) (hb : Num b)
    (h : |val a - rv b| ≤ maxFinite) :
    IsFin (fsub a b) ∧ Neg (fsub a b) ∧ val (fsub a b) = model.fl (val a - rv b) := by
  rw [fsub_eq, sub_eq_add_neg, ← rv_negI hb] at *
  exact fadd_model_neg ha hna (negI_num hb).1 h


/-! ## Doubles -/

theorem val_zero : val 0 = 0 := by simp [val, scaled]

theorem neg_zero_code : Neg 0 := fun h => absurd h (by omega)

/-- **A double's value rounds to itself** under the core's rounding. -/
theorem fl_dbl {x : Int} (hd : Dbl x) (hx : IsFin x) : model.fl (val x) = val x := by
  have hS : (scaled x).natAbs ≤ maxMag := by
    have := posInf_eq; have := negInf_eq; obtain ⟨h1, h2⟩ := hx; unfold scaled; split <;> omega
  calc model.fl (val x) = model.fl ((scaled x : ℝ) / 2 ^ 1074) := rfl
    _ = val (ofExact (scaled x)) := model_fl_grid hS
    _ = val x := by rw [hd.ofExact_scaled hx]

/-- A finite double of scaled value `0` is `+0.0`. -/
theorem dbl_scaled_zero {x : Int} (hd : Dbl x) (hx : IsFin x) (h0 : scaled x = 0) : x = 0 := by
  have := hd.ofExact_scaled hx
  rw [h0, show ofExact 0 = 0 from ofExactDiv_zero 1] at this
  exact this.symm

theorem reals_replicate (k : Nat) (x : Int) :
    reals (List.replicate k (.float x)) = List.replicate k (val x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.replicate_succ, ← List.singleton_append, reals_append, reals_float, ih]
    rfl

/-! ## Constant runs -/

/-- **A constant run's product is the model's**: `k` copies of a double,
`1 ≤ k ≤ 2⁵³`, multiplied once, below the largest double. -/
theorem fmul_model {k : Nat} {x : Int} (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ 53) (hd : Dbl x) (hx : IsFin x)
    (h : |(k : ℝ) * val x| ≤ maxFinite) :
    IsFin (fmul (ofInt k) x) ∧ Neg (fmul (ofInt k) x) ∧
      val (fmul (ofInt k) x) = model.fl (k * val x) := by
  have hkc : ofInt k = exactCode k := ofInt_exact (by simpa using hk)
  have hfk : IsFin (ofInt k) := ofInt_bounds _
  have hsk : scaled (ofInt k) = k * (unitK : Int) := by rw [hkc, FloatCode.scaled_exactCode]
  have hU := unitK_pos
  have hk0 : ¬ ofInt k < 0 := by
    intro h; have := scaled_nonpos h; rw [hsk] at this
    have : (1 : Int) ≤ k := by exact_mod_cast hk1
    have : (1 : Int) * 1 ≤ k * unitK := Int.mul_le_mul this (by omega) (by omega) (by omega)
    omega
  have e : (k : ℝ) * val x = ((k * scaled x : Int) : ℝ) / 2 ^ 1074 := by
    simp only [val]; push_cast; ring
  rw [e] at h ⊢
  have hg := natAbs_le_of_abs h
  unfold fmul mulI
  simp only [hfk.not_nan, hx.not_nan, hfk.not_inf, hx.not_inf, hfk.sv_eq, hx.sv_eq, hsk,
    Bool.or_false, Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h0
    have hs0 : scaled x = 0 := by
      rcases Int.mul_eq_zero.mp h0 with h | h
      · rcases Int.mul_eq_zero.mp h with h | h <;> omega
      · exact h
    have := dbl_scaled_zero hd hx hs0
    subst this
    simp only [hk0, show ¬ (0 : Int) < 0 by omega, decide_false, bne_self_eq_false]
    refine ⟨⟨by have := negInf_eq; simp [zeroOf]; omega, by have := posInf_eq; simp [zeroOf]; omega⟩,
      fun h => by simp [zeroOf] at h, ?_⟩
    rw [show scaled 0 = 0 by simp [scaled], Int.mul_zero, Int.cast_zero, zero_div, model.zero]
    simp [zeroOf, val_zero]
  · rename_i h0
    have hv : (k : Int) * unitK * scaled x = unitK * (k * scaled x) := by ring
    have hk0' : (k : Int) * scaled x ≠ 0 := by
      intro h'; apply h0; rw [hv, h', Int.mul_zero]
    have hr : ofExactDiv ((k : Int) * unitK * scaled x) unitK = ofExact (k * scaled x) := by
      rw [hv]; exact ofExactDiv_mul _ hU
    have hne := (ofExact_good hg).2.2 hk0'
    have e2 : rnd ((k : Int) * unitK * scaled x) unitK = ofExact (k * scaled x) := by
      unfold rnd; simp only [hr, hne, false_and, ite_false]
    rw [e2, model_fl_grid hg]
    exact ⟨(ofExact_good hg).1, (ofExact_good hg).2.1, rfl⟩

/-- **The core's sums with constant runs are tree sums** (#1196): on finite
doubles whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double, a sum
`FloatSumsK` allows is finite, and its value is a `TreeSum` of the values
under the core's rounding, a run's product its `const` node. -/
theorem FloatSumsK.treeSum {vs : List Value} {c : Int} (h : FloatSumsK vs c)
    (hfin : ∀ x, Value.float x ∈ vs → IsFin x)
    (hn : ((2 * (reals vs).length : ℕ) : ℝ) * u < 1) (hov : 2 * FloatBounds.mag (reals vs) ≤ maxFinite) :
    IsFin c ∧ Neg c ∧ model.TreeSum (reals vs) (val c) := by
  induction h with
  | @seq vs ws hp =>
    have hrp := reals_perm hp
    have hfw : ∀ x, Value.float x ∈ ws → IsFin x := fun x hx => hfin x (hp.subset hx)
    obtain ⟨h1, h2, h3⟩ := floatSum_model ws hfw (by rwa [hrp.length_eq])
      (by rwa [mag_perm hrp])
    exact ⟨h1, h2, h3 ▸ StdModel.TreeSum.seq hrp⟩
  | @split vs xs ys a b hp _ _ iha ihb =>
    have hrp : (reals vs).Perm (reals xs ++ reals ys) := by
      rw [← reals_append]; exact reals_perm hp
    have hfx : ∀ x, Value.float x ∈ xs → IsFin x := fun x hx => hfin x (hp.symm.subset (by simp [hx]))
    have hfy : ∀ x, Value.float x ∈ ys → IsFin x := fun x hx => hfin x (hp.symm.subset (by simp [hx]))
    have hlen : (reals vs).length = (reals xs).length + (reals ys).length := by
      rw [hrp.length_eq, List.length_append]
    have hmag : FloatBounds.mag (reals vs) = FloatBounds.mag (reals xs) + FloatBounds.mag (reals ys) := by
      rw [mag_perm hrp, mag_append]
    have hu := u_pos
    have hmx := mag_nonneg (reals xs); have hmy := mag_nonneg (reals ys)
    have hnx : ((2 * (reals xs).length : ℕ) : ℝ) * u < 1 := by
      have : ((2 * (reals xs).length : ℕ) : ℝ) ≤ ((2 * (reals vs).length : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 (by omega)
      nlinarith
    have hny : ((2 * (reals ys).length : ℕ) : ℝ) * u < 1 := by
      have : ((2 * (reals ys).length : ℕ) : ℝ) ≤ ((2 * (reals vs).length : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 (by omega)
      nlinarith
    obtain ⟨fa, na, ta⟩ := iha hfx hnx (by linarith)
    obtain ⟨fb, _, tb⟩ := ihb hfy hny (by linarith)
    have ba := TreeSum.abs_le ta hnx (by linarith)
    have bb := TreeSum.abs_le tb hny (by linarith)
    have hstep : |val a + val b| ≤ maxFinite := by
      have := abs_add_le (val a) (val b); linarith
    obtain ⟨h1, h2, h3⟩ := fadd_model fa fb na hstep
    exact ⟨h1, h2, h3 ▸ StdModel.TreeSum.split hrp ta tb⟩
  | const k x hk hd =>
    have hx : IsFin x := hfin x (List.mem_replicate.mpr ⟨by omega, rfl⟩)
    rw [reals_replicate] at hn hov ⊢
    have hu := u_pos
    have hk53 : k ≤ 2 ^ 53 := by
      have : ((2 * k : ℕ) : ℝ) * u < 1 := by simpa using hn
      have hkr : (k : ℝ) < 2 ^ 53 := by
        rw [u_val] at this; push_cast at this
        have : (2 * (k : ℝ)) < 2 ^ 53 := by
          have h2 : (0 : ℝ) < 2 ^ 53 := by positivity
          rw [mul_one_div, div_lt_one h2] at this; exact this
        linarith
      exact_mod_cast hkr.le
    have hm : FloatBounds.mag (List.replicate k (val x)) = k * (|val x| + tiny) := by
      simp [FloatBounds.mag, List.map_replicate, List.sum_replicate]; ring
    have hstep : |(k : ℝ) * val x| ≤ maxFinite := by
      rw [abs_mul, Nat.abs_cast]
      have ht : 0 ≤ tiny := by unfold tiny; positivity
      have hk0 : (0 : ℝ) ≤ k := by positivity
      rw [hm] at hov; nlinarith [abs_nonneg (val x)]
    obtain ⟨h1, h2, h3⟩ := fmul_model hk hk53 hd hx hstep
    exact ⟨h1, h2, h3 ▸ StdModel.TreeSum.const k (val x)⟩

theorem FloatSumsK.sumBoundRaw {vs : List Value} {c : Int} (h : FloatSumsK vs c) :
    SumBoundRaw vs c :=
  sumBoundRaw_of_near fun hfin hk32 hov => by
    have hnk := nu_lt hk32
    obtain ⟨hfc, _, ht⟩ := FloatSumsK.treeSum h hfin hnk hov
    have hu := u_pos
    have hg := gamma_lt_one hnk
    have hm := mag_nonneg (reals vs)
    have hk1 : ((reals vs).length : ℝ) * u < 1 := by push_cast at hnk; nlinarith
    exact ⟨hfc, ht.error model hk1 (by nlinarith)⟩

/-- A sum `SumOrder` allows of small integers under a shapeless behaviour:
`SumBound`, and the exact sum, which the codes give. -/
theorem sumOrder_of {b : Behaviour} {vs : List Value} {c : Int}
    (hb1 : b ≠ "EXACT") (hb2 : ¬ (b = "ANY" ∨ b = "PAIRWISE")) (hb3 : b ≠ "SEQUENTIAL")
    (hs : SumBound vs c)
    (hx : (∀ v ∈ vs, IntVal v) → scaledAbsSum vs ≤ 2 ^ 53 * unitK → canon c = ofExact (exactSum vs)) :
    SumOrder b vs c := by
  simp only [SumOrder, hb1, hb2, hb3, ↓reduceIte]
  refine ⟨hs, fun ⟨hw, hbd⟩ => ?_⟩
  have hw' : ∀ v ∈ vs, IntVal v := hw
  obtain ⟨hk, hE⟩ := exactSum_int hw'
  obtain ⟨hfE, -⟩ := ofExact_int_val hk (Nat.le_trans hE hbd)
  rw [hx hw' hbd, floatSumCR, nonFinite_int hw', Option.getD_none, fin_canon hfE]

/-- **A sum with constant runs meets `SumOrder` under `SCALED_CONSTANT`**
(#1196): DuckDB's double `SUM` (duckdb-sum-double), a tree of sequential sums
whose constant runs enter as one product, is within `SumBound` and exact on
small integers. -/
theorem FloatSumsK.sumOrder {vs : List Value} {c : Int} (h : FloatSumsK vs c) :
    SumOrder "SCALED_CONSTANT" vs c :=
  sumOrder_of (by decide) (by decide) (by decide)
    (SumBound.of_raw FloatSumsK.canonV FloatSumsK.sumBoundRaw h)
    (fun hw hb => FloatSumsK.int_exact h hw hb)

/-! ## Kahan's sum -/

/-- **A Kahan step's rounded values stay below the largest double**: from a
state whose compensation is within `4u · A` and whose `s − c` is within
`6u · A` of the exact sum `S`, `|S| ≤ A`. -/
theorem kstep_args {s c S A x : ℝ} (hA : 0 ≤ A) (hS : |S| ≤ A) (hcA : |c| ≤ 4 * u * A)
    (hF : |s - c - S| ≤ 6 * u * A) (hov : 2 * (A + |x| + tiny) ≤ maxFinite) :
    |x - c| ≤ maxFinite ∧ |s + model.fl (x - c)| ≤ maxFinite ∧
      |model.fl (s + model.fl (x - c)) - s| ≤ maxFinite ∧
      |model.fl (model.fl (s + model.fl (x - c)) - s) - model.fl (x - c)| ≤ maxFinite := by
  obtain ⟨hu, hu', -, -, -⟩ := fpFacts
  have hτ : (0 : ℝ) ≤ tiny := by unfold tiny; positivity
  have hu1 : u ≤ 1 / 100 := le_trans hu' (by norm_num)
  have hX := abs_nonneg x
  set A' := A + |x| + tiny with hA'
  have hA'0 : 0 ≤ A' := by linarith
  have huA : u * A ≤ 1 / 100 * A := mul_le_mul_of_nonneg_right hu1 hA
  have huA' : u * A' ≤ 1 / 100 * A' := mul_le_mul_of_nonneg_right hu1 hA'0
  have err := fun z (hz : |z| ≤ maxFinite) => model.err z hz
  -- `x − c`
  have h1 : |x - c| ≤ A' := by
    have := abs_sub_le_add x c; linarith
  have h1M : |x - c| ≤ maxFinite := by linarith
  have ey := err _ h1M
  have ey' : u * (|x - c| + tiny) ≤ u * (A' + tiny) := by gcongr
  -- `s + y`
  have esy : s + model.fl (x - c) = (S + x) + (s - c - S) + (model.fl (x - c) - (x - c)) := by ring
  have h2 : |s + model.fl (x - c)| ≤ A' + 6 * u * A + u * (A' + tiny) := by
    rw [esy]
    have := abs_add_le ((S + x) + (s - c - S)) (model.fl (x - c) - (x - c))
    have := abs_add_le (S + x) (s - c - S)
    have := abs_add_le S x
    linarith
  have hut : u * tiny ≤ 1 / 100 * tiny := mul_le_mul_of_nonneg_right hu1 hτ
  have h2' : |s + model.fl (x - c)| ≤ 2 * A' := by linarith
  have h2M : |s + model.fl (x - c)| ≤ maxFinite := by linarith
  have et := err _ h2M
  -- `t − s = (t − (s + y)) + y`
  have ets : model.fl (s + model.fl (x - c)) - s =
      (model.fl (s + model.fl (x - c)) - (s + model.fl (x - c))) + model.fl (x - c) := by ring
  have hy : |model.fl (x - c)| ≤ A' + u * (A' + tiny) := by
    have := abs_sub_abs_le_abs_sub (model.fl (x - c)) (x - c); linarith
  have h3 : |model.fl (s + model.fl (x - c)) - s| ≤ u * (2 * A' + tiny) + A' + u * (A' + tiny) := by
    rw [ets]
    have := abs_add_le (model.fl (s + model.fl (x - c)) - (s + model.fl (x - c))) (model.fl (x - c))
    have : u * (|s + model.fl (x - c)| + tiny) ≤ u * (2 * A' + tiny) := by gcongr
    linarith
  have h3' : |model.fl (s + model.fl (x - c)) - s| ≤ 2 * A' := by linarith
  have h3M : |model.fl (s + model.fl (x - c)) - s| ≤ maxFinite := by linarith
  have ed := err _ h3M
  -- `d − y = (d − (t − s)) + (t − (s + y))`
  have edy : model.fl (model.fl (s + model.fl (x - c)) - s) - model.fl (x - c) =
      (model.fl (model.fl (s + model.fl (x - c)) - s) - (model.fl (s + model.fl (x - c)) - s)) +
        (model.fl (s + model.fl (x - c)) - (s + model.fl (x - c))) := by ring
  refine ⟨h1M, h2M, h3M, ?_⟩
  rw [edy]
  have := abs_add_le (model.fl (model.fl (s + model.fl (x - c)) - s) - (model.fl (s + model.fl (x - c)) - s))
    (model.fl (s + model.fl (x - c)) - (s + model.fl (x - c)))
  have a1 : u * (|model.fl (s + model.fl (x - c)) - s| + tiny) ≤ u * (2 * A' + tiny) := by gcongr
  have a2 : u * (|s + model.fl (x - c)| + tiny) ≤ u * (2 * A' + tiny) := by gcongr
  have : u * (2 * A' + tiny) ≤ 1 / 100 * (2 * A' + tiny) := mul_le_mul_of_nonneg_right hu1 (by linarith)
  have : tiny ≤ A' := by linarith
  linarith

/-- **Kahan's state after any prefix**: its compensation within `4u · A` and
its `s − c` within `6u · A` of the exact sum, `A = Σ(|xᵢ| + 2⁻¹⁰²²)`
(`Rnd.kfold_mid` from `(0, 0)`). -/
theorem kahan_state (xs : List ℝ) (hn : 14 * (xs.length : ℝ) * u ≤ 1)
    (hov : 2 * FloatBounds.mag xs ≤ maxFinite) :
    |(xs.foldl model.toRnd.kstep (0, 0)).2| ≤ 4 * u * FloatBounds.mag xs ∧
      |(xs.foldl model.toRnd.kstep (0, 0)).1 - (xs.foldl model.toRnd.kstep (0, 0)).2 - xs.sum|
        ≤ 6 * u * FloatBounds.mag xs := by
  have hu := u_pos
  have hmag : model.toRnd.mag xs = FloatBounds.mag xs := rfl
  have h := Rnd.kfold_mid (R := model.toRnd) xs [] (0, 0) 0 (fun _ _ => trivial) trivial trivial
    (by simp) (by simp) (by simp) (by simpa using hn) (by simpa [hmag] using hov)
  simp only [List.nil_append, hmag] at h
  obtain ⟨-, -, h3, h4⟩ := h
  refine ⟨h3, le_trans h4 ?_⟩
  have hP := Rnd.mag_eq' (R := model.toRnd) xs
  rw [hmag] at hP
  have hτ : model.toRnd.τ = tiny := rfl
  rw [hτ] at hP
  have hPn : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
  have hm := mag_nonneg xs
  have a : 14 * xs.length * u ^ 2 * FloatBounds.mag xs ≤ u * FloatBounds.mag xs := by
    have := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ u * FloatBounds.mag xs)
    nlinarith
  have ht : 0 ≤ (xs.length : ℝ) * tiny := by unfold tiny; positivity
  have b : 2 * u * (xs.map abs).sum + 3 * u * xs.length * model.toRnd.τ ≤ 3 * u * FloatBounds.mag xs := by
    rw [hτ, hP]; nlinarith
  have : 0 ≤ u * FloatBounds.mag xs := by positivity
  linarith

/-- **Kahan's sum on codes is the model's**, step by step: on finite values
whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double, the running sum
and the compensation are finite codes of their sign, whose values are
`Rnd.kahan`'s state under the core's rounding. -/
theorem kahan_model :
    ∀ (ws : List Value), (∀ x, Value.float x ∈ ws → IsFin x) →
      14 * ((reals ws).length : ℝ) * u ≤ 1 → 2 * FloatBounds.mag (reals ws) ≤ maxFinite →
      IsFin (ws.foldl kahanStep (0, 0)).1 ∧ Neg (ws.foldl kahanStep (0, 0)).1 ∧
        IsFin (ws.foldl kahanStep (0, 0)).2 ∧ Neg (ws.foldl kahanStep (0, 0)).2 ∧
        val (ws.foldl kahanStep (0, 0)).1 = ((reals ws).foldl model.toRnd.kstep (0, 0)).1 ∧
        val (ws.foldl kahanStep (0, 0)).2 = ((reals ws).foldl model.toRnd.kstep (0, 0)).2 := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil =>
    intro _ _ _
    have hz : IsFin 0 := ⟨by have := negInf_eq; omega, by have := posInf_eq; omega⟩
    simp only [List.foldl_nil, reals, floatsOf, List.filterMap_nil, List.map_nil]
    exact ⟨hz, neg_zero_code, hz, neg_zero_code, val_zero, val_zero⟩
  | append_singleton l w ih =>
    intro hfin hn hov
    have hfl : ∀ x, Value.float x ∈ l → IsFin x := fun x hx => hfin x (by simp [hx])
    have hsub : (reals l).Sublist (reals (l ++ [w])) := by
      rw [reals_append]; exact List.sublist_append_left _ _
    have hlen : (reals l).length ≤ (reals (l ++ [w])).length := hsub.length_le
    have hu := u_pos
    have hn' : 14 * ((reals l).length : ℝ) * u ≤ 1 := by
      have : ((reals l).length : ℝ) ≤ (reals (l ++ [w])).length := by exact_mod_cast hlen
      nlinarith
    have hov' : 2 * FloatBounds.mag (reals l) ≤ maxFinite := by
      have := mag_le_of_sublist hsub; linarith
    obtain ⟨fs, ns, fc, nc, vs, vc⟩ := ih hfl hn' hov'
    by_cases hw : ∃ x, w = .float x
    · obtain ⟨x, rfl⟩ := hw
      have hx : IsFin x := hfin x (by simp)
      have hr : reals (l ++ [.float x]) = reals l ++ [val x] := by rw [reals_append, reals_float]
      rw [hr] at hov
      have hmag : FloatBounds.mag (reals l ++ [val x]) = FloatBounds.mag (reals l) + (|val x| + tiny) := by
        rw [mag_append]; simp
      rw [hmag] at hov
      obtain ⟨hcA, hF⟩ := kahan_state (reals l) hn' hov'
      generalize hp : (reals l).foldl model.toRnd.kstep (0, 0) = p at hcA hF vs vc
      have hS : |(reals l).sum| ≤ FloatBounds.mag (reals l) := by
        rw [mag_eq]
        have := abs_sum_le_sum_abs (reals l)
        have : 0 ≤ ((reals l).length : ℝ) * tiny := by unfold tiny; positivity
        linarith
      obtain ⟨a1, a2, a3, a4⟩ := kstep_args (x := val x) (mag_nonneg _) hS hcA hF (by linarith)
      generalize hq : l.foldl kahanStep (0, 0) = q at fs ns fc nc vs vc
      -- the four steps
      have rx : rv x = val x := rv_of_fin hx
      have rc : rv q.2 = p.2 := by rw [rv_of_fin fc, vc]
      obtain ⟨ny, ry⟩ := fsub_model_num (IsFin.num hx) (IsFin.num fc) (by rw [rx, rc]; exact a1)
      rw [rx, rc] at ry
      obtain ⟨ft, nt, vt⟩ := fadd_model_neg fs ns ny (by rw [vs, ry]; exact a2)
      rw [vs, ry] at vt
      obtain ⟨fd, nd, vd⟩ := fsub_model_neg ft nt (IsFin.num fs) (by rw [vt, rv_of_fin fs, vs]; exact a3)
      rw [vt, rv_of_fin fs, vs] at vd
      obtain ⟨fc', nc', vc'⟩ := fsub_model_neg fd nd ny (by rw [vd, ry]; exact a4)
      rw [vd, ry] at vc'
      have hstep : (l ++ [Value.float x]).foldl kahanStep (0, 0) =
          (fadd q.1 (fsub x q.2), fsub (fsub (fadd q.1 (fsub x q.2)) q.1) (fsub x q.2)) := by
        rw [List.foldl_append, hq]; rfl
      have hrstep : (reals l ++ [val x]).foldl model.toRnd.kstep (0, 0) = model.toRnd.kstep p (val x) := by
        rw [List.foldl_append, hp]; rfl
      rw [hstep, hr, hrstep]
      exact ⟨ft, nt, fc', nc', vt, vc'⟩
    · have e : (l ++ [w]).foldl kahanStep (0, 0) = l.foldl kahanStep (0, 0) ∧
          reals (l ++ [w]) = reals l := by
        cases w <;> simp_all [List.foldl_append, kahanStep, reals, floatsOf]
      rw [e.1, e.2]
      exact ⟨fs, ns, fc, nc, vs, vc⟩

/-- **Kahan's sums meet the core's `SumBoundRaw`** (#1196): by
`Rnd.kahan_near` under the core's rounding, the values being doubles. -/
theorem KahanSums.sumBoundRaw {vs : List Value} {c : Int} (h : KahanSums vs c) :
    SumBoundRaw vs c := by
  obtain ⟨hd, ws, hp, rfl⟩ := h
  refine sumBoundRaw_of_near fun hfin hk32 hov => ?_
  have hrp := reals_perm hp
  have hfw : ∀ x, Value.float x ∈ ws → IsFin x := fun x hx => hfin x (hp.subset hx)
  have hk32' : ((reals ws).length : ℝ) ≤ 2 ^ 32 := by rwa [hrp.length_eq]
  have hov' : 2 * FloatBounds.mag (reals ws) ≤ maxFinite := by rwa [mag_perm hrp]
  obtain ⟨hf, -, -, -, hv, -⟩ := kahan_model ws hfw (Rnd.nu_small hk32') hov'
  refine ⟨hf, ?_⟩
  have hx : ∀ y ∈ reals ws, model.toRnd.G y ∧ model.toRnd.fl y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxv : Value.float x ∈ ws := mem_floatsOf.mp hx
    exact ⟨trivial, fl_dbl (hd x (hp.subset hxv)) (hfw x hxv)⟩
  have hnear := Rnd.kahan_near (R := model.toRnd) hx hk32'
    (show 2 * model.toRnd.mag (reals ws) ≤ maxFinite from hov')
  have hnear' := Rnd.Near.perm hrp hnear
  unfold Rnd.Near at hnear'
  rw [Rnd.kahan, ← hv] at hnear'
  exact hnear'

/-- **Kahan's sum meets `SumOrder` under `COMPENSATED`** (#1196): a double
`SUM` by Kahan's sum of the doubles in some order (DuckDB's `kahan_sum`,
duckdb-kahan-sum) is within `SumBound` and exact on small integers. -/
theorem KahanSums.sumOrder {vs : List Value} {c : Int} (h : KahanSums vs c) :
    SumOrder "COMPENSATED" vs c :=
  sumOrder_of (by decide) (by decide) (by decide)
    (SumBound.of_raw KahanSums.canonV KahanSums.sumBoundRaw h)
    (fun hw hb => KahanSums.int_exact h hw hb)

end FloatBridge
