import FloatBridge.Codes
import FloatBounds.Tree
import FloatBounds.Shard
import FloatBounds.IntExact
import FloatBounds.Epsilon
import Sverify.Core.AllowedP
import Sverify.Core.FloatArith
import Sverify.Core.SumBound

/-!
# The core's summation orders are the standard model's tree sums (#1196, part 2)

The core states an engine's double `SUM` under `ANY`, `PAIRWISE` or
`SEQUENTIAL` as `FloatSums`: a sequential sum of a permutation (`floatSum`,
the codes added with `fadd` from `+0.0`), or two such sums of a split added
together. `float-bounds` bounds `StdModel.TreeSum`, the same shapes over the
reals (`TreeSum.error`, `Summed.near`).

`FloatSums.treeSum` ties the two under the core's rounding (`model`, part 1):
on finite doubles whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double
(the hypothesis of the core's `SumBound`), every sum `FloatSums` allows is
finite, and its value is a `TreeSum` of the values (`reals`). No partial sum
overflows: each is a tree sum of fewer values, which `TreeSum.error` keeps
within twice their magnitude (`TreeSum.abs_le`).

The core's finite codes include ones no double has (a negative code of
magnitude zero, `-1`); two such added give `-0.0`, which is not finite. A sum
`FloatSums` builds starts from `+0.0` and rounds with `ofExact`, so a negative
result has a nonzero magnitude (`Neg`), and the sums stay finite.
-/

set_option exponentiation.threshold 2200

namespace FloatBridge

open FloatBounds Substrait FloatCode

/-- The values of the doubles among `vs`, read from their codes. -/
noncomputable def reals (vs : List Value) : List ℝ := (floatsOf vs).map val

theorem reals_perm {vs ws : List Value} (h : vs.Perm ws) : (reals vs).Perm (reals ws) :=
  (h.filterMap _).map _

theorem reals_append (vs ws : List Value) : reals (vs ++ ws) = reals vs ++ reals ws := by
  simp [reals, floatsOf, List.filterMap_append]

theorem reals_float (c : Int) : reals [.float c] = [val c] := by
  simp [reals, floatsOf]

/-- A negative code has a nonzero magnitude: what every sum `FloatSums` builds
satisfies, and what keeps `fadd` from `-0.0`. -/
def Neg (c : Int) : Prop := c < 0 → scaled c < 0

theorem scaled_nonpos {c : Int} (h : c < 0) : scaled c ≤ 0 := by
  unfold scaled; simp only [h, ↓reduceIte]; omega

theorem scaled_nonneg {c : Int} (h : ¬ c < 0) : 0 ≤ scaled c := by
  unfold scaled; simp only [h, ↓reduceIte]; omega

theorem roundMagDiv_pos {m : Nat} (hm : 1 ≤ m) : 1 ≤ roundMagDiv m 1 := by
  have h1 : roundMagDiv 1 1 = 1 := by
    have := roundMagDiv_exact (k := 1) (s := 0) (by decide)
    simpa using this
  have := roundMagDiv_mono (n := 1) (by decide) hm
  omega

theorem posCode_nonneg (m : Nat) : 0 ≤ posCode m := by
  have := posInf_eq
  unfold posCode; split
  · omega
  · split <;> omega

/-- `ofExact` of a nonzero value up to the largest double is finite, nonzero,
and negative only with a nonzero magnitude. -/
theorem ofExact_good {g : Int} (hg : g.natAbs ≤ maxMag) :
    IsFin (ofExact g) ∧ Neg (ofExact g) ∧ (g ≠ 0 → ofExact g ≠ 0) := by
  have hs := scaled_ofExact hg
  refine ⟨ofExact_fin_of_le hg, fun hneg => ?_, fun h0 e => ?_⟩
  · by_cases hgn : g < 0
    · rw [hs]; simp only [hgn, ↓reduceIte]
      have := roundMagDiv_pos (m := g.natAbs) (by omega)
      omega
    · have : 0 ≤ ofExact g := by
        unfold ofExact ofExactDiv; simp only [hgn, ↓reduceIte]; exact posCode_nonneg _
      omega
  · rw [e] at hs
    have h00 : scaled 0 = 0 := by unfold scaled; simp
    have := roundMagDiv_pos (m := g.natAbs) (by omega)
    split at hs <;> omega

/-- **One addition of the core is the model's**, while it stays below the
largest double: the code is `ofExact` of the exact sum, finite and `Neg`. -/
theorem fadd_ofExact {a b : Int} (ha : IsFin a) (hb : IsFin b) (hna : Neg a)
    (hg : (scaled a + scaled b).natAbs ≤ maxMag) :
    fadd a b = ofExact (scaled a + scaled b) := by
  have hp := posInf_eq; have hn := negInf_eq
  unfold fadd addI
  simp only [ha.not_nan, hb.not_nan, hb.not_inf, ha.ne.2.2.1, ha.ne.2.2.2.1, ha.sv_eq, hb.sv_eq,
    Bool.or_false, Bool.false_eq_true, ite_false]
  split
  · rename_i h0
    have hab : ¬ (a < 0 ∧ b < 0) := by
      rintro ⟨h1, h2⟩
      have := hna h1; have := scaled_nonpos h2; omega
    have : (decide (a < 0) && decide (b < 0)) = false := by
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hab
    rw [this, h0]; exact (ofExactDiv_zero 1).symm
  · rename_i h0
    unfold rnd
    have := (ofExact_good hg).2.2 h0
    simp only [ofExact] at this
    simp [this, ofExact]

/-- A code's value as a multiple of `2⁻¹⁰⁷⁴`. -/
theorem val_add (a b : Int) : val a + val b = ((scaled a + scaled b : Int) : ℝ) / 2 ^ 1074 := by
  simp only [val]; push_cast; ring

/-- Below the largest double in the reals, below it in units of `2⁻¹⁰⁷⁴`. -/
theorem natAbs_le_of_abs {g : Int} (h : |(g : ℝ) / 2 ^ 1074| ≤ maxFinite) : g.natAbs ≤ maxMag := by
  rw [abs_div, abs_of_pos two_pow_pos', div_le_iff₀ two_pow_pos', maxFinite_scaled] at h
  have : ((g.natAbs : ℕ) : ℝ) ≤ (maxMag : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact h
  exact_mod_cast this

/-- **A step of a core sum**: below the largest double, `fadd` is the model's
rounded addition, and keeps the sum finite and `Neg`. -/
theorem fadd_model {a b : Int} (ha : IsFin a) (hb : IsFin b) (hna : Neg a)
    (h : |val a + val b| ≤ maxFinite) :
    IsFin (fadd a b) ∧ Neg (fadd a b) ∧ val (fadd a b) = model.fl (val a + val b) := by
  rw [val_add] at h ⊢
  have hg := natAbs_le_of_abs h
  rw [fadd_ofExact ha hb hna hg, model_fl_grid hg]
  exact ⟨(ofExact_good hg).1, (ofExact_good hg).2.1, rfl⟩

/-- A tree sum stays within twice its values' magnitude. -/
theorem TreeSum.abs_le {xs : List ℝ} {s : ℝ} (h : model.TreeSum xs s)
    (hn : ((2 * xs.length : ℕ) : ℝ) * u < 1) (hov : 2 * FloatBounds.mag xs ≤ maxFinite) :
    |s| ≤ 2 * FloatBounds.mag xs := by
  have hg := gamma_lt_one hn
  have hm := mag_nonneg xs
  have hu := u_pos
  have hn1 : (xs.length : ℝ) * u < 1 := by push_cast at hn; nlinarith
  have herr := h.error model hn1 (by nlinarith)
  have hsum : |xs.sum| ≤ FloatBounds.mag xs := by
    rw [mag_eq]
    have := abs_sum_le_sum_abs xs
    have : 0 ≤ (xs.length : ℝ) * tiny := by unfold tiny; positivity
    linarith
  have := abs_sub_abs_le_abs_sub s xs.sum
  nlinarith

theorem mag_le_of_sublist {xs ys : List ℝ} (h : xs.Sublist ys) : FloatBounds.mag xs ≤ FloatBounds.mag ys := by
  rw [FloatBounds.mag, FloatBounds.mag]
  have ht : (0 : ℝ) ≤ tiny := by unfold tiny; positivity
  exact List.Sublist.sum_le_sum (h.map _) fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact add_nonneg (abs_nonneg y) ht

theorem ofInt_zero : FloatCode.ofInt 0 = 0 := by
  rw [ofInt_exact (by decide)]; simp [exactCode, FloatFormat.exactCode]

/-- **A sequential sum of the core is the model's**: the codes added in list
order from `+0.0`. -/
theorem floatSum_model :
    ∀ (ws : List Value), (∀ x, Value.float x ∈ ws → IsFin x) →
      ((2 * (reals ws).length : ℕ) : ℝ) * u < 1 → 2 * FloatBounds.mag (reals ws) ≤ maxFinite →
      IsFin (floatSum ws) ∧ Neg (floatSum ws) ∧ val (floatSum ws) = model.sum (reals ws) := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil =>
    intro _ _ _
    have hz : (0 : Int) < posInf := by have := posInf_eq; omega
    have hz' : negInf < (0 : Int) := by have := negInf_eq; omega
    simp only [floatSum, List.foldl_nil, ofInt_zero, reals, floatsOf, List.filterMap_nil,
      List.map_nil, StdModel.sum, StdModel.sumFrom]
    exact ⟨⟨hz', hz⟩, fun h => absurd h (by omega), by simp [val, scaled]⟩
  | append_singleton l w ih =>
    intro hfin hn hov
    have hfl : ∀ x, Value.float x ∈ l → IsFin x := fun x hx => hfin x (by simp [hx])
    have hsub : (reals l).Sublist (reals (l ++ [w])) := by
      rw [reals_append]; exact List.sublist_append_left _ _
    have hlen : (reals l).length ≤ (reals (l ++ [w])).length := hsub.length_le
    have hu := u_pos
    have hn' : ((2 * (reals l).length : ℕ) : ℝ) * u < 1 := by
      have : ((2 * (reals l).length : ℕ) : ℝ) ≤ ((2 * (reals (l ++ [w])).length : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hlen
      nlinarith
    have hov' : 2 * FloatBounds.mag (reals l) ≤ maxFinite := by
      have := mag_le_of_sublist hsub; linarith
    obtain ⟨hf, hneg, hv⟩ := ih hfl hn' hov'
    by_cases hw : ∃ c, w = .float c
    · obtain ⟨c, rfl⟩ := hw
      have hc : IsFin c := hfin c (by simp)
      have hfold : floatSum (l ++ [.float c]) = fadd (floatSum l) c := by
        simp [floatSum, List.foldl_append]
      rw [hfold]
      have hr : reals (l ++ [.float c]) = reals l ++ [val c] := by rw [reals_append, reals_float]
      have habs := TreeSum.abs_le (StdModel.TreeSum.seq (List.Perm.refl _)) hn' hov'
      rw [← hv] at habs
      have hmag : FloatBounds.mag (reals (l ++ [.float c])) = FloatBounds.mag (reals l) + (|val c| + tiny) := by
        rw [hr, mag_append]; simp
      have ht : 0 ≤ tiny := by unfold tiny; positivity
      have hstep : |val (floatSum l) + val c| ≤ maxFinite := by
        have := abs_add_le (val (floatSum l)) (val c)
        rw [hmag] at hov; nlinarith [abs_nonneg (val c)]
      obtain ⟨h1, h2, h3⟩ := fadd_model hf hc hneg hstep
      refine ⟨h1, h2, ?_⟩
      rw [h3, hv, hr]
      simp [StdModel.sum, StdModel.sumFrom, List.foldl_append, StdModel.add]
    · have e : floatSum (l ++ [w]) = floatSum l ∧ reals (l ++ [w]) = reals l := by
        cases w <;> simp_all [floatSum, List.foldl_append, reals, floatsOf]
      rw [e.1, e.2]
      exact ⟨hf, hneg, hv⟩

/-- **The core's summation orders are tree sums** (#1196, item 2): on finite
doubles whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double, a sum
`FloatSums` allows is finite, and its value is a `TreeSum` of the values under
the core's rounding. -/
theorem FloatSums.treeSum {vs : List Value} {c : Int} (h : FloatSums vs c)
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

/-! ## The core's `SumBound` for these orders -/

theorem tiny_scaled : tiny * 2 ^ 1074 = 2 ^ 52 := by
  rw [tiny, inv_pow]; field_simp

/-- The values' sum and magnitude, in units of `2⁻¹⁰⁷⁴`: the core's
`exactSum` and `scaledAbsSum`. -/
theorem reals_scaled :
    ∀ (vs : List Value), (∀ x, Value.float x ∈ vs → IsFin x) →
      (reals vs).sum * 2 ^ 1074 = exactSum vs ∧
        FloatBounds.mag (reals vs) * 2 ^ 1074 = scaledAbsSum vs + (reals vs).length * 2 ^ 52
  | [], _ => by simp [reals, floatsOf, exactSum, scaledAbsSum, FloatBounds.mag]
  | v :: vs, hfin => by
    have ih := reals_scaled vs fun x hx => hfin x (List.mem_cons_of_mem _ hx)
    cases v with
    | float c =>
      have hc : IsFin c := hfin c (by simp)
      have hr : reals (.float c :: vs) = val c :: reals vs := by simp [reals, floatsOf]
      have hpos := two_pow_pos'
      have hv : val c * 2 ^ 1074 = scaled c := by simp only [val]; field_simp
      have ha : |val c| * 2 ^ 1074 = ((scaled c).natAbs : ℝ) := by
        rw [← abs_of_pos hpos, ← abs_mul, hv, Nat.cast_natAbs, Int.cast_abs]
      rw [hr, List.sum_cons, mag_cons, List.length_cons]
      simp only [exactSum, scaledAbsSum, exact, canon_of_bounds hc]
      refine ⟨?_, ?_⟩
      · push_cast; rw [add_mul, hv, ih.1]
      · push_cast; rw [add_mul, add_mul, ha, tiny_scaled, ih.2]; ring
    | _ => simpa [reals, floatsOf, exactSum, scaledAbsSum] using ih

/-- **The core's `SumBoundRaw` holds of every `ANY`, `PAIRWISE` and
`SEQUENTIAL` sum** (#1196): what `SumOrder` asserts of these orders beside
their shape follows from the shape, by `TreeSum.error` under the core's
rounding. -/
theorem FloatSums.sumBoundRaw {vs : List Value} {c : Int} (h : FloatSums vs c) :
    SumBoundRaw vs c := by
  intro hfin hlen hov
  have hpos := two_pow_pos'
  have hu := u_pos
  obtain ⟨hsum, hmag⟩ := reals_scaled vs hfin
  set n := vs.length
  set k := (reals vs).length
  set S := scaledAbsSum vs
  have hkn : k ≤ n := by
    simp only [k, n, reals, List.length_map]; exact List.length_filterMap_le _ _
  have hn32 : (n : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hlen
  have hk32 : (k : ℝ) ≤ 2 ^ 32 := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  have hnk := nu_lt hk32
  have hnn := nu_lt hn32
  -- `2 · mag ≤ maxFinite`, from the core's `2 (S + n 2⁵²) ≤ maxMag`.
  have hovR : 2 * FloatBounds.mag (reals vs) ≤ maxFinite := by
    have h1 : ((2 * (S + n * 2 ^ 52) : ℕ) : ℝ) ≤ (maxMag : ℝ) := by exact_mod_cast hov
    have h2 : (k : ℝ) * 2 ^ 52 ≤ (n : ℝ) * 2 ^ 52 := by
      have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith
    rw [← maxFinite_scaled] at h1; push_cast at h1
    have : 2 * FloatBounds.mag (reals vs) * 2 ^ 1074 ≤ maxFinite * 2 ^ 1074 := by
      rw [mul_assoc, hmag]; linarith
    exact le_of_mul_le_mul_right this hpos
  obtain ⟨hfc, _, ht⟩ := FloatSums.treeSum h hfin hnk hovR
  refine ⟨hfc, ?_⟩
  have hg := gamma_lt_one hnk
  have hm := mag_nonneg (reals vs)
  have hk1 : (k : ℝ) * u < 1 := by push_cast at hnk; nlinarith
  have hn1 : (n : ℝ) * u < 1 := by push_cast at hnn; nlinarith
  have herr := ht.error model hk1 (by nlinarith)
  -- In units of `2⁻¹⁰⁷⁴`: `|c − Σ| ≤ γₖ (S + k 2⁵²) ≤ γₙ (S + n 2⁵²)`.
  have hd : |((scaled c - exactSum vs : Int) : ℝ)| ≤ gamma n * ((S : ℝ) + n * 2 ^ 52) := by
    have e1 : ((scaled c - exactSum vs : Int) : ℝ) = (val c - (reals vs).sum) * 2 ^ 1074 := by
      rw [sub_mul, hsum]; simp only [val]; push_cast; field_simp
    rw [e1, abs_mul, abs_of_pos hpos]
    have hgm := gamma_mono hkn hn1
    have hg0 := gamma_nonneg hk1
    have hkS : (S : ℝ) + k * 2 ^ 52 ≤ S + n * 2 ^ 52 := by
      have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith
    calc |val c - (reals vs).sum| * 2 ^ 1074 ≤ gamma k * FloatBounds.mag (reals vs) * 2 ^ 1074 :=
          mul_le_mul_of_nonneg_right herr hpos.le
      _ = gamma k * ((S : ℝ) + k * 2 ^ 52) := by rw [mul_assoc, hmag]
      _ ≤ gamma n * ((S : ℝ) + n * 2 ^ 52) := by
          apply mul_le_mul hgm hkS (by positivity) (le_trans hg0 hgm)
  -- `γₙ = n / (2⁵³ − n)`, multiplied out.
  have hn53 : n ≤ 2 ^ 53 := le_trans hlen (by decide)
  have hlt : (n : ℝ) < 2 ^ 53 := by
    have : (n : ℝ) ≤ 2 ^ 32 := hn32
    linarith
  have hgam : gamma n * (2 ^ 53 - n) = n := by
    rw [gamma, u_val]; field_simp
  have hS0 : (0 : ℝ) ≤ (S : ℝ) + n * 2 ^ 52 := by positivity
  have key : |((scaled c - exactSum vs : Int) : ℝ)| * ((2 : ℝ) ^ 53 * (2 ^ 53 - n)) ≤
      ((n : ℝ) * 2 ^ 53 + (2 ^ 53 - n)) * ((S : ℝ) + n * 2 ^ 52) := by
    have h1 := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ 2 ^ 53 * (2 ^ 53 - n) by
      have : (0 : ℝ) ≤ 2 ^ 53 - n := by linarith
      positivity)
    have h2 : gamma n * ((S : ℝ) + n * 2 ^ 52) * (2 ^ 53 * (2 ^ 53 - n)) =
        (n : ℝ) * 2 ^ 53 * ((S : ℝ) + n * 2 ^ 52) := by
      have : gamma n * ((S : ℝ) + n * 2 ^ 52) * (2 ^ 53 * (2 ^ 53 - n)) =
          (gamma n * (2 ^ 53 - n)) * 2 ^ 53 * ((S : ℝ) + n * 2 ^ 52) := by ring
      rw [this, hgam]
    have h3 : (n : ℝ) * 2 ^ 53 * ((S : ℝ) + n * 2 ^ 52) ≤
        ((n : ℝ) * 2 ^ 53 + (2 ^ 53 - n)) * ((S : ℝ) + n * 2 ^ 52) := by
      have : (0 : ℝ) ≤ 2 ^ 53 - n := by linarith
      nlinarith
    linarith
  have hcast : (((scaled c - exactSum vs).natAbs * (2 ^ 53 * (2 ^ 53 - n)) : ℕ) : ℝ) ≤
      (((n * 2 ^ 53 + (2 ^ 53 - n)) * (S + n * 2 ^ 52) : ℕ) : ℝ) := by
    have hsub : ((2 ^ 53 - n : ℕ) : ℝ) = 2 ^ 53 - n := by
      rw [Nat.cast_sub hn53]; push_cast; ring
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, hsub, Nat.cast_natAbs,
      Int.cast_abs]
    exact key
  exact_mod_cast hcast

/-- **The core's `SumBound` holds of every `ANY`, `PAIRWISE` and `SEQUENTIAL`
sum** (#1196, ruling 242): of the codes as they are by `FloatSums.sumBoundRaw`,
and of the canonical codes since the same order over the canonical values
gives the same sum up to `canon` (`FloatSums.canonV`). -/
theorem FloatSums.sumBound {vs : List Value} {c : Int} (h : FloatSums vs c) : SumBound vs c :=
  Substrait.FloatSums.sumBound_of_raw FloatSums.sumBoundRaw h

end FloatBridge
