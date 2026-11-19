import Sverify.DuckDB.LiftSearch
import Sverify.Core.FloatAround

/-!
# DuckDB's `avg` of integers: a set of doubles (#1608 12d-2)

DuckDB sums the integers exactly and divides once, but how it converts the
sum and divides depends on the platform's `long double` and on the plan's
shape (`duckdb-avg-int`). So its result is one of a set of doubles, which
the fact states in two ranges for exact sum `s`, count `n` and `q = s / n`:

* `|s| ≤ 2⁵³` and `n ≤ 2⁵³`: one of the two doubles around `q`, and `q`
  itself when it is a double (`FloatCode.Around`);
* otherwise a double within `8 · 2⁻⁵³` of `q`, relatively
  (`FloatCode.WithinRel`).

`DuckAgg.Allowed` is that set; `DuckAgg.eval`, the lifted plan's value,
is one member of it (`DuckAgg.eval_allowed`). A mean of small integers that
is an integer is exact (`DuckAgg.avgBigint_exact`), and every member is
within one unit in the last place of the model's value in the first range,
and within `16 · 2⁻⁵³` in the second (`DuckAgg.avgBigint_near`).
`AggEntry.allowed_near` carries this to every lifted aggregate, so the
generated entries need no change.

Everything is integer arithmetic on codes, in units of `2⁻¹⁰⁷⁴`: the set
holds codes of doubles only (`posCode`, never a second code of one value,
and never `-0.0`).
-/

namespace Substrait

namespace FloatCode

set_option exponentiation.threshold 2200

/-- A double's code: one code per value, `0` for zero. -/
def IsDouble (r : Int) : Prop := ∃ m, m ≤ maxMag ∧ (r = posCode m ∨ r = -posCode m)

/-- `r` is a double within `c · 2⁻⁵³` of `V / n`, relatively. -/
def WithinRel (c : Nat) (V : Int) (n : Nat) (r : Int) : Prop :=
  IsDouble r ∧ 2 ^ 53 * ((n : Int) * scaled r - V).natAbs ≤ c * V.natAbs

/-- `ofExactDiv` does not see a common factor. -/
theorem ofExactDiv_mul_mul (v : Int) {k n : Nat} (hk : 0 < k) :
    ofExactDiv (k * v) (k * n) = ofExactDiv v n := by
  have hg : gridExp (k * v.natAbs) (k * n) = gridExp v.natAbs n := by
    unfold gridExp; rw [Nat.mul_div_mul_left _ _ hk]
  have hr : roundMagDiv (k * v.natAbs) (k * n) = roundMagDiv v.natAbs n := by
    unfold roundMagDiv; rw [hg, Nat.mul_assoc, rndDiv_mul_left _ _ hk]
  unfold ofExactDiv
  rw [Int.natAbs_mul, Int.natAbs_natCast, hr]
  have : (k : Int) * v < 0 ↔ v < 0 := by
    constructor
    · intro h; rcases Int.lt_or_le v 0 with h' | h'
      · exact h'
      · exact absurd h (Int.not_lt.mpr (Int.mul_nonneg (Int.natCast_nonneg k) h'))
    · intro h; exact Int.mul_neg_of_pos_of_neg (Int.ofNat_lt.mpr hk) h
  simp only [this]

/-- A quotient of at least one rounds to a nonzero magnitude. -/
theorem roundMagDiv_pos {a n : Nat} (hn : 0 < n) (h : n ≤ a) : 0 < roundMagDiv a n := by
  unfold roundMagDiv
  have hP := Nat.two_pow_pos (gridExp a n)
  have hd : n * 2 ^ gridExp a n ≤ a := by
    by_cases hg : gridExp a n = 0
    · rw [hg]; simpa using h
    · have h1 := le_of_gridExp (a := a) (n := n) (by omega)
      have h2 : 2 ^ gridExp a n ≤ 2 ^ (gridExp a n + 52) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n * (a / n) ≤ a := Nat.mul_div_le _ _
      exact Nat.le_trans (Nat.mul_le_mul_left n (Nat.le_trans h2 h1)) h3
  have h1 : 1 ≤ a / (n * 2 ^ gridExp a n) := (Nat.le_div_iff_mul_le (Nat.mul_pos hn hP)).mpr (by simpa using hd)
  exact Nat.mul_pos (Nat.lt_of_lt_of_le h1 (rndDiv_ge _ _)) hP

theorem posCode_ne_zero {m : Nat} (h : 0 < m) : posCode m ≠ 0 := by
  have := posInf_eq
  unfold posCode; split
  · omega
  · split <;> omega

theorem signedMag_ne_zero (neg : Bool) {m : Nat} (h : 0 < m) : signedMag neg m ≠ 0 := by
  have := posCode_ne_zero h
  unfold signedMag; split <;> omega

/-- `fdiv` of finite doubles by a positive one is the rounded quotient,
where that is not zero (no `-0.0`). -/
theorem fdiv_eq_of_ne_zero {a b : Int} (ha : IsFin a) (hb : IsFin b) (hb0 : 0 < scaled b)
    (h : ofExactDiv (scaled a * unitK) (scaled b).natAbs ≠ 0) :
    fdiv a b = ofExactDiv (scaled a * unitK) (scaled b).natAbs := by
  have hbz : isZeroCode b = false := by
    have h0 : b ≠ 0 := fun e => by subst e; exact absurd hb0 (by decide)
    simp [isZeroCode, h0, hb.ne.2.2.2.2]
  unfold fdiv divI
  simp only [ha.not_nan, hb.not_nan, ha.not_inf, hb.not_inf, hbz, ha.sv_eq, hb.sv_eq,
    Bool.or_false, Bool.and_false, Bool.false_eq_true, ite_false,
    show ¬ scaled b < 0 by omega]
  split
  · rename_i hz
    exfalso; apply h
    have ha0 : a = 0 := by
      simp only [isZeroCode, Bool.or_eq_true, beq_iff_eq] at hz
      exact hz.resolve_right ha.ne.2.2.2.2
    subst ha0
    simp only [show scaled 0 = 0 from rfl, Int.zero_mul]
    exact ofExactDiv_zero _
  · unfold rnd; simp [h]

/-- `fdiv` of a zero by a positive finite double is `+0.0`. -/
theorem fdiv_zero_left {b : Int} (hb : IsFin b) (hb0 : 0 < scaled b) : fdiv 0 b = 0 := by
  have h0 : b ≠ 0 := fun e => by subst e; exact absurd hb0 (by decide)
  have hbn : ¬ b < 0 := by unfold scaled at hb0; split at hb0 <;> omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb.ne
  unfold fdiv divI
  simp [isNanCode, isInfCode, isZeroCode, zeroOf, hbn, h0, h1, h2, h3, h4, h5,
    show (0 : Int) ≠ nan by have := nan_eq; omega, show (0 : Int) ≠ negNan by have := negNan_eq'; omega,
    show (0 : Int) ≠ posInf by have := posInf_eq; omega, show (0 : Int) ≠ negInf by have := negInf_eq; omega]

theorem scaled_exactCode (i : Int) : scaled (exactCode i) = i * (unitK : Int) := by
  simp only [scaled, exactCode, FloatFormat.exactCode, fp64_scale, unitK]
  split
  · subst_vars; simp
  · split <;> omega

theorem unitK_pos : 0 < unitK := Nat.two_pow_pos _

/-- Dividing `v · 2¹⁰⁷⁴` by `n · 2¹⁰⁷⁴` rounds as `v / n` does. -/
theorem ofExactDiv_unitK (v : Int) (n : Nat) :
    ofExactDiv (v * unitK * unitK) (n * unitK) = ofExactDiv (v * unitK) n := by
  rw [← ofExactDiv_mul_mul (v * unitK) (k := unitK) (n := n) unitK_pos, Int.mul_comm (v * unitK),
    Nat.mul_comm n]

/-- The rounded quotient of a nonzero `V` by a count `n ≤ |V|`, as `fdiv`
computes it from the doubles of `V / 2¹⁰⁷⁴` and `n`, when both are exact. -/
theorem fdiv_exact_eq {s : Int} {n : Nat} (hs : s.natAbs ≤ 2 ^ 53) (hn0 : 0 < n) (hn : n ≤ 2 ^ 53) :
    fdiv (ofInt s) (ofInt n) = ofExactDiv (s * unitK) n := by
  have ha : ofInt s = exactCode s := ofInt_exact hs
  have hb : ofInt n = exactCode n := ofInt_exact (by simpa using hn)
  have hfa : IsFin (ofInt s) := ofInt_bounds s
  have hfb : IsFin (ofInt n) := ofInt_bounds n
  have hsb : scaled (ofInt n) = n * (unitK : Int) := by rw [hb, scaled_exactCode]
  have hsb0 : 0 < scaled (ofInt n) := by
    rw [hsb]; exact Int.mul_pos (by omega) (Int.ofNat_lt.mpr unitK_pos)
  have hsa : scaled (ofInt s) = s * (unitK : Int) := by rw [ha, scaled_exactCode]
  have hnat : (scaled (ofInt n)).natAbs = n * unitK := by
    rw [hsb, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  by_cases h0 : s = 0
  · subst h0
    rw [show ofInt 0 = 0 by rw [ofInt_exact (by decide)]; rfl, fdiv_zero_left hfb hsb0,
      Int.zero_mul, ofExactDiv_zero]
  · have hne : ofExactDiv (s * unitK) n ≠ 0 := by
      rw [ofExactDiv_eq_signedMag]
      refine signedMag_ne_zero _ (roundMagDiv_pos hn0 ?_)
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      have : 2 ^ 53 ≤ unitK := Nat.pow_le_pow_right (by omega) (by omega)
      have : 1 ≤ s.natAbs := by omega
      exact Nat.le_trans hn (Nat.le_trans ‹2 ^ 53 ≤ unitK› (Nat.le_mul_of_pos_left _ (by omega)))
    rw [fdiv_eq_of_ne_zero hfa hfb hsb0 (by rw [hsa, hnat, ofExactDiv_unitK]; exact hne), hsa, hnat,
      ofExactDiv_unitK]

/-- Three roundings, each within `2⁻⁵³` relatively: of the sum (`A`, with
`|A| = m`), of the count (`nb`) and of the quotient (`R`). Together they
stay within `8 · 2⁻⁵³` of `s / n` (the sum of the three, with room for their
products). All in units of `u = 2¹⁰⁷⁴`. -/
theorem rel_combine {s A R : Int} {n m nb u : Nat} (hu : 0 < u)
    (hA : A.natAbs = m) (hAs : 2 ^ 53 * (A - s * u).natAbs ≤ s.natAbs * u)
    (hm : 2 ^ 53 * m ≤ (2 ^ 53 + 1) * (s.natAbs * u))
    (hb1 : 2 ^ 53 * nb ≤ (2 ^ 53 + 1) * (n * u)) (hb2 : (2 ^ 53 - 1) * (n * u) ≤ 2 ^ 53 * nb)
    (hR : 2 ^ 53 * ((nb : Int) * R - A * u).natAbs ≤ m * u) :
    2 ^ 53 * ((n : Int) * R - s * u).natAbs ≤ 8 * (s * u).natAbs := by
  -- The error times `u` splits into the three roundings' errors.
  have hsplit : ((n : Int) * R - s * u) * u =
      ((nb : Int) * R - A * u) + ((n * u : Nat) - (nb : Int)) * R + (A - s * u) * u := by
    simp only [Int.sub_mul, Int.natCast_mul, Int.mul_assoc, Int.mul_comm (u : Int) R]
    omega
  generalize hX1 : ((nb : Int) * R - A * u).natAbs = X1 at hR
  generalize hr : R.natAbs = r
  generalize hQ : s.natAbs * u = Q at hm hAs
  -- The count's error, times `|R|`.
  have hD2 : 2 ^ 53 * (((n * u : Nat) : Int) - nb).natAbs ≤ n * u := by omega
  have hT2 : 2 ^ 53 * ((((n * u : Nat) : Int) - nb) * R).natAbs ≤ n * u * r := by
    rw [Int.natAbs_mul, hr, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right r hD2
  -- `n · u · |R| ≤ 2 · |s| · u · u`: the quotient is at most about the mean.
  have hZ : nb * r ≤ m * u + X1 := by
    have h := Int.natAbs_add_le ((nb : Int) * R - A * u) (A * u)
    rw [Int.sub_add_cancel, Int.natAbs_mul, Int.natAbs_mul, hr, hA] at h
    simp only [hX1, Int.natAbs_natCast] at h; omega
  have he : (2 ^ 53 - 1) * (n * u * r) ≤ 2 ^ 53 * (nb * r) := by
    have h := Nat.mul_le_mul_right r hb2
    rw [Nat.mul_assoc, Nat.mul_assoc (2 ^ 53)] at h; exact h
  have hf : 2 ^ 53 * (m * u) ≤ (2 ^ 53 + 1) * (Q * u) := by
    have h := Nat.mul_le_mul_right u hm
    rw [Nat.mul_assoc, Nat.mul_assoc (2 ^ 53 + 1)] at h; exact h
  generalize n * u * r = Y at hT2 he
  generalize nb * r = Z at hZ he
  generalize m * u = MU at hR hZ hf
  generalize hW : Q * u = W at hf
  have hY : Y ≤ 2 * W := by omega
  -- The sum's error, times `u`.
  have hT3 : 2 ^ 53 * ((A - s * u) * u).natAbs ≤ W := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, ← Nat.mul_assoc, ← hW]
    exact Nat.mul_le_mul_right u hAs
  -- Together, `2⁵³ · |n R − s u| · u ≤ 5 · |s| u · u`.
  have htri := Int.natAbs_add_le (((nb : Int) * R - A * u) + (((n * u : Nat) : Int) - nb) * R)
    ((A - s * u) * u)
  have htri2 := Int.natAbs_add_le ((nb : Int) * R - A * u) ((((n * u : Nat) : Int) - nb) * R)
  rw [← hsplit, Int.natAbs_mul, Int.natAbs_natCast] at htri
  rw [hX1] at htri2
  have hsu : (s * u).natAbs = s.natAbs * u := by rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [hsu, hQ]
  generalize ((n : Int) * R - s * u).natAbs = E at htri
  generalize ((((n * u : Nat) : Int) - nb) * R).natAbs = T2 at hT2 htri2
  generalize ((A - s * u) * u).natAbs = T3 at hT3 htri
  have h5 : 2 ^ 53 * (E * u) ≤ 5 * (Q * u) := by
    rw [hW]; omega
  have h8 : 2 ^ 53 * E * u ≤ 8 * Q * u := by
    rw [Nat.mul_assoc, Nat.mul_assoc 8]; omega
  exact Nat.le_of_mul_le_mul_right h8 hu

theorem scaled_signedCode (neg : Bool) (m : Nat) :
    scaled (FloatFormat.signedCode neg m) = if neg then -(m : Int) else m := by
  unfold FloatFormat.signedCode scaled
  by_cases h0 : m = 0
  · subst h0; cases neg <;> rfl
  · cases neg <;> simp only [h0, ite_false, Bool.false_eq_true, ite_true] <;> split <;> omega

/-- `|x − y| ≤ y / k` from `x` within `[(1 − 1/k) y, (1 + 1/k) y]`. -/
theorem natAbs_sub_le_of {x y k : Nat} (h1 : k * x ≤ (k + 1) * y) (h2 : (k - 1) * y ≤ k * x) :
    k * ((x : Int) - y).natAbs ≤ y := by
  rcases Nat.le_total x y with h | h
  · rw [show (x : Int) - y = -((y - x : Nat) : Int) by omega, Int.natAbs_neg, Int.natAbs_natCast,
      Nat.mul_sub]
    have : (k - 1) * y = k * y - y := by rw [Nat.sub_mul, Nat.one_mul]
    omega
  · rw [show (x : Int) - y = ((x - y : Nat) : Int) by omega, Int.natAbs_natCast, Nat.mul_sub]
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- A finite rounded quotient is a double's code. -/
theorem isDouble_ofExactDiv {v : Int} {n : Nat} (hf : IsFin (ofExactDiv v n)) :
    IsDouble (ofExactDiv v n) := by
  have := posInf_eq; have := negInf_eq
  refine ⟨roundMagDiv v.natAbs n, ?_, ?_⟩
  · apply Classical.byContradiction; intro hlt
    unfold IsFin ofExactDiv posCode at hf
    simp only [show maxMag < roundMagDiv v.natAbs n by omega, ↓reduceIte] at hf
    split at hf <;> omega
  · unfold ofExactDiv; split
    · right; rfl
    · left; rfl

/-- `s · u` as `±(|s| · u)`. -/
theorem mul_natAbs_sign (s : Int) (u : Nat) :
    s * u = if s < 0 then -((s.natAbs * u : Nat) : Int) else ((s.natAbs * u : Nat) : Int) := by
  split
  · rw [show s = -(s.natAbs : Int) by omega, Int.neg_mul, Int.natAbs_neg, Int.natAbs_natCast]; push_cast; rfl
  · rw [show s = (s.natAbs : Int) by omega, Int.natAbs_natCast]; push_cast; rfl

/-- Past the first range, the model's mean is within `8 · 2⁻⁵³` of `s / n`:
the sum and the count each convert within `2⁻⁵³` (`ofInt_rel`), and the
division rounds within it (`ofExactDiv_err`). A `BIGINT` sum of fewer than
`2⁶⁴` values is below `2¹²⁷`. -/
theorem fdiv_withinRel {s : Int} {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 64)
    (hs : s.natAbs ≤ n * 2 ^ 63) : WithinRel 8 (s * unitK) n (fdiv (ofInt s) (ofInt n)) := by
  have hU : 2 ^ 1074 = unitK := rfl
  have hU1 : 2 ^ 1074 ≤ unitK := Nat.le_refl _
  have hU2 : unitK ≤ 2 ^ 1074 := Nat.le_refl _
  obtain ⟨Nb, hbN, hN1, hN2⟩ := ofInt_rel (i := n) (by omega) (by simp; omega)
  simp only [Int.natAbs_natCast, show decide ((n : Int) < 0) = false by simp, hU] at hbN hN1 hN2
  have hfb : IsFin (ofInt n) := ofInt_bounds n
  have hsb : scaled (ofInt n) = Nb := by rw [hbN, scaled_signedCode]; rfl
  have hnU : unitK ≤ n * unitK := Nat.le_mul_of_pos_left _ hn0
  have hsb0 : 0 < scaled (ofInt n) := by rw [hsb]; omega
  by_cases h0 : s = 0
  · subst h0
    rw [show ofInt 0 = 0 by rw [ofInt_exact (by decide)]; rfl, fdiv_zero_left hfb hsb0]
    exact ⟨⟨0, Nat.zero_le _, Or.inl rfl⟩, by simp [scaled]⟩
  obtain ⟨M, haM, hM1, hM2⟩ := ofInt_rel h0 (by omega)
  rw [hU] at hM1 hM2
  have hfa : IsFin (ofInt s) := ofInt_bounds s
  have hA : scaled (ofInt s) = if decide (s < 0) then -(M : Int) else M := by
    rw [haM, scaled_signedCode]
  have hAabs : (scaled (ofInt s)).natAbs = M := by rw [hA]; split <;> simp
  -- Products with `unitK`, kept as atoms.
  have hSU : unitK ≤ s.natAbs * unitK := Nat.le_mul_of_pos_left _ (by omega)
  have hSU2 : s.natAbs * unitK ≤ 2 ^ 127 * unitK := Nat.mul_le_mul_right _ (by omega)
  have hnU2 : n * unitK ≤ 2 ^ 64 * unitK := Nat.mul_le_mul_right _ (by omega)
  have hMlo : 2 ^ 1000 ≤ M := by omega
  have hMhi : M ≤ 2 ^ 2096 := by omega
  have hMU : 2 ^ 1000 * unitK ≤ M * unitK := Nat.mul_le_mul_right _ hMlo
  have hMU2 : M * unitK ≤ 2 ^ 2096 * unitK := Nat.mul_le_mul_right _ hMhi
  have hAs : 2 ^ 53 * (scaled (ofInt s) - s * unitK).natAbs ≤ s.natAbs * unitK := by
    have h := natAbs_sub_le_of (x := M) (y := s.natAbs * unitK) (k := 2 ^ 53) hM1 hM2
    rw [hA, mul_natAbs_sign s unitK]
    by_cases hneg : s < 0
    · simp only [hneg, decide_true, ite_true]
      rw [show -(M : Int) - -((s.natAbs * unitK : Nat) : Int) =
        -((M : Int) - ((s.natAbs * unitK : Nat) : Int)) by omega, Int.natAbs_neg]
      exact h
    · simp only [hneg, decide_false, Bool.false_eq_true, ite_false]
      exact h
  have hnat : (scaled (ofInt n)).natAbs = Nb := by rw [hsb]; rfl
  have hv : (scaled (ofInt s) * unitK).natAbs = M * unitK := by
    rw [Int.natAbs_mul, hAabs, Int.natAbs_natCast]
  have hfin : IsFin (ofExactDiv (scaled (ofInt s) * unitK) Nb) := by
    apply ofExactDiv_fin (by omega)
    rw [hv]
    have : 2 ^ 2096 * unitK ≤ Nb * 2 ^ 2097 := by omega
    omega
  have hne : ofExactDiv (scaled (ofInt s) * unitK) Nb ≠ 0 := by
    rw [ofExactDiv_eq_signedMag]
    exact signedMag_ne_zero _ (roundMagDiv_pos (by omega) (by rw [hv]; omega))
  rw [fdiv_eq_of_ne_zero hfa hfb hsb0 (by rw [hnat]; exact hne), hnat]
  refine ⟨isDouble_ofExactDiv hfin, ?_⟩
  have herr := ofExactDiv_err (v := scaled (ofInt s) * unitK) (n := Nb) (by omega) hfin
  rw [hv, Nat.max_eq_left (by omega : Nb * 2 ^ 52 ≤ M * unitK)] at herr
  exact rel_combine unitK_pos hAabs hAs (by omega) hN1 hN2 herr

end FloatCode

end Substrait

namespace Substrait

open FloatCode

open scoped Substrait.DuckDB

set_option exponentiation.threshold 2200

/-- What DuckDB's aggregate may give for its argument's values on a group's
rows: for `avg` of integers under DuckDB's semantics, the set of
`duckdb-avg-int` (one of the two doubles around the exact mean when the sum
and the count are at most `2⁵³`, a double within `8 · 2⁻⁵³` of it
otherwise); everywhere else the model's value. -/
def DuckAgg.Allowed : Semantics → DuckAgg → List Value → Value → Prop
  | .duckdb, .avgBigint, vs, r =>
    match vs.filter (· != .null) with
    | [] => r = .null
    | xs => ∃ c, r = .float c ∧
        if (intSum xs).natAbs ≤ 2 ^ 53 ∧ xs.length ≤ 2 ^ 53
        then Around (intSum xs * unitK) xs.length c
        else WithinRel 8 (intSum xs * unitK) xs.length c
  | s, g, vs, r => r = DuckAgg.eval s g vs

/-- A sum of integers each at most `B` in magnitude. -/
theorem intSum_natAbs_le {xs : List Value} {B : Nat} (h : ∀ v ∈ xs, ∃ i, v = .int i ∧ i.natAbs ≤ B) :
    (intSum xs).natAbs ≤ xs.length * B := by
  induction xs with
  | nil => simp [intSum]
  | cons v vs ih =>
    obtain ⟨i, rfl, hi⟩ := h v (List.mem_cons_self ..)
    have := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    have := Int.natAbs_add_le i (intSum vs)
    simp only [intSum, List.length_cons, Nat.succ_mul]
    omega

/-- The non-NULL values of a `BIGINT` column are integers. -/
theorem bigint_filter {vs : List Value} (hv : ∀ v ∈ vs, DuckType.bigint.Has v)
    (h64 : ∀ v ∈ vs, ∀ i, v = .int i → i.natAbs ≤ 2 ^ 63) :
    ∀ v ∈ vs.filter (· != .null), ∃ i, v = .int i ∧ i.natAbs ≤ 2 ^ 63 := by
  intro v hm
  rw [List.mem_filter] at hm
  obtain ⟨hm, hn⟩ := hm
  have := hv v hm
  cases v with
  | int i => exact ⟨i, rfl, h64 _ hm i rfl⟩
  | null => simp at hn
  | _ => simp [DuckType.Has] at this

/-- The model's value is one of the values DuckDB may give, for `BIGINT`
values (at most `2⁶³` in magnitude) and fewer than `2⁶⁴` of them (DuckDB's
count is a `uint64_t`). -/
theorem DuckAgg.eval_allowed (s : Semantics) (g : DuckAgg) {vs : List Value}
    (hv : ∀ v ∈ vs, g.arg.Has v) (h64 : ∀ v ∈ vs, ∀ i, v = .int i → i.natAbs ≤ 2 ^ 63)
    (hn : vs.length < 2 ^ 64) : DuckAgg.Allowed s g vs (DuckAgg.eval s g vs) := by
  cases s <;> cases g <;> try rfl
  have hxs := bigint_filter hv h64
  have hlen : (vs.filter (· != .null)).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hn
  simp only [DuckAgg.Allowed, DuckAgg.eval]
  generalize vs.filter (· != .null) = xs at hxs hlen
  match xs, hxs, hlen with
  | [], _, _ => rfl
  | x :: xs, hxs, hlen =>
    refine ⟨_, rfl, ?_⟩
    have hsum := intSum_natAbs_le hxs
    split
    · rename_i h
      rw [fdiv_exact_eq h.1 (by simp) h.2]
      exact around_ofExactDiv _ (by simp)
    · exact fdiv_withinRel (by simp) hlen hsum

/-- Means of small integers stay exact: when the mean is an integer, DuckDB's
set is the model's one value. -/
theorem DuckAgg.avgBigint_exact {vs xs : List Value} (hxs : vs.filter (· != .null) = xs)
    (hne : xs ≠ []) (hs : (intSum xs).natAbs ≤ 2 ^ 53) (hn : xs.length ≤ 2 ^ 53)
    (hq : (xs.length : Int) ∣ intSum xs) (r : Value) :
    DuckAgg.Allowed .duckdb .avgBigint vs r ↔ r = DuckAgg.eval .duckdb .avgBigint vs := by
  simp only [DuckAgg.Allowed, DuckAgg.eval, hxs]
  match xs, hne, hs, hn, hq with
  | x :: xs, _, hs, hn, hq =>
    have hn0 : 0 < (x :: xs).length := by simp
    obtain ⟨q, hq⟩ := hq
    have hqa : q.natAbs ≤ 2 ^ 53 := by
      have : (intSum (x :: xs)).natAbs = (x :: xs).length * q.natAbs := by
        rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
      have : q.natAbs ≤ (x :: xs).length * q.natAbs := Nat.le_mul_of_pos_left _ hn0
      omega
    have hV : (intSum (x :: xs) * unitK).natAbs = (x :: xs).length * (q.natAbs * unitK) := by
      rw [hq, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast, Nat.mul_assoc]
    have heq := aroundHi_eq_lo_of_int (x := q.natAbs) hn0 hqa
    rw [← hV] at heq
    simp only [hs, hn, and_self, ite_true]
    rw [fdiv_exact_eq hs hn0 hn, ofExactDiv_eq_signedMag]
    have hround : roundMagDiv (intSum (x :: xs) * unitK).natAbs (x :: xs).length =
        aroundLo (intSum (x :: xs) * unitK).natAbs (x :: xs).length := by
      rcases roundMagDiv_around _ _ hn0 with h | h <;> rw [h]; exact heq
    rw [hround]
    unfold Around
    rw [heq]
    constructor
    · rintro ⟨c, rfl, h | h⟩ <;> rw [h]
    · intro h; exact ⟨_, h, Or.inl rfl⟩

/-- How close a member of DuckDB's set is to the model's value `p`: for `avg`
of integers, within one unit in the last place of the mean in the first
range, and within `16 · 2⁻⁵³` of it, relatively, in the second; the same
value everywhere else. -/
def DuckAgg.Near : DuckAgg → List Value → Value → Value → Prop
  | .avgBigint, vs, p, r =>
    match vs.filter (· != .null) with
    | [] => p = .null ∧ r = .null
    | xs => ∃ a b, p = .float a ∧ r = .float b ∧
        if (intSum xs).natAbs ≤ 2 ^ 53 ∧ xs.length ≤ 2 ^ 53
        then (scaled b - scaled a).natAbs ≤ ulpDiv (intSum xs * unitK) xs.length
        else 2 ^ 53 * ((xs.length : Int) * (scaled b - scaled a)).natAbs ≤
          16 * (intSum xs * unitK).natAbs
  | _, _, p, r => r = p

/-- Every member of DuckDB's set is near the model's value. -/
theorem DuckAgg.avgBigint_near {vs : List Value} (hv : ∀ v ∈ vs, DuckType.bigint.Has v)
    (h64 : ∀ v ∈ vs, ∀ i, v = .int i → i.natAbs ≤ 2 ^ 63) (hn : vs.length < 2 ^ 64) {r : Value}
    (hr : DuckAgg.Allowed .duckdb .avgBigint vs r) :
    DuckAgg.Near .avgBigint vs (DuckAgg.eval .duckdb .avgBigint vs) r := by
  have hm := DuckAgg.eval_allowed .duckdb .avgBigint hv h64 hn
  have hxs := bigint_filter hv h64
  have hlen : (vs.filter (· != .null)).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hn
  simp only [DuckAgg.Allowed, DuckAgg.Near, DuckAgg.eval] at hr hm ⊢
  generalize vs.filter (· != .null) = xs at hxs hlen hr hm ⊢
  cases xs with
  | nil => exact ⟨rfl, hr⟩
  | cons x xs =>
    obtain ⟨b, rfl, hb⟩ := hr
    obtain ⟨a, ha, hma⟩ := hm
    refine ⟨_, b, rfl, rfl, ?_⟩
    cases ha
    have hn0 : 0 < (x :: xs).length := by simp
    have hsum := intSum_natAbs_le hxs
    split
    · rename_i h
      simp only [h, and_self, ite_true] at hb hma
      have hV : (intSum (x :: xs) * unitK).natAbs ≤ (x :: xs).length * 2 ^ 1127 := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        have := Nat.mul_le_mul_right unitK h.1
        rw [show unitK = 2 ^ 1074 from rfl, ← Nat.pow_add] at this
        exact Nat.le_trans this (Nat.le_mul_of_pos_left _ hn0)
      obtain ⟨mb, hmb, -, hsb⟩ := around_scaled hV hb
      obtain ⟨ma, hma', -, hsa⟩ := around_scaled hV hma
      have hstep := aroundHi_sub_le (intSum (x :: xs) * unitK).natAbs (x :: xs).length
      have hle := aroundLo_le_hi (intSum (x :: xs) * unitK).natAbs (x :: xs).length
      unfold ulpDiv
      rw [hsb, hsa]
      split <;> rcases hmb with rfl | rfl <;> rcases hma' with rfl | rfl <;> omega
    · rename_i h
      simp only [h, ite_false] at hb hma
      obtain ⟨-, hb⟩ := hb
      obtain ⟨-, ha⟩ := hma
      have := Int.natAbs_add_le (((x :: xs).length : Int) * scaled b - intSum (x :: xs) * unitK)
        (-(((x :: xs).length : Int) * scaled (fdiv (ofInt (intSum (x :: xs))) (ofInt (x :: xs).length)) -
          intSum (x :: xs) * unitK))
      rw [Int.natAbs_neg] at this
      rw [Int.mul_sub]
      have heq : ((x :: xs).length : Int) * scaled b -
          ((x :: xs).length : Int) * scaled (fdiv (ofInt (intSum (x :: xs))) (ofInt (x :: xs).length)) =
          (((x :: xs).length : Int) * scaled b - intSum (x :: xs) * unitK) +
          -(((x :: xs).length : Int) * scaled (fdiv (ofInt (intSum (x :: xs))) (ofInt (x :: xs).length)) -
            intSum (x :: xs) * unitK) := by omega
      rw [heq]
      omega

/-- The arithmetic of `avgBigint_nearRel`: a member `n · D` within `16 · 2⁻⁵³`
of `Q = |V|`, the plan's `A = |p|` within `8 · 2⁻⁵³` of it (`E`), so `D` is
within `17 · 2⁻⁵³` of `A`. -/
theorem nearRel_arith {n D A E Q : Nat} (hn : 0 < n) (h1 : 2 ^ 53 * (n * D) ≤ 16 * Q)
    (h2 : 2 ^ 53 * E ≤ 8 * Q) (h3 : Q ≤ n * A + E) : 2 ^ 53 * D ≤ DuckAgg.nearRel * A := by
  have h4 : 16 * Q ≤ 17 * (n * A) := by omega
  have : n * (2 ^ 53 * D) ≤ n * (17 * A) := by
    rw [Nat.mul_left_comm, Nat.mul_left_comm n 17]; omega
  exact Nat.le_of_mul_le_mul_left this hn

/-- **The mark's band**: every value DuckDB may give for `avg(BIGINT)` is
within `nearRel · 2⁻⁵³` of the plan's value, relative to the plan's value:
the bound `Epsilon.exprEps` reads off `.un (.approx DuckAgg.nearRel)` (D52). -/
theorem DuckAgg.avgBigint_nearRel {vs : List Value} (hv : ∀ v ∈ vs, DuckType.bigint.Has v)
    (h64 : ∀ v ∈ vs, ∀ i, v = .int i → i.natAbs ≤ 2 ^ 63) (hn : vs.length < 2 ^ 64) {r : Value}
    (hr : DuckAgg.Allowed .duckdb .avgBigint vs r) :
    (DuckAgg.eval .duckdb .avgBigint vs = .null ∧ r = .null) ∨
      ∃ a b, DuckAgg.eval .duckdb .avgBigint vs = .float a ∧ r = .float b ∧
        2 ^ 53 * (scaled b - scaled a).natAbs ≤ DuckAgg.nearRel * (scaled a).natAbs := by
  have hN := DuckAgg.avgBigint_near hv h64 hn hr
  have hm := DuckAgg.eval_allowed .duckdb .avgBigint hv h64 hn
  have hxs := bigint_filter hv h64
  have hlen : (vs.filter (· != .null)).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hn
  simp only [DuckAgg.Allowed, DuckAgg.Near, DuckAgg.eval] at hr hm hN ⊢
  generalize vs.filter (· != .null) = xs at hxs hlen hr hm hN ⊢
  cases xs with
  | nil => exact Or.inl ⟨rfl, hr⟩
  | cons x xs =>
    right
    obtain ⟨a, b, ha, hb, hnear⟩ := hN
    cases ha
    refine ⟨_, b, rfl, hb, ?_⟩
    obtain ⟨c, hc, hmc⟩ := hm
    cases hc
    obtain ⟨cb, hcb, hrb⟩ := hr
    rw [hb] at hcb; cases hcb
    have hn0 : 0 < (x :: xs).length := by simp
    generalize hS : intSum (x :: xs) = S at *
    generalize hL : (x :: xs).length = n at *
    have hU : 2 ^ 1074 = unitK := rfl
    have hV : (S * unitK).natAbs = S.natAbs * unitK := by rw [Int.natAbs_mul, Int.natAbs_natCast]
    generalize hA : fdiv (ofInt S) (ofInt n) = a at *
    -- `Q ≤ n · |p| + |n p − V|`.
    have h3 : (S * unitK).natAbs ≤ n * (scaled a).natAbs + ((n : Int) * scaled a - S * unitK).natAbs := by
      have := Int.natAbs_add_le ((n : Int) * scaled a) (-((n : Int) * scaled a - S * unitK))
      rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast,
        show (n : Int) * scaled a + -((n : Int) * scaled a - S * unitK) = S * unitK by omega] at this
      exact this
    split at hnear
    · rename_i h
      simp only [h, and_self, ite_true] at hmc hrb
      by_cases hs0 : S = 0
      · -- A zero sum: both are `+0.0`.
        subst hs0
        have h0 : ∀ m, m = aroundLo (0 * (unitK : Int)).natAbs n ∨ m = aroundHi (0 * (unitK : Int)).natAbs n →
            m = 0 := by
          rintro m (rfl | rfl) <;> simp [aroundLo, aroundHi]
        have hz : ∀ c, Around (0 * (unitK : Int)) n c → scaled c = 0 := by
          intro c hc
          rcases hc with rfl | rfl <;> simp [signedMag, aroundLo, aroundHi, posCode, scaled]
        rw [hz _ hrb, hz _ hmc]; simp
      have hQ : unitK ≤ (S * unitK).natAbs := by rw [hV]; exact Nat.le_mul_of_pos_left _ (by omega)
      have hU1 : 2 ^ 1074 ≤ unitK := Nat.le_of_eq hU
      -- The grid at the quotient is above the subnormals.
      have hg : 0 < gridExp (S * unitK).natAbs n := by
        apply Classical.byContradiction; intro hg0
        have hlt := lt_of_gridExp (S * unitK).natAbs n
        rw [show gridExp (S * unitK).natAbs n = 0 by omega] at hlt
        have : 2 ^ 1010 ≤ (S * unitK).natAbs / n := by
          apply (Nat.le_div_iff_mul_le hn0).mpr
          have : 2 ^ 1010 * n ≤ 2 ^ 1010 * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)
          rw [← Nat.pow_add] at this; omega
        have : 2 ^ 53 < 2 ^ 1010 := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hge := le_of_gridExp hg
      generalize hG : gridExp (S * unitK).natAbs n = g at hge hg
      have hP : 2 ^ (g + 52) = 2 ^ g * 2 ^ 52 := Nat.pow_add _ _ _
      have hnq : n * ((S * unitK).natAbs / n) ≤ (S * unitK).natAbs := Nat.mul_div_le _ _
      have hnP : n * 2 ^ (g + 52) ≤ n * ((S * unitK).natAbs / n) := Nat.mul_le_mul_left _ hge
      -- The plan's value rounds the quotient once: within half a grid step.
      have hfin : IsFin (ofExactDiv (S * unitK) n) := ofExactDiv_fin hn0 (by
        rw [hV]
        have : S.natAbs * unitK ≤ 2 ^ 127 * 2 ^ 1074 := by
          rw [← hU]; exact Nat.mul_le_mul_right _ (by omega)
        rw [← Nat.pow_add] at this
        have : 2 ^ (127 + 1074) ≤ 1 * 2 ^ 2097 := by
          rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
        have := Nat.mul_le_mul_right (2 ^ 2097) hn0
        omega)
      rw [← hA, fdiv_exact_eq h.1 hn0 h.2] at h3 hnear ⊢
      have hw := ofExactDiv_within hn0 hfin
      unfold ulpDiv at hw hnear
      rw [hG] at hw hnear
      rw [hP] at hnP
      have hD := Nat.mul_le_mul_left n hnear
      have e : 2 ^ 52 * (n * 2 ^ g) = n * (2 ^ g * 2 ^ 52) := by
        rw [Nat.mul_comm (2 ^ g) (2 ^ 52), Nat.mul_left_comm]
      have hgrid : 2 ^ 52 * (n * 2 ^ g) ≤ (S * unitK).natAbs := by omega
      generalize (scaled b - scaled (ofExactDiv (S * unitK) n)).natAbs = D at hD ⊢
      generalize n * 2 ^ g = NP at hD hw hgrid
      have h1 := Nat.mul_le_mul_left (2 ^ 53) hD
      exact nearRel_arith hn0 (Nat.le_trans h1 (show 2 ^ 53 * NP ≤ 16 * (S * unitK).natAbs by omega))
        (by omega) h3
    · rename_i h
      simp only [h, ite_false] at hmc
      obtain ⟨-, h2⟩ := hmc
      rw [Int.natAbs_mul, Int.natAbs_natCast] at hnear
      exact nearRel_arith hn0 hnear h2 h3

/-- Every lifted aggregate under DuckDB's semantics: the model's value, which
the plan gives (`AggEntry.agree`), is one DuckDB may give, and every value
DuckDB may give is near it (`DuckAgg.Near`). The generated entries need no
change. -/
theorem AggEntry.allowed_near {g : DuckAgg} (e : AggEntry .duckdb g) {vs : List Value}
    (hv : ∀ v ∈ vs, g.arg.Has v) (h64 : ∀ v ∈ vs, ∀ i, v = .int i → i.natAbs ≤ 2 ^ 63)
    (hn : vs.length < 2 ^ 64) :
    DuckAgg.Allowed .duckdb g vs (g.eval .duckdb vs) ∧
      ∀ r, DuckAgg.Allowed .duckdb g vs r →
        (e.finish.evalP Profile.reference (e.measures.map (·.eval (vs.map ([·]))))).Agree
          (.ok (g.eval .duckdb vs)) ∧ DuckAgg.Near g vs (g.eval .duckdb vs) r := by
  refine ⟨DuckAgg.eval_allowed .duckdb g hv h64 hn, fun r hr => ⟨e.agree vs hv, ?_⟩⟩
  cases g with
  | avgBigint => exact DuckAgg.avgBigint_near hv h64 hn hr
  | sumDouble | avgDouble => exact hr

end Substrait
