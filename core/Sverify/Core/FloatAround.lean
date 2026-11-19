import Sverify.Core.FloatArith

/-!
# The two doubles around a quotient (#1608 12b-2)

A quotient `V / n` of integers (in units of `2⁻¹⁰⁷⁴`) lies between two
doubles of its grid: rounded down (`aroundLo`) and up (`aroundHi`), the same
double when the quotient is one. `Around V n r` says that `r` is one of them.
Rounding to nearest gives one (`around_ofExactDiv`), and an engine whose
result is a set of such quotients (`DuckAgg.Allowed`'s first range) states its
values with it. A comparison of such a value with an integer decides as the
exact comparison does where the grid is fine enough (`Epsilon.intMeanCovered`).

Everything is integer arithmetic on codes: `Around` holds codes of doubles
only (`posCode`, one code per value, never `-0.0`).
-/

namespace Substrait.FloatCode

set_option exponentiation.threshold 2200

/-- The magnitude `a / n` rounded down to its grid (`gridExp`). -/
def aroundLo (a n : Nat) : Nat := a / (n * 2 ^ gridExp a n) * 2 ^ gridExp a n

/-- The magnitude `a / n` rounded up to its grid: `aroundLo` when that is
`a / n`. -/
def aroundHi (a n : Nat) : Nat :=
  (if a % (n * 2 ^ gridExp a n) = 0 then a / (n * 2 ^ gridExp a n)
   else a / (n * 2 ^ gridExp a n) + 1) * 2 ^ gridExp a n

/-- The code of magnitude `m`, negative if `neg`: `0` for the magnitude `0`. -/
def signedMag (neg : Bool) (m : Nat) : Int := if neg then -posCode m else posCode m

/-- `r` is one of the two doubles around `V / n` (in units of `2⁻¹⁰⁷⁴`): the
quotient rounded down or up on its grid, the same double when the quotient
is one. -/
def Around (V : Int) (n : Nat) (r : Int) : Prop :=
  r = signedMag (decide (V < 0)) (aroundLo V.natAbs n) ∨
    r = signedMag (decide (V < 0)) (aroundHi V.natAbs n)

theorem ofExactDiv_eq_signedMag (v : Int) (n : Nat) :
    ofExactDiv v n = signedMag (decide (v < 0)) (roundMagDiv v.natAbs n) := by
  unfold ofExactDiv signedMag; by_cases h : v < 0 <;> simp [h]

/-- Rounding to nearest gives one of the two roundings on the grid. -/
theorem roundMagDiv_around (a n : Nat) (hn : 0 < n) :
    roundMagDiv a n = aroundLo a n ∨ roundMagDiv a n = aroundHi a n := by
  unfold roundMagDiv aroundLo aroundHi
  have hd : 0 < n * 2 ^ gridExp a n := Nat.mul_pos hn (Nat.two_pow_pos _)
  generalize n * 2 ^ gridExp a n = d at hd ⊢
  generalize 2 ^ gridExp a n = P
  have h1 := rndDiv_ge a d
  have h2 := rndDiv_le a d
  have h0 : a % d = 0 → rndDiv a d = a / d := fun h => by unfold rndDiv; split <;> omega
  by_cases hm : a % d = 0
  · left; rw [h0 hm]
  · simp only [hm, ite_false]
    rcases Nat.lt_or_ge (a / d) (rndDiv a d) with h | h
    · right; rw [show rndDiv a d = a / d + 1 by omega]
    · left; rw [show rndDiv a d = a / d by omega]

/-- The two roundings are one grid step apart at most. -/
theorem aroundHi_sub_le (a n : Nat) : aroundHi a n ≤ aroundLo a n + 2 ^ gridExp a n := by
  unfold aroundHi aroundLo
  split
  · exact Nat.le_add_right _ _
  · rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_refl _

theorem aroundLo_le_hi (a n : Nat) : aroundLo a n ≤ aroundHi a n := by
  unfold aroundHi aroundLo
  split
  · exact Nat.le_refl _
  · exact Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- The nearest double to `V / n` is one of the two around it. -/
theorem around_ofExactDiv (V : Int) {n : Nat} (hn : 0 < n) : Around V n (ofExactDiv V n) := by
  rw [ofExactDiv_eq_signedMag]
  rcases roundMagDiv_around V.natAbs n hn with h | h
  · left; rw [h]
  · right; rw [h]

/-- An integer mean of at most `2⁵³` is on its own grid: rounding it down or
up gives it. -/
theorem aroundHi_eq_lo_of_int {x n : Nat} (hn : 0 < n) (hx : x ≤ 2 ^ 53) :
    aroundHi (n * (x * unitK)) n = aroundLo (n * (x * unitK)) n := by
  have hdiv : n * (x * unitK) / n = x * unitK := Nat.mul_div_cancel_left _ hn
  have hg : gridExp (n * (x * unitK)) n = (x * unitK).log2 - 52 := by unfold gridExp; rw [hdiv]
  -- `2 ^ g` divides `x · 2¹⁰⁷⁴`.
  have hdvd : 2 ^ ((x * unitK).log2 - 52) ∣ x * unitK := by
    by_cases hx0 : x = 0
    · subst hx0; simp
    have hU : unitK = 2 ^ 1074 := rfl
    have hpos : x * unitK ≠ 0 := Nat.mul_ne_zero hx0 (by rw [hU]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    have hlt : x * unitK < 2 ^ 1128 := by
      have h1 : x * unitK ≤ 2 ^ 53 * 2 ^ 1074 := by rw [hU]; exact Nat.mul_le_mul_right _ hx
      have h2 : 2 ^ 53 * 2 ^ 1074 < 2 ^ 1128 := by
        rw [← Nat.pow_add]; exact Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hlog : (x * unitK).log2 < 1128 := (Nat.log2_lt hpos).mpr hlt
    by_cases hg1 : (x * unitK).log2 - 52 ≤ 1074
    · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hg1) (by rw [hU]; exact Nat.dvd_mul_left _ _)
    · have hl : (x * unitK).log2 = 1127 := by omega
      have hle := Nat.log2_self_le hpos
      rw [hl] at hle
      have hx53 : 2 ^ 53 ≤ x := by
        have : 2 ^ 53 * 2 ^ 1074 ≤ x * 2 ^ 1074 := by rw [← Nat.pow_add, ← hU]; exact hle
        exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
      have : x = 2 ^ 53 := by omega
      subst this
      rw [hl, hU, ← Nat.pow_add]
      exact Nat.pow_dvd_pow 2 (by omega)
  unfold aroundHi aroundLo
  rw [hg, Nat.mul_mod_mul_left, Nat.mod_eq_zero_of_dvd hdvd, Nat.mul_zero]
  simp

/-- The doubles around `V / n` are within one unit in the last place of it,
and at most `2⁵⁴` units above `2¹⁰⁷⁴ · |V / n|`. -/
theorem around_scaled {V : Int} {n : Nat} (hV : V.natAbs ≤ n * 2 ^ 1127) {r : Int}
    (hr : Around V n r) :
    ∃ m, (m = aroundLo V.natAbs n ∨ m = aroundHi V.natAbs n) ∧ m ≤ maxMag ∧
      scaled r = if V < 0 then -(m : Int) else m := by
  have hP := Nat.two_pow_pos (gridExp V.natAbs n)
  have hlo : aroundLo V.natAbs n ≤ V.natAbs / n := by
    unfold aroundLo; rw [← Nat.div_div_eq_div_mul]; exact Nat.div_mul_le_self _ _
  have hq : V.natAbs / n ≤ 2 ^ 1127 := Nat.div_le_of_le_mul hV
  have hstep : 2 ^ gridExp V.natAbs n ≤ 2 ^ 1127 := by
    by_cases hg : gridExp V.natAbs n = 0
    · rw [hg]; exact Nat.one_le_two_pow
    · have := le_of_gridExp (a := V.natAbs) (n := n) (by omega)
      have : 2 ^ gridExp V.natAbs n ≤ 2 ^ (gridExp V.natAbs n + 52) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  have hhi := aroundHi_sub_le V.natAbs n
  have hmax : 2 ^ 1129 ≤ maxMag := pow_le_maxMag (by omega)
  have h28 : 2 ^ 1127 + 2 ^ 1127 ≤ 2 ^ 1129 := by
    rw [show 2 ^ 1129 = 2 ^ 1127 * 4 by rw [show 1129 = 1127 + 2 from rfl, Nat.pow_add]]; omega
  have hm : ∀ m, (m = aroundLo V.natAbs n ∨ m = aroundHi V.natAbs n) → m ≤ maxMag := by
    rintro m (rfl | rfl) <;> omega
  unfold Around signedMag at hr
  rcases hr with rfl | rfl
  · refine ⟨_, Or.inl rfl, hm _ (Or.inl rfl), ?_⟩
    by_cases h : V < 0 <;> simp [h, scaled_neg_posCode (hm _ (Or.inl rfl)), scaled_posCode (hm _ (Or.inl rfl))]
  · refine ⟨_, Or.inr rfl, hm _ (Or.inr rfl), ?_⟩
    by_cases h : V < 0 <;> simp [h, scaled_neg_posCode (hm _ (Or.inr rfl)), scaled_posCode (hm _ (Or.inr rfl))]

instance (V : Int) (n : Nat) (r : Int) : Decidable (Around V n r) := by
  unfold Around; infer_instance

-- A zero sum: `+0.0` only, never `-0.0` nor the other codes of zero (1, 2, -1, -2).
#guard decide (Around 0 3 0)
#guard [negZero, 1, 2, -1, -2].all fun c => !decide (Around 0 3 c)
-- An integer mean: one double. The fact's mean of 378693551270 over 88085 rows:
-- the two doubles around it, the model's among them.
#guard aroundLo (6 * unitK) 3 = aroundHi (6 * unitK) 3
#guard aroundLo (378693551270 * unitK) 88085 + 2 ^ gridExp (378693551270 * unitK) 88085 =
  aroundHi (378693551270 * unitK) 88085
#guard decide (Around (378693551270 * unitK) 88085 (ofExactDiv (378693551270 * unitK) 88085))


/-- A member of `Around` is within one grid step of the quotient, strictly,
and is the quotient where that is on the grid: `|r · n − V| < 2^g · n`. -/
theorem around_err {V : Int} {n : Nat} (hn : 0 < n) (hV : V.natAbs ≤ n * 2 ^ 1127) {r : Int}
    (hr : Around V n r) :
    ((scaled r * n - V).natAbs < 2 ^ gridExp V.natAbs n * n) ∧
      (V.natAbs % (2 ^ gridExp V.natAbs n * n) = 0 → scaled r * n = V) := by
  obtain ⟨m, hm, -, hs⟩ := around_scaled hV hr
  generalize hQ : V.natAbs = Q at hm hs ⊢
  generalize hg : gridExp Q n = g at hm ⊢
  have hP := Nat.two_pow_pos g
  have hd : 0 < 2 ^ g * n := Nat.mul_pos hP hn
  have hlo : aroundLo Q n * n = Q / (2 ^ g * n) * (2 ^ g * n) := by
    unfold aroundLo; rw [hg, Nat.mul_comm n (2 ^ g), Nat.mul_assoc]
  have hhi : aroundHi Q n * n =
      if Q % (2 ^ g * n) = 0 then aroundLo Q n * n else aroundLo Q n * n + 2 ^ g * n := by
    unfold aroundHi aroundLo; rw [hg, Nat.mul_comm n (2 ^ g)]
    split
    · rfl
    · rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.mul_assoc]
  have hle := Nat.div_mul_le_self Q (2 ^ g * n)
  have hlt := Nat.lt_div_mul_add (a := Q) hd
  have hex : Q % (2 ^ g * n) = 0 → Q / (2 ^ g * n) * (2 ^ g * n) = Q :=
    fun h => Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  have hdm := Nat.div_add_mod' Q (2 ^ g * n)
  have hmn : m * n < Q + 2 ^ g * n ∧ Q < m * n + 2 ^ g * n ∧ (Q % (2 ^ g * n) = 0 → m * n = Q) := by
    rcases hm with rfl | rfl
    · rw [hlo]; exact ⟨by omega, by omega, hex⟩
    · rw [hhi]; split
      · rename_i h; rw [hlo]; exact ⟨by omega, by omega, hex⟩
      · rename_i h
        have : 0 < Q % (2 ^ g * n) := Nat.pos_of_ne_zero h
        rw [hlo]; exact ⟨by omega, by omega, fun h' => absurd h' h⟩
  generalize hmnE : m * n = mn at hmn
  generalize 2 ^ g * n = D at hmn hd hdm ⊢
  obtain ⟨h1, h2, h3⟩ := hmn
  have hmn' : (m : Int) * n = (mn : Int) := by rw [← Int.natCast_mul, hmnE]
  have hVQ : (V < 0 → V = -(Q : Int)) ∧ (¬ V < 0 → V = (Q : Int)) := ⟨fun _ => by omega, fun _ => by omega⟩
  rw [hs]
  constructor
  · split
    · rename_i hneg
      rw [Int.neg_mul, hmn']
      have := hVQ.1 hneg
      rcases Int.natAbs_eq (-(mn : Int) - V) with h4 | h4 <;> omega
    · rename_i hneg
      rw [hmn']
      have := hVQ.2 hneg
      rcases Int.natAbs_eq ((mn : Int) - V) with h4 | h4 <;> omega
  · intro h0
    have := h3 h0
    split
    · rename_i hneg; rw [Int.neg_mul, hmn']; have := hVQ.1 hneg; omega
    · rename_i hneg; rw [hmn']; have := hVQ.2 hneg; omega

set_option exponentiation.threshold 2200 in
/-- **A mean of integers compared with an integer** (#1608 12b-2): where the
values are at most `M` in magnitude over `n ≤ N` rows and `N · max M 1 ≤ 2⁵²`,
every double around the mean `s / n` compares with the double of any integer
`k` as the exact mean does. The grid at the mean is finer than `1 / N`, so no
double around a mean that is not `k` reaches `k`, and a mean that is `k` is on
the grid. -/
theorem around_cmp_int {s : Int} {n M N : Nat} (hn : 0 < n) (hnN : n ≤ N) (hsM : s.natAbs ≤ n * M)
    (hNM : N * max M 1 ≤ 2 ^ 52) {r : Int} (hr : Around (s * unitK) n r) (k : Int) :
    (scaled (ofInt k) < scaled r ↔ k * n < s) ∧ (scaled r < scaled (ofInt k) ↔ s < k * n) ∧
      (scaled r = scaled (ofInt k) ↔ s = k * n) := by
  have hU : unitK = 2 ^ 1074 := rfl
  have hUpos := unitK_pos
  have hM1 : max M 1 ≤ N * max M 1 := Nat.le_mul_of_pos_left _ (by omega)
  have hM52 : M ≤ 2 ^ 52 := by omega
  have hMN : M * N ≤ 2 ^ 52 := by
    have := Nat.mul_le_mul_left N (Nat.le_max_left M 1); rw [Nat.mul_comm M N]; omega
  have hVabs : (s * unitK).natAbs = s.natAbs * unitK := by rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hsMU : s.natAbs * unitK ≤ n * M * unitK := Nat.mul_le_mul_right _ hsM
  have hV : (s * unitK).natAbs ≤ n * 2 ^ 1127 := by
    rw [hVabs]
    have h1 : n * M * unitK ≤ n * 2 ^ 52 * unitK := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM52)
    have h2 : n * 2 ^ 52 * unitK ≤ n * 2 ^ 1127 := by
      rw [Nat.mul_assoc, hU, ← Nat.pow_add]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  obtain ⟨herr, hex⟩ := around_err hn hV hr
  -- The grid step is below `1 / N`: `2^g · N ≤ 2¹⁰⁷⁴`.
  have hstep : 2 ^ gridExp (s * unitK).natAbs n * N ≤ unitK := by
    by_cases hg0 : gridExp (s * unitK).natAbs n = 0
    · rw [hg0, Nat.pow_zero, Nat.one_mul]
      have : 2 ^ 52 ≤ unitK := by rw [hU]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have : N ≤ N * max M 1 := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have hge := le_of_gridExp (a := (s * unitK).natAbs) (n := n) (by omega)
      have hq : (s * unitK).natAbs / n ≤ M * unitK :=
        Nat.div_le_of_le_mul (by rw [hVabs, ← Nat.mul_assoc]; exact hsMU)
      rw [Nat.pow_add] at hge
      generalize 2 ^ gridExp (s * unitK).natAbs n = P at hge ⊢
      have h1 : P * 2 ^ 52 * N ≤ M * unitK * N := Nat.mul_le_mul_right _ (Nat.le_trans hge hq)
      have h2 : M * unitK * N ≤ 2 ^ 52 * unitK := by
        rw [Nat.mul_right_comm]; exact Nat.mul_le_mul_right _ hMN
      have e : 2 ^ 52 * (P * N) = P * 2 ^ 52 * N := by rw [Nat.mul_left_comm, ← Nat.mul_assoc]
      have h3 : 2 ^ 52 * (P * N) ≤ 2 ^ 52 * unitK := by rw [e]; exact Nat.le_trans h1 h2
      exact Nat.le_of_mul_le_mul_left h3 (Nat.two_pow_pos _)
  generalize hg : gridExp (s * unitK).natAbs n = g at herr hex hstep
  have hgn : 2 ^ g * n ≤ unitK := Nat.le_trans (Nat.mul_le_mul_left _ hnN) hstep
  have hgU : 2 ^ g ≤ unitK := Nat.le_trans (Nat.le_mul_of_pos_right _ hn) hgn
  -- `r` against `k · 2¹⁰⁷⁴`, by the sign of `s − k n`.
  generalize hR : scaled r = R at herr hex ⊢
  have hkn : (k * n : Int) * unitK = (k * unitK) * n := by rw [Int.mul_right_comm]
  have hEU : ∀ E : Int, 1 ≤ E → (unitK : Int) ≤ E * unitK := fun E hE => by
    have := Int.mul_le_mul_of_nonneg_right hE (Int.natCast_nonneg unitK); simpa using this
  have herr' : R * n - s * unitK < ((2 ^ g * n : Nat) : Int) ∧ -((2 ^ g * n : Nat) : Int) < R * n - s * unitK := by
    rcases Int.natAbs_eq (R * n - s * unitK) with h | h <;> omega
  have hgn' : ((2 ^ g * n : Nat) : Int) ≤ unitK := by exact_mod_cast hgn
  have hpos : ∀ x y : Int, x * n < y * n → x < y := fun x y h =>
    Int.lt_of_mul_lt_mul_right h (Int.natCast_nonneg n)
  have hgt : k * n < s → k * unitK < R := fun h => by
    have := hEU (s - k * n) (by omega)
    rw [Int.sub_mul, hkn] at this
    exact hpos _ _ (by omega)
  have hlt : s < k * n → R < k * unitK := fun h => by
    have := hEU (k * n - s) (by omega)
    rw [Int.sub_mul, hkn] at this
    exact hpos _ _ (by omega)
  have heq : s = k * n → R = k * unitK := fun h => by
    -- The mean is `k`, on the grid: `2^g` divides `2¹⁰⁷⁴`.
    have hg1074 : g ≤ 1074 := by
      rw [hU] at hgU; exact (Nat.pow_le_pow_iff_right (by omega)).mp hgU
    have hdvd : 2 ^ g * n ∣ (s * unitK).natAbs := by
      rw [hVabs, h, Int.natAbs_mul, Int.natAbs_natCast, hU,
        show 2 ^ 1074 = 2 ^ g * 2 ^ (1074 - g) by rw [← Nat.pow_add]; congr 1; omega]
      rw [Nat.mul_comm]
      exact Nat.mul_dvd_mul (Nat.dvd_mul_left _ _) (Nat.dvd_mul_right _ _)
    have := hex (Nat.mod_eq_zero_of_dvd hdvd)
    rw [h, hkn] at this
    exact Int.eq_of_mul_eq_mul_right (by omega) this
  -- The integer's double.
  rcases Nat.lt_or_ge (2 ^ 53) k.natAbs with hbig | hsmall
  · -- Beyond `2⁵³`, past every value in `[-M, M]`, as `r` is.
    have hRb : R * n < ((M + 1) * unitK : Nat) * n ∧ -(((M + 1) * unitK : Nat) * n : Int) < R * n := by
      have : ((s.natAbs * unitK : Nat) : Int) ≤ ((n * M * unitK : Nat) : Int) := by exact_mod_cast hsMU
      have e1 : (((M + 1) * unitK : Nat) * n : Int) = ((n * M * unitK : Nat) : Int) + (unitK * n : Nat) := by
        push_cast; rw [Int.add_mul, Int.add_mul, Int.one_mul]; ac_rfl
      have e2 : ((unitK * n : Nat) : Int) ≥ ((2 ^ g * n : Nat) : Int) := by
        exact_mod_cast Nat.mul_le_mul_right _ hgU
      rcases Int.natAbs_eq (s * unitK) with h | h <;> rw [hVabs] at h <;> omega
    have hMU : (((M + 1) * unitK : Nat) : Int) ≤ ((2 ^ 53 : Nat) : Int) * unitK := by
      rw [← Int.natCast_mul]; exact Int.ofNat_le.mpr (Nat.mul_le_mul_right _ (by omega))
    have hMU' : -(((2 ^ 53 : Nat) : Int) * unitK) = -((2 ^ 53 : Nat) : Int) * unitK := (Int.neg_mul _ _).symm
    have hRM : R < ((M + 1) * unitK : Nat) ∧ -(((M + 1) * unitK : Nat) : Int) < R := by
      constructor
      · exact hpos _ _ hRb.1
      · exact hpos _ _ (by rw [Int.neg_mul]; exact hRb.2)
    have hs : s.natAbs < k.natAbs * n := by
      have : n * M < n * k.natAbs := Nat.mul_lt_mul_of_pos_left (by omega) hn
      rw [Nat.mul_comm n k.natAbs] at this; omega
    rcases Int.lt_or_le 0 k with hk | hk
    · have hc : ((2 ^ 53 : Nat) : Int) * unitK ≤ scaled (ofInt k) := by
        have := scaled_mono (ofInt_mono (show ((2 ^ 53 : Nat) : Int) ≤ k by omega))
        rwa [ofInt_exact (i := ((2 ^ 53 : Nat) : Int)) (by rw [Int.natAbs_natCast]; exact Nat.le_refl _), scaled_exactCode] at this
      have : k * n > s := by
        have : (k.natAbs : Int) = k := Int.natAbs_of_nonneg (by omega)
        have : ((k.natAbs * n : Nat) : Int) = k * n := by push_cast; rw [this]
        omega
      refine ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => by omega, fun _ => by omega⟩,
        ⟨fun h => by omega, fun h => by omega⟩⟩
    · have hc : scaled (ofInt k) ≤ -((2 ^ 53 : Nat) : Int) * unitK := by
        have := scaled_mono (ofInt_mono (show k ≤ -((2 ^ 53 : Nat) : Int) by omega))
        rwa [ofInt_exact (i := -((2 ^ 53 : Nat) : Int)) (by rw [Int.natAbs_neg, Int.natAbs_natCast]; exact Nat.le_refl _),
          scaled_exactCode] at this
      have : k * n < s := by
        have : (k.natAbs : Int) = -k := Int.ofNat_natAbs_of_nonpos hk
        have : ((k.natAbs * n : Nat) : Int) = -(k * n) := by push_cast; rw [this, Int.neg_mul]
        omega
      refine ⟨⟨fun _ => by omega, fun _ => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
        ⟨fun h => by omega, fun h => by omega⟩⟩
  · rw [ofInt_exact hsmall, scaled_exactCode]
    refine ⟨⟨fun h => ?_, fun h => by have := hgt h; omega⟩,
      ⟨fun h => ?_, fun h => by have := hlt h; omega⟩, ⟨fun h => ?_, fun h => heq h⟩⟩
    · rcases Int.lt_trichotomy (k * n) s with h' | h' | h'
      · exact h'
      · have := heq h'.symm; omega
      · have := hlt h'; omega
    · rcases Int.lt_trichotomy (k * n) s with h' | h' | h'
      · have := hgt h'; omega
      · have := heq h'.symm; omega
      · exact h'
    · rcases Int.lt_trichotomy (k * n) s with h' | h' | h'
      · have := hgt h'; omega
      · exact h'.symm
      · have := hlt h'; omega

end Substrait.FloatCode
