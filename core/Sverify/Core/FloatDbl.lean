import Sverify.Core.FloatArith
import Sverify.Core.Rounding
import Sverify.Core.FloatMoments

/-!
# The reference stays on doubles (ruling 248, #271)

`FloatFormat.Dbl` names the codes of values of the format (`FloatFormat.lean`):
the zeros, `±∞`, the NaNs and the magnitudes with at most `p` significant
bits. Every other integer magnitude up to the largest has a code too, but no
double. This module proves that the reference's double operations produce
only `Dbl` codes, from a few general lemmas: `ofExactDiv` rounds to `p` bits,
so every correctly rounded result is `Dbl` (`dbl_ofExactDiv`), and IEEE 754's
special cases give the special codes. The arithmetic of D31 needs no
hypothesis on its operands (`dbl_fadd`, `dbl_fsub`, `dbl_fmul`, `dbl_fdiv`).
-/

namespace Substrait.FloatCode

/-- A double's code (`fp64.Dbl`). -/
abbrev Dbl (c : Int) : Prop := fp64.Dbl c

theorem dbl_zero : Dbl 0 := fp64.dbl_zero
theorem dbl_negZero : Dbl negZero := fp64.dbl_negZero
theorem dbl_posInf : Dbl posInf := fp64.dbl_posInf
theorem dbl_negInf : Dbl negInf := fp64.dbl_negInf
theorem dbl_nan : Dbl nan := fp64.dbl_nan
theorem dbl_negNan : Dbl negNan := fp64.dbl_negNan

/-- The rounded magnitude `a / n` has at most 53 significant bits. -/
theorem magDbl_roundMagDiv (a n : Nat) : fp64.magDbl (roundMagDiv a n) = true := by
  refine fp64.magDbl_mul (by decide) ?_ _
  have hlt := lt_of_gridExp a n
  rw [Nat.pow_add] at hlt
  have hq : a / (n * 2 ^ gridExp a n) < 2 ^ 53 := by
    rw [← Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm]
    exact hlt
  have := rndDiv_le a (n * 2 ^ gridExp a n)
  show rndDiv a (n * 2 ^ gridExp a n) ≤ 2 ^ fp64.p
  exact Nat.le_trans this (by show _ ≤ 2 ^ 53; omega)

theorem dbl_posCode {m : Nat} (hm : fp64.magDbl m = true) : Dbl (posCode m) := by
  unfold posCode
  split
  · exact dbl_posInf
  · rename_i h
    have := fp64.dbl_ofMag (neg := false) (Nat.le_of_not_lt h) hm
    split
    · exact dbl_zero
    · rename_i h0
      simpa [FloatFormat.ofMag, h0] using this

theorem dbl_neg_posCode {m : Nat} (hm : fp64.magDbl m = true) : Dbl (-posCode m) := by
  unfold posCode
  split
  · have h : -posInf = negInf := by have := posInf_eq; have := negInf_eq; omega
    rw [h]; exact dbl_negInf
  · rename_i h
    have hn : m ≠ fp64.nanMag := by
      have : m ≤ fp64.maxMag := Nat.le_of_not_lt h
      unfold FloatFormat.nanMag; omega
    have := fp64.dbl_ofMag (neg := true) (Nat.le_of_not_lt h) hm
    split
    · simpa using dbl_zero
    · rename_i h0
      simpa [FloatFormat.ofMag, h0, hn] using this

/-- **A correctly rounded result is a double.** -/
theorem dbl_ofExactDiv (v : Int) (n : Nat) : Dbl (ofExactDiv v n) := by
  unfold ofExactDiv
  split
  · exact dbl_neg_posCode (magDbl_roundMagDiv _ _)
  · exact dbl_posCode (magDbl_roundMagDiv _ _)

theorem dbl_ofExact (v : Int) : Dbl (ofExact v) := dbl_ofExactDiv v 1

theorem dbl_rnd (v : Int) (n : Nat) : Dbl (rnd v n) := by
  unfold rnd; dsimp only; split
  · exact dbl_negZero
  · exact dbl_ofExactDiv v n

theorem dbl_zeroOf (neg : Bool) : Dbl (zeroOf neg) := by
  unfold zeroOf; split
  · exact dbl_negZero
  · exact dbl_zero

theorem dbl_infOf (neg : Bool) : Dbl (infOf neg) := by
  unfold infOf; split
  · exact dbl_negInf
  · exact dbl_posInf

theorem dbl_of_isInfCode {c : Int} (h : isInfCode c = true) : Dbl c := by
  simp only [isInfCode, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact dbl_posInf
  · exact dbl_negInf

/-! ## Native doubles -/

theorem dbl_ofMag_infMag (neg : Bool) : Dbl (fp64.ofMag neg fp64.infMag) := by
  cases neg
  · exact dbl_posInf
  · exact dbl_negInf

theorem dbl_ofMag_nanMag (neg : Bool) : Dbl (fp64.ofMag neg fp64.nanMag) := by
  have : fp64.ofMag neg fp64.nanMag = nan := by
    cases neg <;> simp [FloatFormat.ofMag, FloatFormat.nan, FloatFormat.nanMag]
  rw [this]; exact dbl_nan

/-- A sign and a magnitude of a double, `±∞` or NaN give a double. -/
theorem dbl_ofParts {neg : Bool} {m : Nat}
    (h : (m ≤ maxMag ∧ fp64.magDbl m = true) ∨ m = fp64.infMag ∨ m = fp64.nanMag) :
    Dbl (ofParts neg m) := by
  unfold ofParts
  split
  · exact dbl_negZero
  rcases h with ⟨h1, h2⟩ | rfl | rfl
  · exact fp64.dbl_ofMag h1 h2
  · exact dbl_ofMag_infMag neg
  · exact dbl_ofMag_nanMag neg

set_option exponentiation.threshold 2100 in
/-- **A native double's code is a double.** -/
theorem dbl_ofFloat (f : Float) : Dbl (ofFloat f) := by
  unfold ofFloat
  dsimp only
  apply dbl_ofParts
  generalize f.toBits.toNat = bits
  have hm : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have he : (bits / 2 ^ 52) % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize bits % 2 ^ 52 = m at hm ⊢
  generalize (bits / 2 ^ 52) % 2 ^ 11 = e at he ⊢
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  · rename_i h2047
    have he' : e ≤ 2046 := by simp at h2047; omega
    split
    · refine .inl ⟨?_, fp64.magDbl_small (by decide) (by show m < 2 ^ 53; omega)⟩
      rw [maxMag_def]
      exact Nat.le_trans (Nat.le_of_lt hm) (by decide)
    · refine .inl ⟨?_, fp64.magDbl_mul (by decide) (by show 2 ^ 52 + m ≤ 2 ^ 53; omega) _⟩
      rw [maxMag_def]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))

theorem dbl_lift₂ (op : Float → Float → Float) (a b : Int) : Dbl (lift₂ op a b) := dbl_ofFloat _

/-! ## The arithmetic of D31, on any operands -/

theorem dbl_addI (a b : Int) : Dbl (addI a b) := by
  unfold addI
  split
  · exact dbl_nan
  split
  · split
    · exact dbl_nan
    · exact dbl_posInf
  split
  · split
    · exact dbl_nan
    · exact dbl_negInf
  split
  · exact dbl_of_isInfCode (by assumption)
  · try dsimp only
    split
    · exact dbl_zeroOf _
    · exact dbl_rnd _ _

theorem dbl_mulI (a b : Int) : Dbl (mulI a b) := by
  unfold mulI
  split
  · exact dbl_nan
  try dsimp only
  split
  · exact dbl_nan
  split
  · exact dbl_infOf _
  · try dsimp only
    split
    · exact dbl_zeroOf _
    · exact dbl_rnd _ _

theorem dbl_divI (a b : Int) : Dbl (divI a b) := by
  unfold divI
  split
  · exact dbl_nan
  try dsimp only
  split
  · exact dbl_nan
  split
  · exact dbl_infOf _
  split
  · exact dbl_zeroOf _
  split
  · split
    · exact dbl_nan
    · exact dbl_infOf _
  split
  · exact dbl_zeroOf _
  · exact dbl_rnd _ _

theorem dbl_fadd (a b : Int) : Dbl (fadd a b) := dbl_addI a b
theorem dbl_fsub (a b : Int) : Dbl (fsub a b) := dbl_addI a _
theorem dbl_fmul (a b : Int) : Dbl (fmul a b) := dbl_mulI a b
theorem dbl_fdiv (a b : Int) : Dbl (fdiv a b) := dbl_divI a b

set_option exponentiation.threshold 2100

/-! ## Rounding to an integer keeps a double a double

A double of `2⁵³` or more is an integer, a multiple of `K = 2¹⁰⁷⁴` in
magnitude, so `floor`, `ceil` and `round` leave it; below, they give a
multiple of `K` of at most 53 bits. These need the argument to be a double:
an integer magnitude past `2⁵³ · K` that is not a multiple of `K` has no
double, and its floor need not have one either. -/

/-- The magnitude of a double's code. -/
theorem Dbl.magDbl {c : Int} (h : Dbl c) (hm : mag c ≤ maxMag) : fp64.magDbl (mag c) = true := by
  obtain ⟨m0, m1, m2⟩ := maxMag_lt_mag_special
  have hP := posInf_eq; have hN := negInf_eq
  have hpi : maxMag < mag posInf := by unfold mag; omega
  have hni : maxMag < mag negInf := by unfold mag; omega
  unfold Dbl FloatFormat.Dbl FloatFormat.dbl at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | ⟨_, h⟩
  · subst h; simp [mag, FloatFormat.magDbl]
  · subst h; exact absurd hm (Nat.not_le.mpr m0)
  · subst h; exact absurd hm (Nat.not_le.mpr hpi)
  · subst h; exact absurd hm (Nat.not_le.mpr hni)
  · subst h; exact absurd hm (Nat.not_le.mpr m2)
  · subst h; exact absurd hm (Nat.not_le.mpr m1)
  · exact h

/-- A double's magnitude of `2⁵³ · K` or more is a multiple of `K`. -/
theorem K_dvd_of_magDbl {m : Nat} (hd : fp64.magDbl m = true) (hm : 2 ^ 53 * K ≤ m) : K ∣ m := by
  simp only [FloatFormat.magDbl, beq_iff_eq] at hd
  have hm0 : m ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos 53) K_pos) hm)
  have hL : 1127 ≤ m.log2 := by
    rw [Nat.le_log2 hm0]
    have e : (2 : Nat) ^ 1127 = 2 ^ 53 * K := by unfold K; rw [← Nat.pow_add]
    rw [e]; exact hm
  have hdvd : 2 ^ (m.log2 + 1 - fp64.p) ∣ m := Nat.dvd_of_mod_eq_zero hd
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show 1074 ≤ m.log2 + 1 - fp64.p by
    show 1074 ≤ m.log2 + 1 - 53; omega)) hdvd

/-- A rounding of magnitudes to multiples of `K` that leaves multiples of `K`
and moves by less than `K` keeps doubles. -/
theorem magDbl_roundK {f : Nat → Nat} (hfix : ∀ m, K ∣ m → f m = m)
    (hform : ∀ m, ∃ j, j ≤ m / K + 1 ∧ f m = j * K) {m : Nat} (hd : fp64.magDbl m = true) :
    fp64.magDbl (f m) = true := by
  by_cases hbig : 2 ^ 53 * K ≤ m
  · rw [hfix m (K_dvd_of_magDbl hd hbig)]; exact hd
  · obtain ⟨j, hj, he⟩ := hform m
    have : m / K < 2 ^ 53 := (Nat.div_lt_iff_lt_mul K_pos).mpr (by rw [Nat.mul_comm]; omega)
    rw [he]
    exact fp64.magDbl_mul (by decide) (by show j ≤ 2 ^ 53; omega) _

theorem floorMag_fix {m : Nat} (h : K ∣ m) : floorMag m = m := by
  unfold floorMag; exact Nat.div_mul_cancel h

theorem ceilMag_fix {m : Nat} (h : K ∣ m) : ceilMag m = m := by
  obtain ⟨q, rfl⟩ := h
  have hK := K_pos
  have h1 : (K - 1) / K = 0 := Nat.div_eq_of_lt (by omega)
  unfold ceilMag
  rw [show K * q + K - 1 = (K - 1) + q * K by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_right _ _ hK, h1, Nat.zero_add, Nat.mul_comm]

theorem roundMag_fix {m : Nat} (h : K ∣ m) : roundMag m = m := by
  obtain ⟨q, rfl⟩ := h
  have hK := K_pos
  have h2 : K / 2 < K := Nat.div_lt_self hK (by decide)
  unfold roundMag
  rw [show K * q + K / 2 = K / 2 + q * K by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt h2, Nat.zero_add, Nat.mul_comm]

theorem floorMag_zero : floorMag 0 = 0 := by simp [floorMag]
theorem ceilMag_zero : ceilMag 0 = 0 := by
  have hK := K_pos
  have h1 : (K - 1) / K = 0 := Nat.div_eq_of_lt (by omega)
  simp [ceilMag, h1]
theorem roundMag_zero : roundMag 0 = 0 := by
  have h1 : K / 2 / K = 0 := Nat.div_eq_of_lt (Nat.div_lt_self K_pos (by decide))
  simp [roundMag, h1]

theorem floorMag_form (m : Nat) : ∃ j, j ≤ m / K + 1 ∧ floorMag m = j * K := ⟨m / K, by omega, rfl⟩

theorem ceilMag_form (m : Nat) : ∃ j, j ≤ m / K + 1 ∧ ceilMag m = j * K := by
  refine ⟨(m + K - 1) / K, ?_, rfl⟩
  have hK := K_pos
  have : (m + K - 1) / K ≤ (m + K) / K := Nat.div_le_div_right (by omega)
  rw [Nat.add_div_right _ hK] at this; exact this

theorem roundMag_form (m : Nat) : ∃ j, j ≤ m / K + 1 ∧ roundMag m = j * K := by
  refine ⟨(m + K / 2) / K, ?_, rfl⟩
  have hK := K_pos
  have : (m + K / 2) / K ≤ (m + K) / K := Nat.div_le_div_right (by omega)
  rw [Nat.add_div_right _ hK] at this; exact this

theorem evenMag_fix {m : Nat} (h : K ∣ m) : evenMag m = m := by
  have hK := K_pos
  unfold evenMag evenQuot
  have h0 : 2 * 0 < K := by omega
  rw [Nat.mod_eq_zero_of_dvd h]
  simp only [h0, ↓reduceIte]
  exact Nat.div_mul_cancel h

theorem evenMag_form (m : Nat) : ∃ j, j ≤ m / K + 1 ∧ evenMag m = j * K := by
  refine ⟨evenQuot m, ?_, rfl⟩
  unfold evenQuot
  split <;> (try split) <;> (try split) <;> omega

/-- `onMag` of maps that keep doubles' magnitudes keeps doubles. -/
theorem dbl_onMag {pos neg : Nat → Nat}
    (hpb : ∀ m, m ≤ maxMag → pos m ≤ maxMag) (hnb : ∀ m, m ≤ maxMag → neg m ≤ maxMag)
    (hpd : ∀ m, fp64.magDbl m = true → fp64.magDbl (pos m) = true)
    (hnd : ∀ m, fp64.magDbl m = true → fp64.magDbl (neg m) = true)
    {c : Int} (hc : Dbl c) : Dbl (onMag pos neg c) := by
  unfold onMag
  split
  · exact hc
  rename_i hm
  have hm' : mag c ≤ maxMag := Nat.le_of_not_lt hm
  have hd := hc.magDbl hm'
  have hcode : ∀ m, m ≤ maxMag → code m = fp64.ofMag false m := by
    intro m _; unfold code FloatFormat.ofMag; simp
  have hneg : ∀ m, m ≤ maxMag → -code m = fp64.ofMag true m := by
    intro m hm
    have : m ≠ fp64.nanMag := by unfold FloatFormat.nanMag; show m ≠ maxMag + 2; omega
    unfold code FloatFormat.ofMag; split <;> simp_all
  split
  · rw [hneg _ (hnb _ hm')]; exact fp64.dbl_ofMag (hnb _ hm') (hnd _ hd)
  · rw [hcode _ (hpb _ hm')]; exact fp64.dbl_ofMag (hpb _ hm') (hpd _ hd)

theorem dbl_floor {c : Int} (hc : Dbl c) : Dbl (floor c) := by
  unfold floor; exact dbl_onMag floorMag_bound ceilMag_bound
    (fun _ => magDbl_roundK (fun _ h => floorMag_fix h) floorMag_form)
    (fun _ => magDbl_roundK (fun _ h => ceilMag_fix h) ceilMag_form) hc

theorem dbl_ceil {c : Int} (hc : Dbl c) : Dbl (ceil c) := by
  unfold ceil; exact dbl_onMag ceilMag_bound floorMag_bound
    (fun _ => magDbl_roundK (fun _ h => ceilMag_fix h) ceilMag_form)
    (fun _ => magDbl_roundK (fun _ h => floorMag_fix h) floorMag_form) hc

theorem dbl_round {c : Int} (hc : Dbl c) : Dbl (round c) := by
  unfold round; exact dbl_onMag roundMag_bound roundMag_bound
    (fun _ => magDbl_roundK (fun _ h => roundMag_fix h) roundMag_form)
    (fun _ => magDbl_roundK (fun _ h => roundMag_fix h) roundMag_form) hc

theorem dbl_roundEven {c : Int} (hc : Dbl c) : Dbl (roundEven c) := by
  unfold roundEven; exact dbl_onMag evenMag_bound evenMag_bound
    (fun _ => magDbl_roundK (fun _ h => evenMag_fix h) evenMag_form)
    (fun _ => magDbl_roundK (fun _ h => evenMag_fix h) evenMag_form) hc

/-! ## The other operations on doubles -/

/-- A magnitude of a double is `k · 2ˢ` with `k < 2⁵³`. -/
theorem magDbl_iff {m : Nat} : fp64.magDbl m = true ↔ ∃ k s, k < 2 ^ 53 ∧ m = k * 2 ^ s := by
  constructor
  · intro h
    simp only [FloatFormat.magDbl, beq_iff_eq] at h
    refine ⟨m / 2 ^ (m.log2 + 1 - 53), m.log2 + 1 - 53, ?_, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
  · rintro ⟨k, s, hk, rfl⟩
    exact fp64.magDbl_mul (by decide) (by show k ≤ 2 ^ 53; omega) s

/-- The remainder of two doubles' magnitudes is one: `fmod` is exact. -/
theorem magDbl_mod {a b : Nat} (ha : fp64.magDbl a = true) (hb : fp64.magDbl b = true) (hb0 : 0 < b) :
    fp64.magDbl (a % b) = true := by
  obtain ⟨k1, s1, hk1, rfl⟩ := magDbl_iff.mp ha
  obtain ⟨k2, s2, hk2, rfl⟩ := magDbl_iff.mp hb
  rw [magDbl_iff]
  have hlt : k1 * 2 ^ s1 % (k2 * 2 ^ s2) < k2 * 2 ^ s2 := Nat.mod_lt _ hb0
  have hle : k1 * 2 ^ s1 % (k2 * 2 ^ s2) ≤ k1 * 2 ^ s1 := Nat.mod_le _ _
  rcases Nat.le_total s2 s1 with h | h
  · -- `2^s2` divides both, so the remainder, below `k2 · 2^s2`.
    have hd : 2 ^ s2 ∣ k1 * 2 ^ s1 % (k2 * 2 ^ s2) :=
      (Nat.dvd_mod_iff (Nat.dvd_mul_left _ _)).mpr
        (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_mul_left _ _))
    obtain ⟨j, hj⟩ := hd
    refine ⟨j, s2, ?_, by rw [hj, Nat.mul_comm]⟩
    rw [hj, Nat.mul_comm] at hlt
    exact Nat.lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_right hlt) (by omega)
  · have hd : 2 ^ s1 ∣ k1 * 2 ^ s1 % (k2 * 2 ^ s2) :=
      (Nat.dvd_mod_iff (Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_mul_left _ _))).mpr
        (Nat.dvd_mul_left _ _)
    obtain ⟨j, hj⟩ := hd
    refine ⟨j, s1, ?_, by rw [hj, Nat.mul_comm]⟩
    rw [hj, Nat.mul_comm] at hle
    exact Nat.lt_of_le_of_lt (Nat.le_of_mul_le_mul_right hle (Nat.two_pow_pos _)) hk1

/-- `finiteParts` reads a double's magnitude. -/
theorem Dbl.finiteParts {c : Int} (h : Dbl c) (hm : (FloatCode.finiteParts c).2 ≤ maxMag) :
    fp64.magDbl (FloatCode.finiteParts c).2 = true := by
  unfold FloatCode.finiteParts at hm ⊢
  split
  · simp [FloatFormat.magDbl]
  · rename_i h0; simp only [h0, ↓reduceIte] at hm; exact h.magDbl hm

theorem dbl_fmod {a b : Int} (ha : Dbl a) (hb : Dbl b) : Dbl (fmod a b) := by
  unfold fmod
  dsimp only
  split
  · exact dbl_nan
  rename_i h
  split
  · exact ha
  rename_i hinf
  have e1 : (infMag : Nat) = maxMag + 1 := rfl
  have e2 : (nanMag : Nat) = maxMag + 2 := rfl
  have e3 : (fp64.infMag : Nat) = maxMag + 1 := rfl
  have e4 : (fp64.nanMag : Nat) = maxMag + 2 := rfl
  have hma : (finiteParts a).2 ≤ maxMag := by
    omega
  have hmb : (finiteParts b).2 ≤ maxMag := by
    have : (finiteParts b).2 ≠ maxMag + 1 := by rw [← e1]; exact hinf
    omega
  have hb0 : 0 < (finiteParts b).2 := by omega
  refine dbl_ofParts (.inl ⟨Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hb0)) hmb, ?_⟩)
  exact magDbl_mod (ha.finiteParts hma) (hb.finiteParts hmb) hb0

theorem dbl_neg_of_dbl {c : Int} (h : Dbl c) (h0 : c ≠ negZero) : Dbl (-c) := by
  have hP := fp64.posInf_eq; have hN := fp64.negInf_eq; have hZ := fp64.negZero_eq
  have hY := fp64.negNan_eq; have hQ := fp64.nan_eq
  unfold Dbl FloatFormat.Dbl FloatFormat.dbl at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Int.natAbs_neg] at h ⊢
  show _ ∨ _
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact .inl (.inl (.inl (.inl (.inl (.inl (by omega))))))
  · exact absurd h h0
  · exact .inl (.inl (.inl (.inr (by omega))))
  · exact .inl (.inl (.inl (.inl (.inr (by omega)))))
  · exact .inl (.inr (by omega))
  · exact .inl (.inl (.inr (by omega)))
  · exact .inr h

theorem dbl_negI {c : Int} (h : Dbl c) : Dbl (negI c) := by
  unfold negI
  split
  · exact dbl_negZero
  split
  · exact dbl_zero
  · exact dbl_neg_of_dbl h (by assumption)

theorem dbl_canon {c : Int} (h : Dbl c) : Dbl (canon c) := by
  rcases canon_cases c with ⟨_, h1⟩ | ⟨_, h1⟩ | h1
  · rw [h1]; exact dbl_zero
  · rw [h1]; exact dbl_nan
  · rw [h1]; exact h

theorem dbl_roundTo (d : Int) {c : Int} (h : Dbl c) : Dbl (roundTo d c) := by
  unfold roundTo
  dsimp only
  split
  · exact h
  split
  · exact dbl_zero
  try dsimp only
  split <;> split <;> first | exact h | exact dbl_ofFloat _

theorem dbl_nonFinite {vs : List Value} {c : Int} (h : nonFinite vs = some c) : Dbl c := by
  unfold nonFinite at h
  split at h
  · cases h; exact dbl_nan
  split at h
  · cases h; exact dbl_posInf
  split at h
  · cases h; exact dbl_negInf
  · cases h

theorem dbl_floatSumCR (vs : List Value) : Dbl (floatSumCR vs) := by
  unfold floatSumCR
  cases hn : nonFinite vs
  · exact dbl_ofExact _
  · exact dbl_nonFinite hn

theorem dbl_floatAvgCR (vs : List Value) : Dbl (floatAvgCR vs) := by
  unfold floatAvgCR
  cases hn : nonFinite vs
  · exact dbl_ofExactDiv _ _
  · exact dbl_nonFinite hn

/-- A correctly rounded square root has at most 53 significant bits. -/
theorem magDbl_sqrtMag (a b : Nat) : fp64.magDbl (sqrtMag a b) = true := by
  have hq' : ∀ t, t / 2 ^ (gridExp t (2 ^ 60) + 60) < 2 ^ 53 := by
    intro t
    have hlt := lt_of_gridExp t (2 ^ 60)
    rw [Nat.pow_add, Nat.mul_comm (2 ^ gridExp t (2 ^ 60)), ← Nat.div_div_eq_div_mul,
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm 53]
    exact hlt
  have hq := hq' (isqrt (a * 2 ^ 120 / b))
  unfold sqrtMag
  rcases roundGrid_cases (isqrt (a * 2 ^ 120 / b)) (gridExp (isqrt (a * 2 ^ 120 / b)) (2 ^ 60))
    (decide ((a * 2 ^ 120) % b = 0 ∧ isqrt (a * 2 ^ 120 / b) * isqrt (a * 2 ^ 120 / b) = a * 2 ^ 120 / b))
    with h | h <;> rw [h]
  · exact fp64.magDbl_mul (by decide) (by show _ ≤ 2 ^ 53; omega) _
  · exact fp64.magDbl_mul (by decide) (by show _ ≤ 2 ^ 53; omega) _

end Substrait.FloatCode
