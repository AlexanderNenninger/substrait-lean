import FloatBounds.Model
import Sverify.Core.FloatExact

/-!
# The core's doubles meet the standard model (#1196, part 1)

`float-bounds` proves its bounds for any rounding that meets the standard
model (`StdModel`), and the core rounds with integer codes (D31,
`FloatCode.ofExact`): a value `S · 2⁻¹⁰⁷⁴` rounds to the double nearest to it,
ties to even. The link between the two was trusted (`NativeLink`,
`docs/proofs.md`, "What is trusted").

`FloatBridge.model` is the core's rounding as a `StdModel`: a real `z` goes to
the nearest multiple of `2⁻¹⁰⁷⁴` and then through `ofExact`. On the values the
core rounds, multiples of `2⁻¹⁰⁷⁴`, it is `ofExact` itself (`fl_grid`), so
what `float-bounds` proves of `StdModel.fl` holds of the core's codes.

The error bound takes one look past `ofExact_rel`: rounding to the grid first
moves `z` by up to half a unit, and the second rounding moves the grid point
`g` by at most `(|g| − 1) / 2⁵³` where it moves it at all
(`FloatCode.ofExact_err_near`), which is below `|z| · 2¹⁰⁷⁴ / 2⁵³`.
-/

namespace FloatBridge

open FloatBounds Substrait FloatCode

/-- A code's value: its scaled magnitude over `2¹⁰⁷⁴`. -/
noncomputable def val (c : Int) : ℝ := (scaled c : ℝ) / 2 ^ 1074

/-- The core's rounding of a real: to the nearest multiple of `2⁻¹⁰⁷⁴`, then
`ofExact`. Past the largest double the model asks nothing, and `fl` is the
identity there. -/
noncomputable def fl (z : ℝ) : ℝ :=
  if |z| ≤ maxFinite then val (ofExact (round (z * 2 ^ 1074))) else z

theorem two_pow_pos' : (0 : ℝ) < 2 ^ 1074 := by positivity

set_option exponentiation.threshold 2200 in
theorem maxFinite_scaled : maxFinite * 2 ^ 1074 = (maxMag : ℝ) := by
  rw [maxMag_def, maxFinite]; push_cast; norm_num

theorem round_mono' {a b : ℝ} (h : a ≤ b) : round a ≤ round b := by
  rw [round_eq, round_eq]; exact Int.floor_mono (by linarith)

/-- The grid point of a real up to the largest double is at most the largest
double's magnitude. -/
theorem round_natAbs_le {z : ℝ} (hz : |z| ≤ maxFinite) : (round (z * 2 ^ 1074)).natAbs ≤ maxMag := by
  have hx : |z * 2 ^ 1074| ≤ (maxMag : ℝ) := by
    rw [abs_mul, abs_of_pos two_pow_pos', ← maxFinite_scaled]
    exact mul_le_mul_of_nonneg_right hz two_pow_pos'.le
  have hM : ((maxMag : Nat) : ℝ) = ((maxMag : Int) : ℝ) := by norm_cast
  have h1 : round (z * 2 ^ 1074) ≤ (maxMag : Int) := by
    have := round_mono' (le_of_abs_le hx)
    rwa [hM, round_intCast] at this
  have h2 : -(maxMag : Int) ≤ round (z * 2 ^ 1074) := by
    have := round_mono' (neg_le_of_abs_le hx)
    rwa [hM, ← Int.cast_neg, round_intCast] at this
  omega

/-- **On the grid, `fl` is the core's `ofExact`.** -/
theorem fl_grid {S : Int} (hS : S.natAbs ≤ maxMag) : fl ((S : ℝ) / 2 ^ 1074) = val (ofExact S) := by
  have hz : |(S : ℝ) / 2 ^ 1074| ≤ maxFinite := by
    rw [abs_div, abs_of_pos two_pow_pos', div_le_iff₀ two_pow_pos', maxFinite_scaled, ← Int.cast_abs]
    have : (|S| : Int) ≤ (maxMag : Int) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hS
    exact_mod_cast this
  simp only [fl, hz, ↓reduceIte, div_mul_cancel₀ _ two_pow_pos'.ne', round_intCast]

/-- `u · tiny = 2⁻¹⁰⁷⁵`: half a unit of the grid. -/
theorem u_mul_tiny : u * tiny = 1 / 2 / 2 ^ 1074 := by
  rw [u_val, tiny]; field_simp

set_option exponentiation.threshold 2200 in
/-- **The standard model's bound** for the core's rounding. -/
theorem fl_err (z : ℝ) (hz : |z| ≤ maxFinite) : |fl z - z| ≤ u * (|z| + tiny) := by
  have hg := round_natAbs_le hz
  have hpos := two_pow_pos'
  set x := z * 2 ^ 1074 with hxdef
  set g := round x
  have hxg : |x - g| ≤ 1 / 2 := abs_sub_round x
  have hfl : fl z - z = ((scaled (ofExact g) : ℝ) - x) / 2 ^ 1074 := by
    simp only [fl, hz, ↓reduceIte, val, hxdef, g]; field_simp
  rw [hfl, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, mul_add, add_mul, u_mul_tiny,
    div_mul_cancel₀ _ hpos.ne']
  have hux : u * |z| * 2 ^ 1074 = |x| / 2 ^ 53 := by
    rw [u_val, hxdef, abs_mul, abs_of_pos hpos]; ring
  rw [hux]
  have htri : |(scaled (ofExact g) : ℝ) - x| ≤ |(scaled (ofExact g) : ℝ) - g| + |x - g| := by
    have := abs_sub_le (scaled (ofExact g) : ℝ) g x
    rw [abs_sub_comm (g : ℝ) x] at this; exact this
  rcases ofExact_err_near hg with h | h
  · rw [h]
    have : (0 : ℝ) ≤ |x| / 2 ^ 53 := by positivity
    rw [abs_sub_comm]
    linarith
  · -- `2⁵³ |d| + 1 ≤ |g| ≤ |x| + 1/2`
    have hd : (2 : ℝ) ^ 53 * |(scaled (ofExact g) : ℝ) - g| + 1 ≤ |(g : ℝ)| := by
      have h' : (((2 ^ 53 * (scaled (ofExact g) - g).natAbs + 1 : ℕ)) : ℝ) ≤ (g.natAbs : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, Int.cast_sub] at h'
      rw [show (2 : ℝ) ^ 53 = 9007199254740992 by norm_num]; exact h'
    have hgx : |(g : ℝ)| ≤ |x| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (g : ℝ) x
      rw [abs_sub_comm] at this; linarith
    have : |(scaled (ofExact g) : ℝ) - g| ≤ |x| / 2 ^ 53 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith

theorem fl_nonneg (z : ℝ) (hz : 0 ≤ z) : 0 ≤ fl z := by
  unfold fl
  split
  · next h =>
    have hg := round_natAbs_le h
    have h0 : (0 : Int) ≤ round (z * 2 ^ 1074) := by
      have := round_mono' (show (0 : ℝ) ≤ z * 2 ^ 1074 by positivity)
      rwa [round_zero] at this
    have := scaled_ofExact_nonneg hg h0
    exact div_nonneg (by exact_mod_cast this) two_pow_pos'.le
  · exact hz

theorem fl_nonpos (z : ℝ) (hz : z ≤ 0) : fl z ≤ 0 := by
  unfold fl
  split
  · next h =>
    have hg := round_natAbs_le h
    have h0 : round (z * 2 ^ 1074) ≤ 0 := by
      have := round_mono' (show z * 2 ^ 1074 ≤ 0 from mul_nonpos_of_nonpos_of_nonneg hz two_pow_pos'.le)
      rwa [round_zero] at this
    have := scaled_ofExact_nonpos hg h0
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast this) two_pow_pos'.le
  · exact hz

theorem fl_idem (z : ℝ) : fl (fl z) = fl z := by
  by_cases hz : |z| ≤ maxFinite
  · have hg := round_natAbs_le hz
    have h := fl_grid (scaled_ofExact_le hg)
    have hfz : fl z = (scaled (ofExact (round (z * 2 ^ 1074))) : ℝ) / 2 ^ 1074 := by
      simp only [fl, hz, ↓reduceIte, val]
    rw [hfz, h, ofExact_idem hg]; rfl
  · simp only [fl, hz, ↓reduceIte]

theorem fl_zero : fl 0 = 0 := by
  have : |(0 : ℝ)| ≤ maxFinite := by rw [abs_zero]; exact (fpFacts.max_ge.trans' (by positivity))
  simp only [fl, this, ↓reduceIte, zero_mul, round_zero, val]
  have : scaled (ofExact 0) = 0 := by
    have := scaled_ofExact (g := 0) (by simp)
    simpa [roundMagDiv_zero] using this
  simp [this]

/-- **The core's rounding is a `StdModel`.** -/
noncomputable def model : StdModel where
  fl := fl
  err := fl_err
  nonneg := fl_nonneg
  nonpos := fl_nonpos
  idem := fl_idem
  zero := fl_zero

/-- What `model` rounds a multiple of `2⁻¹⁰⁷⁴` to is the core's `ofExact`. -/
theorem model_fl_grid {S : Int} (hS : S.natAbs ≤ maxMag) :
    model.fl ((S : ℝ) / 2 ^ 1074) = val (ofExact S) := fl_grid hS

end FloatBridge
