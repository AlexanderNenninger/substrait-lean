import FloatBounds.Model
import Sverify.Core.FloatExact

/-!
# The core's doubles meet the standard model (#1196, part 1)

`float-bounds` proves its bounds for any rounding that meets the standard
model (`StdModel`), and the core rounds with integer codes (D31,
`FloatCode.ofExact`): a value `S · 2⁻¹⁰⁷⁴` rounds to the double nearest to it,
ties to even. Until now the link between the two was trusted
(`NativeLink`, `docs/proofs.md`, "What is trusted").

`FloatBridge.model` is the core's rounding as a `StdModel`: a real `z` goes to
the nearest multiple of `2⁻¹⁰⁷⁴` and then through `ofExact`. On the values the
core rounds, multiples of `2⁻¹⁰⁷⁴`, it is `ofExact` itself (`fl_grid`), so the
theorems of `float-bounds` about `StdModel.fl` hold of the core's codes.

The error bound needs one look past `ofExact_rel`: rounding to the grid first
moves `z` by up to half a unit, and the second rounding's error is at most
`u · |z|`, not `u · |g|` for the grid point `g` (`ofExact_err_near`): where `g`
is the least integer of its binade it is a double, and does not move.
-/

namespace FloatBridge

open FloatBounds Substrait FloatCode

/-! ## The core's rounding of an integer -/

/-- The code of `±m`, for a magnitude below `+∞`. -/
theorem scaled_ofMag (neg : Bool) {m : Nat} (hm : m ≤ maxMag) :
    scaled (ofMag neg m) = if neg then -(m : Int) else m := by
  rw [ofMag_eq neg hm]
  cases neg
  · simp [scaled_posCode hm]
  · simp [scaled_neg_posCode hm]

/-- A magnitude `k · 2ˢ` with `k < 2⁵³` rounds to itself. -/
theorem scaled_ofExact_exact {g : Int} {k s : Nat} (hk : k < 2 ^ 53) (hg : g.natAbs = k * 2 ^ s)
    (hm : k * 2 ^ s ≤ maxMag) : scaled (ofExact g) = g := by
  have h := ofExact_exact (decide (g < 0)) hk hm
  have hx : exact (ofMag (decide (g < 0)) (k * 2 ^ s)) = g := by
    simp only [exact, scaled_ofMag _ hm]
    clear hm h
    generalize k * 2 ^ s = m at hg
    by_cases hneg : g < 0
    · simp only [hneg, decide_true, ↓reduceIte]; omega
    · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  rw [hx] at h
  rw [h, scaled_ofMag _ hm]
  clear h hx hm
  generalize k * 2 ^ s = m at hg
  by_cases hneg : g < 0
  · simp only [hneg, decide_true, ↓reduceIte]; omega
  · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

theorem ofExact_maxMag : ofExact (maxMag : Int) = posCode maxMag := by
  obtain ⟨k, s, hk, hks⟩ : ∃ k s : Nat, k < 2 ^ 53 ∧ k * 2 ^ s = maxMag :=
    ⟨2 ^ 53 - 1, 2045, Nat.sub_lt (Nat.two_pow_pos 53) Nat.one_pos, maxMag_def.symm⟩
  have h := ofExact_exact false hk (Nat.le_of_eq hks)
  rw [hks] at h
  have hx : exact (ofMag false maxMag) = (maxMag : Int) := by
    rw [exact, scaled_ofMag false (Nat.le_refl _)]; rfl
  rw [hx, ofMag_eq false (Nat.le_refl _)] at h
  exact h

theorem ofExact_le_max {g : Int} (hg : g ≤ maxMag) : ofExact g ≤ posCode maxMag :=
  ofExact_maxMag ▸ ofExact_mono hg

/-- An integer up to the largest double rounds to a finite double. -/
theorem ofExact_fin {g : Int} (hg : g.natAbs ≤ maxMag) : IsFin (ofExact g) := by
  have hp := posInf_eq; have hn := negInf_eq
  have hpos : posCode maxMag = 2 * maxMag + 1 := by
    simp [posCode, show maxMag ≠ 0 from Nat.pos_iff_ne_zero.mp maxMag_pos]
  have hup := ofExact_le_max (g := g) (by omega)
  have hlow : -(posCode maxMag : Int) ≤ ofExact g := by
    have := ofExact_le_max (g := -g) (by omega)
    rw [ofExact_neg] at this; omega
  unfold IsFin; omega

end FloatBridge
