import SubstraitLean.Profile
import SubstraitLean.Order
import SubstraitLean.EngineTables

/-!
# The reference on Polars: the shims, proved (#444)

The translation from the reference to Polars 2.1.0 writes one small shim per
value choice Polars makes differently (`python/src/sverify/_polars_shims.py`,
its `SHIMS`), and checks the preconditions it cannot drop on the data (its
`GUARDS`). This module states what Polars does natively for each of them, as
its facts record it (`characterization/polars/facts/`), and proves once, per
shim, that the shimmed expression gives the reference's value. The lemmas are
named as the Python shims: `Polars.<name>`.

**Trusted**: the model of Polars's own functions below (`Polars.floorDiv`,
`Polars.floorMod`, `Polars.round`, `Polars.find`, `Polars.sortWith`, …), each
from its fact. The shims are then theorems, as `Rel.duckdb_shim_sound` is for
DuckDB.

* Value side (`SHIMS`): `int_div_trunc`, `int_mod_trunc`, `round_half_away`,
  `sum_empty_null`, `avg_int_declared`, `one_zero`, `strpos_chars`,
  `substring_wrap`, `null_order`, `tie_order`, `decimal_round_half_away`,
  `decimal_div_half_away`, `max_nan_greatest` (and `min_ignore_nan`, which
  needs only `one_zero`).
* Guards (`GUARDS`): each flag holds exactly where the reference's issue
  does, so a guard refuses exactly the batches the precondition rules out
  (A3: `sum_leaves_i64`; A4: `makes_infinite`, `agg_makes_infinite`; B1:
  `sum_makes_nan`; and `int_overflows`, `div_overflows`, `zero_divisor`).
* Error side: Polars's own value where the reference raises (a wrapped
  integer, NULL for a zero divisor, NaN from `∞ - ∞`, IEEE `±∞`) needs no
  shim. `Polars.written_faithful`: Polars with the value shims agrees with the
  reference wherever the reference reports no issue, so a plan `verify`
  proves free of issues (up to the assumed ones, whose guards stay) runs on
  Polars as `Rel.eval` (`Rel.polars_sound`).
-/

namespace Substrait.Polars

/-! ## Integers: `division_type` = `TRUNCATE` -/

/-- Polars's `//` of integers floors (polars-int-divide), exactly: the engine
computes on 128 bits, where a 64-bit quotient cannot overflow but for
`MIN // -1`, which the reference raises on. -/
def floorDiv (a b : Int) : Int := a.fdiv b

/-- Polars's `%` of integers takes the divisor's sign (polars-int-modulus). -/
def floorMod (a b : Int) : Int := a.fmod b

/-- `int_div_trunc`: one more than the floored quotient where the remainder is
not zero and the signs differ. -/
def intDivTrunc (a b : Int) : Int :=
  if floorMod a b ≠ 0 ∧ (decide (a < 0) ≠ decide (b < 0)) then floorDiv a b + 1 else floorDiv a b

/-- `int_mod_trunc`: the divisor taken off where the remainder's sign is not
the dividend's. -/
def intModTrunc (a b : Int) : Int :=
  let r := floorMod a b
  if r ≠ 0 ∧ (decide (r < 0) ≠ decide (a < 0)) then r - b else r

theorem fmod_eq_zero_iff {a b : Int} : a.fmod b = 0 ↔ b ∣ a := Int.dvd_iff_fmod_eq_zero.symm

/-- The floored remainder has the divisor's sign. -/
theorem fmod_sign (a : Int) {b : Int} : (0 < b → 0 ≤ a.fmod b) ∧ (b < 0 → a.fmod b ≤ 0) := by
  refine ⟨fun h => Int.fmod_nonneg_of_pos a h, fun h => ?_⟩
  have := Int.fmod_nonneg_of_pos (-a) (b := -b) (by omega)
  rw [Int.neg_fmod_neg] at this
  omega

/-- **`Polars.int_div_trunc`**: the shimmed quotient is the reference's
(`Int.tdiv`, `BinFn.idiv`). -/
theorem int_div_trunc (a : Int) {b : Int} (hb : b ≠ 0) : intDivTrunc a b = a.tdiv b := by
  unfold intDivTrunc floorDiv floorMod
  rw [Int.tdiv_eq_fdiv]
  by_cases hd : b ∣ a
  · have : a.fmod b = 0 := fmod_eq_zero_iff.mpr hd
    simp [hd, this]
  · have : a.fmod b ≠ 0 := fun h => hd (fmod_eq_zero_iff.mp h)
    simp only [hd, ite_false, ne_eq, this, not_false_eq_true, true_and]
    have hs : b.sign = if 0 < b then 1 else -1 := by
      rcases Int.lt_trichotomy b 0 with h | h | h
      · simp [Int.sign_eq_neg_one_of_neg h, show ¬ 0 < b by omega]
      · omega
      · simp [Int.sign_eq_one_of_pos h, h]
    by_cases ha : 0 ≤ a <;> by_cases hb' : 0 ≤ b <;> simp_all <;> omega

/-- **`Polars.int_mod_trunc`**: the shimmed remainder is the reference's
(`Int.tmod`, `BinFn.imod`). -/
theorem int_mod_trunc (a : Int) {b : Int} (hb : b ≠ 0) : intModTrunc a b = a.tmod b := by
  have hq := int_div_trunc a hb
  have h1 := Int.fmod_add_mul_fdiv a b
  have h2 := Int.tmod_add_mul_tdiv a b
  unfold intDivTrunc floorDiv floorMod at hq
  unfold intModTrunc floorMod
  dsimp only
  -- The remainders differ by `b` exactly where the quotients differ by one.
  have hfm : a.fmod b ≠ 0 → (decide (a.fmod b < 0) ≠ decide (a < 0) ↔
      decide (a < 0) ≠ decide (b < 0)) := by
    intro hne
    have hsgn := fmod_sign a (b := b)
    by_cases hbp : 0 < b <;> simp_all <;> omega
  by_cases hc : a.fmod b ≠ 0 ∧ (decide (a < 0) ≠ decide (b < 0))
  · simp only [hc, ne_eq, not_false_eq_true, and_self, ite_true] at hq
    have hc' : a.fmod b ≠ 0 ∧ (decide (a.fmod b < 0) ≠ decide (a < 0)) :=
      ⟨hc.1, (hfm hc.1).mpr hc.2⟩
    simp only [hc', ne_eq, not_false_eq_true, and_self, ite_true]
    rw [← hq] at h2
    rw [Int.mul_add] at h2
    omega
  · simp only [hc, ite_false] at hq
    have hc' : ¬ (a.fmod b ≠ 0 ∧ (decide (a.fmod b < 0) ≠ decide (a < 0))) := by
      rintro ⟨h0, h⟩; exact hc ⟨h0, (hfm h0).mp h⟩
    simp only [hc', ite_false]
    rw [← hq] at h2
    omega

/-! ## Doubles: `rounding` and `zero_sign` -/

/-- How Polars's `round(0, mode=…)` rounds a double's ties (polars-round). -/
inductive RoundMode | halfToEven | halfAwayFromZero
  deriving DecidableEq

/-- Polars's `round` to an integer. `half_to_even`, its default, is IEEE's
`roundeven`; `half_away_from_zero` is C's `round`, the reference's
`roundMag`. Trusted: polars-round. -/
def round : RoundMode → Int → Int
  | .halfToEven, c =>
    let x := FloatCode.toFloat c
    let f := x.floor
    let d := x - f
    let up := d > 0.5 || (d == 0.5 && (f / 2).floor * 2 != f)
    if x.isNaN || x.isInf then c else FloatCode.ofFloat (if up then f + 1 else f)
  | .halfAwayFromZero, c => FloatCode.round c

-- The ties where the modes differ (polars-round).
#guard round .halfToEven (FloatCode.ofFloat 2.5) == FloatCode.ofFloat 2.0
#guard round .halfAwayFromZero (FloatCode.ofFloat 2.5) == FloatCode.ofFloat 3.0
#guard round .halfToEven (FloatCode.ofFloat (-0.5)) == 0

/-- **`Polars.round_half_away`**: with `mode="half_away_from_zero"`, Polars
rounds as the reference (`UnFn.fround`). -/
theorem round_half_away (c : Int) : round .halfAwayFromZero c = FloatCode.round c := rfl

/-- `one_zero`: `-0.0` as `0.0`. Polars compares IEEE doubles, where
`-0.0 = 0.0`, so the shim sends both zeros to `0.0` (polars-zero-sign). On
the full set of codes (`FloatFormat.negZero`, #444 step 1b). -/
def oneZero (c : Int) : Int := if c = 0 ∨ c = FloatCode.negZero then 0 else c

/-- **`Polars.one_zero`**: the shim is `canon` on every code but the negative
NaN, whose sign Polars keeps (`nan_kind`, refines up to `canon`, B2); so the
keys it groups, deduplicates and joins on are the reference's codes. -/
theorem one_zero {c : Int} (h : c ≠ FloatCode.negNan) : oneZero c = FloatCode.canon c := by
  unfold oneZero
  have hz := fp64.negZero_ne_negNan
  by_cases h0 : c = 0
  · subst h0; simp [FloatCode.canon_zero]
  · by_cases hn : c = FloatCode.negZero
    · subst hn; simp [fp64.canon_negZero]
    · simp only [h0, hn, or_self, ite_false]
      exact (fp64.canon_eq_self ⟨hn, h⟩).symm

theorem one_zero_isRef {c : Int} (h : FloatCode.IsRef c ∨ c = FloatCode.negZero) :
    FloatCode.IsRef (oneZero c) := by
  have hne : c ≠ FloatCode.negNan := by
    rcases h with h | h
    · intro e; subst e; exact fp64.not_isRef_negNan h
    · intro e; exact fp64.negZero_ne_negNan (h.symm.trans e)
  rw [one_zero hne]
  exact fp64.isRef_canon_of_isRef_or (h.elim .inl fun e => .inr (.inl e))

/-! ## Aggregates: `empty_group_aggregates` and `avg_int_result` -/

/-- Polars's `sum` of a group's integers: 0 for no values (polars-sum-int),
exact on 128 bits. -/
def sum0 (vs : List Int) : Int := vs.sum

/-- `sum_empty_null`: NULL where the group has no values. -/
def sumEmptyNull (vs : List Int) : Value := if vs.length = 0 then .null else .int (sum0 vs)

theorem intSum_map_int : ∀ vs : List Int, intSum (vs.map .int) = vs.sum
  | [] => rfl
  | v :: vs => by simp [intSum, intSum_map_int vs, List.sum_cons]

/-- **`Polars.sum_empty_null`**: the shimmed `SUM` is the reference's
(`AggFn.sum`): NULL for no values. -/
theorem sum_empty_null (vs : List Int) : sumEmptyNull vs = AggFn.sum.apply (vs.map .int) := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    simp only [sumEmptyNull, List.length_cons, Nat.add_one_ne_zero, ite_false, sum0,
      AggFn.apply, List.map_cons]
    rw [← List.map_cons, intSum_map_int]

/-- `avg_int_declared`: the exact 128-bit sum truncated by the count
(`int_div_trunc`), NULL for no values. Polars's own `mean` is a `Float64`
(polars-avg-int). -/
def avgIntDeclared (vs : List Int) : Value :=
  if vs.length = 0 then .null else .int (intDivTrunc vs.sum vs.length)

theorem sum_between (lo hi : Int) : ∀ vs : List Int, (∀ x ∈ vs, lo ≤ x ∧ x ≤ hi) →
    vs.length * lo ≤ vs.sum ∧ vs.sum ≤ vs.length * hi
  | [], _ => by simp
  | v :: vs, h => by
    have ih := sum_between lo hi vs fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hv := h v (List.mem_cons_self ..)
    simp only [List.length_cons, List.sum_cons, Int.natCast_add, Int.natCast_one, Int.add_mul,
      Int.one_mul]
    omega

/-- A truncated mean lies between the values. -/
theorem tdiv_mean_between {s lo hi : Int} {n : Nat} (hn : 0 < n) (h1 : n * lo ≤ s)
    (h2 : s ≤ n * hi) : lo ≤ s.tdiv n ∧ s.tdiv n ≤ hi := by
  have hn' : (0 : Int) < n := by omega
  have hd := Int.emod_add_ediv_mul s n
  have hr0 := Int.emod_nonneg s (b := n) (by omega)
  have hr1 := Int.emod_lt_of_pos s hn'
  -- `s = q n + r`, `0 ≤ r < n`.
  have hq := Int.mul_comm (s / n) n
  have l1 : lo ≤ s / n := by
    apply Int.le_of_lt_add_one
    apply Int.lt_of_mul_lt_mul_left (a := (n : Int)) _ (by omega)
    rw [Int.mul_add, Int.mul_one]
    omega
  have l2 : s / n ≤ hi := Int.le_of_mul_le_mul_left (by omega) hn'
  rw [Int.tdiv_eq_ediv]
  simp only [Int.sign_eq_one_of_pos hn']
  split
  · omega
  · rename_i hnot
    have hm : s % n ≠ 0 := fun h => hnot (.inr (Int.dvd_of_emod_eq_zero h))
    -- `s` is not a multiple of `n`, so the quotient is below `hi`.
    have l3 : s / n < hi := by
      apply Int.lt_of_mul_lt_mul_left (a := (n : Int)) _ (by omega)
      omega
    omega

theorem foldl_min_le_mem : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, xs.foldl min x ≤ y
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h
      exact Int.le_trans (foldl_min_le_mem (min y z) zs _ (List.mem_cons_self ..)) (Int.min_le_left _ _)
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Int.le_trans (foldl_min_le_mem (min x y) zs _ (List.mem_cons_self ..)) (Int.min_le_right _ _)
      · exact foldl_min_le_mem (min x z) zs y (List.mem_cons_of_mem _ h)

theorem le_foldl_max_mem : ∀ (x : Int) (xs : List Int), ∀ y ∈ x :: xs, y ≤ xs.foldl max x
  | x, [], y, hy => by simp at hy; subst hy; exact Int.le_refl _
  | x, z :: zs, y, hy => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h
      exact Int.le_trans (Int.le_max_left _ _) (le_foldl_max_mem (max y z) zs _ (List.mem_cons_self ..))
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Int.le_trans (Int.le_max_right _ _) (le_foldl_max_mem (max x y) zs _ (List.mem_cons_self ..))
      · exact le_foldl_max_mem (max x z) zs y (List.mem_cons_of_mem _ h)

theorem intsOf_map_int (vs : List Int) : intsOf (vs.map .int) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [intsOf] at ih ⊢; exact ih

/-- **`Polars.avg_int_declared`**: the shimmed `AVG` of integers is the
reference's (`AggFn.iavg`): the truncated mean, which lies between the
values, so the reference's clamp leaves it. -/
theorem avg_int_declared (vs : List Int) : avgIntDeclared vs = AggFn.iavg.apply (vs.map .int) := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    have hl : (v :: vs).length ≠ 0 := by simp only [List.length_cons]; omega
    simp only [avgIntDeclared, hl, ite_false, AggFn.apply, List.map_cons]
    rw [← List.map_cons, intSum_map_int, List.length_map, int_div_trunc _ (by simp only [List.length_cons]; omega)]
    congr 1
    unfold clampInts
    rw [intsOf_map_int]
    simp only
    have hb := sum_between (vs.foldl min v) (vs.foldl max v) (v :: vs) fun x hx =>
      ⟨foldl_min_le_mem v vs x hx, le_foldl_max_mem v vs x hx⟩
    have hm := tdiv_mean_between (s := (v :: vs).sum) (n := (v :: vs).length) (by simp) hb.1 hb.2
    rw [Int.max_eq_left hm.1, Int.min_eq_left hm.2]

/-! ## `MIN` and `MAX` of doubles: `nan_order` = `GREATEST`, `zero_sign` = `ONE_ZERO` -/

section MinMax
open FloatCode

/-- The codes a column of doubles holds on Polars: the reference's, `-0.0`
or the negative NaN, whose sign Polars keeps (`nan_kind`). -/
def DoubleCode (c : Int) : Prop := IsRef c ∨ c = negZero ∨ c = negNan

theorem canon_le_nan {c : Int} (h : DoubleCode c) : canon c ≤ nan :=
  (fp64.isRef_canon_of_isRef_or h).2

/-- A double read with one zero (`one_zero`, up to the NaN's sign). -/
def canonV : Value → Value
  | .int c => .int (canon c)
  | v => v

/-- Polars's `min` of a group's doubles (polars-min-max-nan,
polars-min-max-zero): NULL without values, else one of them that is at most
each value that is not NaN, so NaN only when every value is. Which of two
zeros it keeps is the platform's (`f64::min`), so the order is up to the sign
of zero. Trusted. -/
def MinIgnoreNan (vs : List Int) (r : Value) : Prop :=
  match vs with
  | [] => r = .null
  | _ :: _ => ∃ c ∈ vs, r = .int c ∧ ∀ x ∈ vs, canon x ≠ nan → canon c ≤ canon x

/-- Polars's `max`: as `min`, at least each value that is not NaN. Trusted. -/
def MaxIgnoreNan (vs : List Int) (r : Value) : Prop :=
  match vs with
  | [] => r = .null
  | _ :: _ => ∃ c ∈ vs, r = .int c ∧ ∀ x ∈ vs, canon x ≠ nan → canon x ≤ canon c

/-- `max_nan_greatest`: NaN where the group holds one, else Polars's `max`
read with one zero. -/
def maxNanGreatest (vs : List Int) (r : Value) : Value :=
  if vs.any (fun x => decide (canon x = nan)) then .int nan else canonV r

theorem map_canon_cons (v : Int) (vs : List Int) :
    (Value.int (canon v) :: vs.map fun c => Value.int (canon c)) =
      (v :: vs).map fun c => Value.int (canon c) := rfl

/-- **`Polars.min_ignore_nan`**: Polars's `min`, read with one zero, is the
reference's `MIN` (`AggFn.min`): NaN is the greatest double there, so a `min`
that skips NaN agrees, and the zeros are one. -/
theorem min_ignore_nan {vs : List Int} {r : Value} (hv : ∀ x ∈ vs, DoubleCode x)
    (h : MinIgnoreNan vs r) : canonV r = AggFn.min.apply (vs.map fun c => .int (canon c)) := by
  cases vs with
  | nil => simp only [MinIgnoreNan] at h; subst h; rfl
  | cons v vs =>
    obtain ⟨c, hc, rfl, hle⟩ := h
    simp only [List.map_cons, AggFn.apply]
    have hmem := pickFold_mem (fun a b => !a.le b) (.int (canon v)) (vs.map fun c => .int (canon c))
    have hlo := pickFold_min_le (.int (canon v)) (vs.map fun c => .int (canon c))
    generalize pickFold (fun a b => !a.le b) (.int (canon v)) (vs.map fun c => .int (canon c)) = m
      at hmem hlo ⊢
    rw [map_canon_cons] at hmem hlo
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
    have h1 : canon y ≤ canon c := Value.le_int.mp (hlo _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    have h2 : canon c ≤ canon y := by
      by_cases hn : canon y = nan
      · rw [hn]; exact canon_le_nan (hv c hc)
      · exact hle y hy hn
    show Value.int (canon c) = Value.int (canon y)
    rw [Int.le_antisymm h2 h1]

/-- **`Polars.max_nan_greatest`**: the shimmed `max` is the reference's `MAX`
(`AggFn.max`): NaN where the group holds one, as NaN is the greatest double,
else Polars's `max` with one zero. -/
theorem max_nan_greatest {vs : List Int} {r : Value} (hv : ∀ x ∈ vs, DoubleCode x)
    (h : MaxIgnoreNan vs r) :
    maxNanGreatest vs r = AggFn.max.apply (vs.map fun c => .int (canon c)) := by
  cases vs with
  | nil => simp only [MaxIgnoreNan] at h; subst h; rfl
  | cons v vs =>
    obtain ⟨c, hc, rfl, hge⟩ := h
    simp only [List.map_cons, AggFn.apply]
    have hmem := pickFold_mem (fun a b => !b.le a) (.int (canon v)) (vs.map fun c => .int (canon c))
    have hhi := pickFold_max_ge (.int (canon v)) (vs.map fun c => .int (canon c))
    generalize pickFold (fun a b => !b.le a) (.int (canon v)) (vs.map fun c => .int (canon c)) = m
      at hmem hhi ⊢
    rw [map_canon_cons] at hmem hhi
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
    unfold maxNanGreatest
    split
    · rename_i hany
      obtain ⟨z, hz, hzn⟩ := List.any_eq_true.mp hany
      have h1 : canon z ≤ canon y := Value.le_int.mp (hhi _ (List.mem_map.mpr ⟨z, hz, rfl⟩))
      have h2 := canon_le_nan (hv y hy)
      have hzn : canon z = nan := of_decide_eq_true hzn
      show Value.int nan = Value.int (canon y)
      congr 1; omega
    · rename_i hnone
      have hy' : canon y ≠ nan := fun e =>
        hnone (List.any_eq_true.mpr ⟨y, hy, decide_eq_true e⟩)
      have h1 : canon c ≤ canon y := Value.le_int.mp (hhi _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
      have h2 := hge y hy hy'
      show Value.int (canon c) = Value.int (canon y)
      rw [Int.le_antisymm h1 h2]

end MinMax

/-! ## Decimals: `decimal_rescale` = `TIE_AWAY_FROM_ZERO` -/

/-- Polars's cast of an unscaled decimal to a scale `k` digits smaller, and
its `×` and `/` past the result's scale, round half to even
(polars-decimal-arith, polars-decimal-casts). -/
def rescaleEven (k : Nat) (u : Int) : Int :=
  let q := u.natAbs / 10 ^ k
  let r := u.natAbs % 10 ^ k
  let m : Int := (if 2 * r > 10 ^ k ∨ (2 * r = 10 ^ k ∧ q % 2 = 1) then q + 1 else q : Nat)
  if u < 0 then -m else m

#guard rescaleEven 1 125 == 12 && rescaleEven 1 135 == 14 && rescaleEven 2 (-250) == -2

/-- `decimal_round_half_away`: `(|u| + 5·10ᵏ⁻¹) // 10ᵏ`, with `u`'s sign. -/
def decimalRoundHalfAway (k : Nat) (u : Int) : Int :=
  let q : Int := ((u.natAbs + 5 * 10 ^ (k - 1)) / 10 ^ k : Nat)
  if u < 0 then -q else q

/-- **`Polars.decimal_round_half_away`**: the shimmed rescale is the
reference's (`roundDiv10`, `UnFn.dround`), on 128 bits: `|u| < 10³⁸`, so
`|u| + 5·10ᵏ⁻¹` fits. -/
theorem decimal_round_half_away {k : Nat} (hk : 0 < k) (u : Int) :
    decimalRoundHalfAway k u = roundDiv10 k u := by
  have h : 10 ^ k / 2 = 5 * 10 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.pow_succ, Nat.add_sub_cancel]
    omega
  simp only [decimalRoundHalfAway, roundDiv10, h]

/-- `decimal_div_half_away`: with `|x| = a·|n| + b`, `a·10ᵏ + ⌊(2b·10ᵏ + |n|) / 2|n|⌋`,
negated where `x` and `n` differ in sign. -/
def decimalDivHalfAway (x n : Int) (k : Nat) : Int :=
  let an := n.natAbs
  let ax := x.natAbs
  let q : Int := ((ax / an) * 10 ^ k + (2 * (ax % an) * 10 ^ k + an) / (2 * an) : Nat)
  if (x < 0) = (n < 0) then q else -q

/-- **`Polars.decimal_div_half_away`**: the shimmed quotient is the
reference's (`roundDivInt?`, `BinFn.ddiv`) of the dividend at `k` more
places, a decimal `AVG` (`decimalAvgs`) or `sverify_decimal_div`. The
split keeps every step within 128 bits (`_polars_shims.decimal_div_half_away`). -/
theorem decimal_div_half_away {n : Int} (hn : n ≠ 0) (x : Int) (k : Nat) :
    roundDivInt? (x * 10 ^ k) n = some (decimalDivHalfAway x n k) := by
  have hT : (0 : Int) < 10 ^ k := Int.pow_pos (by decide)
  have han : 0 < n.natAbs := Int.natAbs_pos.2 hn
  have habs : (x * 10 ^ k).natAbs = x.natAbs * 10 ^ k := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
  have hsign : (x * 10 ^ k < 0) = (x < 0) := by
    apply propext; constructor
    · intro h; exact Int.lt_of_not_ge fun h0 => absurd h (Int.not_lt.2 (Int.mul_nonneg h0 (Int.le_of_lt hT)))
    · intro h; exact Int.mul_neg_of_neg_of_pos h hT
  have key : (2 * (x.natAbs * 10 ^ k) + n.natAbs) / (2 * n.natAbs)
      = (x.natAbs / n.natAbs) * 10 ^ k
        + (2 * (x.natAbs % n.natAbs) * 10 ^ k + n.natAbs) / (2 * n.natAbs) := by
    generalize x.natAbs = ax, n.natAbs = an at *
    generalize hA : ax / an = A
    generalize hR : ax % an = R
    have hd : an * A + R = ax := by rw [← hA, ← hR]; exact Nat.div_add_mod ax an
    subst hd
    have : 2 * ((an * A + R) * 10 ^ k) + an
        = (2 * R * 10 ^ k + an) + 2 * an * (A * 10 ^ k) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
      omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.add_comm]
  unfold roundDivInt? decimalDivHalfAway
  simp only [hn, ite_false, habs, hsign, key]

/-! ## Strings: `string_positions` -/

/-- Does `t` occur in `cs`? What `str.find` being not NULL says
(polars-strpos). -/
def occurs (t : List Char) : List Char → Bool
  | [] => t.isPrefixOf []
  | c :: cs => t.isPrefixOf (c :: cs) || occurs t cs

/-- The characters of the first part of `s.str.split(t)`: those before the
first `t`, or all of them (polars-strpos). -/
def splitFirstLen (t : List Char) : List Char → Nat
  | [] => 0
  | c :: cs => if t.isPrefixOf (c :: cs) then 0 else splitFirstLen t cs + 1

/-- `strpos_chars`: 1 for an empty `t`, 0 where `t` does not occur, else one
more than the characters before it. -/
def strposChars (s t : String) : Int :=
  if t.toList = [] then 1
  else if !occurs t.toList s.toList then 0
  else splitFirstLen t.toList s.toList + 1

theorem findFrom_eq (t : List Char) : ∀ (cs : List Char) (i : Nat),
    Text.findFrom t cs i = if occurs t cs then some (i + splitFirstLen t cs) else none
  | [], i => by
    unfold Text.findFrom
    by_cases hp : t.isPrefixOf [] <;> simp [occurs, splitFirstLen, hp]
  | c :: cs, i => by
    unfold Text.findFrom
    by_cases hp : t.isPrefixOf (c :: cs)
    · simp [occurs, splitFirstLen, hp]
    · simp only [hp, ite_false, Bool.false_eq_true, occurs, splitFirstLen, Bool.false_or]
      rw [findFrom_eq t cs (i + 1)]
      split <;> simp; omega

/-- **`Polars.strpos_chars`**: the shimmed position is the reference's
(`Text.strpos`), up to the size cap every position stays below. -/
theorem strpos_chars (s t : String) : Text.strpos s t = Text.capped (strposChars s t) := by
  unfold Text.strpos strposChars
  rw [findFrom_eq]
  by_cases he : t.toList = []
  · rw [he]
    cases hs : s.toList <;> simp [occurs, List.isPrefixOf, splitFirstLen]
  · simp only [he, ite_false]
    by_cases ho : occurs t.toList s.toList
    · simp [ho, Int.add_comm]
    · simp [ho]

/-- `substring_wrap`: a negative start counts from the end, in characters, as
a 1-based position (`negative_start` = `WRAP_FROM_END`). -/
def wrapStart (a : Int) (s : String) : Int := if a < 0 then a + s.length + 1 else a

/-- **`Polars.substring_wrap`**: the substring from the rewritten start is the
reference's (`Text.substrWrap`). -/
theorem substring_wrap (s : String) (a : Int) (n : Option Nat) :
    Text.substr s (wrapStart a s) n = Text.substrWrap s a n := rfl

/-! ## Sorts: `null_order` and `tie_order` -/

/-- Polars's `nulls_last` for a key (`SORT_DIRECTIONS`): as the key states,
and last for an `UNSPECIFIED` key (D8). Natively Polars puts NULLs first in
both directions (polars-null-order). -/
def nullsLast (k : SortKey) : Bool := if k.nullsOpen then true else !k.nullsFirst

/-- Polars's sort comparator for keys with `descending` and `nulls_last`
written per key: NULLs first unless `nulls_last`, the values by
`Value.le` (polars-null-order). -/
def sortWith (ks : List (SortKey × Bool)) : Row → Row → Bool :=
  sortLeWith Value.le (ks.map fun (k, last) => (k, !last))

/-- **`Polars.null_order`**: with each key's `nulls_last` written, Polars
orders rows as the reference (`sortLe`). -/
theorem null_order (ks : List SortKey) : sortWith (ks.map fun k => (k, nullsLast k)) = sortLe ks := by
  rw [← sortLeWith_le]
  unfold sortWith
  congr 1
  rw [List.map_map]
  congr 1
  funext k
  simp only [Function.comp, nullsLast, SortKey.firstNulls]
  cases k.nullsOpen <;> cases k.nullsFirst <;> rfl

/-- **`Polars.tie_order`**: Polars's sort with `maintain_order=True` is
stable (polars-sort-stability): its rows, each with its input position, are a
permutation of the input sorted by the keys and, among ties, by position
(`zipIdxLE`). Any such result is `Rel.eval`'s, `List.mergeSort`, for a total
preorder of the keys (`sortLe`'s, `sortLe_totalPre`). -/
theorem tie_order (le : Row → Row → Bool) (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b || le b a) (rows : List Row) (out : List (Row × Nat))
    (hperm : out.Perm rows.zipIdx) (hsorted : out.Pairwise fun a b => List.zipIdxLE le a b) :
    out.map (·.1) = rows.mergeSort le := by
  rw [← List.mergeSort_zipIdx]
  congr 1
  have hs := List.pairwise_mergeSort (List.zipIdxLE_trans htrans) (List.zipIdxLE_total htotal)
    rows.zipIdx (le := List.zipIdxLE le)
  have hp := List.mergeSort_perm rows.zipIdx (List.zipIdxLE le)
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_) hsorted hs (hperm.trans hp.symm)
  -- Two entries that tie both ways have one position, hence are one entry.
  have ha' := List.mem_zipIdx' (hperm.mem_iff.mp ha)
  have hb' := List.mem_zipIdx' (hp.mem_iff.mp hb)
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [List.zipIdxLE] at hab hba
  have h12 : a2 = b2 := by
    by_cases h1 : le a1 b1 <;> by_cases h2 : le b1 a1 <;> simp [h1, h2] at hab hba <;> omega
  subst h12
  simp only [Prod.mk.injEq, and_true]
  exact ha'.2.trans hb'.2.symm

/-! ## Guards: a precondition checked on the data -/

/-- `int_overflows`: the exact (128-bit) result leaves 64 bits. -/
def intOverflows (w : Int) : Bool := decide (w < FloatCode.minI64) || decide (FloatCode.maxI64 < w)

/-- **`Polars.int_overflows`**: the flag is the reference's `wraps` issue of
`+`, `-`, `*` (`BinFn.issue`). -/
theorem intOverflows_eq (w : Int) : intOverflows w = !inI64 w := by
  simp only [intOverflows, inI64, between]
  by_cases h1 : FloatCode.minI64 ≤ w <;> by_cases h2 : w ≤ FloatCode.maxI64 <;> simp [h1, h2] <;> omega

theorem int_overflows (f : BinFn) (hf : f = .add ∨ f = .sub ∨ f = .mul) (a b : Int) :
    intOverflows (match f with | .add => a + b | .sub => a - b | _ => a * b) =
      (f.issue (.int a) (.int b)).isSome := by
  rcases hf with rfl | rfl | rfl <;> simp only [BinFn.issue, wrapIf, intOverflows_eq] <;>
    split <;> simp_all

/-- `div_overflows`: `MIN / -1`. -/
def divOverflows (a b : Int) : Bool := a == FloatCode.minI64 && b == -1

/-- **`Polars.div_overflows`**: on 64-bit integers and a divisor that is not
zero, the flag is the reference's overflow of `/`. -/
theorem div_overflows {a b : Int} (ha : inI64 a = true) (hb : b ≠ 0) :
    divOverflows a b = (BinFn.idiv.issue (.int a) (.int b)).isSome := by
  simp only [inI64, between, Bool.and_eq_true, decide_eq_true_eq] at ha
  have hmin : FloatCode.minI64 = -(2 ^ 63) := rfl
  have hmax : FloatCode.maxI64 = 2 ^ 63 - 1 := rfl
  simp only [divOverflows, BinFn.issue, hb, ite_false]
  by_cases h : a = FloatCode.minI64 ∧ b = -1
  · obtain ⟨rfl, rfl⟩ := h
    decide
  · have hfit : inI64 (a.tdiv b) = true := by
      simp only [inI64, between, Bool.and_eq_true, decide_eq_true_eq]
      rw [hmin, hmax] at ha ⊢
      have hq := Int.natAbs_tdiv a b
      by_cases hb1 : b.natAbs = 1
      · rcases Int.natAbs_eq b with e | e <;> rw [hb1] at e <;> subst e
        · simp; omega
        · have : a ≠ -(2 ^ 63) := fun e => h ⟨by rw [hmin]; exact e, rfl⟩
          simp; omega
      · have h2 : 2 ≤ b.natAbs := by omega
        have : a.natAbs.div b.natAbs ≤ a.natAbs / 2 := Nat.div_le_div_left h2 (by omega)
        have : (a.tdiv b).natAbs ≤ 2 ^ 62 := by
          rw [hq]; change a.natAbs / b.natAbs ≤ _ at *; omega
        omega
    have hne : ¬ (a == FloatCode.minI64 && b == -1) = true := by simpa using h
    simp [hfit, hne]

/-- `zero_divisor`: a divisor of 0 for a value that is not NULL. -/
def zeroDivisor (v : Value) (b : Int) : Bool := v != .null && b == 0

/-- **`Polars.zero_divisor`**: the flag is the reference's division by zero of
integers (`BinFn.issue`). -/
theorem zero_divisor (f : BinFn) (hf : f = .idiv ∨ f = .imod) (a b : Int) :
    zeroDivisor (.int a) b = (f.issue (.int a) (.int b) == some .divByZero) := by
  rcases hf with rfl | rfl <;> by_cases h : b = 0 <;> simp [zeroDivisor, BinFn.issue, h] <;>
    split <;> simp [show (b == 0) = false from by simpa using h] <;> decide

/-- `sum_leaves_i64` of the exact (128-bit) sum. -/
def sumLeavesI64 (total : Int) : Bool := intOverflows total

/-- **`Polars.sum_leaves_i64`** (A3): the guard flags a group exactly where
the reference's integer `SUM` leaves 64 bits (`Measure.sumOk`, `sumWraps`). -/
theorem sum_leaves_i64 (m : Measure) (hm : m.sumDigits = none) (vs : List Int) :
    sumLeavesI64 (sum0 vs) = !m.sumOk (intSum (vs.map .int)) := by
  simp only [sumLeavesI64, intOverflows_eq, sum0, Measure.sumOk, hm, intSum_map_int]

/-- `sum_makes_nan`: a group holds both `+∞` and `-∞`. -/
def sumMakesNan (vs : List Value) : Bool :=
  vs.contains (.int FloatCode.posInf) && vs.contains (.int FloatCode.negInf)

/-- **`Polars.sum_makes_nan`** (B1): the guard flags a group exactly where the
reference's double `SUM` or `AVG` would make a NaN (`AggFn.makesNan`), which
it raises on; Polars gives NaN (polars-nonfinite-aggregates). -/
theorem sum_makes_nan (f : AggFn) (hf : f = .fsum ∨ f = .avg) (vs : List Value) :
    sumMakesNan vs = f.makesNan vs := by
  rcases hf with rfl | rfl <;> rfl

/-- `fractional_power_of_negative`: a negative base, `-∞` included, to a
finite power that is not a whole number (`x < 0`, `y` finite, `floor y ≠ y`). -/
def fractionalPowerOfNegative (x y : Int) : Bool :=
  decide (x < 0) && decide (FloatCode.negInf < y) && decide (y < FloatCode.posInf) &&
    FloatCode.floor y != y

/-- **`Polars.fractional_power_of_negative`**: on a double's code (none is
below `-∞`), the guard flags a row exactly where the reference's `power`
raises a domain error: a finite negative base (`nanCase`) or `-∞`
(`negInfPow`) to a finite non-integer power. Polars computes `x ** 0.5` as
`sqrt(x)`, NaN for `-∞`, where IEEE's `pow` gives `+∞`. -/
theorem fractional_power_of_negative {a : Int} (ha : FloatCode.negInf ≤ a) (b : Int) :
    fractionalPowerOfNegative a b = (BinFn.fpow.issue (.int a) (.int b) == some .domain) := by
  simp only [fractionalPowerOfNegative, BinFn.issue, negInfPow, nanIssue, nanCase]
  by_cases h1 : a = FloatCode.negInf
  · subst h1
    have : FloatCode.negInf < 0 := fp64.negInf_lt_zero
    by_cases hb1 : FloatCode.negInf < b <;> by_cases hb2 : b < FloatCode.posInf <;>
      by_cases hf : FloatCode.floor b = b <;> simp [*]
  · have h2 : FloatCode.negInf < a := by omega
    by_cases h0 : a < 0 <;> by_cases hb1 : FloatCode.negInf < b <;>
      by_cases hb2 : b < FloatCode.posInf <;> by_cases hf : FloatCode.floor b = b <;> simp [*]

/-- `makes_infinite`: finite arguments, an infinite result (`is_finite`,
`is_infinite` on codes). -/
def makesInfinite (y : Int) (xs : List Int) : Bool := xs.all isFiniteCode && isInfCode y

/-- **`Polars.makes_infinite`** (A4): Polars's IEEE operations are Lean's
native ones (`lift₂`), so the guard flags a row exactly where the reference's
overflow to `±∞` does (`BinFn.infIssue`). -/
theorem makes_infinite (f : BinFn) (hf : f.makesInf = true) (a b : Int) :
    makesInfinite (match (f.apply (.int a) (.int b)) with | .int r => r | _ => 0) [a, b] =
      (f.infIssue (.int a) (.int b)).isSome := by
  have hf' : f = .fadd ∨ f = .fsub ∨ f = .fmul ∨ f = .fdiv ∨ f = .fpow := by
    cases f <;> simp_all [BinFn.makesInf]
  rcases hf' with rfl | rfl | rfl | rfl | rfl <;>
    simp [BinFn.infIssue, makesInfinite, BinFn.apply, BinFn.makesInf, Bool.and_assoc] <;>
    split <;> simp_all

/-- `agg_makes_infinite`: finite values, an infinite aggregate. -/
def aggMakesInfinite (result : Value) (vs : List Value) : Bool :=
  vs.all finiteValue && isInfValue result

/-- **`Polars.agg_makes_infinite`** (A4): on the aggregate the reference
computes, the guard flags a group exactly where `Measure.makesInf` does.
Polars sums in its own order (`sum_order = ANY`, polars-sum-float), so on
Polars it flags the groups whose own sum overflows: the same groups but at
the edge, where one order's rounding overflows and another's does not. -/
theorem agg_makes_infinite (m : Measure) (hm : m.fn.infAgg = true) (grp : Relation) :
    aggMakesInfinite (m.eval grp) (m.inputs grp) = m.makesInf grp := by
  simp [aggMakesInfinite, Measure.makesInf, hm, Bool.and_comm]

/-! ## The error side: no shim for a verified plan -/

/-- Polars's integer `+`, `-`, `*` wrap around (polars-int-arith). -/
def wrap64 (x : Int) : Int := (x + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

theorem wrap64_of_inI64 {x : Int} (h : inI64 x = true) : wrap64 x = x := by
  simp only [inI64, between, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmin : FloatCode.minI64 = -(2 ^ 63) := rfl
  have hmax : FloatCode.maxI64 = 2 ^ 63 - 1 := rfl
  unfold wrap64; omega

/-- **Polars as the translation writes it**, on the functions of the slice:
integer `+ - *` wrap (polars-int-arith), integer `/` and `%` by zero are
NULL and otherwise the shims `int_div_trunc` and `int_mod_trunc` of the
floored ones (polars-int-divide, polars-int-modulus), and double operations
are IEEE's, NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞` (polars-double-arith); every
other function is the reference's. -/
def bin : BinFn → Value → Value → Value
  | .add, .int a, .int b => .int (wrap64 (a + b))
  | .sub, .int a, .int b => .int (wrap64 (a - b))
  | .mul, .int a, .int b => .int (wrap64 (a * b))
  | .idiv, .int a, .int b => if b = 0 then .null else .int (intDivTrunc a b)
  | .imod, .int a, .int b => if b = 0 then .null else .int (intModTrunc a b)
  | f, .int a, .int b =>
    if nanCase f a b then .int FloatCode.nan else f.apply (.int a) (.int b)
  | f, v, w => f.apply v w

def written : Impl := ⟨UnFn.apply, bin⟩

/-- **`Polars.written_faithful`**: Polars, with the value shims, agrees with
the reference wherever the reference reports no issue. Its own values
elsewhere (a wrapped integer, NULL for a zero divisor, NaN, `±∞`) are on the
error side, where a verified plan does not go. -/
theorem nanCase_issue {f : BinFn} {a b : Int} (hn : nanCase f a b = true) :
    f.issue (.int a) (.int b) ≠ none := by
  cases f <;> simp only [nanCase, Bool.false_eq_true] at hn <;>
    simp only [BinFn.issue, nanIssue, nanCase] at * <;> (try split) <;> simp_all

theorem written_faithful : written.Faithful := by
  refine ⟨fun _ _ _ => rfl, fun f v w h => ?_⟩
  show bin f v w = f.apply v w
  cases v <;> cases w <;> (try (cases f <;> rfl))
  rename_i a b
  have hfloat : bin f (.int a) (.int b) =
      (if nanCase f a b then .int FloatCode.nan else f.apply (.int a) (.int b)) ∨
      f = .add ∨ f = .sub ∨ f = .mul ∨ f = .idiv ∨ f = .imod := by
    cases f <;> simp [bin]
  rcases hfloat with he | rfl | rfl | rfl | rfl | rfl
  · rw [he]
    have : nanCase f a b = false := by
      cases hn : nanCase f a b
      · rfl
      · exact absurd h (nanCase_issue hn)
    simp [this]
  all_goals simp only [BinFn.issue, wrapIf] at h
  · simp only [bin, BinFn.apply]; split at h <;> simp_all [wrap64_of_inI64]
  · simp only [bin, BinFn.apply]; split at h <;> simp_all [wrap64_of_inI64]
  · simp only [bin, BinFn.apply]; split at h <;> simp_all [wrap64_of_inI64]
  · simp only [bin, BinFn.apply]
    split
    · rfl
    · rename_i hb; rw [int_div_trunc a hb]
  · simp only [bin, BinFn.apply]
    split
    · rfl
    · rename_i hb; rw [int_mod_trunc a hb]

end Substrait.Polars

namespace Substrait

/-- **A verified plan runs on Polars.** When `Rel.mayIssues` reports nothing
but assumed issues (whose guards the translation keeps), on every catalog
that satisfies the preconditions, Polars as the translation writes it, run
without its other guards, gives `Rel.eval`'s rows. -/
theorem Rel.polars_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.Sound cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat Polars.written = r.eval cat :=
  Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm Polars.written_faithful

end Substrait
