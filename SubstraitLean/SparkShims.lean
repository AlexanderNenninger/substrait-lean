import Sverify.Polars.Shims

/-!
# The reference on Spark: the shims, proved (#739)

The translation from the reference to Spark 4.3.0 is Spark SQL written by
`sverify_spark.dialect` under `SPARK_CONF` (ANSI mode on). Where Spark's value
differs from the reference's on the reference's non-raising domain, the
writer writes a shim; where Spark raises or gives its own value only where
the reference raises (the error side), it writes nothing. This module states
what Spark does for each, as its facts record it
(`engines/spark/facts/`), and proves once, per shim, that the
shimmed expression gives the reference's value. The lemmas are named as the
shims of `Profile.spark.obs` (`EngineTables.lean`): `Spark.<name>`, or, for a
shim another engine writes the same way, `Shim.<name>` (`engines/Sverify/Engines/Shims.lean`).

**Trusted**: the model of Spark's own functions (`Spark.bin` below; the sort
`Shim.sortWith`, the `DECIMAL(38,0)` sum `Shim.sumEmptyNull`), each from its
fact.

* `int_sum_decimal` (spark-sum-int): Spark adds a `BIGINT` `SUM` in `BIGINT`
  and, under ANSI, raises as soon as a partial sum leaves 64 bits, which
  depends on the order of the rows. The writer sums `DECIMAL(38,0)` values
  and checks the total: no partial sum of fewer than 10¹⁸ 64-bit values
  leaves 38 digits, in any order (`Spark.partial_sums_fit`), so the decimal
  sum is the exact total, the reference's `SUM` (`Shim.sum_empty_null`).
* `int_avg_decimal` (spark-avg-int): Spark's `avg` of integers is a double.
  The writer divides the exact decimal sum by the count with `div`, which
  truncates: the reference's `AVG` of integers (`Shim.avg_trunc`).
* `null_order` (spark-null-order): Spark puts NULLs first in an ascending
  key; the writer states the placement on every key (`Shim.null_order`).
* `one_zero` (spark-zero-sign, spark-zero-order): `-0.0` as `0.0` where a
  result's zero is observed (`Dialect.canon`, `Shim.one_zero`).
* `decimal_negate_sub` (spark-decimal-negate, SP-1): Spark's `-x` rounds a
  decimal past 34 significant digits; the writer negates as `0 - x` there,
  exact where its type keeps the scale, and refuses the rest.
* Error side: under ANSI, integer `+ - *` and `MIN div -1` raise where the
  reference raises (spark-int-arith, spark-int-divide); a zero divisor
  raises; `0 · ∞`, `∞ - ∞` and `sqrt(-1)` are NaN (spark-double-arith,
  spark-math-domain); `date_add` wraps past 2³¹ days (SP-2). None needs a
  shim: `Spark.written_faithful`, hence `Rel.spark_sound`, as
  `Rel.polars_sound` is for Polars.
-/

namespace Substrait.Spark

/-! ## Aggregates: `SUM` and `AVG` of integers -/

/-- `|x| ≤ 2⁶³` for a 64-bit integer. -/
theorem natAbs_le_of_inI64 {x : Int} (h : inI64 x = true) : x.natAbs ≤ 2 ^ 63 := by
  simp only [inI64, between, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmin : FloatCode.minI64 = -(2 ^ 63) := rfl
  have hmax : FloatCode.maxI64 = 2 ^ 63 - 1 := rfl
  omega

/-- A sum of 64-bit integers is at most `n · 2⁶³` in absolute value. -/
theorem natAbs_sum_le : ∀ vs : List Int, (∀ x ∈ vs, inI64 x = true) →
    vs.sum.natAbs ≤ vs.length * 2 ^ 63
  | [], _ => by simp
  | v :: vs, h => by
    have hv := natAbs_le_of_inI64 (h v (List.mem_cons_self ..))
    have ih := natAbs_sum_le vs fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.sum_cons, List.length_cons]
    have := Int.natAbs_add_le v vs.sum
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **`Spark.partial_sums_fit`**: every sum of some of the values (a partial
sum, in whatever order the tasks add and merge them, is the sum of a
sublist) of fewer than 10¹⁸ 64-bit integers fits `DECIMAL(38,0)`. So
Spark's decimal `SUM` never raises on them and is exact. -/
theorem partial_sums_fit {vs : List Int} (hv : ∀ x ∈ vs, inI64 x = true)
    (hn : vs.length < 10 ^ 18) {ws : List Int} (hs : ws.Sublist vs) :
    ws.sum.natAbs < 10 ^ 38 := by
  have h1 := natAbs_sum_le ws fun x hx => hv x (hs.subset hx)
  have h2 := hs.length_le
  have h3 : ws.length * 2 ^ 63 < 10 ^ 18 * 2 ^ 63 := Nat.mul_lt_mul_of_pos_right (by omega) (by decide)
  have h4 : (10 : Nat) ^ 18 * 2 ^ 63 < 10 ^ 38 := by decide
  omega

/-! ## Decimals: `-x` past 34 digits (SP-1) -/

/-- Spark's `-x` of a decimal, on its unscaled value `u`: exact below 34
significant digits, past them rounded to 34 by some `r`
(spark-decimal-negate, SP-1). `abs` negates a negative value the same way. -/
def negate (r : Int → Int) (u : Int) : Int := if u.natAbs < 10 ^ 34 then -u else r (-u)

/-- Spark's `0 - x` with `0` a `DECIMAL(1, 0)`: exact where its type keeps
the scale, up to 37 digits, or 38 at scale 6 or less (spark-decimal-negate). -/
def subZero (u : Int) : Int := 0 - u

/-- `decimal_negate_sub`, the writer's negation of a `DECIMAL(p, s)`: `-x`
up to 34 digits, `0 - x` past them where its type keeps the scale, refused
(`none`) otherwise. -/
def decimalNegate (r : Int → Int) (p s : Nat) (u : Int) : Option Int :=
  if p ≤ 34 then some (negate r u) else if p ≤ 37 ∨ s ≤ 6 then some (subZero u) else none

/-- **`Spark.decimal_negate_sub`**: on a value of a `DECIMAL(p, s)`, the
shimmed negation is the reference's, `-u`, however Spark rounds past 34
digits; it is refused exactly at 38 digits past scale 6. -/
theorem decimal_negate_sub (r : Int → Int) {p s : Nat} {u : Int} (hu : u.natAbs < 10 ^ p) :
    decimalNegate r p s u = if p ≤ 37 ∨ s ≤ 6 then some (-u) else none := by
  unfold decimalNegate negate subZero
  by_cases hp : p ≤ 34
  · have h34 : u.natAbs < 10 ^ 34 :=
      Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) hp)
    have h37 : p ≤ 37 ∨ s ≤ 6 := .inl (by omega)
    simp [hp, h34, h37]
  · by_cases h : p ≤ 37 ∨ s ≤ 6 <;> simp [hp, h]

/-! ## The error side: no shim for a verified plan -/

/-- Spark's `date_add(d, CAST(n AS INT))`: the days added as 32-bit `int`s,
wrapping past 2³¹ - 1 (SP-2); a count outside `INT` fails the cast (ANSI),
modelled as NULL. -/
def wrap32 (x : Int) : Int := (x + 2 ^ 31) % 2 ^ 32 - 2 ^ 31

variable [Boxes.Ambient]
/-- **Spark as the writer writes it, under ANSI**, on the functions of the
slice: integer `+ - *` raise past 64 bits (spark-int-arith), integer `div`
truncates and raises at a zero divisor and `MIN div -1` (spark-int-divide),
`%` truncates and raises at a zero divisor (spark-int-modulus), doubles are
IEEE's with NaN for `∞ - ∞`, `0 · ∞`, `∞ / ∞` (spark-double-arith), and
`date_add` wraps at 2³¹ days (spark-date-range). A raise is modelled as NULL:
the theorem below needs only that it happens where the reference raises.
Every other function is the reference's. -/
def bin : BinFn → Value → Value → Value
  | .add, .int a, .int b => if inI64 (a + b) then .int (a + b) else .null
  | .sub, .int a, .int b => if inI64 (a - b) then .int (a - b) else .null
  | .mul, .int a, .int b => if inI64 (a * b) then .int (a * b) else .null
  | .idiv, .int a, .int b => if b = 0 then .null else if inI64 (a.tdiv b) then .int (a.tdiv b) else .null
  | .imod, .int a, .int b => if b = 0 then .null else .int (a.tmod b)
  | .dateAdd, .date a, .int b =>
    if -2 ^ 31 ≤ b ∧ b < 2 ^ 31 then .date (wrap32 (a + b)) else .null
  | f, .float a, .float b =>
    if nanCase f a b then .float FloatCode.nan else f.apply (.float a) (.float b)
  | f, v, w => f.apply v w

def written : Impl := ⟨UnFn.apply, bin⟩

omit [Boxes.Ambient] in
theorem wrap32_of_small {x : Int} (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) : wrap32 x = x := by
  unfold wrap32; omega

/-- **`Spark.written_faithful`**: Spark under ANSI, as the writer writes it,
agrees with the reference wherever the reference reports no issue. Its
raises and its own values elsewhere (NaN, a wrapped date) are on the error
side, where a verified plan does not go. -/
theorem written_faithful : written.Faithful := by
  refine ⟨fun _ _ _ => rfl, fun f v w h => ?_⟩
  show bin f v w = f.apply v w
  unfold bin
  split
  · simp only [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?, wrapIf] at h
    split at h <;> simp_all [BinFn.apply]
  · simp only [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?, wrapIf] at h
    split at h <;> simp_all [BinFn.apply]
  · simp only [BinFn.issue, wrapNum, BinFn.apply, Value.numOf?, wrapIf] at h
    split at h <;> simp_all [BinFn.apply]
  · rename_i a b
    simp only [BinFn.issue] at h
    by_cases hb : b = 0 <;> by_cases hi : inI64 (a.tdiv b) = true <;> simp_all [BinFn.apply]
  · rename_i a b
    simp only [BinFn.issue] at h
    by_cases hb : b = 0 <;> simp_all [BinFn.apply]
  · rename_i a b
    simp only [BinFn.issue, rangeIssue] at h
    split at h
    · rename_i hr
      simp only [between, Bool.and_eq_true, decide_eq_true_eq] at hr
      have h1 : Time.dayMin = -719162 := rfl
      have h2 : Time.dayMax = 2932896 := rfl
      have hb : -2 ^ 31 ≤ b ∧ b < 2 ^ 31 := by omega
      simp only [BinFn.apply, hb, and_self, ite_true]
      rw [wrap32_of_small (by omega) (by omega)]
    · simp at h
  · rename_i a b
    have : nanCase f a b = false := by
      cases hn : nanCase f a b
      · rfl
      · exact absurd h (Polars.nanCase_issue hn)
    simp [this]
  · rfl

end Substrait.Spark

namespace Substrait

variable [Boxes.Ambient]
/-- **A verified plan runs on Spark.** When `Rel.mayIssues` reports nothing
but assumed issues (whose guards the writer keeps), on every catalog that
satisfies the preconditions, Spark under ANSI as the writer writes it gives
`Rel.eval`'s rows. -/
theorem Rel.spark_sound {cat : Catalog} (hcat : cat.WF) {A : String → List AVal}
    {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsmall : r.Small cat) (hs : r.looseSub = true)
    (hm : (r.mayIssues cat A F T false).all (·.1.assumed) = true) :
    r.eval cat Spark.written = r.eval cat :=
  Rel.guardFree_sound hcat hA hF hT hwf hsmall hs hm Spark.written_faithful

end Substrait
