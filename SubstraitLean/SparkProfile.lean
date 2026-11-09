import SubstraitLean.SparkShims

/-!
# Spark's profile (#271, #739)

`Profile.spark` states what Spark 4.3.0 computes under
`sverify_spark.dialect.SPARK_CONF` (ANSI mode on), as its facts record it
(`engines/spark/facts/`): a diff against the reference, `sparkBin` and
`sparkUn`, as DuckDB's profile is (`DuckDBProfile.lean`). It is an engine
fact, a sibling of the reference: no profile refines another
(`docs/core-semantics.md`, "Terminology").

Where Spark differs, by its facts:

* `∞ - ∞`, `0 · ∞`, `∞ / ∞` and `fmod(±∞, y)` are NaN, where the reference
  raises (spark-double-arith, spark-double-divide, spark-double-modulus).
* `/` by a zero raises `DIVIDE_BY_ZERO` under ANSI, also where a plan asks
  for IEEE division (spark-double-divide).
* `power` is `StrictMath.pow`: a negative finite base to a finite power that
  is not an integer is NaN, `(-∞) ^ y` is `+∞` or `0` (spark-math-domain).
* The elementary functions are NaN outside their domains (`sqrt(-1)`,
  `asin(2)`, `sin(±∞)`); the logarithms of `x ≤ 0`, `-0.0` included, are
  NULL (spark-math-domain).
* `floor` and `ceil` return a `BIGINT`: `±∞` and values past 64 bits raise
  `ARITHMETIC_OVERFLOW` (spark-round, spark-floor-ceil-bigint). A rounded
  negative value that reaches zero is `0.0` (`round_zero_sign` = `POSITIVE`),
  the reference's `eval`.
* `<<` and `>>` take the count modulo 64 (spark-int-shift), where the
  reference raises outside `[0, 64)`.
* `power(±1, ±∞)` and `power(1, NaN)` are NaN (`StrictMath.pow`), where C's
  `pow` gives `1` (`pow_one_inf`, D40); `floor` and `ceil` of NaN are `0`, a
  `BIGINT` (`float_to_int`). The writer refuses double `power` and passes NaN
  through `floor` and `ceil` (`Profile.sparkWritten`).

* `atan2` adds `0.0` to its arguments, so `-0.0` is `0.0`: `atan2(-0.0, -1)`
  is `π`, and `atan2(0, 0)` is `0` (`zero_sign`, `on_domain_error`). The
  writer refuses double `atan2`.

Integer arithmetic, `div` and `%` raise where the reference raises
(spark-int-arith, spark-int-divide, spark-int-modulus): no diff. Functions
the facts do not cover are taken to be the reference's.

Every value Spark gives where the reference's differs is in the scope of an
option Spark's table allows (`Profile.spark_withinOk`, `Engine.lean`).
-/

namespace Substrait

/-- Spark's `power` of doubles (`StrictMath.pow`) where it differs from the
reference: `(-∞) ^ y` for a finite `y` that is not an integer is `+∞` for
`y > 0` and `0` for `y < 0`, and a negative finite base to such a power is
NaN; the reference raises on both. -/
def sparkPow (a b : Int) : Option Outcome :=
  if negInfPow a b then some (.ok (.float (if 0 < b then FloatCode.posInf else 0)))
  else if nanCase .fpow a b then some (.ok (.float FloatCode.nan))
  -- `power(±1, ±∞)` and `power(1, NaN)`: NaN, where C's `pow` gives `1`
  -- (`pow_one_inf` = `NAN`, D40).
  else if powOneInf a b then some (.ok (.float FloatCode.nan)) else none

/-- **Spark's binary functions** on non-NULL arguments where they differ from
the reference (`none`: as the reference). Doubles: IEEE's NaN where the
reference raises on a created NaN, and no IEEE division. Integers: the
shifts take the count modulo 64. -/
def sparkBin : BinFn → Value → Value → Option Outcome
  | .fadd, .float a, .float b => if nanCase .fadd a b then some (.ok (.float FloatCode.nan)) else none
  | .fsub, .float a, .float b => if nanCase .fsub a b then some (.ok (.float FloatCode.nan)) else none
  | .fmul, .float a, .float b => if nanCase .fmul a b then some (.ok (.float FloatCode.nan)) else none
  -- A zero divisor raises, as the reference's does.
  | .fdiv, .float a, .float b => if nanCase .fdiv a b then some (.ok (.float FloatCode.nan)) else none
  | .fmod, .float a, .float b => if nanCase .fmod a b then some (.ok (.float FloatCode.nan)) else none
  -- No IEEE division: a zero divisor raises `DIVIDE_BY_ZERO`.
  | .fdivIeee, .float a, .float b =>
    if FloatCode.canon b = 0 then some (.error .divByZero)
    else if nanCase .fdiv a b then some (.ok (.float FloatCode.nan)) else none
  | .fpow, .float a, .float b => sparkPow a b
  -- Spark adds `0.0` to both arguments, so `-0.0` is `0.0` (spark-math-domain):
  -- `atan2(0, 0)` is `0`, and `atan2(-0.0, -1)` is `π` (`zero_sign`).
  | .fatan2, .float a, .float b =>
    if FloatCode.canon a = 0 ∧ FloatCode.canon b = 0 then some (.ok (.float 0))
    else if a = FloatCode.negZero ∨ b = FloatCode.negZero then
      some (.ok (.float (FloatCode.lift₂ Float.atan2 (FloatCode.canon a) (FloatCode.canon b))))
    else none
  -- Java's `<<` and `>>` on a `BIGINT` read the count's low six bits.
  | .bit .shl, .int a, .int b =>
    if 0 ≤ b ∧ b < 64 then none else some (.ok (.int ((BitVec.ofInt 64 a) <<< (b % 64).toNat).toInt))
  | .bit .shr, .int a, .int b =>
    if 0 ≤ b ∧ b < 64 then none
    else some (.ok (.int ((BitVec.ofInt 64 a).sshiftRight (b % 64).toNat).toInt))
  | _, _, _ => none

/-- A logarithm (`ln`, `log10`, `log2`), which Spark makes NULL at `x ≤ 0`. -/
def FMath.sparkNull : FMath → Bool
  | .ln | .log10 | .log2 => true
  | _ => false

/-- **Spark's unary functions** on non-NULL arguments where they differ from
the reference: an elementary function outside its domain is NaN, or NULL for
a logarithm (Hive's rule); `floor` and `ceil` of `±∞`, or past 64 bits,
raise `ARITHMETIC_OVERFLOW`, as their `BIGINT` result overflows. -/
def sparkUn : UnFn → Value → Option Outcome
  | .fmath f, .float x =>
    if f.apply x = none then some (.ok (if f.sparkNull then .null else .float FloatCode.nan)) else none
  -- A `BIGINT` (`float_to_int`): NaN is `0`; `±∞`, and a value whose floor
  -- or ceiling leaves 64 bits (no double strictly between `2⁶³ - 1` and
  -- `2⁶³`), overflow.
  | .ffloor, .float x | .fceil, .float x =>
    if FloatCode.canon x = FloatCode.nan then some (.ok (.float 0))
    else if isInfCode x ∨ (FloatCode.ofInt (2 ^ 63) ≤ x ∧ x < FloatCode.posInf) ∨
        (FloatCode.negInf < x ∧ x < FloatCode.ofInt (-(2 ^ 63)))
    then some (.error .overflow) else none
  | _, _ => none

/-- **Spark's profile**: what Spark 4.3.0 computes under ANSI, as a diff
against the reference (`sparkBin`, `sparkUn`). -/
def Profile.spark : Profile where
  un f v := (sparkUn f v).getD (Profile.reference.un f v)
  bin f v w := (sparkBin f v w).getD (Profile.reference.bin f v w)

/-- `floor` and `ceil`, which the writer computes as the reference does
(`sverify_spark.dialect`: NaN, `±∞` and doubles of `2⁵²` and more pass
through, the rest through `BIGINT` and back). -/
def UnFn.sparkWritten : UnFn → Bool
  | .ffloor | .fceil => true
  | _ => false

/-- `power` and `atan2` of doubles, which the writer refuses (Spark's are
Java's, within an ulp of C's, spark-elem-rounding): a plan with them does not
run on Spark. -/
def BinFn.sparkWritten : BinFn → Bool
  | .fpow | .fatan2 => true
  | _ => false

/-- Spark's profile with the functions of `UnFn.sparkWritten` and
`BinFn.sparkWritten` as the writer writes them: the reference's. What a plan
written for Spark computes there (`Engine.spark`). -/
def Profile.sparkWritten : Profile where
  un f := if f.sparkWritten then Profile.reference.un f else Profile.spark.un f
  bin f := if f.sparkWritten then Profile.reference.bin f else Profile.spark.bin f


-- Spark adds `0.0` to `atan2`'s arguments: `atan2(-0.0, -1)` is `+π` there,
-- `-π` in the reference (`atan2?`), and `atan2(-0.0, 1)` is `+0.0`.
#guard match sparkBin .fatan2 (.float FloatCode.negZero) (.float FloatCode.negOne) with
  | some (.ok (.float c)) => c == FloatCode.ofFloat 3.141592653589793
  | _ => false
#guard match sparkBin .fatan2 (.float FloatCode.negZero) (.float FloatCode.one) with
  | some (.ok (.float c)) => c == 0
  | _ => false

end Substrait
