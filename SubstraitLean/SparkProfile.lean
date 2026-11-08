import SubstraitLean.SparkShims

/-!
# Spark as a profile (#739)

`Profile.spark` is the semantics a plan verified with
`verify(semantics="spark")` is checked under: what Spark 4.3.0 computes under
`sverify.sql.spark.SPARK_CONF` (ANSI mode on), as its facts record it
(`characterization/spark/facts/`), on the options where sverify models
Spark's own choice, and the reference elsewhere (D21, `docs/engine-profiles.md`,
"Spark as a profile"):

* `±∞`: a double that overflows is `±∞` (spark-double-arith), with no
  precondition, as under DuckDB's and Polars's profiles.
* The error side stays the reference's. Under ANSI, Spark raises where the
  reference raises (integer overflow, a zero divisor, a bad cast); where it
  gives a value of its own instead (NaN from `∞ - ∞`, NULL from `ln(0)`, a
  `date_add` past 2³¹ days), the reference raises, so a verified plan never
  reaches it (`Spark.written_faithful`).
* Every value-side option is the reference's: no Spark choice is stated in a
  plan, and the writer's shims (`SparkShims.lean`) realize the reference's
  where Spark's own differs (a `BIGINT` `SUM`, an integer `AVG`, the NULL
  placement, the sign of zero).

So `Profile.spark` evaluates as the reference does, and a plan the checker
proves under the reference is proved under Spark's profile as it is:
`Profile.spark_eval`. What the profile adds is the route: a plan verified
with `semantics="spark"` runs on Spark natively, and Spark's choices
(`Profile.spark.table`) refine the core (`Rel.allowed_spark_core`).
-/

namespace Substrait

/-- **Spark's profile**: the reference's functions, raising where it raises. -/
def Profile.spark : Profile := Profile.reference

/-- Under Spark's profile an expression evaluates as under the reference. -/
theorem Profile.spark_eval (e : Expr) (row : Row) :
    e.evalP Profile.spark row = e.evalP Profile.reference row := rfl

/-! ## What Spark computes (#271, #1189)

`Profile.sparkRun` is Spark 4.3.0 under `SPARK_CONF` (ANSI mode on), function by
function, as `characterization/spark/facts/` records it: the profile a plan
lowered for Spark runs under (`Engine.spark`), an engine fact where
`Profile.spark` above is the semantics a user verifies under. It states the
arithmetic core (#271 S1); every other function is an error, with its exit
(`Spark.exitUn`, `Spark.exitBin`): refused on Spark, or stated by a later
stage (S2 temporal, S3 strings, S4 decimals and rounding). Nothing is taken
from the reference unprobed. -/

namespace Spark

/-- A zero result with IEEE's sign: `-0.0` where `neg` (spark-zero-sign). -/
def signedZero (neg : Bool) (r : Int) : Int := if r = 0 ∧ neg = true then FloatCode.negZero else r

/-- `0.0` or `-0.0`. -/
def isZeroCode (c : Int) : Bool := c == 0 || c == FloatCode.negZero

/-- The binary functions of the arithmetic core. -/
def coreBin : BinFn → Bool
  | .add | .sub | .mul | .eq | .lt | .and | .or | .fadd | .fsub | .fmul | .fdiv | .fmod
  | .idiv | .imod | .bit _ | .greatest | .least => true
  | _ => false

/-- The unary functions of the arithmetic core. -/
def coreUn : UnFn → Bool
  | .not | .isNull | .neg | .itof | .fneg | .ftoi | .narrow _ | .isNum _ | .raise _
  | .fmath .sqrt => true
  | _ => false

/-- Spark's binary functions:
* `+ - * /` of doubles are IEEE's, NaN where `nanCase` (spark-double-arith), with
  IEEE's two zeros (`-0.0 + -0.0`, `-0.0 - 0.0`, a zero product or quotient of
  operands of different signs: spark-zero-sign);
* `/` and `%` of doubles raise at a zero divisor (spark-double-divide,
  spark-double-modulus), `%` is C's `fmod` (`FloatCode.fmod`: NaN for an infinite
  dividend, the dividend for an infinite divisor) with the dividend's sign;
* `<<` and `>>` of a count outside 0–63 take it modulo 64 (spark-int-shift),
  which no choice of `shift_range` states: open (an error), where the
  reference raises too;
* integer `+ - * div %` raise where the reference raises (spark-int-arith,
  spark-int-divide, spark-int-modulus), and the comparisons, `AND`, `OR`,
  `GREATEST`, `LEAST` are the reference's (spark-kleene, spark-nan-equality,
  spark-nan-order, spark-zero-order).
A NaN Spark creates has the platform's sign (spark-nan-sign); the model's one
NaN stands for it, the sign being `nan_kind`'s. -/
def runBin : BinFn → Value → Value → Outcome
  | .fadd, .float a, .float b => .ok (.float (if nanCase .fadd a b then FloatCode.nan
      else signedZero (a == FloatCode.negZero && b == FloatCode.negZero) (FloatCode.fadd a b)))
  | .fsub, .float a, .float b => .ok (.float (if nanCase .fsub a b then FloatCode.nan
      else signedZero (a == FloatCode.negZero && b == 0) (FloatCode.fsub a b)))
  | .fmul, .float a, .float b => .ok (.float (if nanCase .fmul a b then FloatCode.nan
      else signedZero (decide (a < 0) != decide (b < 0)) (FloatCode.fmul a b)))
  | .fdiv, .float a, .float b =>
    if isZeroCode b then .error .divByZero
    else .ok (.float (if nanCase .fdiv a b then FloatCode.nan
      else signedZero (decide (a < 0) != decide (b < 0)) (FloatCode.fdiv a b)))
  | .fmod, .float a, .float b =>
    if isZeroCode b then .error .divByZero
    else .ok (.float (signedZero (decide (a < 0)) (FloatCode.fmod a b)))
  -- A count outside 0–63 is taken modulo 64 (spark-int-shift), a value no
  -- choice of `shift_range` states: open, where the reference raises.
  | .bit .shl, .int a, .int b =>
    if 0 ≤ b ∧ b < 64 then Profile.reference.bin (.bit .shl) (.int a) (.int b) else .error .domain
  | .bit .shr, .int a, .int b =>
    if 0 ≤ b ∧ b < 64 then Profile.reference.bin (.bit .shr) (.int a) (.int b) else .error .domain
  | f, v, w => if coreBin f then Profile.reference.bin f v w else .error .raised

/-- Spark's unary functions: `-x` of a double flips the sign of zero
(spark-zero-sign); `sqrt` is NaN for a negative (spark-math-domain). Where
Spark's value is one no option of the core states (`-NaN`, the saturation of
`CAST(2⁶³ AS BIGINT)`) or no fact records (`sqrt(-0.0)`), the call is open: an
error, so nothing is claimed. The others of the core are the
reference's (spark-kleene, spark-is-null, spark-bigint-to-double, spark-int-arith,
`isNum` as `x IS NOT NULL`, `raise` as `raise_error`). -/
def runUn : UnFn → Value → Outcome
  | .fneg, .float a =>
    -- `-NaN` flips the sign bit (spark-nan-sign), which `fp.neg` has no option
    -- for: open.
    if a = FloatCode.nan ∨ a = FloatCode.negNan then .error .raised
    else .ok (.float (if a = 0 then FloatCode.negZero else if a = FloatCode.negZero then 0
      else FloatCode.neg a))
  | .fmath .sqrt, .float a =>
    -- `sqrt(-0.0)` is not probed on Spark: open.
    if a = FloatCode.negZero then .error .raised
    else if a < 0 ∧ a ≠ FloatCode.negNan then .ok (.float FloatCode.nan)
    else Profile.reference.un (.fmath .sqrt) (.float a)
  | .ftoi, .float a =>
    -- `2⁶³` saturates to `2⁶³ - 1` (spark-cast-double-to-int), which no cast
    -- option states: open, where the reference raises.
    if a = FloatCode.ofInt (2 ^ 63) then .error .badCast
    else Profile.reference.un .ftoi (.float a)
  | f, v => if coreUn f then Profile.reference.un f v else .error .raised

end Spark

/-- **What Spark computes**, as its facts record it (#271 S1): the profile a
lowered plan runs under on Spark. -/
def Profile.sparkRun : Profile where
  un := Spark.runUn
  bin := Spark.runBin

end Substrait
