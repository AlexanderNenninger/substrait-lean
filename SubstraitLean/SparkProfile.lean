import SubstraitLean.SparkShims

/-!
# Spark as a profile (#739)

`Profile.spark` is the semantics a plan verified with
`verify(semantics="spark")` is checked under: what Spark 4.3.0 computes under
`sverify.sql.spark.SPARK_CONF` (ANSI mode on), as its facts record it
(`characterization/spark/facts/`), on the options where sverify models
Spark's own choice, and the reference elsewhere (D21, `docs/core-semantics.md`,
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

end Substrait
