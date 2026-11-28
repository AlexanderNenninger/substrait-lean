import Sverify.Engines.LoweringSearch
import Sverify.Spark.LoweringSchemas

/-!
# Regenerating the Spark lowering (`poe regen-lowering`)

Runs the lowering generator's search (`engines/Sverify/Engines/LoweringSearch.lean`)
for Spark's profile and writes what it finds, entries and proofs, to
`engines/spark/Sverify/Spark/LoweringOn`. A build checks those modules and
never searches; run this when `Profile.spark`, the generator or the model's
functions change. Not part of the library: `lake build` does not elaborate it.
-/

namespace Substrait

attribute [local instance] Boxes.Ambient.none in
generate_lowering sparkOn : Profile.spark
  unfolding [Profile.spark, sparkBin, sparkUn, sparkPow, FMath.sparkNull, Spark.wrap32,
    BinFn.sparkOnFloats, nanCase, isInfCode, FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply,
    domainIssue, nanIssue, negInfPow, powOneInf, atan2?, logb?]
  using [Spark.spark_bin_nondouble_l, Spark.spark_bin_nondouble_r, Spark.spark_un_nondouble,
    Spark.ref_bin_nondouble_l, Spark.ref_bin_nondouble_r,
    BinFn.apply_eq_nondouble_l, BinFn.apply_eq_nondouble_r, BinFn.apply_lt_nondouble_l,
    BinFn.apply_lt_nondouble_r, Value.isNum_float_nondouble]
  -- `sverify_split_first` is internal (ruling 286): no plan Spark lowers calls it.
  excluding [BinFn.splitFirst]
  hand_written LoweringSearch.sparkSchemas
  writing "engines/spark/Sverify/Spark/LoweringOn"
  refusing [BinFn.fpow, BinFn.fatan2, UnFn.ftod, BinFn.splitFirst]

end Substrait
