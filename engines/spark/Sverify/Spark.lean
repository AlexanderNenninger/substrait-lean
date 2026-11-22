import Sverify.Spark.Engine
import Sverify.Spark.Lowering
import Sverify.Spark.LoweringLemmas
import Sverify.Spark.LoweringOn.Arith
import Sverify.Spark.LoweringOn.Bits
import Sverify.Spark.LoweringOn.Math
import Sverify.Spark.LoweringOn.Native
import Sverify.Spark.LoweringOn.Other
import Sverify.Spark.LoweringOn.Table
import Sverify.Spark.LoweringSchemas
import Sverify.Spark.Profile
import Sverify.Spark.Shims
import Sverify.Spark.Tables

/-! Spark's Lean half (#1189, step 5): its table, its shims, its profile and
its `Engine` value. It imports only the core, the analysis and
engines-common, which the standalone build of this package checks. -/
