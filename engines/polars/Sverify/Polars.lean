import Sverify.Polars.Engine
import Sverify.Polars.Lowering
import Sverify.Polars.LoweringLemmas
import Sverify.Polars.LoweringOn.Bits
import Sverify.Polars.LoweringOn.Integers
import Sverify.Polars.LoweringOn.Math
import Sverify.Polars.LoweringOn.Native
import Sverify.Polars.LoweringOn.Other
import Sverify.Polars.LoweringOn.Table
import Sverify.Polars.LoweringSchemas
import Sverify.Polars.OpenSums
import Sverify.Polars.Profile
import Sverify.Polars.Shims
import Sverify.Polars.Tables

/-! Polars's Lean half (#1189, step 5): its table, its shims, its profile and
its `Engine` value. It imports only the core, the analysis and
engines-common, which the standalone build of this package checks. -/
