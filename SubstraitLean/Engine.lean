import SubstraitLean.Obligations
import Sverify.DuckDB.Engine
import Sverify.Polars.Engine
import Sverify.Spark.Engine
import SubstraitLean.EngineTables

/-!
# The engines' Engine values, together (#900)

Each engine's `Engine` value and the proofs that its functions are within its
table and that its run is sound are in its package
(`engines/duckdb/Sverify/DuckDB/Engine.lean`,
`engines/polars/Sverify/Polars/Engine.lean`,
`engines/spark/Sverify/Spark/Engine.lean`); the structure and `Engine.Sound`
are engines-common (`engines/Sverify/Engines/Engine.lean`,
`engines/Sverify/Engines/Sound.lean`). This module checks them together.
-/

namespace Substrait

-- No engine's certificate is empty: each but the reference has rows that
-- are not theorems (so `Refines` is a real hypothesis, which `#print axioms`
-- cannot show).
#guard letI := Boxes.Ambient.none; !(Engine.duckdb {} rfl).testedRows.isEmpty && !Engine.polars.testedRows.isEmpty &&
  !Engine.spark.testedRows.isEmpty && Engine.reference.testedRows.isEmpty

end Substrait
