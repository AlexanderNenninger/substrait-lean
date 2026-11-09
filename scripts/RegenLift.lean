import SubstraitLean.LiftSearch
import SubstraitLean.LiftCache

/-!
# Regenerating the lift from DuckDB SQL (`poe regen-lift`)

Runs the lift generator's search (`SubstraitLean/LiftSearch.lean`) under each
semantics and writes what it finds, entries and proofs, to
`SubstraitLean/LiftDuckDB/Duckdb` and `Reference`. A build checks those
modules and never searches; run this when `DuckDBSQL.lean`, the generator or
the model's functions change (a build that fails in those modules says so).
Not part of the library: `lake build` does not elaborate it.
-/

namespace Substrait

-- The search's budget per candidate: the generated check's under DuckDB's
-- semantics (`DOUBLE * DOUBLE` and `/` split nine double cases), half of it
-- under the reference's.
set_option maxHeartbeats 800000 in
generate_lift liftDuckDB : Semantics.duckdb
  using [FMath.apply, FMath.inDomain, FMath.lo?, FMath.hi?, Option.all, Value.pick, Value.ltB]
  cache liftCache
  writing "SubstraitLean/LiftDuckDB/Duckdb"

set_option maxHeartbeats 400000 in
generate_lift liftReference : Semantics.reference
  using [FMath.apply, FMath.inDomain, FMath.lo?, FMath.hi?, Option.all, Value.pick, Value.ltB]
  cache liftCache
  writing "SubstraitLean/LiftDuckDB/Reference"

end Substrait
