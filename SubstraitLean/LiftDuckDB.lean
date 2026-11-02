import SubstraitLean.LiftSearch

/-!
# The generated lift from DuckDB SQL (#268)

`generate_lift` builds what each DuckDB function (`DuckFn`) lifts to, with
DuckDB's semantics and with the reference's. `liftDuckDB.coverage` and
`liftReference.coverage` list how each lifts.
-/

namespace Substrait

generate_lift liftDuckDB : Semantics.duckdb using []

generate_lift liftReference : Semantics.reference using []

end Substrait
