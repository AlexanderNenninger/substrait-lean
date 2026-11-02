import SubstraitLean.LiftSearch

/-!
# The generated lift from DuckDB SQL (#268)

`generate_lift` builds what each DuckDB function (`DuckFn`) lifts to, with
DuckDB's semantics and with the reference's. `liftDuckDB.coverage` and
`liftReference.coverage` list how each lifts.
-/

namespace Substrait

generate_lift liftDuckDB : Semantics.duckdb
  using [FMath.apply, FMath.inDomain, FMath.lo?, FMath.hi?, Option.all]

generate_lift liftReference : Semantics.reference
  using [FMath.apply, FMath.inDomain, FMath.lo?, FMath.hi?, Option.all]

/-- The generated lift table of the semantics. -/
def Lift.duckdb : (s : Semantics) → Lift s
  | .duckdb => liftDuckDB
  | .reference => liftReference

/-- The lift tables as JSON (`substrait-check --lift-table`): for each
semantics and DuckDB function, its argument and result types and the
Substrait expression it lifts to (`template`), over its arguments as field
references `0`, `1`, … whose `functionReference`s are `functions`' anchors, or
why the lift refuses it (`refused`). -/
def Lift.tableJson : Lean.Json :=
  let entries := [Semantics.duckdb, .reference].flatMap fun s => DuckFn.all.map fun f =>
    let how : List (String × Lean.Json) := match (Lift.duckdb s).entry f, f.refused s with
      | some e, _ => [("template", (Lean.Json.parse e.json).toOption.getD .null)]
      | none, some why => [("refused", Lean.toJson why)]
      | none, none => [("template", .null)]
    Lean.Json.mkObj ([("semantics", Lean.toJson s.name), ("construct", Lean.toJson f.sql),
      ("args", Lean.toJson (f.args.map DuckType.substrait)),
      ("result", Lean.toJson f.result.substrait)] ++ how)
  Lean.Json.mkObj [("functions", LiftSearch.functionsJson), ("lift", Lean.Json.arr entries.toArray)]

end Substrait
