import SubstraitCheck
import Sverify.DuckDB.Boxes

/-!
# An engine from outside, as a package adds one (the template; a test)

A package with an engine of its own requires this repository and copies this
file. It states its `Engine` value (profile, choices, observation rows,
translation, functions, and the proof that its table allows them) and proves
it sound (`Engine.Sound`), writes its registry entry from that theorem
(`engine_entry%`, `EngineEntry`), checks the entry's rows with
`#check_engine_profiles`, and builds a checker over `builtinEntries ++ [its
entry]`:

```lean
def main (args : List String) : IO UInt32 :=
  Substrait.Checker.checkerMain (Substrait.builtinEntries ++ [myEntry]) args
```

An entry whose theorem does not state its engine's soundness does not
type-check. This module does that for `dummy`, Spark's engine under another
name, and checks what the checker then reports. It is built
with the library (`lean_lib SubstraitCheckExamples`), not into
`substrait-check`.
-/

namespace Substrait.DummyEngine

-- The black-box catalogue in scope: DuckDB's, as the built-in engines bring
-- it. An engine with black boxes of its own declares them as a `scoped
-- instance` and joins them to DuckDB's with `Boxes.combine` (#1189).
open scoped Substrait.DuckDB

section
variable [Boxes.Ambient]

/-- The engine: Spark's, under another name and version. A real engine states
its own profile, table, rows, translation and functions. -/
def Engine.dummy : Engine :=
  { Engine.spark with
    name := "dummy", table := { Profile.spark.table with name := "dummy", version := "0.1.0" },
    within := Engine.spark.within }

/-- Its run is sound under guard elimination's side condition, as Spark's is. -/
theorem Engine.dummy_sound : Engine.dummy.Sound Engine.GuardFreeSide := Engine.spark_sound

end

def dummy : EngineEntry :=
  { (engine_entry% Engine.dummy_sound) with
    executes := "batch",
    shims := [("int_sum_decimal", .expression), ("int_avg_decimal", .expression),
      ("null_order", .argument), ("sort on the keys", .sort), ("decimal_negate_sub", .expression)] }

#check_engine_profiles [dummy]

-- An entry whose theorem does not state its engine's soundness does not
-- elaborate: here Spark's table within the core's. Nor does one whose side
-- condition is no named predicate.
#guard_msgs (drop info) in
#check_failure (engine_entry% Profile.spark_le_core)

-- A shim without a cost fails the build.
/-- error: dummy: a shim or row without evidence or cost -/
#guard_msgs in
#check_engine_profiles [{ dummy with shims := [] }]

def entries : List EngineEntry := builtinEntries ++ [dummy]
def engines : List EngineProfile := entries.map (·.rows)

open Lean (Json) in
def has (j : Json) (path : List String) : Bool :=
  (path.foldlM (fun (j : Json) k => (j.getObjVal? k).toOption) j).isSome

-- The checker's tables list it beside the built-in engines.
#guard has (tablesJson engines) ["profiles", "dummy"]
#guard has (tablesJson engines) ["choices", "dummy"]
#guard !has (tablesJson builtinEngines) ["profiles", "dummy"]
#guard ((realizabilityJson entries).getObjValD "dummy" |>.getObjValD "theorem") ==
  "DummyEngine.Engine.dummy_sound"
#guard ((realizabilityJson entries).getObjValD "dummy" |>.getObjValD "side") ==
  "Engine.GuardFreeSide"
-- A request under its name gets the reference's report, pending `dummy`.
#guard (Checker.underProfile engines (Lean.Json.mkObj [("profile", "dummy")]) (Lean.Json.mkObj [])
  true |>.toOption.map (·.1.getObjValD "pending")) == some "dummy"
#guard (Checker.underProfile builtinEngines (Lean.Json.mkObj [("profile", "dummy")])
  (Lean.Json.mkObj []) true |>.toOption.map (·.1.getObjValD "profile")) == some "reference"
-- The derived engine-wide facts take it in.
#guard Epsilon.statsProvedOn "agg.var" engines == ["duckdb", "polars", "spark", "dummy"]
#guard Epsilon.statsProvedOn "agg.stat" engines == ["duckdb", "spark", "dummy"]

end Substrait.DummyEngine
