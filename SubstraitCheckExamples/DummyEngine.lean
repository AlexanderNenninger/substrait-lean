import SubstraitCheck
import Sverify.DuckDB.Boxes

/-!
# An engine profile from outside, as a package adds one (test)

A package with an engine profile of its own requires this repository, states
its entry as an `EngineProfile`, checks it with `#check_engine_profiles`, and
builds a checker over `builtinEngines ++ [its entry]`:

```lean
def main (args : List String) : IO UInt32 :=
  Substrait.Checker.checkerMain (Substrait.builtinEngines ++ [myEngine]) args
```

This module does that for `dummy`, an engine with Spark's choices and rows
under another name, and checks what the checker then reports. It is built
with the library (`lean_lib SubstraitCheckExamples`), not into
`substrait-check`.
-/

namespace Substrait.DummyEngine

-- The black-box catalogue in scope: DuckDB's, as the built-in engines bring
-- it. An engine with black boxes of its own declares them as a `scoped
-- instance` and joins them to DuckDB's with `Boxes.combine` (#1189).
open scoped Substrait.DuckDB

/-- The translation theorem the entry names: here a stand-in, Spark's table
within the core's. A real profile names its `Rel.<engine>_sound`. -/
theorem dummy_sound : Profile.spark.table.Le Profile.core.table := Profile.spark_le_core

def dummy : EngineProfile :=
  { table := { Profile.spark.table with name := "dummy", version := "0.1.0" },
    obs := withReruns Profile.spark.obs,
    translationTheorem := "DummyEngine.dummy_sound",
    executes := "batch", asReference := true,
    shims := [("int_sum_decimal", .expression), ("int_avg_decimal", .expression),
      ("Dialect.canon", .expression), ("null_order", .argument), ("sort on the keys", .sort),
      ("decimal_negate_sub", .expression)] }

#check_engine_profiles [dummy]

-- A name that resolves to nothing fails the build.
/-- error: dummy: no translation theorem DummyEngine.nowhere -/
#guard_msgs in
#check_engine_profiles [{ dummy with translationTheorem := "DummyEngine.nowhere" }]

-- A shim without a cost fails it too.
/-- error: dummy: a shim or row without evidence or cost -/
#guard_msgs in
#check_engine_profiles [{ dummy with shims := [] }]

def engines : List EngineProfile := builtinEngines ++ [dummy]

open Lean (Json) in
def has (j : Json) (path : List String) : Bool :=
  (path.foldlM (fun (j : Json) k => (j.getObjVal? k).toOption) j).isSome

-- The checker's tables list it beside the built-in engines.
#guard has (tablesJson engines) ["profiles", "dummy"]
#guard has (tablesJson engines) ["choices", "dummy"]
#guard !has (tablesJson builtinEngines) ["profiles", "dummy"]
#guard ((realizabilityJson engines).getObjValD "dummy" |>.getObjValD "theorem") ==
  "DummyEngine.dummy_sound"
-- A request under its name gets the reference's report, marked `dummy`.
#guard (Checker.underProfile engines (Lean.Json.mkObj [("profile", "dummy")]) (Lean.Json.mkObj [])
  true |>.toOption.map (·.1.getObjValD "profile")) == some "dummy"
#guard (Checker.underProfile builtinEngines (Lean.Json.mkObj [("profile", "dummy")])
  (Lean.Json.mkObj []) true |>.toOption.map (·.1.getObjValD "profile")) == some "reference"
-- The derived engine-wide facts take it in.
#guard Epsilon.statsProvedOn engines == ["duckdb", "spark", "dummy"]

end Substrait.DummyEngine
