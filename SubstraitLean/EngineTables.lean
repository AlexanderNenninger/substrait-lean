import Sverify.Engines.Transfer
import Sverify.Engines.Entry
import Sverify.DuckDB.Engine
import Sverify.Substrait.Profile
import Sverify.Spark.Engine
import Sverify.Polars.Engine

/-!
# The engines' tables, together (#444, step 3a)

`builtinEntries`, the engines of this repository with their soundness
proofs, `builtinEngines`, their tables, and the reports
over them: `substrait-check --options` (`tablesJson`), `--dependencies`
(`Rel.dependenciesJson`) and `--transfer` (`transferJson`). Each engine's
choice table and observation rows are in its package
(`engines/duckdb/Sverify/DuckDB/Tables.lean`,
`engines/polars/Sverify/Polars/Tables.lean`,
`engines/spark/Sverify/Spark/Tables.lean`), with the proof that it refines
the core, and the costs of the shims its rows name; each engine's `Engine`
value and the proof that it is sound are in its package's `Engine.lean`. The
rows' constructors, `EngineProfile`, `EngineEntry` and the JSON a table is
reported in are engines-common (`engines/Sverify/Engines/Tables.lean`,
`engines/Sverify/Engines/Entry.lean`).
-/

namespace Substrait

/-! ## The engines -/

/-- The engines of this repository, each with the proof that its run is
sound (`Engine.duckdb_sound`, `Engine.polars_sound`, `Engine.spark_sound`),
DuckDB under its default settings. The checker is built over them
(`checkerMain`). -/
def builtinEntries : List EngineEntry := [
  { (engine_entry% Engine.duckdb_sound) with shims := Profile.duckdb.shimCosts },
  { (engine_entry% Engine.polars_sound) with
    shims := Profile.polars.shimCosts, executes := "streaming" },
  { (engine_entry% Engine.spark_sound) with
    shims := Profile.spark.shimCosts, executes := "batch" }]

/-- The tables of `builtinEntries`, as the reports read them. -/
def builtinEngines : List EngineProfile := builtinEntries.map (·.profile)

variable [Boxes.Ambient]
example : builtinEngines.all (·.rowsWf) := by decide +kernel

open Lean (Json toJson) in
/-- `substrait-check --options`: the options, the groups' options, each
profile's choices and observation rows (the engines `es`), the profiles'
versions, and the tool table. -/
def tablesJson (es : List EngineProfile) : Json :=
  optionsJson
    |>.setObjVal! "choices" (Json.mkObj ([
        ("reference", profileRowsJson Profile.reference.table Profile.reference.obs true),
        ("core", choicesJson Profile.core.table),
        ("substrait", profileRowsJson Profile.substrait.table Profile.substrait.obs false)] ++
      es.map fun e => (e.name, profileRowsJson e.table e.obs false)))
    |>.setObjVal! "profiles" (Json.mkObj ([
        ("reference", Json.mkObj [("engine", Json.null)]),
        ("core", Json.mkObj [("engine", Json.null)]),
        ("substrait", Json.mkObj [("engine", Json.null), ("yaml", toJson Profile.substrait.table.version)])] ++
      es.map fun e => (e.name, Json.mkObj [
        ("engine", toJson e.name), ("versions", toJson [e.table.version]),
        ("executes", toJson e.executes),
        ("missing", Json.arr <| (e.table.missing.map fun (f, ids) =>
          Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray)])))
    |>.setObjVal! "observations" (Json.mkObj ([("reference", obsTableJson Profile.reference.obs),
        ("substrait", obsTableJson Profile.substrait.obs)] ++
      es.map fun e => (e.name, obsTableJson e.obs)))
    |>.setObjVal! "versions" (Json.mkObj (es.map fun e => (e.name, toJson e.table.version)))
    |>.setObjVal! "tools" (toolsJson es)
    |>.setObjVal! "levels" obsLevelsJson

/-! ## The dependency and transfer reports, over these profiles (`engines/Sverify/Engines/Transfer.lean`) -/

/-- The profiles a report compares. -/
def reportProfiles (es : List EngineProfile) : List (ProfileTable × ObsTable) :=
  (Profile.reference.table, Profile.reference.obs) ::
    (Profile.substrait.table, Profile.substrait.obs) :: es.map fun e => (e.table, e.obs)

open Lean (Json toJson) in
/-- `substrait-check --dependencies`: the options the plan meets, each with
every profile's choice and observation row; per pair of profiles whether a
proof under the first holds under the second (`transferB`); and per engine
the shims its translation from the reference needs for this plan. -/
def Rel.dependenciesJson (es : List EngineProfile) (r : Rel) : Json :=
  let reads := r.reads.eraseDups
  let choiceAt (t : ProfileTable) (p : Read) : Json :=
    match t.choice? p.1 p.2.1 with | some c => c.json | none => Json.null
  let rowAt (obs : ObsTable) (p : Read) : Json :=
    match obs.row? p.1 p.2.1 with | some row => row.json | none => Json.null
  Json.mkObj [
    ("options", Json.arr <| (reads.map fun p => Json.mkObj ([
      ("group", toJson p.1), ("option", toJson p.2.1), ("preferences", toJson p.2.2),
      ("tool", toJson ((Profile.reference.tools.find? (·.option == p.2.1)).map fun t =>
        match t.tool with | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open"))] ++
      (reportProfiles es).map fun (t, obs) => (t.name, Json.mkObj [
        ("choice", choiceAt t p), ("allows", toJson (t.allows p.1 p.2.1 p.2.2)),
        ("row", rowAt obs p), ("version", toJson t.version)]))).toArray),
    ("transfer", Json.mkObj ((reportProfiles es).map fun (t, _) => (t.name,
      Json.mkObj ((reportProfiles es).map fun (u, _) => (u.name, toJson (transferB r t u)))))),
    ("functions", toJson r.functions),
    ("missing", Json.mkObj (es.map fun e => (e.name,
      Json.arr <| ((e.table.missingIn r.functions).map fun (f, ids) =>
        Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray))),
    -- A shim the plan needs at an option, unless every read there states a
    -- preference the engine gives as stated (a key's `NULLS LAST` on Polars):
    -- the shim is for the reference's default (#444, step 3b).
    ("shims", Json.mkObj (es.map fun e => (e.name,
      Json.arr <| ((reads.map fun p => (p.1, p.2.1)).eraseDups.filterMap fun (g, o) =>
        let stated := reads.filter fun p => p.1 == g && p.2.1 == o
        if stated.all (fun p => !p.2.2.isEmpty &&
            (e.table.allows g o p.2.2).all (Profile.reference.table.allows g o p.2.2).contains) then none
        else (e.obs.row? g o).bind fun row => row.shim.map fun sh =>
          Json.mkObj [("group", toJson g), ("option", toJson o), ("shim", toJson sh)]).toArray)))]

/-- The profiles by name: the reference, the core, Substrait, and the engines
(DuckDB under its default settings). -/
def profileNamed (es : List EngineProfile) (name : String) : Option (ProfileTable × ObsTable) :=
  ((Profile.reference.table, Profile.reference.obs) :: (Profile.core.table, []) ::
    (Profile.substrait.table, Profile.substrait.obs) :: es.map fun e => (e.table, e.obs)).find?
    (·.1.name == name)

open Lean (Json toJson) in
/-- `substrait-check --transfer`, on stdin `{"from": P, "to": E, "depends":
[{"group", "option", "preferences"?, "behaviours"?}], "functions"?: [...]}`:
whether a proof under `P` that uses only `depends` holds under `E`. Each row
fails where `E` allows a behaviour not below one the proof used (`behaviourLe`;
`behaviours`, or else all `P` allows there), and each function `E` lacks fails. With
`depends` = `Rel.reads` and no `behaviours`, this is `transferB`, which
`Rel.transfer_of_transferB` proves sound. -/
def transferJson (es : List EngineProfile) (input : Json) : Except String Json := do
  let name (k : String) : Except String (ProfileTable × ObsTable) := do
    let n ← input.getObjValAs? String k
    match profileNamed es n with
    | some p => pure p
    | none => throw s!"unknown profile {n}"
  let (P, _) ← name "from"
  let (E, obsE) ← name "to"
  let rows := (input.getObjValAs? (Array Json) "depends").toOption.getD #[]
  let mut failures : Array Json := #[]
  for row in rows do
    let group := (row.getObjValAs? String "group").toOption
    let option ← row.getObjValAs? String "option"
    let ps := (row.getObjValAs? (List String) "preferences").toOption.getD []
    let used := (row.getObjValAs? (List String) "behaviours").toOption.getD (P.allowsAt group option ps)
    let target := E.allowsAt group option ps
    unless target.all (fun b => used.any (behaviourLe option b ·)) do
      failures := failures.push (Json.mkObj [("group", toJson group), ("option", toJson option),
        ("from", toJson used), ("to", toJson target), ("facts", toJson (obsE.factsAt group option))])
  let fns := (input.getObjValAs? (List String) "functions").toOption.getD []
  for (f, ids) in E.missingIn fns do
    failures := failures.push (Json.mkObj [("function", toJson f), ("facts", toJson ids)])
  return Json.mkObj [("ok", toJson failures.isEmpty), ("failures", Json.arr failures)]

end Substrait
