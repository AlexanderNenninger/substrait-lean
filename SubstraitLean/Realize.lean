import SubstraitLean.Epsilon

/-!
# How each engine realizes a plan (#1166, theme 3)

The verdict a `--contract` report gives per engine, as `"engines"`: the class
of the plan on the engine's translation from the reference (D22), its
evidence and where that comes from, the shims the translation writes, the
options it realizes only up to an observation, and what refuses it. Python's
`sverify.routes` reads it and words it; before this module it computed the
same from the tables itself.

Each option the proof depends on (`Epsilon.dependsReads`, as `deps`) reads the
engine's observation row there (`ObsTable.row?`, D15):

* the class is `refused` for a refused row, `observed` for a row equal to the
  reference's only up to its observation, `shim` for a refinement after a
  shim, `exact` otherwise; a shim is not needed where every read states a
  preference the engine gives as stated (`givesAsStated`, #444 step 3b);
* the plan's class is the worst over the options, and its evidence `proved`
  only where every row's is (`Evidence.proved`); a test, a probe or a row
  without evidence is `tested`;
* a filter, key or sort on a double the engine computes only within a bound
  may keep other rows (#568's threshold rule): where `Epsilon.rowsExact` does
  not show it keeps the same rows, the plan is refused there.

Where no option has a row, the translation's tests stand for the plan: `exact`,
`tested`. `"transfer"` gives, per other profile a plan may be verified under,
the options where the engine allows a behaviour that profile does not
(`transferB`, which `Rel.transfer_of_transferB` proves sound). `"sorted"`
says whether the plan's result comes out of a sort.

What the postcondition observes (the observation it states, a tolerance the
plan's `ε` must meet, the columns it reads) is applied to `"observed"` in
Python for now; a later step brings it here.
-/

namespace Substrait.Realize

open Lean (Json toJson)

/-- A plan's class on an engine (D22), best first. -/
inductive RouteClass | exact | observed | shim | refused
  deriving Repr, DecidableEq

def RouteClass.rank : RouteClass → Nat
  | .exact => 0 | .observed => 1 | .shim => 2 | .refused => 3

def RouteClass.name : RouteClass → String
  | .exact => "exact" | .observed => "observed" | .shim => "shim" | .refused => "refused"

/-- The worse of two classes. -/
def RouteClass.max (a b : RouteClass) : RouteClass := if a.rank < b.rank then b else a

/-- Does an engine whose choice at `d` is `c` give the behaviours the plan
states there, as stated? Only where every read states one, and the choice
delivers the first preference it supports. -/
def givesAsStated : Option Choice → Dep → Bool
  | some (.oneOf bs), d | some (.asked bs _), d =>
    d.stated && !d.behaviours.isEmpty && d.behaviours.all bs.contains
  | _, _ => false

/-- An engine row's class at `d`. -/
def rowClass (E : EngineProfile) (d : Dep) (r : ObsRow) : RouteClass :=
  if r.shim.isSome && givesAsStated (E.table.choice? d.group d.option) d then .exact
  else match r.cls, r.shim with
    | .refused, _ => .refused
    | .refinesUpTo, _ | .approx, _ => .observed
    | .refines, some _ => .shim
    | .refines, none => .exact

def _root_.Substrait.Evidence.facts : Evidence → List String
  | .proved _ ids | .tested ids | .probed ids => ids
  | .none => []

def _root_.Substrait.Evidence.theorem? : Evidence → Option String
  | .proved thm _ => some thm
  | _ => none

/-- The engine's rows at the plan's dependencies. -/
def rowsAt (E : EngineProfile) (ds : List Dep) : List (Dep × ObsRow) :=
  ds.filterMap fun d => (E.obs.row? d.group d.option).map (d, ·)

/-- The plan's class on `E`: the worst over its rows, `exact` without any. -/
def planClass (E : EngineProfile) (rows : List (Dep × ObsRow)) (rowsExact : Bool) : RouteClass :=
  let worst := rows.foldl (fun c (d, r) => c.max (rowClass E d r)) .exact
  if threshold E rows rowsExact then .refused else worst
where
  /-- #568: a double the engine computes only within a bound, under a filter,
  key or sort that may keep other rows. -/
  threshold (E : EngineProfile) (rows : List (Dep × ObsRow)) (rowsExact : Bool) : Bool :=
    !rowsExact && rows.any fun (d, r) =>
      rowClass E d r == .observed && r.q.floats != .exact

/-- Every row's evidence is a proof; none without rows (the translation's
tests stand for the plan then). -/
def planProved (rows : List (Dep × ObsRow)) : Bool :=
  !rows.isEmpty && rows.all fun (_, r) => r.evidence.theorem?.isSome

def where_ (d : Dep) : List (String × Json) := [("group", toJson d.group), ("option", toJson d.option)]

/-- The options where `E` allows a behaviour `P` does not, among `reads`: a
proof under `P` carries over to `E` where there are none (`transferB`). -/
def transferFailures (P E : EngineProfile) (reads : List Read) : List Json :=
  reads.eraseDups.filter (!E.table.leAtB P.table ·) |>.map fun (g, o, ps) =>
    Json.mkObj [("group", toJson g), ("option", toJson o), ("preferences", toJson ps),
      ("from", toJson (P.table.allows g o ps)), ("to", toJson (E.table.allows g o ps)),
      ("facts", toJson (E.obs.factsAt (some g) o))]

/-- The profiles besides the reference that a plan may be verified under. -/
def sources (es : List EngineProfile) : List EngineProfile :=
  { table := Profile.substrait.table, obs := Profile.substrait.obs, translationTheorem := "" } :: es

/-- One engine's verdict, as JSON. -/
def engineJson (es : List EngineProfile) (E : EngineProfile) (ds : List Dep) (reads : List Read)
    (rowsExact : Bool) : Json :=
  let rows := rowsAt E ds
  let cls := planClass E rows rowsExact
  let facts := (rows.flatMap fun (_, r) => r.evidence.facts).eraseDups
  let theorems := (rows.filterMap fun (_, r) => r.evidence.theorem?).eraseDups
  let shims := rows.filterMap fun (d, r) =>
    if rowClass E d r == .shim then r.shim.map fun s => Json.mkObj (where_ d ++ [("shim", toJson s)])
    else none
  let observed := rows.filterMap fun (d, r) =>
    if rowClass E d r == .observed then
      some (Json.mkObj (where_ d ++ [("observation", r.q.sparseJson), ("shim", toJson r.shim),
        ("facts", toJson r.evidence.facts)]))
    else none
  let refused := rows.filterMap fun (d, r) =>
    if rowClass E d r == .refused then
      some (Json.mkObj ([("code", toJson "option_refused")] ++ where_ d ++
        [("facts", toJson r.evidence.facts)]))
    else none
  let threshold := if planClass.threshold E rows rowsExact
    then [Json.mkObj [("code", toJson "threshold")]] else []
  Json.mkObj [
    ("class", toJson cls.name),
    ("evidence", toJson (if planProved rows then "proved" else "tested")),
    ("rows", toJson rows.length),
    ("theorems", toJson theorems), ("facts", toJson facts),
    ("version", toJson E.table.version),
    ("shims", Json.arr shims.toArray), ("observed", Json.arr observed.toArray),
    ("problems", Json.arr (refused ++ threshold).toArray),
    ("transfer", Json.mkObj ((sources es).filter (·.name != E.name) |>.map fun P =>
      let fs := transferFailures P E reads
      (P.name, Json.mkObj [("ok", toJson fs.isEmpty), ("failures", Json.arr fs.toArray)])))]

/-- Whether the plan's result comes out of a sort: its root, under projections,
is a sort or a fetch of one. -/
def sortedRoot : Rel → Bool
  | .emit r _ | .project r _ => sortedRoot r
  | .orderBy _ _ => true
  | .fetch (.orderBy _ _) _ _ => true
  | _ => false

/-- `"engines"` and `"sorted"` of a `--contract` request, given its
`"rows_exact"` (`Epsilon.rowsExactByEngine`). -/
def enginesJson (es : List EngineProfile) (input : Json) (rowsExact : Json) :
    Except String (List (String × Json)) := do
  let some reads ← Epsilon.dependsReads input | return []
  let some tj := (input.getObjVal? "transform").toOption | return []
  let plan ← ContractCheck.parseJsonPlan tj
  let all := plan.root.reads
  let ds := deps reads
  let exact (e : String) : Bool := (rowsExact.getObjValAs? Bool e).toOption.getD true
  return [("engines", Json.mkObj (es.map fun E => (E.name, engineJson es E ds all (exact E.name)))),
    ("sorted", toJson (sortedRoot plan.root))]

end Substrait.Realize
