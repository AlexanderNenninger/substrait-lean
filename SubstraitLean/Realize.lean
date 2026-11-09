import SubstraitLean.Epsilon
import SubstraitLean.PolarsShims

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

Where an option has no row, the translation's tests stand for it: the class
does not change, and the evidence is `tested`. `"class_basis"` and
`"sorted_basis"` are `"computed"`: no theorem connects the class to the
engine's refinement yet (#900). `"guard_free_theorem"` names the theorem by
which the engine's translation runs a `guard_free` plan without its other
guards (`guardFreeTheorems`), or is null where it keeps every guard. `"transfer"` gives, per other profile a plan may be verified under,
the options where the engine allows a behaviour that profile does not
(`transferB`, which `Rel.transfer_of_transferB` proves sound). `"sorted"`
says whether the plan's result comes out of a sort.

`"translated_evidence"` is the evidence a translated run from the reference
carries: `"proved"` only where `"evidence"` is and nothing in
`"tested_because"` (`testedBecause`) makes it rest on a test. An engine the
request names (`"engines"`) without a profile here gets a verdict too
(`unprofiledJson`, `"profile": false`), so every engine a route may reach has
one.

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
  | .proved _ ids | .tested ids .. | .probed ids .. => ids
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

/-- The dependencies without a row, which rest on the translation's tests. A
call's base entry (`(g, "base")`, D34: the group's, where its options may be
dead) stands for the call, not an option: without a row of its own it adds
nothing. -/
def withoutRow (ds : List Dep) (rows : List (Dep × ObsRow)) : List Dep :=
  ds.filter fun d => d.option != "base" &&
    !(rows.any fun (d', _) => d'.option == d.option && d'.group == d.group)

/-- A base entry without a row adds nothing; an option without one is named. -/
example : (withoutRow [⟨"g", "base", [], true⟩] []).isEmpty = true := by decide
example : (withoutRow [⟨"g", "overflow", [], true⟩] []).length = 1 := by decide

/-- Every dependency has a row and every row's evidence is a proof. A plan
without rows rests on the translation's tests. -/
def planProved (ds : List Dep) (rows : List (Dep × ObsRow)) : Bool :=
  !rows.isEmpty && (withoutRow ds rows).isEmpty && rows.all fun (_, r) => r.evidence.theorem?.isSome

/-- The theorem by which each engine's translation runs a plan whose report
is `guard_free` without its other guards, keeping the assumed issues'. An
engine not listed keeps every guard. -/
def guardFreeTheorems : List (String × String) := [("polars", "Rel.polars_sound")]

/-- The names in `guardFreeTheorems` are theorems. -/
example := @Rel.polars_sound

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
    -- The class is computed from the rows; no theorem connects it to the
    -- engine's refinement yet (#900).
    ("class_basis", toJson "computed"),
    ("evidence", toJson (if planProved ds rows then "proved" else "tested")),
    ("rows", toJson rows.length),
    ("without_row", Json.arr ((withoutRow ds rows).map fun d => Json.mkObj (where_ d)).toArray),
    ("theorems", toJson theorems), ("facts", toJson facts),
    -- The facts the proved rows' theorems rest on: a proof of the engine's
    -- model, which those facts say the engine is (#900's per-plan Refines).
    ("proved_facts", toJson (rows.flatMap fun (_, r) =>
      if r.evidence.theorem?.isSome then r.evidence.facts else []).eraseDups),
    ("issues", toJson (rows.filterMap fun (_, r) => r.evidence.issue?).eraseDups),
    ("guard_free_theorem", toJson (guardFreeTheorems.lookup E.name)),
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

/-- Why a translated run on `E` of a plan proved under the reference rests on
tests, beside the rows (`"without_row"`): `"robust_by_facts"` where, under
the plan's bound, a postcondition holds on the engine's doubles by the
engine's facts and not by a theorem (`"robust"`'s `"proved_on"`, #1045:
Kahan sums, whose sign `TreeSum.sign` does not cover);
`"allowed_orders_only"` where, under an observation that states its
doubles, a postcondition is proved on every order of the reference but not
on every result it allows (`Report.allowed`, #1071). -/
def testedBecause (E : EngineProfile) (input : Json) (rep : ContractCheck.Report)
    (robust : Json) : List String :=
  let obs := (input.getObjVal? "observation").toOption
  let floatsPlan := (obs.bind (·.getObjValAs? Bool "floats_plan" |>.toOption)).getD false
  let approxs : List Bool :=
    ((obs.bind (·.getObjValAs? (Array Bool) "approx" |>.toOption)).getD #[]).toList
  let rob : List Json := ((robust.getArr?).toOption.getD #[]).toList
  let proved := rep.ensures.flatten.map (·.2.1)
  let byFacts := floatsPlan && (List.range proved.length).any fun i =>
    let r := rob.getD i .null
    proved.getD i false && !approxs.getD i false &&
      (r.getObjValAs? Bool "robust").toOption.getD false &&
      !(((r.getObjValAs? (Array String) "proved_on").toOption.getD #[]).contains E.name)
  let ordersOnly := obs.isSome && !floatsPlan && (List.range proved.length).any fun i =>
    proved.getD i false && !rep.allowed.getD i true && (rep.ignores.getD i none).isSome
  (if byFacts then ["robust_by_facts"] else []) ++ (if ordersOnly then ["allowed_orders_only"] else [])

/-- The verdict on an engine without a profile in this checker (an optional
one, DataFusion): no option has a row, so the translation's tests stand for
the plan. -/
def unprofiledJson : Json := Json.mkObj [
  ("class", toJson "exact"), ("class_basis", toJson "computed"),
  ("evidence", toJson "tested"), ("translated_evidence", toJson "tested"),
  ("tested_because", toJson ["no_profile"]), ("profile", toJson false),
  ("rows", toJson (0 : Nat)), ("without_row", Json.arr #[]),
  ("theorems", Json.arr #[]), ("facts", Json.arr #[]), ("proved_facts", Json.arr #[]),
  ("issues", Json.arr #[]), ("guard_free_theorem", .null), ("version", .null),
  ("shims", Json.arr #[]), ("observed", Json.arr #[]), ("problems", Json.arr #[]),
  ("transfer", Json.mkObj [])]

variable [Boxes.Ambient]
/-- `"engines"` and `"sorted"` of a `--contract` request, given its
`"rows_exact"` (`Epsilon.rowsExactByEngine`), its report and `"robust"`
(`EngineRobust.robust`). An engine the request names (`"engines"`) without a
profile here gets `unprofiledJson`. -/
def enginesJson (es : List EngineProfile) (input : Json) (rowsExact : Json)
    (rep : ContractCheck.Report) (robust : Json) :
    Except String (List (String × Json)) := do
  let some reads ← Epsilon.dependsReads input | return []
  let some tj := (input.getObjVal? "transform").toOption | return []
  let plan ← ContractCheck.parseJsonPlan tj
  let all := plan.root.reads
  let ds := deps reads
  -- Without the threshold analysis's answer, the rows may differ.
  let exact (e : String) : Bool := (rowsExact.getObjValAs? Bool e).toOption.getD false
  let profiled := es.map fun E =>
    let because := testedBecause E input rep robust
    let v := engineJson es E ds all (exact E.name)
    let proved := (v.getObjValAs? String "evidence").toOption == some "proved"
    (E.name, v.setObjVal! "profile" (toJson true)
      |>.setObjVal! "tested_because" (toJson because)
      |>.setObjVal! "translated_evidence"
        (toJson (if proved && because.isEmpty then "proved" else "tested")))
  let named : List String :=
    ((input.getObjValAs? (Array String) "engines").toOption.getD #[]).toList
  let others := named.eraseDups.filter (fun n => !es.any (·.name == n)) |>.map (·, unprofiledJson)
  return [("engines", Json.mkObj (profiled ++ others)),
    ("sorted", toJson (sortedRoot plan.root)), ("sorted_basis", toJson "computed")]

end Substrait.Realize
