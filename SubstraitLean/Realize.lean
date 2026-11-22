import SubstraitLean.Epsilon
import Sverify.Polars.Engine
import Sverify.DuckDB.Profile

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
guards (`guardFreeTheorems`), or is null where it keeps every guard.
`"marks_theorem"` names the theorem by which it runs the expressions the
checker marked without their checks on a checked run (`marksTheorems`,
ruling 223), or is null where it keeps every check. `"transfer"` gives, per other profile a plan may be verified under,
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

/-- The theorem by which each engine's translation runs the expressions the
checker marked (`Rel.marks`) without their checks, the one against `±∞`
included, on a checked run (ruling 223). An engine not listed keeps every
check of every expression; Polars runs all or none (`guardFreeTheorems`). -/
def marksTheorems : List (String × String) := [("duckdb", "Rel.duckdb_marks_written")]

/-- The names in `marksTheorems` are theorems. -/
example := @Rel.duckdb_marks_written

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
  { table := Profile.substrait.table, obs := Profile.substrait.obs } :: es

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
    ("marks_theorem", toJson (marksTheorems.lookup E.name)),
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

/-! ### Each column's `ε`, normalised (#1166)

`Epsilon.epsilon` writes a double column's bound in several shapes: a kind's
value as a number or as `{"value", "proved"}`, `"proved"` as one flag or one
per kind, `"proved_on"` naming the engines a statistic's bound is proved on
(D30). `epsBounds` reads them into one shape, per engine where one is named:
`{"bounds": {kind: {"value", "proved"}}, "unbounded", "why"}`, with a group's
own bound (`"per_group"`, `"theorem"`, #929) where the checker gives one. -/

/-- The kinds of bound a tolerance compares (`sv.within`). -/
def epsKinds : List String := ["abs", "rel", "ulps"]

/-- A column's `ε`, normalised; `proved` per kind, on `engine` where given (a
bound with `"proved_on"` is proved there only). -/
def epsBounds (engine : Option String) (eps : Json) : Json :=
  let flag (k : String) : Bool :=
    match eps.getObjVal? "proved" with
    | .ok (.bool b) => b
    | .ok j => (j.getObjValAs? Bool k).toOption.getD false
    | .error _ => false
  let on : Option (List String) := (eps.getObjValAs? (List String) "proved_on").toOption
  let provedAt (k : String) : Bool := match engine, on with
    | some e, some es => if k == "abs" then es.contains e else flag k
    | _, _ => flag k
  let bounds := epsKinds.filterMap fun k =>
    match eps.getObjVal? k with
    | .ok (.num n) => some (k, Json.mkObj [("value", .num n), ("proved", toJson (provedAt k))])
    | .ok j@(.obj _) => match j.getObjVal? "value" with
      | .ok (.num n) => some (k, Json.mkObj [("value", .num n),
          ("proved", toJson ((j.getObjValAs? Bool "proved").toOption.getD (provedAt k)))])
      | _ => none
    | _ => none
  let named := epsKinds.any fun k => (eps.getObjVal? k).isOk
  -- A group's own bound (#929, no row cap) and the theorem behind it pass through.
  let extra := ["per_group", "theorem"].filterMap fun k =>
    (eps.getObjVal? k).toOption.map (k, ·)
  Json.mkObj ([("bounds", Json.mkObj bounds), ("unbounded", toJson (named && bounds.isEmpty)),
    ("why", (eps.getObjVal? "why").toOption.getD .null)] ++ extra)

/-- Every column's `ε` of `Epsilon.epsilon`'s answer, normalised (`epsBounds`). -/
def epsilonBounds (engine : Option String) (eps : Json) : Json :=
  match eps with
  | .obj kvs => Json.mkObj (kvs.toList.map fun (c, e) => (c, epsBounds engine e))
  | _ => Json.mkObj []

-- A column the checker names no finite bound for is unbounded; a statistic's
-- bound is proved only on the engines `"proved_on"` names.
#guard epsBounds none (Json.mkObj [("abs", .null), ("why", toJson "no cap")]) ==
  Json.mkObj [("bounds", Json.mkObj []), ("unbounded", toJson true), ("why", toJson "no cap")]
#guard epsBounds (some "spark") (Json.mkObj [("abs", toJson (0.5 : Float)),
    ("proved", Json.mkObj [("abs", toJson true)]), ("proved_on", toJson ["duckdb"])]) ==
  Json.mkObj [("bounds", Json.mkObj [("abs", Json.mkObj [("value", toJson (0.5 : Float)),
    ("proved", toJson false)])]), ("unbounded", toJson false), ("why", .null)]
-- `"proved"` as one flag, and a kind's value with its own flag.
#guard epsBounds none (Json.mkObj [("abs", toJson (2.0 : Float)), ("proved", toJson true),
    ("rel", Json.mkObj [("value", toJson (0.5 : Float)), ("proved", toJson false)])]) ==
  Json.mkObj [("bounds", Json.mkObj [("abs", Json.mkObj [("value", toJson (2.0 : Float)),
    ("proved", toJson true)]), ("rel", Json.mkObj [("value", toJson (0.5 : Float)),
    ("proved", toJson false)])]), ("unbounded", toJson false), ("why", .null)]

/-! ### What a postcondition observes of a realization (#1071, ruling 265)

The class, the shims and the problems above describe what the engine's rows say. A
postcondition states what it observes (`sv.equivalent`), and the rows that hold only up to an
observation are met against it here: a row whose observation the postcondition's refines gives
the plan as it is, one that does not is shimmed or refuses the plan, and a row that bounds the
doubles per plan is met against the plan's `ε` and the tolerance the postcondition states.
Tolerances compare exactly: a stated tolerance arrives as the exact decimal of the double the
user passed, `ε` as the checker's own rounded-up decimal, and both are read as rationals. The
numeric tolerance is a type of this module's own; `FloatObs` and `Obs.le` are unchanged.
Python words the problems (`sverify.routes`), from the codes and data here. -/

/-- A tolerance on doubles (`sv.within`): at most `abs` apart, `rel` of the larger magnitude
apart, or `ulps` units in the last place apart. A bound is its exact decimal. -/
structure Tol where
  abs : Option Lean.JsonNumber := none
  rel : Option Lean.JsonNumber := none
  ulps : Option Nat := none
  deriving BEq

/-- The exact value of a decimal JSON number. -/
def _root_.Lean.JsonNumber.toRat (n : Lean.JsonNumber) : Rat :=
  (n.mantissa : Rat) / ((10 ^ n.exponent : Nat) : Rat)

/-- The bound of kind `k` (`"abs"`, `"rel"`, `"ulps"`), as a rational. -/
def Tol.get (t : Tol) : String → Option Rat
  | "abs" => t.abs.map (·.toRat)
  | "rel" => t.rel.map (·.toRat)
  | "ulps" => t.ulps.map fun n => (n : Rat)
  | _ => none

/-- Every pair this tolerance accepts, `b` accepts: each bound given here is given in `b`, at
least as large (`Within.refines`). -/
def Tol.refines (a b : Tol) : Bool :=
  epsKinds.all fun k => match a.get k with
    | none => true
    | some x => (b.get k).any (x ≤ ·)

/-- How a postcondition observes doubles: exactly, within the plan's own bound, or within a
tolerance. -/
inductive Fl | exact | plan | within (t : Tol)
  deriving BEq

/-- `x` refines `y` on doubles (`Observation.coarser_than`'s floats rule): exact refines every
level, a level refines itself, a tolerance refines a larger one. -/
def Fl.refines : Fl → Fl → Bool
  | .exact, _ => true
  | .plan, .plan => true
  | .within a, .within b => a.refines b
  | _, _ => false

/-- The coarser of two levels on doubles (`_coarsest`). -/
def Fl.coarsest (x y : Fl) : Fl := if x.refines y then y else x

/-- A stated observation: the components but the doubles (`Obs.floats` is exact here), and the
doubles. -/
structure Seen where
  q : Obs := Obs.exact
  floats : Fl := .exact

/-- The components of `a` that are coarser than `b`'s, but the doubles (`coarser_than`),
in the order Python names them. -/
def Obs.coarserThan (a b : Obs) : List String :=
  [("rows", !a.rows.le b.rows), ("elements", !a.elements.le b.elements),
   ("zeros", !a.zeros.le b.zeros), ("timestamps", !a.times.le b.times),
   ("strings", !(a.strings.rank ≤ b.strings.rank)), ("decimals", !a.decimals.le b.decimals),
   ("errors", !(a.errors.rank ≤ b.errors.rank))].filterMap fun (n, c) => if c then some n else none

/-- The coarser of two observations on each component but the doubles. -/
def Obs.coarsest (a b : Obs) : Obs where
  rows := if a.rows.le b.rows then b.rows else a.rows
  elements := if a.elements.le b.elements then b.elements else a.elements
  zeros := if a.zeros.le b.zeros then b.zeros else a.zeros
  times := if a.times.le b.times then b.times else a.times
  strings := if a.strings.rank ≤ b.strings.rank then b.strings else a.strings
  decimals := if a.decimals.le b.decimals then b.decimals else a.decimals
  errors := if a.errors.rank ≤ b.errors.rank then b.errors else a.errors

/-- A double column's `ε` as `epsBounds` gives it: its bounds by kind with whether each is
proved, whether it has none, and why. -/
structure EpsCol where
  bounds : List (String × Lean.JsonNumber × Bool) := []
  unbounded : Bool := false
  why : Option String := none

def EpsCol.ofJson (j : Json) : EpsCol :=
  let bs := match j.getObjVal? "bounds" with
    | .ok (.obj kvs) => kvs.toList.filterMap fun (k, b) =>
      match b.getObjVal? "value", (b.getObjValAs? Bool "proved").toOption with
      | .ok (.num n), some p => some (k, n, p)
      | _, _ => none
    | _ => []
  { bounds := bs, unbounded := (j.getObjValAs? Bool "unbounded").toOption.getD false
    why := (j.getObjValAs? String "why").toOption }

/-- The columns' `ε` as `epsilonBounds` gives them. -/
def epsCols (eps : Json) : List (String × EpsCol) :=
  match eps with
  | .obj kvs => kvs.toList.map fun (c, e) => (c, EpsCol.ofJson e)
  | _ => []

/-- A column with a bound above zero. -/
def EpsCol.positive (e : EpsCol) : Bool := e.bounds.any fun (_, v, _) => v.mantissa != 0

/-- What a bound that rows give per plan (`"floats": {"bound": "plan"}`) meets or misses of
the postcondition (`_plan_bound`): the problems, as data for Python to word. -/
inductive PProb
  /-- A column with no bound, under a stated tolerance. -/
  | unbounded (col : String) (why : Option String)
  /-- A column a postcondition reads, held to the reference's exact value: the condition's index. -/
  | held (col : String) (cond : Nat)
  /-- A column whose bounds meet none of the stated tolerance's kinds. -/
  | notMet (col : String)
  deriving BEq

/-- The plan-bound problems of the columns, and whether the bound that meets the stated one
rests on an unproved bound (`_plan_bound`). -/
def planBound (stated : Fl) (eps : List (String × EpsCol)) (held : List (String × Nat)) :
    List (PProb × EpsCol) × Bool :=
  eps.foldl (init := ([], false)) fun (ps, unp) (col, e) =>
    if e.unbounded then
      (match stated with | .within _ => ps ++ [(.unbounded col e.why, e)] | _ => ps, true)
    else if !e.positive then (ps, unp)
    else match held.lookup col with
      | some i => (ps ++ [(.held col i, e)], unp)
      | none =>
        let met : List Bool := e.bounds.filterMap fun (k, v, pr) =>
          match stated with
          | .plan => some pr
          | .within t => (t.get k).bind fun s => if v.toRat ≤ s then some pr else none
          | .exact => none
        if met.isEmpty then (ps ++ [(.notMet col, e)], unp)
        else if met.any id then (ps, unp) else (ps, true)

/-- The tolerance the plan's `ε` gives (`_with_bound`): per kind every bounded column has, the
largest. `plan` where none does. -/
def planTol (eps : List (String × EpsCol)) : Fl :=
  let found := (eps.map (·.2)).filter (·.positive)
  let kinds := epsKinds.filter fun k => !found.isEmpty && found.all fun e => e.bounds.any (·.1 == k)
  if kinds.isEmpty then .plan
  else
    let most (k : String) : Option Lean.JsonNumber :=
      (found.filterMap fun e => (e.bounds.find? (·.1 == k)).map (·.2.1)).foldl
        (fun (m : Option Lean.JsonNumber) v => match m with
          | none => some v | some w => if w.toRat < v.toRat then some v else some w) none
    .within { abs := if kinds.contains "abs" then most "abs" else none
              rel := if kinds.contains "rel" then most "rel" else none
              ulps := if kinds.contains "ulps" then (most "ulps").map fun n => n.toRat.floor.toNat
                else none }

/-- Every bound of every column is proved, and there is a column (`_all_proved`). -/
def allProved (eps : List (String × EpsCol)) : Bool :=
  !eps.isEmpty && eps.all fun (_, e) => e.bounds.all (·.2.2)

def Tol.json (t : Tol) : Json :=
  Json.mkObj ([("abs", t.abs.map Json.num), ("rel", t.rel.map Json.num),
    ("ulps", t.ulps.map fun n => toJson n)].filterMap fun (k, v) => v.map (k, ·))

def Fl.json : Fl → Json
  | .exact => toJson "exact" | .plan => toJson "plan" | .within t => t.json

/-- An observation as Python reads it (`from_json`): the components that are not exact, and
the doubles where they are not. -/
def Seen.json (s : Seen) : Json :=
  let comps := s.q.sparseJson
  match s.floats with
  | .exact => comps
  | .plan => comps.setObjVal! "floats" (Json.mkObj [("bound", toJson "plan")])
  | .within t => comps.setObjVal! "floats" t.json

/-- The problem as data. -/
def PProb.json : PProb × EpsCol → Json
  | (p, e) =>
    let bounds := Json.arr (e.bounds.map fun (k, v, pr) =>
      Json.mkObj [("kind", toJson k), ("value", .num v), ("proved", toJson pr)]).toArray
    match p with
    | .unbounded col why => Json.mkObj [("code", toJson "unbounded"), ("column", toJson col),
        ("why", toJson why)]
    | .held col i => Json.mkObj [("code", toJson "held"), ("column", toJson col),
        ("condition", toJson i), ("bounds", bounds)]
    | .notMet col => Json.mkObj [("code", toJson "not_met"), ("column", toJson col),
        ("bounds", bounds)]

/-- Where the plan realizes the options, met against what the postcondition observes
(`realization`). `v` is the engine's verdict (`engineJson`): its class, evidence, shims and
problems are the start. -/
def realizeJson (E : EngineProfile) (ds : List Dep) (rows : List (Dep × ObsRow))
    (v : Json) (stated : Seen) (eps : List (String × EpsCol)) (held : List (String × Nat)) :
    Json × List Json := Id.run do
  let cls0 := match (v.getObjValAs? String "class").toOption with
    | some "refused" => RouteClass.refused | some "shim" => .shim
    | some "observed" => .observed | _ => .exact
  let mut worst := cls0
  let mut proved := (v.getObjValAs? String "evidence").toOption == some "proved"
  let mut shims : List Json := ((v.getObjValAs? (Array Json) "shims").toOption.getD #[]).toList
  let mut problems : List Json := ((v.getObjValAs? (Array Json) "problems").toOption.getD #[]).toList
  let mut seen : List Seen := []
  let mut boundProved : List Bool := []
  let mut told : List PProb := []
  for (d, r) in rows do
    if rowClass E d r == .observed then
      let planRow := r.q.floats != .exact
      let rest := { r.q with floats := .exact }
      let (pb, untested) := if planRow then planBound stated.floats eps held else ([], false)
      if untested then proved := false
      let gives : Seen := { q := rest, floats := if planRow then planTol eps else .exact }
      seen := seen ++ [gives]
      if gives.floats != .exact && gives.floats != .plan then
        boundProved := boundProved ++ [!untested && allProved eps]
      let missed := rest.coarserThan stated.q
      let loc := where_ d ++ [("facts", toJson r.evidence.facts)]
      if !missed.isEmpty then
        match r.shim with
        | some s =>
          if worst.rank < RouteClass.shim.rank then worst := .shim
          shims := shims ++ [Json.mkObj (where_ d ++ [("shim", toJson s)])]
        | none =>
          problems := problems ++ [Json.mkObj ([("code", toJson "observation_missed"),
            ("components", toJson missed), ("observed", rest.sparseJson)] ++ loc)]
      for p in pb do
        if !told.contains p.1 then
          told := told ++ [p.1]
          problems := problems ++ [(PProb.json p).mergeObj (Json.mkObj loc)]
  let gives : Option Seen :=
    if worst == .observed then seen.head?.map fun x => seen.tail.foldl
      (fun a b => { q := a.q.coarsest b.q, floats := a.floats.coarsest b.floats }) x
    else none
  let out := Json.mkObj [("class", toJson worst.name),
    ("evidence", toJson (if proved then "proved" else "tested")),
    ("shims", Json.arr shims.toArray), ("problems", Json.arr problems.toArray),
    ("observation", match gives with | some g => g.json | none => .null),
    ("bound_proved", if boundProved.isEmpty then .null else toJson (boundProved.all id))]
  return (out, problems)

/-- A component's level from its name, as `Obs.json` writes it. -/
def Seen.ofJson? (j : Json) : Option Seen := do
  let str (k : String) : Option String := (j.getObjValAs? String k).toOption
  let rows ← match str "rows" with
    | some "sequence" => some RowsObs.sequence | some "ties permuted" => some .tiesPermuted
    | some "multiset" => some .multiset | _ => none
  let elements ← match str "elements" with
    | some "sequence" => some ElemsObs.sequence | some "multiset" => some .multiset | _ => none
  let zeros ← match str "zeros" with
    | some "exact" => some ZeroNaNObs.exact | some "canon" => some .canon | _ => none
  let times ← match str "timestamps" with
    | some "ns" => some TimeObs.exact | some "us" => some (.truncated .us)
    | some "ms" => some (.truncated .ms) | some "s" => some (.truncated .s) | _ => none
  let strings ← match str "strings" with
    | some "exact" => some StringObs.exact | some "nfc" => some .nfc
    | some "casefold" => some .casefold | some "ascii" => some .ascii | _ => none
  let decimals ← match str "decimals" with
    | some "exact" => some DecObs.exact | some "value" => some .value | _ => none
  let errors ← match str "errors" with
    | some "exact" => some ErrorObs.exact | some "kind" => some .kind
    | some "raises" => some .raises | _ => none
  let num (k : String) (t : Json) : Option Lean.JsonNumber :=
    match t.getObjVal? k with
    | .ok (.str s) => (match Json.parse s with | .ok (.num n) => some n | _ => none)
    | _ => none
  let floats ← match j.getObjVal? "floats" with
    | .ok (.str "exact") => some Fl.exact
    | .ok (.str "plan") => some Fl.plan
    | .ok t@(.obj _) => some (Fl.within { abs := (num "abs" t), rel := (num "rel" t),
        ulps := ((t.getObjValAs? Nat "ulps").toOption) })
    | _ => none
  return { q := { rows := rows, elements := elements, zeros := zeros, times := times,
    strings := strings, errors := errors, decimals := decimals }, floats := floats }

/-- The double columns a postcondition holds to the reference's exact value under the plan's
bound (`observed`): those it reads, where it is proved, not `approx` and not robust, by the
index of the first such condition. `conds` is each condition's `{"kind", "approx", "reads"}`
(`"reads"` null: every column), `proved` and `robust` those of the expression conditions in
order, `keys` the proofs of the `unique` conditions. -/
def heldCols (doubles : List Nat) (names : List String) (conds : List Json) (proved robust keys : List Bool) :
    List (String × Nat) := Id.run do
  let mut held : List (String × Nat) := []
  let mut ei := 0
  let mut ki := 0
  let mut i := 0
  for m in conds do
    let kind := (m.getObjValAs? String "kind").toOption.getD "other"
    let approx := (m.getObjValAs? Bool "approx").toOption.getD false
    let (p, rb) := if kind == "expr" then (proved.getD ei false, robust.getD ei false)
      else if kind == "unique" then (keys.getD ki false, false) else (false, false)
    if kind == "expr" then ei := ei + 1
    if kind == "unique" then ki := ki + 1
    if !approx && p && !rb then
      let reads : List Nat := match m.getObjVal? "reads" with
        | .ok (.arr a) => a.toList.filterMap fun x => x.getNat?.toOption
        | _ => doubles
      for c in reads do
        if doubles.contains c then
          if let some n := names[c]? then
            if (held.lookup n).isNone then held := held ++ [(n, i)]
    i := i + 1
  return held

variable [Boxes.Ambient]
/-- `"engines"` and `"sorted"` of a `--contract` request, given its
`"rows_exact"` (`Epsilon.rowsExactByEngine`), its report and `"robust"`
(`EngineRobust.robust`). An engine the request names (`"engines"`) without a
profile here gets `unprofiledJson`. -/
def enginesJson (es : List EngineProfile) (input : Json) (rowsExact : Json)
    (rep : ContractCheck.Report) (robust : Json) (eps : Json) :
    Except String (List (String × Json)) := do
  let some reads ← Epsilon.dependsReads input | return []
  let some tj := (input.getObjVal? "transform").toOption | return []
  let plan ← ContractCheck.parseJsonPlan tj
  let all := plan.root.reads
  let ds := deps reads
  -- Without the threshold analysis's answer, the rows may differ.
  let exact (e : String) : Bool := (rowsExact.getObjValAs? Bool e).toOption.getD false
  -- What the postcondition observes (#1071): `seen`, the double columns it holds to the
  -- reference's exact value, and each engine's rows met against both.
  let obs := (input.getObjVal? "observation").toOption
  let stated? : Option Seen := obs.bind fun o => (o.getObjVal? "lenses").toOption.bind Seen.ofJson?
  let doubles : List Nat := (rep.outputKinds.zipIdx.filter fun (k, _) =>
    (k.getObjValAs? String "kind").toOption == some "float").map (·.2)
  let conds : List Json := ((obs.bind (·.getObjValAs? (Array Json) "ensures_meta" |>.toOption)).getD #[]).toList
  let robustFlags : List Bool := (((robust.getArr?).toOption.getD #[]).toList.map fun r =>
    (r.getObjValAs? Bool "robust").toOption.getD false)
  let held : List (String × Nat) := match stated? with
    | some st => if st.floats == .plan then
        heldCols doubles plan.names conds (rep.ensures.flatten.map (·.2.1)) robustFlags
          (rep.keys.map (·.2))
      else []
    | none => []
  let profiled := es.map fun E =>
    let because := testedBecause E input rep robust
    let v := engineJson es E ds all (exact E.name)
    let proved := (v.getObjValAs? String "evidence").toOption == some "proved"
    let epsE := epsilonBounds (some E.name) eps
    let v := v.setObjVal! "profile" (toJson true)
      |>.setObjVal! "epsilon" epsE
      |>.setObjVal! "tested_because" (toJson because)
      |>.setObjVal! "translated_evidence"
        (toJson (if proved && because.isEmpty then "proved" else "tested"))
    let v := match stated? with
      | some st =>
        let rows := rowsAt E ds
        let cols := epsCols epsE
        let (realized, asked) := realizeJson E ds rows v st cols held
        -- The problems the stated doubles meet that the plan's own bound does not.
        let added : List Json := if st.floats == .plan then [] else
          let (_, base) := realizeJson E ds rows v { st with floats := .plan } cols []
          asked.filter (!base.contains ·)
        v.setObjVal! "realized" realized |>.setObjVal! "floats_added" (Json.arr added.toArray)
      | none => v
    (E.name, v)
  let named : List String :=
    ((input.getObjValAs? (Array String) "engines").toOption.getD #[]).toList
  let others := named.eraseDups.filter (fun n => !es.any (·.name == n)) |>.map fun n =>
    (n, unprofiledJson.setObjVal! "epsilon" (epsilonBounds (some n) eps))
  return [("engines", Json.mkObj (profiled ++ others)),
    ("seen", Json.mkObj [("held", Json.mkObj (held.map fun (c, i) => (c, toJson i)))]),
    ("epsilon_bounds", epsilonBounds none eps),
    ("sorted", toJson (sortedRoot plan.root)), ("sorted_basis", toJson "computed")]

end Substrait.Realize
