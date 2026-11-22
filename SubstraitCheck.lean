import SubstraitLean

/-!
`substrait-check`: Sverify's Lean checker. `substrait-check plan.json` parses
a Substrait JSON plan, checks it is well-formed, and evaluates it; the other
modes and commands, each with its line of `--help`, are `modes` and
`commands` below, and `--serve` answers the modes' requests on stdin.

Exit codes: 0 ok (for `--contract`: every postcondition proved), 1
parse/unsupported error, 2 ill-formed plan or a usage error (an unknown
flag, a file that can't be read), 3 not incrementally maintainable, 4 some
postcondition not proved, 5 the plan cannot be split into shards.
-/

open Substrait Parse

namespace Substrait.Checker

/-- Were the generated entries' proofs checked in this build (`--build`)? -/
def generatedChecked : Bool := generated_checked%

/-- The version of what the checker prints and reads, which `sverify` checks
at startup (`sverify.engine.PROTOCOL`): bump both when the output of a mode
changes shape (a JSON field added, renamed or dropped, a new mode), so that a
stale build fails with a clear message instead of a `KeyError`. -/
def protocol : Nat := 3

/-- Shared static checks; `none` means the plan passed. -/
def checkPlan (plan : Plan) : Option (UInt32 × String) :=
  let cat := plan.catalog
  let arity := plan.root.arity cat
  -- `checkWF_iff` makes this the decision procedure for `Rel.WF`.
  if !plan.root.checkWF cat then some (2, "well-formed: no")
  else if !plan.names.isEmpty && plan.names.length != arity then
    some (2, s!"well-formed: no (root names {plan.names} do not match arity {arity})")
  -- `Rel.kinds_sound`: a well-kinded plan evaluates to its kinds.
  else if (plan.root.inferKinds cat plan.tableKinds).isNone then some (2, "well-kinded: no")
  else none

/-- Why a plan has no delta rule: each operator that blocks it (`Rel.blockers`)
with the tables it reads, e.g. `aggregate over orders; left join over a, b`. -/
def blockedMessage (bs : List (String × List String)) : String :=
  let one := fun (k, ts) =>
    if ts.isEmpty then k else s!"{k} over {", ".intercalate ts.eraseDups}"
  s!"not incrementally maintainable: no delta rule for {"; ".intercalate (bs.map one)}"

variable [Boxes.Ambient]
/-- `--delta`: the Substrait JSON plan an engine runs to maintain the plan
incrementally, on one line. It reads the old tables `t` and change tables
`t$delta` (the same columns plus a trailing `__weight`); its output is the
change to the result, with a trailing `__weight` column. -/
def delta (plan : Plan) : IO UInt32 := do
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  -- `isIncremental_iff`: this decides `Rel.Incremental`.
  if !plan.root.isIncremental then
    IO.eprintln (blockedMessage plan.root.blockers); return 3
  let d := plan.root.delta Write.deltaName
  -- `Rel.weighted_eval` needs the delta plan to be incremental and well-formed.
  if !d.isIncremental || !d.checkWF (Write.deltaCatalog plan) then
    IO.eprintln "the delta plan failed its static checks"; return 2
  IO.println (Write.writeDeltaPlan plan d).compress
  return 0

/-- `--reads`: the columns of each table the plan needs. `Rel.zeval_prune`
proves a store keeping a superset of them, consolidated, gives the view: the
set printed is `S` with `Rel.readsOnly` true, for a well-formed incremental
plan. -/
def reads (plan : Plan) : IO UInt32 := do
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  let cat := plan.catalog
  let r := plan.root
  let cols (t : String) : Lean.Json :=
    -- `isIncremental_iff`: this decides `Rel.Incremental`, which the theorem needs.
    if r.isIncremental then
      .arr ((r.colsOf cat t (List.range (r.arity cat))).eraseDups.mergeSort.map
        (fun i => Lean.toJson i)).toArray
    else .str "all"
  IO.println (Lean.Json.mkObj (r.tables.eraseDups.map fun t => (t, cols t))).compress
  return 0

/-- A result value, printed by its column's kind: integers (unbounded in the
model, so `MAX + 1` is a value) exactly, doubles as doubles, and the values
in a list or struct by their own kinds (a decimal in a list with its scale,
#628). A column of unknown kind falls back to `Value.render`. -/
partial def renderCell : Kind → Value → String
  | _, .float c => s!"{FloatCode.toFloat c}d"
  | _, .dec s i => decimalString s i
  | _, .int i | _, .ts i | _, .date i => toString i
  | .list k, .list vs => "[" ++ ", ".intercalate (vs.map (renderCell k)) ++ "]"
  | .struct ks, .struct vs =>
    "[" ++ ", ".intercalate ((vs.zipIdx).map fun (v, i) => renderCell (ks.getD i .other) v) ++ "]"
  | _, v => v.render

#guard renderCell (.list (.dec 4 1)) (.list [.dec 1 10, .null, .dec 1 25]) == "[1.0, NULL, 2.5]"
#guard renderCell (.struct [.str, .dec 9 3]) (.struct [.str "a", .dec 3 1500]) == "[\"a\", 1.500]"

/-- A value as JSON, doubles as their codes (`core/Sverify/Core/Float.lean`). -/
def valueJson : Value → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .int i | .float i | .date i | .ts i | .tod i | .dec _ i => .num (Lean.JsonNumber.fromInt i)
  | .str s => .str s
  | .list vs | .struct vs => .arr (vs.attach.map fun ⟨v, _⟩ => valueJson v).toArray

/-- `--outcomes`: a `Project` over a `VALUES`, each row's expressions
evaluated under the profile `p` (`Expr.evalP`): the value, or the error it
raises. One JSON list per row, for probing an engine's functions (#242).
`--outcomes-duckdb-stopgap` evaluates under DuckDB's profile: an internal
stopgap for one test, to be replaced by the `semantics="duckdb"`
engine-to-engine path (#1288). No other engine gets one. -/
def outcomes (p : Profile := Profile.reference) (plan : Plan) : IO UInt32 := do
  let rec body : Rel → Option (Relation × List Expr)
    | .emit r _ => body r
    | .project (.values _ rows) es => some (rows, es)
    | _ => none
  let some (rows, es) := body plan.root
    | IO.eprintln "error: --outcomes needs a Project over a VALUES"; return 1
  for row in rows do
    let outs := es.map fun e => match e.evalP p row with
      | .ok v => Lean.Json.mkObj [("ok", valueJson v)]
      | .error k => Lean.Json.mkObj [("error", toString (repr k))]
    IO.println (Lean.Json.arr outs.toArray).compress
  return 0

/-- The first error the reference profile `p` raises evaluating `es` on `rows`
(`Expr.evalP`), as its name. -/
def firstError (p : Profile) (rows : Relation) (es : List Expr) : Option String :=
  rows.findSome? fun row => es.findSome? fun e => match e.evalP p row with
    | .error k => some (toString (repr k))
    | .ok _ => none

/-- The first error the reference profile `p` raises in the arguments and filters
of a window's aggregates, each on the frame of each row (`WinFn.valueIn`):
`before` are the sorted rows already visited. -/
def windowRaised (p : Profile) (part : List Nat) (fns : List WinFn) :
    List Row → List Row → Option String
  | _, [] => none
  | before, x :: after =>
    let pb := before.filter (samePart part x)
    let pa := after.filter (samePart part x)
    (fns.findSome? fun
      | .agg m sort fr =>
        let frame := fr.rows sort pb x pa
        firstError p frame m.filter.toList <|> firstError p (m.kept frame) [m.arg]
      | _ => none) <|> windowRaised p part fns (before ++ [x]) after

-- A window aggregate raises only on the rows a frame holds: `12.35` (a `DECIMAL(3, 2)` of
-- 4 digits) is the last row, so `1 PRECEDING` holds it in no frame, and the whole
-- partition holds it in the last row's.
section
local instance : Boxes.Ambient := Boxes.Ambient.none
private def windowRows' : Relation := [[.int 1, .dec 2 5], [.int 2, .dec 2 1235]]
private def windowAgg (fr : Frame) : List WinFn :=
  [.agg { fn := .sum, arg := .un (.decimal 3 2) (.field 1) } [{ col := 0 }] fr]
#guard (windowRaised Profile.reference [] (windowAgg ⟨false, .preceding 1, .preceding 1⟩) []
  windowRows').isNone
#guard (windowRaised Profile.reference [] (windowAgg Frame.all) [] windowRows').isSome
end

/-- The first error the reference profile `p` raises in the plan: each
filter, projection and aggregate evaluates its expressions on the rows its
input gives (`Rel.evalFast`, which equals `Rel.eval`), inputs first. An
aggregate's argument is evaluated on the rows its filter keeps. A join's or
semi join's condition is evaluated on the pairs `Rel.evalFast` tests, the left
row with the right rows of its equi-join keys (`JoinIndex.candidates`; all of
them where the condition has none), not on the cross product, which is
quadratic (`test_eval_fast`). So a raise on a pair the key index drops can be
missed: the reference evaluates `on` eagerly on every pair (D19), and no
theorem says `evalFast` raises where `Rel.eval` does (`candidates_eq` says only
that a dropped pair's `on` is not TRUE). Every error reported is real. A window's
aggregates are evaluated on the frame of each row, as `WinFn.valueIn` does: a row
that no frame holds raises nothing (`windowRaised`). -/
def relRaised (cat : Catalog) (p : Profile) : Rel → Option String
  | .read _ | .values _ _ => none
  | .filter r c => relRaised cat p r <|> firstError p (r.evalFast cat) [c]
  | .project r es => relRaised cat p r <|> firstError p (r.evalFast cat) es
  | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ =>
    relRaised cat p r
  | .window r part sort fns =>
    relRaised cat p r <|> windowRaised p part fns [] ((r.evalFast cat).mergeSort (sortLe sort))
  | .cross a b | .unionAll a b => relRaised cat p a <|> relRaised cat p b
  | .join a b _ on | .semi a b _ on =>
    let index := JoinIndex.make on (a.arity cat) (b.evalFast cat)
    relRaised cat p a <|> relRaised cat p b <|> (a.evalFast cat).findSome? fun x =>
      firstError p ((index.candidates x).map (x ++ ·)) [on]
  | .aggregate r gs ms =>
    let rows := r.evalFast cat
    relRaised cat p r <|> firstError p rows gs <|> ms.findSome? fun m =>
      firstError p rows m.filter.toList <|> firstError p (m.kept rows) [m.arg]

/-- `--raises`: the first error the reference raises anywhere in the plan
(`relRaised`), printed as its name; nothing where it raises none. -/
def raises (plan : Plan) : IO UInt32 := do
  if let some e := relRaised plan.catalog Profile.reference plan.root then
    IO.println e
  return 0

/-- The first assumed issue (`Issue.assumed`) the plan as written runs into on
its data, evaluated as `Rel.HasIssue` states it: `Expr.issues` on every row an
operator evaluates (its loose input under a filter or join, `Rel.loose`), and
per group the true `SUM` (`Measure.sumOk`) and an aggregate of finite doubles
that is `±∞` (`Measure.makesInf`). A window's aggregates are not evaluated:
none where the plan has one. The test oracle of the assumed check (#2018). -/
def relAssumed (cat : Catalog) : Bool → Rel → Option (Issue × Expr)
  | _, .read _ | _, .values _ _ => none
  | _, .filter r c => relAssumed cat true r <|> exprAssumed (r.loose.evalFast cat) [c]
  | u, .project r es =>
    relAssumed cat u r <|> exprAssumed ((if u then r.loose else r).evalFast cat) es
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r | u, .unnest r _ =>
    relAssumed cat u r
  | _, .window _ _ _ _ => none
  | u, .cross a b | u, .unionAll a b => relAssumed cat u a <|> relAssumed cat u b
  | _, .join a b _ on | _, .semi a b _ on =>
    relAssumed cat true a <|> relAssumed cat true b <|>
      exprAssumed ((Rel.cross a.loose b.loose).evalFast cat) [on]
  | u, .aggregate r gs ms =>
    let rows := r.evalFast cat
    relAssumed cat u r <|>
      exprAssumed ((if u then r.loose else r).evalFast cat) (gs ++ ms.flatMap Measure.exprs) <|>
      ms.findSome? fun m => (aggGroups gs rows).findSome? fun grp =>
        if m.fn = .sum ∧ !m.sumOk (intSum (m.inputs grp)) then some (.sumWraps, m.arg)
        else if m.makesInf grp then some (.infinite, m.arg) else none
where
  exprAssumed (rows : Relation) (es : List Expr) : Option (Issue × Expr) :=
    rows.findSome? fun row => es.findSome? fun e => (e.issues row).find? (·.1.assumed)

/-- `--assumed`: the first assumed issue the plan runs into on its data
(`relAssumed`), printed as its name; nothing where it runs into none. -/
def assumed (plan : Plan) : IO UInt32 := do
  if let some (i, _) := relAssumed plan.catalog false plan.root then
    IO.println (Issue.name i)
  return 0

/-- `spec`: evaluate with `Rel.eval`, the specification, in place of
`Rel.evalFast` (equal by `Rel.evalFast_eq`; `--eval-spec`, for tests).
`full := false` prints only the well-formedness verdict and the rows
(`--rows`). -/
def check (plan : Plan) (spec : Bool := false) (full : Bool := true) : IO UInt32 := do
  let cat := plan.catalog
  if full then
    IO.println plan.root.render
    let tables := (plan.tables.filter (!isInternalKey ·.1) |>.map fun (t, n, _) => s!"{t}({n})").eraseDups
    unless tables.isEmpty do
      IO.println s!"tables: {", ".intercalate tables}"
    IO.println s!"arity: {plan.root.arity cat}"
  if let some (code, msg) := checkPlan plan then
    IO.println msg; return code
  IO.println "well-formed: yes"
  if full then
    IO.println s!"incremental: {if plan.root.isIncremental then "yes" else "no"}"
    IO.println s!"roundtrip: {if Write.roundtrips plan then "ok" else "FAILED"}"
  -- Named tables have no data in the schema-only catalog, so only
  -- `VirtualTable` rows show up here.
  -- Lean's evaluator panics at the black boxes it does not evaluate
  -- (`Text.lean`: non-ASCII `UPPER`/`LOWER`, regular expressions) and goes
  -- on with a placeholder; `runOn` refuses the answer of any mode that panicked (#70).
  -- The writer's kinds, which call a bare double literal's column a double
  -- where `Rel.kinds` calls it an integer (#96).
  let kinds := (Write.relKinds (Write.planSchemas plan) cat plan.root).map Write.WKind.toKind
  let rows := (if spec then plan.root.eval cat else plan.root.evalFast cat).map fun row =>
    let cells := row.zipIdx.map fun (v, i) => renderCell (kinds.getD i .other) v
    s!"({", ".intercalate cells})"
  IO.println s!"rows ({rows.length}):"
  for row in rows do
    IO.println s!"  {row}"
  return 0

/-- `--eval-choices`: the rows with the values every order of the ties
allows (`Rel.evalChoices`), as one JSON object: `{"rows": [...]}`, each
cell `{"v": c}`, `{"any": [c, …]}`, `{"concat": {"sep": s, "classes":
[[c, …], …]}}` or `{"collect": [[c, …], …]}` with `c` as `renderCell` writes
it; `{"rows": null}` where the data leaves a choice it does not list. -/
def evalChoices (plan : Plan) : IO UInt32 := do
  let cat := plan.catalog
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  let kinds := (Write.relKinds (Write.planSchemas plan) cat plan.root).map Write.WKind.toKind
  let cellJson (k : Kind) : TieChoice → Lean.Json
    | .val v => Lean.Json.mkObj [("v", renderCell k v)]
    | .anyOf vs => Lean.Json.mkObj [("any", Lean.toJson (vs.map (renderCell k)))]
    | .concat sep cs => Lean.Json.mkObj [("concat", Lean.Json.mkObj
        [("sep", Lean.toJson sep), ("classes", Lean.toJson (cs.map (·.map (renderCell .str))))])]
    | .collect cs =>
      let ek := match k with | .list e => e | _ => .other
      Lean.Json.mkObj [("collect", Lean.toJson (cs.map (·.map (renderCell ek))))]
  let out := match plan.root.evalChoices cat with
    | some rows => Lean.Json.arr (rows.map fun row =>
        Lean.Json.arr (row.zipIdx.map fun (c, i) => cellJson (kinds.getD i .other) c).toArray).toArray
    | none => Lean.Json.null
  IO.println (Lean.Json.mkObj [("rows", out)]).compress
  return 0

/-- `--write`: the plan in Lean's written form (the plan `Rel.eval` runs, as
Substrait JSON). -/
def write (plan : Plan) : IO UInt32 := do
  -- Decimals (#27) are written back as Substrait's own calls and casts where
  -- that parses back to the same plan.
  if plan.root.decimalOps && !Write.roundtrips plan then
    IO.eprintln "error: this decimal arithmetic cannot be written for the engines yet (#27)"
    return 1
  -- Arguments of nested calls become columns (`Parse.Plan.writtenRoot`).
  IO.println (Write.writePlan (Write.planSchemas plan) plan.catalog plan.writtenRoot plan.names).compress
  return 0

open Lean (Json toJson) in
/-- A `--contract` report under the profile the request names (`"profile"`).
Under the reference it is the report as it is. Under Substrait, the
reference's proof carries over when the transfer check passes on the
transformation: Substrait allows only behaviours the reference allows at every
option it meets (`Rel.transfer_of_transferB`). Where it does not, no
postcondition or key is proved under Substrait, and `"transfer"` names the
options. An engine of `es` (DuckDB, Polars, Spark, or one from outside)
has no report under its profile yet (#1288, #271): its
request gets the reference's report, labelled `"reference"`, with `"pending"`
naming the profile asked for. Polars's plan is built with `division_type:
FLOOR`, which the parser reads as the reference's templates
(`Polars.elaborate_eq`, `engines/polars/Sverify/Polars/Profile.lean`), so the
plan's meaning is the same; only the label differs. A name the checker does
not know gets the reference's report alone. -/
def underProfile (es : List EngineProfile) (j : Json) (report : Json) (proved : Bool) :
    Except String (Json × Bool) := do
  let name := (j.getObjValAs? String "profile").toOption.getD "reference"
  unless name == "substrait" do
    let report := report.setObjVal! "profile" "reference"
    return (if (engineNamed? es name).isSome then report.setObjVal! "pending" name else report,
      proved)
  let tj ← j.getObjVal? "transform"
  let plan ← ContractCheck.parseJsonPlan tj
  let P := Profile.reference.table
  let S := Profile.substrait.table
  let failures := plan.root.reads.eraseDups.filter fun p => !S.leAtB P p
  let report := report.setObjVal! "profile" "substrait"
  if failures.isEmpty then
    return (report.setObjVal! "transfer" (Json.mkObj [("from", "reference"), ("ok", true),
      ("failures", Json.arr #[])]), proved)
  let unprove (k : String) (r : Json) : Json :=
    match r.getObjValAs? (Array Json) k with
    | .ok xs => r.setObjVal! k (Json.arr (xs.map (·.setObjVal! "proved" false)))
    | .error _ => r
  let rows := failures.map fun (g, o, ps) => Json.mkObj [("group", toJson g), ("option", toJson o),
    ("preferences", toJson ps), ("substrait", toJson (S.allows g o ps)),
    ("reference", toJson (P.allows g o ps))]
  return (unprove "keys" (unprove "ensures" report) |>.setObjVal! "transfer"
    (Json.mkObj [("from", "reference"), ("ok", false), ("failures", Json.arr rows.toArray)]), false)

/-- A black box's laws, as `--black-boxes` and the report print them. -/
def lawsJson (ls : List BlackBox.Law) : Lean.Json :=
  Lean.Json.arr (ls.map fun
    | .nonNull => Lean.Json.arr #["non_null"]
    | .atLeast k => Lean.Json.arr #["at_least", Lean.toJson k]
    | .atMost k => Lean.Json.arr #["at_most", Lean.toJson k]).toArray

/-- The calls of a plan's window measures, which `Rel.ctors` and
`Rel.aggFns` leave out. -/
def _root_.Substrait.Rel.windowCtors : Rel → List Functions.Ctor
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ | .aggregate r _ _ => r.windowCtors
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => a.windowCtors ++ b.windowCtors
  | .window r _ _ fns => r.windowCtors ++ (WinFn.aggs fns).flatMap fun m => .agg m.fn :: m.ctors

/-- The black boxes a plan calls, by name, once each. -/
def _root_.Substrait.Rel.blackBoxNames (r : Rel) : List String :=
  ((r.ctors ++ r.aggFns.map Functions.Ctor.agg ++ r.windowCtors).filterMap fun
    | .un (.bbox n) | .bin (.bbox2 n) | .agg (.bbox n) => some n
    | _ => none).eraseDups

/-- The black boxes `r` calls with the laws their rows declare, the one
source of what each proof may assume of them (#1484): `[{"name", "laws"}]`,
the laws as in `blackBoxJson`. -/
def blackBoxesOf (r : Rel) : Lean.Json :=
  let lawsOf (n : String) : List BlackBox.Law :=
    match Boxes.Ambient.boxes.scalar? n, Boxes.Ambient.boxes.aggregate? n with
    | some f, _ => f.laws
    | none, some f => f.laws
    | none, none => []
  Lean.Json.arr (r.blackBoxNames.map fun (n : String) => Lean.Json.mkObj
    [("name", Lean.Json.str n), ("laws", lawsJson (lawsOf n))]).toArray

/-- A black box whose function breaks its declared law: `non_null`, and it
gives NULL. The model keeps the sample there and the compiled checker panics
(`BlackBox.Scalar.call`), so `runOn` refuses the rows (#1484). Internal, for
`--law-break-selftest`. -/
def lawBreakRow : BlackBox.Scalar where
  name := "law_break_selftest"
  args := [.str]
  result := .int
  laws := [.nonNull]
  sample := .int 0
  eval _ := .null

/-- `--contract`: try to prove a contract request's postconditions from its
preconditions (`SubstraitLean/ContractCheck.lean` has the input format) and
print a JSON report; exit 4 when one is not proved. The request is parsed once
for the report, the plan an engine runs and the black boxes. -/
def contract (es : List EngineProfile) (input : String) : IO UInt32 := do
  match (do
      let j ← Lean.Json.parse input
      let R ← ContractCheck.parse j
      return (j, R, ← R.check) : Except String _) with
  | .error e => IO.eprintln s!"error: {e}"; return 1
  | .ok (j, R, report) =>
    -- The profile it was checked under (`underProfile`), and the options
    -- the transformation meets (#444).
    let depends := (Epsilon.depends j).toOption.getD Lean.Json.null
    -- Per double SUM or AVG output, the plan's #85 bound (`Epsilon.lean`).
    let eps := (Epsilon.epsilon es j).toOption.getD (Lean.Json.mkObj [])
    -- The same carried through the arithmetic, per engine.
    let byEngine := (Epsilon.epsilonByEngine es j).toOption.getD
      (Lean.Json.mkObj [])
    -- Per engine, whether filters, keys and sorts keep the same rows under ε.
    let rowsExact := (Epsilon.rowsExactByEngine es j).toOption.getD
      (Lean.Json.mkObj [])
    -- Per postcondition, whether it holds on every engine's doubles (#1045).
    let robust := (EngineRobust.robust es j).toOption.getD (Lean.Json.arr #[])
    -- The margin checks of threshold filters on double sums (#929).
    let margins := (Epsilon.marginChecksJson es j).toOption.getD (Lean.Json.arr #[])
    -- The pair counts of its as-of joins (#1447).
    let asofs := (Epsilon.asofChecksJson j).toOption.getD (Lean.Json.arr #[])
    -- Per engine, the plan's class, evidence and what refuses it (#1166).
    let engines := (Realize.enginesJson es j rowsExact report robust eps).toOption.getD []
    -- The plan an engine runs, or the gate that keeps the plan as
    -- written (#1787, `SubstraitLean/RunPlan.lean`).
    let runPlan := R.runPlanJson ++ [("assumed_check", R.assumedCheckJson R.kenv)]
    let withRun := runPlan.foldl (fun b (k, v) => b.setObjVal! k v) report.json
    -- A decision on a marked value (D52, ruling 104): an error issue.
    let source := (EngineRobust.sourceIssues es j).toOption.getD []
    let issues := ((withRun.getObjValAs? (Array Lean.Json) "issues").toOption.getD #[]) ++
      source.toArray
    let base := withRun |>.setObjVal! "issues" (Lean.Json.arr issues)
        |>.setObjVal! "depends" depends
        |>.setObjVal! "epsilon" eps |>.setObjVal! "epsilon_by_engine" byEngine
        |>.setObjVal! "rows_exact" rowsExact |>.setObjVal! "robust" robust
        |>.setObjVal! "margin_checks" margins
        |>.setObjVal! "asof_checks" asofs
        -- The black boxes the transformation calls, with their laws (#1484).
        |>.setObjVal! "black_boxes"
          ((R.transform.map fun T => blackBoxesOf T.root).getD (Lean.Json.arr #[]))
    match underProfile es j (engines.foldl (fun r (k, v) => r.setObjVal! k v) base)
        (report.allProved && source.isEmpty) with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok (out, proved) =>
      IO.println out.compress
      return if proved then 0 else 4

/-- `--shard`: split a plan for evaluation on shards of some of its tables
(`SubstraitLean/ShardCheck.lean`), or say why it cannot be split (exit 5). -/
def shard (input : String) : IO UInt32 := do
  match Lean.Json.parse input with
  | .error e => IO.eprintln s!"error: {e}"; return 1
  | .ok j => match ShardCheck.check j with
    | .error e => IO.eprintln e; return 5
    | .ok out => IO.println out.compress; return 0

/-- `mode` on the plan the input parses to. -/
def onPlan (mode : Plan → IO UInt32) (input : String) : IO UInt32 :=
  match parsePlan input with
  | .ok plan => mode plan
  | .error e => do IO.eprintln s!"error: {e}"; return 1

/-- Where a flag goes on `--help`'s page. -/
inductive Group | check | diagnostics | serve | tables
  deriving BEq

def Group.title : Group → String
  | .check => "Checking a plan"
  | .diagnostics => "Diagnostics"
  | .serve => "Serving"
  | .tables => "Tables and coverage"

/-- A flag of `substrait-check`: what it does (`run`) and its line on the
`--help` page, side by side, so the two can't drift. -/
structure Flag (α : Type) where
  flag : String
  group : Group
  /-- What it reads, as the help page writes it: `<plan.json>`, `< report.json`. -/
  arg : String := ""
  help : String
  run : α

/-- The flag and its argument, the help page's left column. -/
def Flag.usage (f : Flag α) : String :=
  if f.flag.isEmpty then f.arg else if f.arg.isEmpty then f.flag else s!"{f.flag} {f.arg}"

/-- A mode that reads a plan. -/
def planMode (flag : String) (group : Group) (help : String) (mode : Plan → IO UInt32) :
    Flag (String → IO UInt32) :=
  { flag, group, arg := "<plan.json>", help, run := onPlan mode }

/-- The modes that read an input: from the file named after the flag, or as a
`--serve` request. The default check's flag is empty. -/
def modes (es : List EngineProfile) : List (Flag (String → IO UInt32)) := [
  planMode "" .check "parse the plan, check it is well-formed, and evaluate it" (check · false),
  planMode "--eval-spec" .check "the same, evaluated with Rel.eval (the specification)"
    (check · true),
  planMode "--rows" .check "the well-formedness verdict and the rows only (#825)"
    (check · false false),
  planMode "--eval-choices" .check "the rows with every value the ties allow, as JSON"
    evalChoices,
  planMode "--write" .check "the plan Rel.eval runs, as Substrait JSON" write,
  planMode "--delta" .check "the plan an engine runs to maintain this one incrementally" delta,
  planMode "--reads" .check "per table, the columns the output needs (#1329), as JSON" reads,
  { flag := "--contract", group := .check, arg := "<contract.json>",
    help := "prove a contract's postconditions; a JSON report, exit 4 if one fails",
    run := contract es },
  { flag := "--shard", group := .check, arg := "<request.json>",
    help := "split a plan for evaluation on shards, or say why not (exit 5)", run := shard },
  planMode "--dependencies" .check "the options the plan meets and the transfer check (#444)"
    fun plan => do IO.println (plan.root.dependenciesJson es).compress; return 0,
  planMode "--outcomes" .diagnostics "per VALUES row, the reference's value or error (#242)"
    (outcomes Profile.reference),
  -- Internal stopgap; converges to `semantics="duckdb"` (#1288).
  planMode "--outcomes-duckdb-stopgap" .diagnostics "--outcomes under DuckDB's profile (internal)"
    (outcomes (Profile.duckdb {})),
  planMode "--raises" .diagnostics "the first error the reference raises in the plan" raises,
  planMode "--assumed" .diagnostics "the first assumed issue the plan runs into (#2018)" assumed,
  { flag := "--law-break-selftest", group := .diagnostics, arg := "<text>",
    help := "call a law-breaking black box, which must be refused (internal)",
    run := fun input => do IO.println (repr (lawBreakRow.call [.str input])); return 0 }]

/-- One request of `--serve`: the mode flag (empty for the default check)
and the input text. -/
def runModes (es : List EngineProfile) (flag : String) (input : String) : IO UInt32 := do
  match (modes es).find? (·.flag == flag) with
  | some m => m.run input
  | none => IO.eprintln s!"unknown mode {flag}"; return 1

/-- `act` with stdout and stderr captured. -/
def capture (act : IO UInt32) : IO (UInt32 × ByteArray × ByteArray) := do
  let out ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let err ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let code ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) act
  return (code, (← out.get).data, (← err.get).data)

/-- One request, in any mode: its answer, unless Lean panicked while
computing it. A panic (`Text.lean`: non-ASCII `UPPER`/`LOWER`/`ILIKE`, regular
expressions Rust and RE2 read differently; the black boxes) prints `PANIC` to
stderr and goes on with a placeholder, which would be printed as a result. The
request is refused instead, in every mode (`--outcomes` included), with the
panic's message (#70, R6). -/
def runOn (es : List EngineProfile) (flag : String) (input : String) : IO UInt32 := do
  let (code, out, err) ← capture (runModes es flag input)
  let some errText := String.fromUTF8? err
    | IO.eprintln "error: rows not evaluated: the checker's stderr is not UTF-8"
      return 1
  if let some msg := (errText.splitOn "\n").find? (·.startsWith "PANIC") then
    IO.eprintln s!"error: rows not evaluated: {(msg.splitOn ": ").drop 1 |> ": ".intercalate}"
    return 1
  (← IO.getStdout).write out
  (← IO.getStderr).write err
  return code

partial def readExactly (h : IO.FS.Stream) (n : Nat) (acc : ByteArray := .empty) : IO ByteArray := do
  if acc.size ≥ n then return acc
  let chunk ← h.read (n - acc.size).toUSize
  if chunk.isEmpty then throw (IO.userError "unexpected end of input")
  readExactly h n (acc ++ chunk)

/-- `substrait-check --serve`: answer requests on stdin until it closes.
A request is a line `<flag> <n>` (flag `-` for the default check) and then
`n` bytes of input; the reply is a line `<exit code> <m> <k>` and then `m`
bytes of stdout and `k` bytes of stderr. Saves a process start (most of it
Lean's module initialization) per plan. -/
partial def serve (es : List EngineProfile) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match line.trimAscii.toString.splitOn " " with
    | [flag, n] =>
      let input ← readExactly stdin n.toNat!
      let flag := if flag == "-" then "" else flag
      let run := try runOn es flag (String.fromUTF8! input) catch e => do
        IO.eprintln s!"error: {e}"; pure 1
      let (code, out, err) ← capture run
      stdout.putStr s!"{code} {out.size} {err.size}\n"
      stdout.write out
      stdout.write err
      stdout.flush
    | _ => IO.eprintln s!"bad request {line}"; return 1
  return 0

/-- The black boxes' table (#325) as JSON, which `tests/test_black_box.py`
compares with `sverify.black_box`. -/
def blackBoxJson : Lean.Json :=
  let obj := Lean.Json.mkObj
  let ty : BlackBox.Ty → Lean.Json
    | .int => "int" | .double => "double" | .str => "str" | .bool => "bool" | .date => "date"
    | .timestamp => "timestamp"
    | .atom => "atom" | .doubles => "doubles" | .ints => "ints" | .strs => "strs" | .any => "any"
  let laws := lawsJson
  Lean.Json.arr ((Boxes.Ambient.boxes.scalars.map fun f => obj [
      ("name", f.name), ("kind", "scalar"), ("anchor", Lean.toJson (Write.bbAnchor f.name)),
      ("args", Lean.Json.arr (f.args.map ty).toArray), ("result", ty f.result),
      ("strict", Lean.toJson f.strict), ("raises", Lean.toJson (f.raises == .sometimes)),
      ("laws", laws f.laws)]) ++
    (Boxes.Ambient.boxes.aggregates.map fun f => obj [
      ("name", f.name), ("kind", "aggregate"), ("anchor", Lean.toJson (Write.bbAnchor f.name)),
      ("raises", Lean.toJson (f.raises == .sometimes)),
      ("args", Lean.Json.arr #[ty f.arg]), ("result", ty f.result),
      ("empty", Write.writeValue f.empty), ("laws", laws f.laws)])).toArray

/-- A command that prints `out` and exits 0. -/
def prints (flag : String) (group : Group) (help : String) (out : Unit → String) :
    Flag (Unit → IO UInt32) :=
  { flag, group, help, run := fun _ => do IO.print (out ()); return 0 }

/-- The commands that take no file. -/
def commands (entries : List EngineEntry) : List (Flag (Unit → IO UInt32)) :=
  let es := entries.map (·.rows)
  [{ flag := "--serve", group := .serve,
     help := "answer requests for the modes above on stdin, one process for many plans",
     run := fun _ => serve es },
   { flag := "--transfer", group := .serve, arg := "< report.json",
     help := "the option-wise transfer check on a dependency report (#444)",
     run := fun _ => do
       let input ← (← IO.getStdin).readToEnd
       match Lean.Json.parse input >>= transferJson es with
       | .ok out => IO.println out.compress; return 0
       | .error e => IO.eprintln s!"error: {e}"; return 1 },
   prints "--version" .serve "the protocol of what the checker prints and reads" fun _ =>
     s!"substrait-check protocol {protocol}\n",
   -- Without `check_generated`, the theorems over the generated entries rest on
   -- `sorryAx` (docs/trusted-base.md).
   prints "--build" .diagnostics "whether this build checked the generated entries' proofs"
     fun _ => s!"generated proofs {if generatedChecked then "checked" else "unchecked"}\n",
   { flag := "--lowering-coverage", group := .tables,
     help := "how each construct is lowered to DuckDB (#241), one per line",
     run := fun _ => do
       for (c, how, _) in duckdbOn.coverage do
         IO.println s!"error_on_division_by_zero=on\t{c}\t{how}"
       return 0 },
   { flag := "--lowering-coverage-polars", group := .tables,
     help := "how each construct is lowered to Polars (#271), one per line",
     run := fun _ => do
       for (c, how, _) in polarsOn.coverage do
         IO.println s!"{c}\t{how}"
       return 0 },
   prints "--lowering-table" .tables
     "the DuckDB lowering's templates, and Polars's under \"polars\", as JSON (#241, #271)" fun _ =>
     (Lowering.duckdbTableJson.setObjVal! "polars" Lowering.polarsTableJson).compress ++ "\n",
   prints "--lowering-cache" .tables "a new LoweringCache.lean from this build's coverage (#242)"
     fun _ => loweringCacheSource,
   prints "--lift-table" .tables "what each DuckDB SQL function lifts to, as JSON (#268)" fun _ =>
     Lift.tableJson.pretty ++ "\n",
   prints "--lift-cache" .tables "a new LiftCache.lean from this build's tables (#268)" fun _ =>
     Lift.cacheSource,
   prints "--black-boxes" .tables "the black boxes and their laws, as JSON (#325)" fun _ =>
     blackBoxJson.compress ++ "\n",
   prints "--rules" .tables "the rewrite rules and the gate's defaults, as JSON (#1787)" fun _ =>
     ContractCheck.rulesJson.compress ++ "\n",
   prints "--functions" .tables "the function tables, as JSON (#544)" fun _ =>
     Functions.tableJson.compress ++ "\n",
   prints "--options" .tables "the options, profiles' choices and observations, as JSON (#444)"
     fun _ => (tablesJson es).compress ++ "\n",
   prints "--realizability" .tables "per engine, the reference's obligations, as JSON (#444)"
     fun _ => (realizabilityJson entries).compress ++ "\n",
   prints "--profile-diff" .tables "where Substrait's choices and the reference's differ (#444)"
     fun _ => substraitDiffJson.compress ++ "\n"]

/-- `--help`'s page, from the flags' own lines. -/
def helpPage (modes : List (Flag (String → IO UInt32))) (cmds : List (Flag (Unit → IO UInt32))) :
    String :=
  let rows := modes.map (fun f => (f.group, f.usage, f.help)) ++
    cmds.map (fun f => (f.group, f.usage, f.help))
  let width := rows.foldl (fun n (_, u, _) => max n u.length) "-h, --help".length
  let line := fun (u h : String) => s!"  {u.pushn ' ' (width - u.length)}  {h}"
  let group := fun (g : Group) =>
    s!"{g.title}:\n" ++ "\n".intercalate ((rows.filter (·.1 == g)).map fun (_, u, h) => line u h)
  "substrait-check: Sverify's Lean checker. It parses a Substrait JSON plan, checks\n" ++
  "it and evaluates it under the reference semantics, and answers sverify's requests.\n\n" ++
  "usage: substrait-check [MODE] <plan.json>\n" ++
  "       substrait-check COMMAND\n\n" ++
  "\n\n".intercalate ([Group.check, .diagnostics, .serve, .tables].map group) ++ "\n\n" ++
  line "-h, --help" "print this page" ++ "\n\n" ++
  "Example:\n  substrait-check --rows tests/fixtures/filter_project.json\n\n" ++
  "Exit codes: 0 ok, 1 parse error or unsupported plan, 2 ill-formed plan or usage error,\n" ++
  "3 not incrementally maintainable, 4 some postcondition not proved, 5 no split into shards.\n"

/-- A usage error: `msg` and a pointer to `--help` on stderr, exit 2. -/
def usageError (msg : String) : IO UInt32 := do
  IO.eprintln s!"substrait-check: {msg}\nRun substrait-check --help for the flags."
  return 2

/-- The checker over the engines `entries`: `substrait-check`'s `main` with
`builtinEntries`, or a package's own checker with its engine added. -/
def checkerMain (entries : List EngineEntry) (args : List String) : IO UInt32 := do
  let es := entries.map (·.rows)
  let ms := modes es
  let cs := commands entries
  -- A mode on the file `path`, or one line naming it when it can't be read.
  let onFile := fun (flag path : String) => do
    match ← (IO.FS.readFile path).toBaseIO with
    | .ok input => runOn es flag input
    | .error e =>
      IO.eprintln s!"substrait-check: cannot read {path}: {(toString e).splitOn "\n" |>.headD ""}"
      return 2
  match args with
  | [] => IO.eprint (helpPage ms cs); return 2
  | ["--help"] | ["-h"] => IO.print (helpPage ms cs); return 0
  | [arg] =>
    if let some c := cs.find? (·.flag == arg) then return ← c.run ()
    if let some m := ms.find? (·.flag == arg) then
      return ← usageError s!"{arg} needs a file: {m.usage}"
    if arg.startsWith "-" then return ← usageError s!"unknown option {arg}"
    onFile "" arg
  | [flag, path] =>
    if ms.any (·.flag == flag) then return ← onFile flag path
    if cs.any (·.flag == flag) then return ← usageError s!"{flag} takes no file"
    usageError s!"unknown option {flag}"
  | _ => usageError s!"too many arguments: {" ".intercalate args}"

end Substrait.Checker
