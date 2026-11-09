import SubstraitLean

/-!
`substrait-check plan.json`: parse a Substrait JSON plan, check it is
well-formed, and evaluate it.

`substrait-check --eval-spec plan.json`: the same, evaluated with `Rel.eval`
(the specification) in place of `Rel.evalFast` (`SubstraitLean/EvalFast.lean`),
which is faster and proved equal; for tests.

`substrait-check --delta plan.json`: print the Substrait JSON plan an engine
runs to maintain `plan.json` incrementally, on one line. It reads the old
tables `t` and change tables `t$delta` (the same columns plus a trailing
`__weight`); its output is the change to the result, with a trailing
`__weight` column.

`substrait-check --contract contract.json`: try to prove postconditions from
preconditions (see `SubstraitLean/ContractCheck.lean` for the input format)
and print a JSON report.

`substrait-check --shard request.json`: split a plan for evaluation on
shards of some of its tables (see `SubstraitLean/ShardCheck.lean`), or say
why it cannot be split.

`substrait-check --write plan.json`: print the plan in Lean's written form
(the plan `Rel.eval` runs, as Substrait JSON). `--write-datafusion`: the same
plan for DataFusion to run, compensating for where its semantics differ
(`SubstraitLean/DataFusion.lean`); it does not parse back to the same `Rel`.

`substrait-check --lowering-coverage`: print how each construct is lowered to
DuckDB under each setting of `error_on_division_by_zero`, one per line:
natively, or the generated template (`SubstraitLean/LoweringDuckDB.lean`).

`substrait-check --lowering-table`: print, as JSON, the DuckDB lowering's
templates that are not the native call, for `sverify.sql.lowering`.

`substrait-check --lowering-cache`: print a new `SubstraitLean/LoweringCache.lean`
from this build's coverage, the templates the next build tries first.

`substrait-check --lift-table`: print, as JSON, what each DuckDB SQL function
lifts to under each semantics, generated and proved (`SubstraitLean/LiftDuckDB.lean`).

`substrait-check --outcomes plan.json`: for a plan that projects expressions
over a `VALUES`, each row's outcomes under the reference profile
(`Expr.evalP`): the value (doubles as their codes) or the error raised, one
JSON list per row. `sverify_dev.probe` compares them with DuckDB (#242).

`substrait-check --rows plan.json`: the default check's well-formedness
verdict and rows only, without the plan, its round trip or its other
facts: what the counterexample search reads (#825).

`substrait-check --version`: print `substrait-check protocol <n>` (see
`protocol`).

`substrait-check --serve`: answer requests for the modes above on stdin, one
process for many plans (see `serve`).

Exit codes: 0 ok (for `--contract`: every postcondition proved), 1
parse/unsupported error, 2 ill-formed plan, 3 not incrementally maintainable,
4 some postcondition not proved, 5 the plan cannot be split into shards.
-/

open Substrait Parse

namespace Substrait.Checker

/-- Were the generated entries' proofs checked in this build (`--build`)? -/
def generatedChecked : Bool := generated_checked%

/-- The version of what the checker prints and reads, which `sverify` checks
at startup (`sverify.engine.PROTOCOL`): bump both when the output of a mode
changes shape (a JSON field added, renamed or dropped, a new mode), so that a
stale build fails with a clear message instead of a `KeyError`. -/
def protocol : Nat := 2

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

def delta (plan : Plan) : IO UInt32 := do
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  -- `isIncremental_iff`: this decides `Rel.Incremental`.
  if !plan.root.isIncremental then
    IO.eprintln "not incrementally maintainable (left join, fetch or window)"; return 3
  let d := plan.root.delta Write.deltaName
  -- `Rel.weighted_eval` needs the delta plan to be incremental and well-formed.
  if !d.isIncremental || !d.checkWF (Write.deltaCatalog plan) then
    IO.eprintln "the delta plan failed its static checks"; return 2
  IO.println (Write.writeDeltaPlan plan d).compress
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
  -- on with a placeholder; refuse such rows rather than print them (#70).
  -- The writer's kinds, which call a bare double literal's column a double
  -- where `Rel.kinds` calls it an integer (#96).
  let kinds := (Write.relKinds (Write.planSchemas plan) cat plan.root).map Write.WKind.toKind
  let (panics, rows) ← IO.FS.withIsolatedStreams (isolateStderr := true) do
    -- `lazyPure`: evaluated here, not hoisted out of the isolated streams.
    IO.lazyPure fun _ => (if spec then plan.root.eval cat else plan.root.evalFast cat).map fun row =>
      let cells := row.zipIdx.map fun (v, i) => renderCell (kinds.getD i .other) v
      s!"({", ".intercalate cells})"
  if let some msg := (panics.splitOn "\n").find? (·.startsWith "PANIC") then
    IO.eprintln s!"error: rows not evaluated: {(msg.splitOn ": ").drop 1 |> ": ".intercalate}"
    return 1
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
  let (panics, out) ← IO.FS.withIsolatedStreams (isolateStderr := true) do
    IO.lazyPure fun _ => match plan.root.evalChoices cat with
      | some rows => Lean.Json.arr (rows.map fun row =>
          Lean.Json.arr (row.zipIdx.map fun (c, i) => cellJson (kinds.getD i .other) c).toArray).toArray
      | none => Lean.Json.null
  if let some msg := (panics.splitOn "\n").find? (·.startsWith "PANIC") then
    IO.eprintln s!"error: rows not evaluated: {(msg.splitOn ": ").drop 1 |> ": ".intercalate}"
    return 1
  IO.println (Lean.Json.mkObj [("rows", out)]).compress
  return 0

def write (plan : Plan) : IO UInt32 := do
  -- Decimals (#27) are written back as Substrait's own calls and casts where
  -- that parses back to the same plan.
  if plan.root.decimalOps && !Write.roundtrips plan then
    IO.eprintln "error: this decimal arithmetic cannot be written for the engines yet (#27)"
    return 1
  -- Arguments of nested calls become columns (`Rel.bindArgs`, #821), so the
  -- writers' guards read a column where they would copy a call. Decimal
  -- arithmetic stays as the parser read it: it must parse back (#27).
  -- The bound plan is written only where it parses back as itself.
  let bound := plan.root.bindArgs plan.catalog
  let root := if plan.root.decimalOps || !Write.roundtrips { plan with root := bound } then plan.root
    else bound
  IO.println (Write.writePlan (Write.planSchemas plan) plan.catalog root plan.names).compress
  return 0

/-- `--write-datafusion`: the plan as DataFusion runs it
(`SubstraitLean/DataFusion.lean`), or the reason it does not get it. -/
def writeDataFusion (plan : Plan) : IO UInt32 := do
  if let some msg := DataFusion.refusal plan then
    IO.eprintln s!"error: {msg}"; return 1
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  IO.println (DataFusion.writePlan plan).compress
  return 0

open Lean (Json toJson) in
/-- A `--contract` report under the profile the request names (`"profile"`).
Under the reference it is the report as it is. Under Substrait, the
reference's proof carries over when the transfer check passes on the
transformation: Substrait allows only behaviours the reference allows at every
option it meets (`Rel.transfer_of_transferB`). Where it does not, no
postcondition or key is proved under Substrait, and `"transfer"` names the
options. Under Polars's profile the report is the reference's of the plan as
parsed: a plan states Polars's choices (`division_type: FLOOR`), which the
parser reads as their templates, and `Polars.elaborate_eq` proves that
evaluating those under the reference is evaluating the calls under
`Profile.polars` (`SubstraitLean/PolarsProfile.lean`); so does any engine of `es`
marked `asReference`, an out-of-tree one among them. An engine whose profile is
its own (DuckDB's, Spark's: `DuckDBProfile.lean`, `SparkProfile.lean`) has no
report under it yet (#1288): its request gets the reference's report, labelled
`"reference"`, with `"pending"` naming the profile asked for. A name the
checker does not know gets the reference's report alone. -/
def underProfile (es : List EngineProfile) (j : Json) (report : Json) (proved : Bool) :
    Except String (Json × Bool) := do
  let name := (j.getObjValAs? String "profile").toOption.getD "reference"
  if (engineNamed? es name).any (·.asReference) then
    return (report.setObjVal! "profile" name, proved)
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

/-- One request of `--serve`: the mode flag (empty for the default check)
and the input text. -/
def runOn (es : List EngineProfile) (flag : String) (input : String) : IO UInt32 := do
  if flag == "--contract" then
    match Lean.Json.parse input with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok j => match ContractCheck.check j with
      | .error e => IO.eprintln s!"error: {e}"; return 1
      | .ok report =>
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
        -- Per engine, the plan's class, evidence and what refuses it (#1166).
        let engines := (Realize.enginesJson es j rowsExact report robust eps).toOption.getD []
        let base := report.json |>.setObjVal! "depends" depends
            |>.setObjVal! "epsilon" eps |>.setObjVal! "epsilon_by_engine" byEngine
            |>.setObjVal! "rows_exact" rowsExact |>.setObjVal! "robust" robust
            |>.setObjVal! "margin_checks" margins
        match underProfile es j (engines.foldl (fun r (k, v) => r.setObjVal! k v) base)
            report.allProved with
        | .error e => IO.eprintln s!"error: {e}"; return 1
        | .ok (out, proved) =>
          IO.println out.compress
          return if proved then 0 else 4
  if flag == "--shard" then
    match Lean.Json.parse input with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok j => match ShardCheck.check j with
      | .error e => IO.eprintln e; return 5
      | .ok out => IO.println out.compress; return 0
  let mode ← match flag with
    | "" => pure (check · false)
    | "--eval-spec" => pure (check · true)
    | "--rows" => pure (check · false false)
    | "--eval-choices" => pure evalChoices
    | "--delta" => pure delta
    | "--write" => pure write
    | "--write-datafusion" => pure writeDataFusion
    | "--outcomes" => pure (outcomes Profile.reference)
    -- Internal stopgap; converges to `semantics="duckdb"` (#1288).
    | "--outcomes-duckdb-stopgap" => pure (outcomes (Profile.duckdb {}))
    | "--dependencies" => pure fun plan => do
        -- The options the plan meets and the transfer check (#444).
        IO.println (plan.root.dependenciesJson es).compress
        return 0
    | _ => IO.eprintln s!"unknown mode {flag}"; return 1
  match parsePlan input with
  | .ok plan => mode plan
  | .error e => IO.eprintln s!"error: {e}"; return 1

/-- `act` with stdout and stderr captured. -/
def capture (act : IO UInt32) : IO (UInt32 × ByteArray × ByteArray) := do
  let out ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let err ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let code ← IO.withStdout (IO.FS.Stream.ofBuffer out) <|
    IO.withStderr (IO.FS.Stream.ofBuffer err) act
  return (code, (← out.get).data, (← err.get).data)

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
  let law : BlackBox.Law → Lean.Json
    | .nonNull => Lean.Json.arr #["non_null"]
    | .atLeast k => Lean.Json.arr #["at_least", Lean.toJson k]
    | .atMost k => Lean.Json.arr #["at_most", Lean.toJson k]
  let laws (ls : List BlackBox.Law) := Lean.Json.arr (ls.map law).toArray
  Lean.Json.arr ((BlackBox.scalars.map fun f => obj [
      ("name", f.name), ("kind", "scalar"), ("anchor", Lean.toJson (Write.bbAnchor f.name)),
      ("args", Lean.Json.arr (f.args.map ty).toArray), ("result", ty f.result),
      ("strict", Lean.toJson f.strict), ("raises", Lean.toJson (f.raises == .sometimes)),
      ("laws", laws f.laws)]) ++
    (BlackBox.aggregates.map fun f => obj [
      ("name", f.name), ("kind", "aggregate"), ("anchor", Lean.toJson (Write.bbAnchor f.name)),
      ("raises", Lean.toJson (f.raises == .sometimes)),
      ("args", Lean.Json.arr #[ty f.arg]), ("result", ty f.result),
      ("empty", Write.writeValue f.empty), ("laws", laws f.laws)])).toArray

/-- The checker over the engine profiles `es`: `substrait-check`'s `main`
with `builtinEngines`, or a package's own checker with its profile added. -/
def checkerMain (es : List EngineProfile) (args : List String) : IO UInt32 := do
  match args with
  | ["--serve"] => serve es
  | ["--version"] => do
    IO.println s!"substrait-check protocol {protocol}"
    return 0
  -- Whether this build checked the generated entries' proofs (`check_generated`):
  -- without it, the theorems over them rest on `sorryAx` (docs/trusted-base.md).
  | ["--build"] => do
    IO.println s!"generated proofs {if generatedChecked then "checked" else "unchecked"}"
    return 0
  | ["--lift-cache"] => do
    -- A new SubstraitLean/LiftCache.lean from this build's tables (#268).
    IO.print Lift.cacheSource
    return 0
  | ["--lift-table"] => do
    -- What DuckDB SQL lifts to, generated and proved (#268).
    IO.println Lift.tableJson.pretty
    return 0
  | ["--lowering-cache"] => do
    -- A new SubstraitLean/LoweringCache.lean from this build's coverage (#242).
    IO.print loweringCacheSource
    return 0
  | ["--lowering-table"] => do
    -- The DuckDB lowering's templates, for sverify.sql.lowering (#241).
    IO.println Lowering.duckdbTableJson.compress
    return 0
  | ["--black-boxes"] => do
    -- The black boxes' table (#325), for sverify.black_box's test.
    IO.println blackBoxJson.compress
    return 0
  | ["--functions"] => do
    -- The function tables (#544, #269), for the Python mirror's agreement test.
    IO.println Functions.tableJson.compress
    return 0
  | ["--transfer"] => do
    -- The option-wise transfer check on a dependency report, from stdin (#444).
    let input ← (← IO.getStdin).readToEnd
    match Lean.Json.parse input >>= transferJson es with
    | .ok out => IO.println out.compress; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | ["--profile-diff"] => do
    -- Where Substrait's choices and the reference's differ (#444 step 2).
    IO.println substraitDiffJson.compress
    return 0
  | ["--options"] => do
    -- The options, the groups' options, the profiles' choices and
    -- observations, and the reference's tools (#444).
    IO.println (tablesJson es).compress
    return 0
  | ["--realizability"] => do
    -- `obligations reference E` per engine: the realizability table (#444, step 3b).
    IO.println (realizabilityJson es).compress
    return 0
  | ["--lowering-coverage"] => do
    -- How each construct is lowered to DuckDB (#241); a golden test.
    for (c, how, _) in duckdbOn.coverage do
      IO.println s!"error_on_division_by_zero=on\t{c}\t{how}"
    return 0
  | [path] => runOn es "" (← IO.FS.readFile path)
  | [flag, path] =>
    if ["--delta", "--contract", "--write", "--write-datafusion", "--shard", "--outcomes",
        "--outcomes-duckdb-stopgap", "--eval-spec", "--eval-choices", "--rows", "--dependencies"].contains flag then
      return ← runOn es flag (← IO.FS.readFile path)
    usage
  | _ => usage
where
  usage := do
    IO.eprintln "usage: substrait-check [--delta | --contract | --write | --write-datafusion | --shard | --outcomes | --eval-spec | --eval-choices | --rows | --dependencies] <file.json> | --serve | --version | --build | --lowering-coverage | --lowering-cache | --lowering-table | --lift-table | --lift-cache | --black-boxes | --functions | --options | --realizability | --profile-diff | --transfer"
    return 1

end Substrait.Checker
