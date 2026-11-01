import SubstraitLean

/-!
`substrait-check plan.json`: parse a Substrait JSON plan, check it is
well-formed, and evaluate it.

`substrait-check --delta plan.json`: print the Substrait JSON plans an engine
runs to maintain `plan.json` incrementally, one per line. They read the old
tables `t` and change tables `t$delta` (the same columns plus a trailing
`__weight`); concatenated, their outputs are the change to the result, with a
trailing `__weight` column. Each plan is union-free (see `Rel.terms`).

`substrait-check --contract contract.json`: try to prove postconditions from
preconditions (see `SubstraitLean/ContractCheck.lean` for the input format)
and print a JSON report.

`substrait-check --shard request.json`: split a plan for evaluation on
shards of some of its tables (see `SubstraitLean/ShardCheck.lean`), or say
why it cannot be split.

`substrait-check --write plan.json`: print the plan in Lean's written form
(the plan `Rel.eval` runs, as Substrait JSON). `--write-datafusion`: the same
plan for DataFusion to run, compensating for where its semantics differ
(`Write.writeRel`); it does not parse back to the same `Rel`.

`substrait-check --serve`: answer requests for the modes above on stdin, one
process for many plans (see `serve`).

Exit codes: 0 ok (for `--contract`: every postcondition proved), 1
parse/unsupported error, 2 ill-formed plan, 3 not incrementally maintainable,
4 some postcondition not proved, 5 the plan cannot be split into shards.
-/

open Substrait Parse

/-- Shared static checks; `none` means the plan passed. -/
def checkPlan (plan : Plan) : Option (UInt32 × String) :=
  let cat := plan.catalog
  let arity := plan.root.arity cat
  -- `checkWF_iff` makes this the decision procedure for `Rel.WF`.
  if !plan.root.checkWF cat then some (2, "well-formed: no")
  else if !plan.names.isEmpty && plan.names.length != arity then
    some (2, s!"well-formed: no (root names {plan.names} do not match arity {arity})")
  else none

def delta (plan : Plan) : IO UInt32 := do
  if let some (code, msg) := checkPlan plan then
    IO.eprintln msg; return code
  -- `isIncremental_iff`: this decides `Rel.Incremental`.
  if !plan.root.isIncremental then
    IO.eprintln "not incrementally maintainable (left join, fetch or window)"; return 3
  let cat := Write.deltaCatalog plan
  let terms := Write.deltaTerms plan
  -- `Rel.weighted_eval` needs each term to be incremental and well-formed.
  for term in terms do
    if !term.isIncremental || term.hasUnion || !term.checkWF cat then
      IO.eprintln "a delta term failed its static checks"; return 2
  for term in terms do
    IO.println (Write.writeDeltaPlan plan term).compress
  return 0

/-- `i · 10⁻ˢ` in decimal digits (`decimalString 2 (-5)` is `-0.05`). -/
def decimalString (s : Nat) (i : Int) : String :=
  if s = 0 then toString i else
    let digits := (toString i.natAbs).toList
    let digits := List.replicate (s + 1 - digits.length) '0' ++ digits
    let k := digits.length - s
    (if i < 0 then "-" else "") ++ String.ofList (digits.take k) ++ "." ++ String.ofList (digits.drop k)

#guard decimalString 2 (-5) == "-0.05" && decimalString 2 1234 == "12.34" && decimalString 0 7 == "7"
#guard decimalString 3 1000 == "1.000" && decimalString 1 0 == "0.0"

/-- A result value, printed by its column's kind: integers (unbounded in the
model, so `MAX + 1` is a value) exactly, doubles as doubles. A column of
unknown kind falls back to `Value.render`. -/
def renderCell : Kind → Value → String
  | .float, .int c => s!"{FloatCode.toFloat c}d"
  | .dec _ s, .int i => decimalString s i
  | .int, .int i | .time, .int i | .date, .int i => toString i
  | _, v => v.render

def check (plan : Plan) : IO UInt32 := do
  let cat := plan.catalog
  IO.println plan.root.render
  let tables := (plan.tables.filter (!isInternalKey ·.1) |>.map fun (t, n, _) => s!"{t}({n})").eraseDups
  unless tables.isEmpty do
    IO.println s!"tables: {", ".intercalate tables}"
  IO.println s!"arity: {plan.root.arity cat}"
  if let some (code, msg) := checkPlan plan then
    IO.println msg; return code
  IO.println "well-formed: yes"
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
    IO.lazyPure fun _ => (plan.root.eval cat).map fun row =>
      let cells := row.zipIdx.map fun (v, i) => renderCell (kinds.getD i .other) v
      s!"({", ".intercalate cells})"
  if let some msg := (panics.splitOn "\n").find? (·.startsWith "PANIC") then
    IO.eprintln s!"error: rows not evaluated: {(msg.splitOn ": ").drop 1 |> ": ".intercalate}"
    return 1
  IO.println s!"rows ({rows.length}):"
  for row in rows do
    IO.println s!"  {row}"
  return 0

def write (df : Bool) (plan : Plan) : IO UInt32 := do
  -- Decimals (#27) are written back as Substrait's own calls and casts where
  -- that parses back to the same plan; DataFusion does not compute them as
  -- the reference does.
  if plan.root.decimalOps then
    if df then
      IO.eprintln "error: DataFusion does not compute decimals as the reference does (#27)"
      return 1
    if !Write.roundtrips plan then
      IO.eprintln "error: this decimal arithmetic cannot be written for the engines yet (#27)"
      return 1
  if df then
    if plan.root.anyExpr Expr.nestedAccess then
      IO.eprintln "error: DataFusion does not run struct fields, list elements or cardinality as the reference does (#94)"
      return 1
    if let some (code, msg) := checkPlan plan then
      IO.eprintln msg; return code
  IO.println (Write.writePlan (Write.planSchemas plan) plan.catalog plan.root plan.names df).compress
  return 0

/-- One request of `--serve`: the mode flag (empty for the default check)
and the input text. -/
def runOn (flag : String) (input : String) : IO UInt32 := do
  if flag == "--contract" then
    match Lean.Json.parse input with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok j => match ContractCheck.check j with
      | .error e => IO.eprintln s!"error: {e}"; return 1
      | .ok report =>
        IO.println report.json.compress
        return if report.allProved then 0 else 4
  if flag == "--shard" then
    match Lean.Json.parse input with
    | .error e => IO.eprintln s!"error: {e}"; return 1
    | .ok j => match ShardCheck.check j with
      | .error e => IO.eprintln e; return 5
      | .ok out => IO.println out.compress; return 0
  let mode ← match flag with
    | "" => pure check
    | "--delta" => pure delta
    | "--write" => pure (write false)
    | "--write-datafusion" => pure (write true)
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
partial def serve : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match line.trimAscii.toString.splitOn " " with
    | [flag, n] =>
      let input ← readExactly stdin n.toNat!
      let flag := if flag == "-" then "" else flag
      let run := try runOn flag (String.fromUTF8! input) catch e => do
        IO.eprintln s!"error: {e}"; pure 1
      let (code, out, err) ← capture run
      stdout.putStr s!"{code} {out.size} {err.size}\n"
      stdout.write out
      stdout.write err
      stdout.flush
    | _ => IO.eprintln s!"bad request {line}"; return 1
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--serve"] => serve
  | [path] => runOn "" (← IO.FS.readFile path)
  | [flag, path] =>
    if ["--delta", "--contract", "--write", "--write-datafusion", "--shard"].contains flag then
      return ← runOn flag (← IO.FS.readFile path)
    usage
  | _ => usage
where
  usage := do
    IO.eprintln "usage: substrait-check [--delta | --contract | --write | --write-datafusion | --shard] <file.json> | --serve"
    return 1
