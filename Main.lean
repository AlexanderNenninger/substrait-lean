import SubstraitLean

/-!
`substrait-check plan.json`: parse a Substrait JSON plan, check it is
well-formed, and evaluate it.

`substrait-check --delta plan.json`: print the Substrait JSON plans an engine
runs to maintain `plan.json` incrementally, one per line. They read the old
tables `t` and change tables `t$delta` (the same columns plus a trailing
`__weight`); concatenated, their outputs are the change to the result, with a
trailing `__weight` column. Each plan is union-free (see `Rel.terms`).

Exit codes: 0 ok, 1 parse/unsupported error, 2 ill-formed plan,
3 not incrementally maintainable.
-/

open Substrait Parse

def load (path : String) : IO (Except String Plan) :=
  return parsePlan (← IO.FS.readFile path)

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
    IO.eprintln "not incrementally maintainable (left join or fetch)"; return 3
  let cat := Write.deltaCatalog plan
  let terms := Write.deltaTerms plan
  -- `Rel.weighted_eval` needs each term to be incremental and well-formed.
  for term in terms do
    if !term.isIncremental || term.hasUnion || !term.checkWF cat then
      IO.eprintln "a delta term failed its static checks"; return 2
  for term in terms do
    IO.println (Write.writeDeltaTerm plan term).compress
  return 0

def check (plan : Plan) : IO UInt32 := do
  let cat := plan.catalog
  IO.println plan.root.render
  let tables := (plan.tables.map fun (t, n, _) => s!"{t}({n})").eraseDups
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
  let rows := plan.root.eval cat
  IO.println s!"rows ({rows.length}):"
  for row in rows do
    IO.println s!"  {Row.render row}"
  return 0

def main (args : List String) : IO UInt32 := do
  let (mode, path) ← match args with
    | [path] => pure (check, path)
    | ["--delta", path] => pure (delta, path)
    | _ => IO.eprintln "usage: substrait-check [--delta] <plan.json>"; return 1
  match ← load path with
  | .ok plan => mode plan
  | .error e => IO.eprintln s!"error: {e}"; return 1
