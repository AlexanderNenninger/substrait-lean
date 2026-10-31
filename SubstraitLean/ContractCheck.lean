import SubstraitLean.Contracts
import SubstraitLean.Safety
import SubstraitLean.Guards
import SubstraitLean.Keys
import SubstraitLean.Check
import SubstraitLean.Parse
import SubstraitLean.Pretty
import SubstraitLean.Semantic
import SubstraitLean.Write

/-!
# Checking a contract

Input (JSON):

```json
{ "requires": [<plan>, ...],   -- each: one table, select of its preconditions
  "ensures": [<plan>, ...],    -- each: the transformation, select of postconditions
  "transform": <plan>,         -- the transformation, to report facts and keys
  "keys": {"<table>": [[<col>, ...], ...]},   -- input keys (by column position)
  "ensures_keys": [[<col>, ...], ...],        -- keys to prove on the output
  "references": {"<table>": [[<col>, "<table>", <col>], ...]} }
      -- input foreign keys: every non-NULL value of the column occurs in the
      -- other table's column (`ForeignKeys.Hold`)
```

Output: a JSON report (`Report.json`). Besides what is proved, it carries
`optimized`, the transformation rewritten with the facts and keys of the
preconditions (`Rel.optimize`, sound by `Rel.optimize_sound` on data meeting
them), in Lean's written form, and `rewrites`, the names of the rewrites
applied.

A postcondition is **proved** when its column of `ensures` is certainly TRUE
under `Rel.aeval` with each table described by its schema refined by its
preconditions; `contract_sound` is the theorem that makes this a proof.

`Rel.eval` breaks ties in a window's `ORDER BY` one particular way. The
proofs are about the engine's result only when no window has ties, which
`Rel.windowsTotal` checks with the input keys (`Rel.window_deterministic`).
Otherwise nothing is reported as proved: the result depends on the engine.

The schema description (`schemaEnv`, from `baseSchema` types and nullability) and
the JSON handling are trusted.
-/

namespace Substrait.ContractCheck

open Lean (Json)
open Parse

/-- What a column's declared type allows. -/
def typeEnv (ty : Json) : AVal :=
  -- Doubles, timestamps and dates are integer codes (`SubstraitLean/Float.lean`).
  let ints := ["i8", "i16", "i32", "i64", "fp32", "fp64", "precisionTimestamp", "timestamp", "date"]
  let kinds := ints ++ ["string", "varchar", "fixedChar", "bool"]
  let kind := (kinds.find? fun k => (ty.getObjVal? k).toOption.isSome).getD ""
  let body := ty.getObjValD kind
  let nullable := (body.getObjValAs? String "nullability").toOption != some "NULLABILITY_REQUIRED"
  -- `BIGINT` and timestamps (microseconds) are 64-bit: what makes `a / 2` safe.
  let i64 := ["i64", "precisionTimestamp", "timestamp"]
  if i64.contains kind then ⟨nullable, some ⟨some FloatCode.minI64, some FloatCode.maxI64⟩, false, false, false⟩
  else if ints.contains kind then ⟨nullable, some Bound.top, false, false, false⟩
  else if ["string", "varchar", "fixedChar"].contains kind then ⟨nullable, none, false, false, true⟩
  else if kind == "bool" then ⟨nullable, none, true, true, false⟩
  else AVal.top

def schemaEnv (schema : Json) : List AVal :=
  match (schema.getObjVal? "struct").toOption.bind (·.getObjValAs? (Array Json) "types" |>.toOption) with
  | some tys => tys.toList.map typeEnv
  | none => []

/-- Bounds near the 64-bit limits every `BIGINT` has go without saying
(leaving them out only weakens what is shown). Not for double codes. -/
def _root_.Substrait.Bound.shown (b : Bound) : Bound :=
  ⟨b.lo.filter (-2 ^ 60 < ·), b.hi.filter (· < 2 ^ 60)⟩

def _root_.Substrait.Bound.render (b : Bound) : String :=
  let b := b.shown
  match b.lo, b.hi with
  | none, none => "any integer"
  | some l, some h => if l == h then s!"the integer {l}" else s!"an integer in [{l}, {h}]"
  | some l, none => s!"an integer ≥ {l}"
  | none, some h => s!"an integer ≤ {h}"

def _root_.Substrait.AVal.render (a : AVal) : String :=
  let parts := (if a.tt then ["TRUE"] else []) ++ (if a.ff then ["FALSE"] else []) ++
    (a.int.map fun b => [b.render]).getD [] ++ (if a.str then ["a string"] else []) ++
    (if a.null then ["NULL"] else [])
  match parts with
  | [] => "nothing (no rows)"
  | [p] => p
  | ps => ", ".intercalate ps.dropLast ++ " or " ++ ps.getLast!

/-- Machine-readable abstract value, so callers can display codes as doubles
or timestamps. -/
def _root_.Substrait.AVal.json (a : AVal) : Json :=
  let bound (o : Option Int) : Json := (o.map fun i => Json.str (toString i)).getD .null
  Json.mkObj [("null", Lean.toJson a.null), ("true", Lean.toJson a.tt), ("false", Lean.toJson a.ff),
    ("string", Lean.toJson a.str),
    ("int", match a.int with
      | some b => Json.mkObj [("lo", bound b.lo), ("hi", bound b.hi)]
      | none => .null)]

structure Report where
  ensures : List (String × Bool × String)
  facts : List (String × String × Json)
  /-- Requested output keys, and whether `Rel.keys_sound` proves them. -/
  keys : List (List Nat × Bool)
  /-- Does every window order its partitions totally (`Rel.windowsTotal`)? -/
  deterministic : Bool := true
  /-- Runtime errors and wrap-arounds `Rel.mayIssues_sound` cannot rule out. -/
  issues : List (Issue × Expr) := []
  /-- The transformation runs correctly without row-level checks
  (`Rel.guardFree_sound`): every issue is an integer `SUM`. -/
  guardFree : Bool := false
  /-- The transformation after `Rel.optimize`, as Substrait JSON. -/
  optimized : Json := .null
  /-- The rewrites `Rel.optimize` applied. -/
  rewrites : List String := []

def Report.json (r : Report) : Json :=
  Json.mkObj [
    ("ensures", Json.arr (r.ensures.map fun (n, ok, v) =>
      Json.mkObj [("name", Lean.toJson n), ("proved", Lean.toJson ok),
        ("value", Lean.toJson v)]).toArray),
    ("facts", Json.arr (r.facts.map fun (n, v, a) =>
      Json.mkObj [("name", Lean.toJson n), ("value", Lean.toJson v), ("abstract", a)]).toArray),
    ("keys", Json.arr (r.keys.map fun (k, ok) =>
      Json.mkObj [("cols", Lean.toJson k), ("proved", Lean.toJson ok)]).toArray),
    ("deterministic", Lean.toJson r.deterministic),
    ("issues", Json.arr (r.issues.map fun (i, e) =>
      Json.mkObj [("kind", Lean.toJson (Issue.name i)), ("error", Lean.toJson i.isError),
        ("expr", Lean.toJson e.render)]).toArray),
    ("guard_free", Lean.toJson r.guardFree),
    ("optimized", r.optimized),
    ("rewrites", Lean.toJson r.rewrites)]

def Report.allProved (r : Report) : Bool :=
  r.ensures.all (·.2.1) && r.keys.all (·.2) && !r.issues.any (·.1.isError)

def natLists (j : Json) : List (List Nat) :=
  ((j.getArr?).toOption.getD #[]).toList.map fun k =>
    ((k.getArr?).toOption.getD #[]).toList.filterMap fun c => (c.getNat?).toOption

def foreignKeys (j : Json) : ForeignKeys := fun t =>
  (((j.getObjVal? t).toOption.bind (·.getArr?.toOption)).getD #[]).toList.filterMap fun fk =>
    match fk.getArr?.toOption.map Array.toList with
    | some [c, s, p] => do
      pure ((← c.getNat?.toOption), (← s.getStr?.toOption), (← p.getNat?.toOption))
    | _ => none

def parseJsonPlan (j : Json) : Except String Plan := parsePlan j.compress

def check (input : Json) : Except String Report := do
  let ensures ← ((input.getObjValAs? (Array Json) "ensures").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let transform ← match (input.getObjVal? "transform").toOption with
    | some j => some <$> parseJsonPlan j
    | none => pure none
  let plans := ensures ++ requires ++ transform.toList
  let tables : Tables := plans.flatMap (·.tables)
  for (t, n, _) in tables do
    if tables.any fun (t', n', _) => t' == t && n' != n then
      throw s!"table {t} has different schemas in different plans"
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  let schemas : String → List AVal := fun t => match tables.lookup t with
    | some (_, s) => schemaEnv s
    | none => []
  let mut pre : List (String × List Expr) := []
  for p in requires do
    let some (t, cs) := p.root.colExprs cat
      | throw "a precondition plan must only select from one table"
    pre := (t, cs) :: pre
  let preOf (t : String) : List Expr := (pre.filter (·.1 == t)).flatMap (·.2)
  let A := fun t => tableEnv (schemas t) (preOf t)
  let F := fun t => (preOf t).flatMap Expr.factsOf
  let inputKeys : String → List (List Nat) := fun t =>
    natLists ((input.getObjVal? "keys").toOption.bind (·.getObjVal? t |>.toOption) |>.getD (.arr #[]))
  let T := Rel.keyedWindows cat A F inputKeys
  let tied := "undetermined: rows may tie in a window's ORDER BY, and the engine orders them"
  let mut results : List (String × Bool × String) := []
  for q in ensures do
    -- `contract_sound` needs the postcondition plan to be well-formed.
    if !q.root.checkWF cat then throw "a postcondition plan is not well-formed"
    let env := q.root.aeval cat A F T
    let names := if q.names.length == env.length then q.names
      else (List.range env.length).map (s!"#{·}")
    let total := q.root.windowsTotal cat A F inputKeys
    results := results ++ names.zip (env.map fun a =>
      if total then (a.certainlyTrue, a.render) else (false, tied))
  let facts := match transform with
    | some p =>
      if !p.root.checkWF cat then []
      else
        let fenv := p.root.aeval cat A F T
        let fnames := if p.names.length == fenv.length then p.names
          else (List.range fenv.length).map (s!"#{·}")
        fnames.zip (fenv.map fun a => (a.render, a.json))
    | none => []
  -- Keys: a requested key holds if it contains a derived one (`KeyOn.superset`).
  let deterministic := transform.all (·.root.windowsTotal cat A F inputKeys)
  let wanted := natLists ((input.getObjVal? "ensures_keys").toOption.getD (.arr #[]))
  let keys ← match transform with
    | some p =>
      if !p.root.checkWF cat then throw "the transformation plan is not well-formed"
      let derived := p.root.keys cat A F inputKeys
      pure (wanted.map fun k => (k, deterministic && derived.any fun k' => k'.all (k.contains ·)))
    | none => pure (wanted.map (·, false))
  let issues := match transform with
    | some p => if p.root.checkWF cat then (p.root.mayIssues cat A F T false).eraseDups else []
    | none => []
  let guardFree := match transform with
    | some p => p.root.checkWF cat && p.root.looseSub && issues.all (·.1 == .sumWraps)
    | none => false
  let (optimized, rewrites) := match transform with
    | some p =>
      if !p.root.checkWF cat then (.null, [])
      else
        let R := foreignKeys ((input.getObjVal? "references").toOption.getD (.obj {}))
        let (q, log) := p.root.optimize cat A F inputKeys R
        (Write.writePlan (Write.planSchemas p) cat q p.names, log)
    | none => (.null, [])
  return {
    optimized
    rewrites
    ensures := results
    facts
    keys
    deterministic
    issues
    guardFree }

end Substrait.ContractCheck
