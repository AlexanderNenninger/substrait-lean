import SubstraitLean.Contracts
import SubstraitLean.Check
import SubstraitLean.Parse

/-!
# Checking a contract

Input (JSON):

```json
{ "requires": [<plan>, ...],   -- each: one table, select of its preconditions
  "ensures": [<plan>, ...],    -- each: the transformation, select of postconditions
  "transform": <plan> }        -- optional: the transformation, to report facts
```

A postcondition is **proved** when its column of `ensures` is certainly TRUE
under `Rel.aeval` with each table described by its schema refined by its
preconditions; `contract_sound` is the theorem that makes this a proof. The
schema description (`schemaEnv`, from `baseSchema` types and nullability) and
the JSON handling are trusted.
-/

namespace Substrait.ContractCheck

open Lean (Json)
open Parse

/-- What a column's declared type allows. -/
def typeEnv (ty : Json) : AVal :=
  let kinds := ["i8", "i16", "i32", "i64", "string", "varchar", "fixedChar", "bool"]
  let kind := (kinds.find? fun k => (ty.getObjVal? k).toOption.isSome).getD ""
  let body := ty.getObjValD kind
  let nullable := (body.getObjValAs? String "nullability").toOption != some "NULLABILITY_REQUIRED"
  if ["i8", "i16", "i32", "i64"].contains kind then ⟨nullable, some Bound.top, false, false, false⟩
  else if ["string", "varchar", "fixedChar"].contains kind then ⟨nullable, none, false, false, true⟩
  else if kind == "bool" then ⟨nullable, none, true, true, false⟩
  else AVal.top

def schemaEnv (schema : Json) : List AVal :=
  match (schema.getObjVal? "struct").toOption.bind (·.getObjValAs? (Array Json) "types" |>.toOption) with
  | some tys => tys.toList.map typeEnv
  | none => []

def _root_.Substrait.Bound.render (b : Bound) : String :=
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

structure Report where
  ensures : List (String × Bool × String)
  facts : List (String × String)

def Report.json (r : Report) : Json :=
  Json.mkObj [
    ("ensures", Json.arr (r.ensures.map fun (n, ok, v) =>
      Json.mkObj [("name", Lean.toJson n), ("proved", Lean.toJson ok),
        ("value", Lean.toJson v)]).toArray),
    ("facts", Json.arr (r.facts.map fun (n, v) =>
      Json.mkObj [("name", Lean.toJson n), ("value", Lean.toJson v)]).toArray)]

def Report.allProved (r : Report) : Bool := r.ensures.all (·.2.1)

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
  let mut results : List (String × Bool × String) := []
  for q in ensures do
    -- `contract_sound` needs the postcondition plan to be well-formed.
    if !q.root.checkWF cat then throw "a postcondition plan is not well-formed"
    let env := q.root.aeval cat A
    let names := if q.names.length == env.length then q.names
      else (List.range env.length).map (s!"#{·}")
    results := results ++ names.zip (env.map fun a => (a.certainlyTrue, a.render))
  let facts := match transform with
    | some p =>
      if !p.root.checkWF cat then []
      else
        let fenv := p.root.aeval cat A
        let fnames := if p.names.length == fenv.length then p.names
          else (List.range fenv.length).map (s!"#{·}")
        fnames.zip (fenv.map AVal.render)
    | none => []
  return {
    ensures := results
    facts }

end Substrait.ContractCheck
