import SubstraitLean.Contracts
import SubstraitLean.Safety
import SubstraitLean.Guards
import SubstraitLean.Keys
import SubstraitLean.Check
import SubstraitLean.Parse
import SubstraitLean.Pretty
import SubstraitLean.Semantic
import SubstraitLean.Write
import SubstraitLean.Infer

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
  let kinds := ints ++ ["string", "varchar", "fixedChar", "bool", "decimal"]
  let kind := (kinds.find? fun k => (ty.getObjVal? k).toOption.isSome).getD ""
  let body := ty.getObjValD kind
  let nullable := (body.getObjValAs? String "nullability").toOption != some "NULLABILITY_REQUIRED"
  -- `BIGINT` and timestamps (microseconds) are 64-bit: what makes `a / 2` safe.
  let i64 := ["i64", "precisionTimestamp", "timestamp"]
  if i64.contains kind then ⟨nullable, some ⟨some FloatCode.minI64, some FloatCode.maxI64⟩, false, false, false⟩
  else if ints.contains kind then ⟨nullable, some Bound.top, false, false, false⟩
  else if ["string", "varchar", "fixedChar"].contains kind then ⟨nullable, none, false, false, true⟩
  else if kind == "bool" then ⟨nullable, none, true, true, false⟩
  -- A decimal is its unscaled integer, of at most `p` digits (#27): what makes
  -- `a + b` of two columns fit its precision.
  else if kind == "decimal" then
    let p := (body.getObjValAs? Nat "precision").toOption.getD 38
    ⟨nullable, some ⟨some (1 - 10 ^ p), some (10 ^ p - 1)⟩, false, false, false⟩
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

/-- `i · 10⁻ˢ` in decimal digits (`decimalString 2 (-5)` is `-0.05`). -/
def _root_.decimalString (s : Nat) (i : Int) : String :=
  if s = 0 then toString i else
    let digits := (toString i.natAbs).toList
    let digits := List.replicate (s + 1 - digits.length) '0' ++ digits
    let k := digits.length - s
    (if i < 0 then "-" else "") ++ String.ofList (digits.take k) ++ "." ++ String.ofList (digits.drop k)

#guard decimalString 2 (-5) == "-0.05" && decimalString 2 1234 == "12.34" && decimalString 0 7 == "7"
#guard decimalString 3 1000 == "1.000" && decimalString 1 0 == "0.0"

/-- A decimal's bound (`Bound.render`) in its digits at scale `s`, as the
column's type says (#250): `DECIMAL(38, 4) ≥ 45.0000`, not its unscaled
`450000`. -/
def _root_.Substrait.Bound.renderDecimal (p s : Nat) (b : Bound) : String :=
  let b := b.shown
  let ty := s!"decimal({p}, {s})"
  let txt := decimalString s
  match b.lo, b.hi with
  | none, none => s!"any {ty}"
  | some l, some h => if l == h then s!"the {ty} {txt l}" else s!"a {ty} in [{txt l}, {txt h}]"
  | some l, none => s!"a {ty} ≥ {txt l}"
  | none, some h => s!"a {ty} ≤ {txt h}"

def _root_.Substrait.AVal.render (a : AVal) (dec : Option (Nat × Nat) := none) : String :=
  let bound (b : Bound) := match dec with
    | some (p, s) => b.renderDecimal p s
    | none => b.render
  let parts := (if a.tt then ["TRUE"] else []) ++ (if a.ff then ["FALSE"] else []) ++
    (a.int.map fun b => [bound b]).getD [] ++ (if a.str then ["a string"] else []) ++
    (if a.null then ["NULL"] else [])
  match parts with
  | [] => "nothing (no rows)"
  | [p] => p
  | ps => ", ".intercalate ps.dropLast ++ " or " ++ ps.getLast!

/-- Machine-readable abstract value, so callers can display codes as doubles
or timestamps. -/
def _root_.Substrait.AVal.json (a : AVal) (dec : Option (Nat × Nat) := none) : Json :=
  let bound (o : Option Int) : Json := (o.map fun i => Json.str (toString i)).getD .null
  Json.mkObj ([("null", Lean.toJson a.null), ("true", Lean.toJson a.tt), ("false", Lean.toJson a.ff),
    ("string", Lean.toJson a.str),
    ("int", match a.int with
      | some b => Json.mkObj [("lo", bound b.lo), ("hi", bound b.hi)]
      | none => .null)] ++
    -- A decimal's integers are unscaled, at this precision and scale (#250).
    (dec.map fun (p, s) => [("decimal", Json.mkObj [("precision", Lean.toJson p),
      ("scale", Lean.toJson s)])]).getD [])

def need (n : String × Nat × Bound) : Json :=
  let bound (o : Option Int) : Json := (o.map fun i => Json.str (toString i)).getD .null
  Json.mkObj [("table", Lean.toJson n.1), ("col", Lean.toJson n.2.1),
    ("lo", bound n.2.2.lo), ("hi", bound n.2.2.hi)]

/-- A value column `col` of `table` must not hold. -/
def needNe (n : String × Nat × Int) : Json :=
  Json.mkObj [("table", Lean.toJson n.1), ("col", Lean.toJson n.2.1),
    ("ne", Json.str (toString n.2.2))]

def _root_.Substrait.Infer.Bounds.json (b : Infer.Bounds) : Json :=
  Json.mkObj [("needs", Json.arr (b.needs.map need ++ b.nes.map needNe).toArray),
    ("split", Lean.toJson b.split),
    ("why", match b.why with | some w => Lean.toJson w | none => .null)]

structure Report where
  ensures : List (String × Bool × String)
  /-- For each postcondition, the base-table ranges that would make it hold
  (`Infer.suggest`): untrusted, and only suggested. -/
  suggestions : List Infer.Bounds := []
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
  /-- For each issue, what would rule it out (`SubstraitLean/Infer.lean`):
  untrusted candidates, which the caller proves by adding them to the
  preconditions. -/
  bounds : List (Issue × Expr × Infer.Bounds) := []
  /-- The ranges of `bounds` that follow from the operations alone, merged
  per base-table column. -/
  inferred : List (String × Nat × Bound) := []
  /-- The values `bounds` rule out per base-table column (a divisor's 0). -/
  inferredNes : List (String × Nat × Int) := []

def Report.json (r : Report) : Json :=
  Json.mkObj [
    ("ensures", Json.arr ((r.ensures.zip (r.suggestions ++
        List.replicate r.ensures.length ({ why := none } : Infer.Bounds))).map fun ((n, ok, v), b) =>
      Json.mkObj [("name", Lean.toJson n), ("proved", Lean.toJson ok),
        ("value", Lean.toJson v), ("suggest", if ok then .null else b.json)]).toArray),
    ("facts", Json.arr (r.facts.map fun (n, v, a) =>
      Json.mkObj [("name", Lean.toJson n), ("value", Lean.toJson v), ("abstract", a)]).toArray),
    ("keys", Json.arr (r.keys.map fun (k, ok) =>
      Json.mkObj [("cols", Lean.toJson k), ("proved", Lean.toJson ok)]).toArray),
    ("deterministic", Lean.toJson r.deterministic),
    ("issues", Json.arr (r.issues.map fun (i, e) =>
      Json.mkObj [("kind", Lean.toJson (Issue.name i)), ("error", Lean.toJson i.isError),
        ("expr", Lean.toJson e.render),
        ("bound", match r.bounds.find? (fun (i', e', _) => i' == i && e' == e) with
          | some (_, _, b) => b.json
          | none => .null)]).toArray),
    ("inferred", Json.arr (r.inferred.map need ++ r.inferredNes.map needNe).toArray),
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
  let tied := "undetermined: rows may tie in the ORDER BY of a window or of FIRST, LAST or " ++
    "STRING_AGG, and the engine orders them"
  let mut results : List (String × Bool × String) := []
  let mut suggestions : List Infer.Bounds := []
  for q in ensures do
    -- `contract_sound` needs the postcondition plan to be well-formed.
    if !q.root.checkWF cat then throw "a postcondition plan is not well-formed"
    let env := q.root.aeval cat A F T
    let names := if q.names.length == env.length then q.names
      else (List.range env.length).map (s!"#{·}")
    let total := q.root.windowsTotal cat A F inputKeys
    results := results ++ names.zip (env.map fun a =>
      if total then (a.certainlyTrue, a.render) else (false, tied))
    suggestions := suggestions ++ (List.range env.length).map fun i =>
      let b := Infer.suggest cat A F T q.root i
      { b with needs := Infer.trim A b.needs }
  let facts := match transform with
    | some p =>
      if !p.root.checkWF cat then []
      else
        let fenv := p.root.aeval cat A F T
        let fnames := if p.names.length == fenv.length then p.names
          else (List.range fenv.length).map (s!"#{·}")
        let decs := (p.root.kinds tables).map fun | .dec pr sc => some (pr, sc) | _ => none
        fnames.zip ((fenv.zip (decs ++ List.replicate fenv.length none)).map fun (a, d) =>
          (a.render d, a.json d))
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
  let bounds := match transform with
    | some p =>
      if !p.root.checkWF cat then [] else
        (Infer.Rel.bounds cat A F T false p.root).map fun (i, e, b) =>
          (i, e, { b with needs := Infer.trim A b.needs })
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
    suggestions
    facts
    keys
    deterministic
    issues
    bounds
    inferred := Infer.merged A (bounds.filter (·.1.isError))
    inferredNes := Infer.mergedNes (bounds.filter (·.1.isError))
    guardFree }

end Substrait.ContractCheck
