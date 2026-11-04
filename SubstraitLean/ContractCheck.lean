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
import SubstraitLean.Rows
import SubstraitLean.Implied

/-!
# Checking a contract

Input (JSON):

```json
{ "requires": [<plan>, ...],   -- each: one table, select of its preconditions
  "ensures": [<plan>, ...],    -- each: the transformation, select of postconditions
  "transform": <plan>,         -- the transformation, to report facts and keys
  "keys": {"<table>": [[<col>, ...], ...]},   -- input keys (by column position)
  "ensures_keys": [[<col>, ...], ...],        -- keys to prove on the output
  "references": {"<table>": [[<col>, "<table>", <col>], ...]},
      -- input foreign keys: every non-NULL value of the column occurs in the
      -- other table's column (`ForeignKeys.Hold`)
  "max_rows": {"<table>": <n>},
      -- row caps (`sv.max_rows`): the postconditions, facts and issues are
      -- checked on the plan with these reads capped (`Rel.capReads`), which is the plan
      -- on data within the caps (`Rel.capReads_eval`); float `SUM` and `AVG`
      -- get their error bounds from them (#85)
  "rows_per": {"<table>": [[[<col>, ...], <n>], ...]} }
      -- at most <n> rows per value of the columns (`sv.rows_per`, `RowsPer`):
      -- an aggregate grouping by them has groups of at most <n> rows, which
      -- bound its integer and decimal `SUM`s (`Rel.issuesCapped_sound`)
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
  /-- Runtime errors and wrap-arounds `Rel.issuesCapped_sound` cannot rule
  out: an integer `SUM` the row caps or the bounds on rows per key keep
  within 64 bits is left out. -/
  issues : List (Issue × Expr) := []
  /-- The plan's constant errors (`Rel.constIssues`, #609, D21), also in
  `issues`: they raise on any data, so no precondition rules them out. -/
  constant : List (Issue × Expr) := []
  /-- At most this many output rows, on inputs within their caps
  (`Rel.maxRows_sound` of the capped plan). -/
  rows : Option Nat := none
  /-- Each relation of the transformation, in pre-order: its operator, its
  depth, at most how many rows it has (`Rel.maxRows_sound` of its capped
  plan) and, for an aggregate, at most how many rows a group has
  (`Rel.groupRows_sound`). -/
  relations : List (String × Nat × Option Nat × Option Nat) := []
  /-- The transformation runs correctly without row-level checks
  (`Rel.guardFree_sound`): every issue is an integer `SUM`. -/
  guardFree : Bool := false
  /-- The expressions that run correctly without their checks
  (`Rel.evalG_marks`), as `Rel.marksJson`; `.null` when none is known. -/
  unchecked : Json := .null
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
  /-- Predicates the transformation implies on its base tables (#81): for
  each table, abstract rows (as column bounds) one of which every row that
  reaches the output lies in (`Rel.need`, `Rel.need_eval`). -/
  implied : List (String × List (List (Nat × Bound))) := []

/-- The node's name in `sverify.sql`'s model. -/
def _root_.Substrait.Rel.nodeName : Rel → String
  | .read _ => "Read" | .values _ _ => "Values" | .filter _ _ => "Filter"
  | .project _ _ => "Project" | .emit _ _ => "Emit" | .cross _ _ => "Cross"
  | .join _ _ _ _ => "Join" | .fetch _ _ _ => "Fetch" | .unionAll _ _ => "UnionAll"
  | .window _ _ _ _ => "Window" | .semi _ _ _ _ => "Semi" | .orderBy _ _ => "OrderBy"
  | .distinct _ => "Distinct" | .unnest _ _ => "Unnest" | .aggregate _ _ _ => "Aggregate"

/-- The inputs of a node, in the order of `Marks.input`. -/
def _root_.Substrait.Rel.inputs : Rel → List Rel
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .unnest r _ | .aggregate r _ _ => [r]
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => [a, b]

/-- `Marks` as JSON, each node named, so the SQL writer can check it walks
the same tree: `{"node": "Filter", "slots": [0], "inputs": [...]}`. -/
partial def _root_.Substrait.Rel.marksJson (r : Rel) (m : Marks) : Json :=
  Json.mkObj [("node", Lean.toJson r.nodeName), ("slots", Lean.toJson m.slots),
    ("inputs", Json.arr (r.inputs.zipIdx.map fun (x, i) => x.marksJson (m.input i)).toArray)]

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
    ("rows", match r.rows with | some n => Lean.toJson n | none => .null),
    ("relations", Json.arr (r.relations.map fun (op, d, n, g) =>
      Json.mkObj [("op", Lean.toJson op), ("depth", Lean.toJson d),
        ("rows", match n with | some n => Lean.toJson n | none => .null),
        ("group_rows", match g with | some n => Lean.toJson n | none => .null)]).toArray),
    ("issues", Json.arr (r.issues.map fun (i, e) =>
      Json.mkObj [("kind", Lean.toJson (Issue.name i)), ("error", Lean.toJson i.isError),
        ("expr", Lean.toJson e.render),
        ("constant", Lean.toJson (r.constant.contains (i, e))),
        ("bound", match r.bounds.find? (fun (i', e', _) => i' == i && e' == e) with
          | some (_, _, b) => b.json
          | none => .null)]).toArray),
    ("inferred", Json.arr (r.inferred.map need ++ r.inferredNes.map needNe).toArray),
    ("implied", Json.arr (r.implied.map fun (t, Es) =>
      Json.mkObj [("table", Lean.toJson t), ("any", Json.arr (Es.map fun E =>
        Json.arr (E.map fun (j, b) => need (t, j, b)).toArray).toArray)]).toArray),
    ("guard_free", Lean.toJson r.guardFree),
    ("unchecked", r.unchecked),
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

/-- The predicates `r` implies on each base table it reads (`Rel.need` from
the root), as column bounds, one list per abstract row; tables where an
abstract row bounds no column are left out (their predicate is TRUE). -/
def impliedOf (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (r : Rel) :
    List (String × List (List (Nat × Bound))) :=
  r.tables.eraseDups.filterMap fun t =>
    match Rel.need cat A F t (.lit (.bool true)) r with
    | some Es =>
      let bs := Es.map envBounds
      if bs.isEmpty || bs.any (·.isEmpty) then none else some (t, bs)
    | none => none

def parseJsonPlan (j : Json) : Except String Plan := parsePlan j.compress

def rowCaps (j : Json) : String → Option Nat := fun t =>
  (j.getObjValAs? Nat t).toOption

/-- The bounds on rows per key of each table (`sv.rows_per`). -/
def rowsPer (j : Json) : String → List (List Nat × Nat) := fun t =>
  (((j.getObjVal? t).toOption.bind (·.getArr?.toOption)).getD #[]).toList.filterMap fun e =>
    match e.getArr?.toOption.map Array.toList with
    | some [k, n] => do
      let n ← n.getNat?.toOption
      pure (((k.getArr?).toOption.getD #[]).toList.filterMap (·.getNat?.toOption), n)
    | _ => none

/-- The operator of a relation, as the report names it. -/
def opName : Rel → String
  | .read t => s!"read {t}"
  | .values _ _ => "values"
  | .filter _ _ => "filter"
  | .project _ _ => "project"
  | .emit _ _ => "emit"
  | .cross _ _ => "cross"
  | .join _ _ .inner _ => "join"
  | .join _ _ .left _ => "left join"
  | .fetch _ _ _ => "fetch"
  | .unionAll _ _ => "union all"
  | .window _ _ _ _ => "window"
  | .semi _ _ false _ => "semi join"
  | .semi _ _ true _ => "anti join"
  | .orderBy _ _ => "order by"
  | .distinct _ => "distinct"
  | .aggregate _ _ _ => "aggregate"
  | .unnest _ _ => "unnest"

/-- Each relation of `r` in pre-order, with its depth, its row bound on
the capped plan and an aggregate's bound on the rows of a group. -/
def relationBounds (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (caps : String → Option Nat)
    (P : String → List (List Nat × Nat)) (d : Nat) (r : Rel) :
    List (String × Nat × Option Nat × Option Nat) :=
  let group := match r with
    | .aggregate i gs _ =>
      let c := i.capped cat A F K caps
      let g := c.groupRows cat A F K P gs
      match g, c.maxRows with
      | some a, some b => some (min a b)
      | some a, none => some a
      | none, b => if gs.isEmpty then b else none
    | _ => none
  let here := (opName r, d, (r.capped cat A F K caps).maxRows, group)
  let rest := match r with
    | .read _ | .values _ _ => []
    | .filter i _ | .project i _ | .emit i _ | .fetch i _ _ | .window i _ _ _ | .orderBy i _
    | .distinct i | .aggregate i _ _ | .unnest i _ => relationBounds cat A F K caps P (d + 1) i
    | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
      relationBounds cat A F K caps P (d + 1) a ++ relationBounds cat A F K caps P (d + 1) b
  here :: rest

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
  let implied : List (String × List (List (Nat × Bound))) :=
    ((transform.map (·.root)).filter (·.checkWF cat)).elim [] (impliedOf cat A F)
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let perKey := rowsPer ((input.getObjVal? "rows_per").toOption.getD (.obj {}))
  let tied := "undetermined: rows may tie in the ORDER BY of a window or of FIRST, LAST, " ++
    "STRING_AGG, MODE, ARG_MIN or ARG_MAX, and the engine orders them"
  let mut results : List (String × Bool × String) := []
  let mut suggestions : List Infer.Bounds := []
  for q in ensures do
    -- `contract_sound` needs the postcondition plan to be well-formed.
    if !(q.root.capReads caps).checkWF cat then throw "a postcondition plan is not well-formed"
    let env := (q.root.capReads caps).aeval cat A F T
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
        let fenv := (p.root.capReads caps).aeval cat A F T
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
  let raw := match transform with
    | some p => if p.root.checkWF cat then p.root.mayIssues cat A F T false else []
    | none => []
  let constant := match transform with
    | some p => if p.root.checkWF cat then p.root.constIssues else []
    | none => []
  let issues := match transform with
    | some p =>
      if p.root.checkWF cat then
        ((p.root.issuesCapped cat A F T inputKeys caps perKey) ++ constant).eraseDups
      else []
    | none => []
  let rows := match transform with
    | some p => if p.root.checkWF cat then (p.root.capped cat A F inputKeys caps).maxRows else none
    | none => none
  let relations := match transform with
    | some p =>
      if p.root.checkWF cat then relationBounds cat A F inputKeys caps perKey 0 p.root else []
    | none => []
  let bounds := match transform with
    | some p =>
      if !p.root.checkWF cat then [] else
        (Infer.Rel.bounds cat A F T false p.root).map fun (i, e, b) =>
          (i, e, { b with needs := Infer.trim A b.needs })
    | none => []
  let guardFree := match transform with
    | some p => p.root.checkWF cat && p.root.looseSub && raw.all (·.1.assumed) && constant.isEmpty
    | none => false
  let unchecked := match transform with
    | some p =>
      if p.root.checkWF cat && p.root.looseSub then
        p.root.marksJson (p.root.marks cat A F T false)
      else .null
    | none => .null
  let (optimized, rewrites) := match transform with
    | some p =>
      if !p.root.checkWF cat then (.null, [])
      else
        let R := foreignKeys ((input.getObjVal? "references").toOption.getD (.obj {}))
        let (q, log) := p.root.optimize cat A F inputKeys R
        (Write.writePlan (Write.planSchemas p) cat q p.names, log)
    | none => (.null, [])
  return {
    implied
    optimized
    rewrites
    ensures := results
    suggestions
    facts
    keys
    deterministic
    issues
    rows
    relations
    bounds
    -- Only for the issues the caps leave.
    inferred := Infer.merged A (bounds.filter fun (i, e, _) => i.isError && issues.contains (i, e))
    inferredNes :=
      Infer.mergedNes (bounds.filter fun (i, e, _) => i.isError && issues.contains (i, e))
    guardFree
    constant
    unchecked }

end Substrait.ContractCheck
