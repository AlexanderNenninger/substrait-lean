import Sverify.Analysis.Contracts
import Sverify.Analysis.Safety
import Sverify.Analysis.Guards
import Sverify.Analysis.Keys
import SubstraitLean.Check
import Sverify.Frontend.Parse
import SubstraitLean.Pretty
import SubstraitLean.Semantic
import SubstraitLean.Write
import SubstraitLean.Infer
import Sverify.Analysis.Rows
import Sverify.Analysis.Knowledge
import SubstraitLean.Implied
import Sverify.Core.Robust
import Sverify.Core.AllowedNear
import Sverify.Analysis.AllowedAnalysis
import SubstraitLean.AnalysisCongr

/-!
# Checking a contract

Input (JSON):

```json
{ "requires": [<plan>, ...],   -- each: one table, select of its preconditions
  "ensures": [<plan>, ...],    -- each: the transformation, select of postconditions;
      -- `parse` keeps only the selected conditions and refuses a plan that
      -- selects from anything other than the transformation (`postOf`)
  "transform": <plan>,         -- the transformation, which the postconditions are over
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

/-- What a column's declared type allows: a list's elements and a struct's
fields by their types (#925), `depth` levels down. -/
def typeEnvD : Nat → Json → AVal
  | 0, _ => AVal.top
  | depth + 1, ty =>
    -- Numbers: integers, doubles (by their codes, `core/Sverify/Core/Float.lean`), timestamps and dates.
    let ints := ["i8", "i16", "i32", "i64", "fp32", "fp64", "precisionTimestamp", "timestamp", "date"]
    let kinds := ints ++ ["string", "varchar", "fixedChar", "bool", "decimal", "list", "struct"]
    let kind := (kinds.find? fun k => (ty.getObjVal? k).toOption.isSome).getD ""
    let body := ty.getObjValD kind
    let nullable := (body.getObjValAs? String "nullability").toOption != some "NULLABILITY_REQUIRED"
    -- The column's number kind (#923).
    let nk : Option NumKind :=
      if ["i8", "i16", "i32", "i64"].contains kind then some .int
      else if ["fp32", "fp64"].contains kind then some .float
      else if ["precisionTimestamp", "timestamp"].contains kind then some .ts
      else if kind == "date" then some .date
      else none
    -- `BIGINT` is 64-bit: what makes `a / 2` safe. A DATE or TIMESTAMP of the
    -- reference lies in 0001-01-01 … 9999-12-31 by its type (D32,
    -- `Value.InCalendar`): what makes `date_part` of a column read safe. The
    -- source read checks it (`sverify.engine.Connection.put`).
    if kind == "i64" then
      { null := nullable, int := some ⟨some FloatCode.minI64, some FloatCode.maxI64⟩, nk := nk }
    else if ["precisionTimestamp", "timestamp"].contains kind then
      { null := nullable, int := some ⟨some Time.tsMin, some Time.tsMax⟩, nk := nk }
    else if kind == "date" then
      { null := nullable, int := some ⟨some Time.dayMin, some Time.dayMax⟩, nk := nk }
    else if ints.contains kind then { null := nullable, int := some Bound.top, nk := nk }
    else if ["string", "varchar", "fixedChar"].contains kind then
      { null := nullable, str := true }
    else if kind == "bool" then { null := nullable, tt := true, ff := true }
    -- A decimal is its unscaled integer, of at most `p` digits (#27): what makes
    -- `a + b` of two columns fit its precision.
    else if kind == "decimal" then
      let p := (body.getObjValAs? Nat "precision").toOption.getD 38
      let sc := (body.getObjValAs? Nat "scale").toOption.getD 0
      { null := nullable, int := some ⟨some (1 - 10 ^ p), some (10 ^ p - 1)⟩, nk := some (.dec sc) }
    else if kind == "list" then
      { null := nullable, list := true, elems := some (typeEnvD depth (body.getObjValD "type")) }
    else if kind == "struct" then
      let tys := ((body.getObjValAs? (Array Json) "types").toOption.getD #[]).toList
      { null := nullable, struct := true, fields := some (tys.map (typeEnvD depth)) }
    else AVal.top

/-- What a column's declared type allows. -/
def typeEnv (ty : Json) : AVal := typeEnvD 8 ty

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

/-- A string literal as SQL writes it. -/
def sqlString (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

/-- The strings a column may hold (#708). -/
def _root_.Substrait.AVal.renderStrs (a : AVal) : String :=
  match a.strs with
  | some [s] => s!"the string {sqlString s}"
  | some l => s!"one of the strings {", ".intercalate (l.map sqlString)}"
  | none => "a string"

/-- A list's length, in `b` (#925). -/
def _root_.Substrait.Bound.renderLen (b : Bound) : Option String :=
  match b.lo.filter (0 < ·), b.hi with
  | none, none => none
  | some l, some h => some (if l == h then s!"length {l}" else s!"length in [{l}, {h}]")
  | some l, none => some s!"length ≥ {l}"
  | none, some h => some s!"length ≤ {h}"

/-- What `a` describes, `depth` levels into lists (#925). -/
def _root_.Substrait.AVal.renderD : Nat → AVal → Option (Nat × Nat) → String
  | depth, a, dec =>
  let bound (b : Bound) := match dec with
    | some (p, s) => b.renderDecimal p s
    | none => b.render
  -- A list by its length and its elements: "a list (length ≤ 5; of a string)".
  let list : String :=
    let elems := match depth, a.elems with
      | d + 1, some e => [s!"of {e.renderD d none}"]
      | _, _ => []
    match a.card.renderLen.toList ++ elems with
    | [] => "a list"
    | ps => s!"a list ({"; ".intercalate ps})"
  let parts := (if a.tt then ["TRUE"] else []) ++ (if a.ff then ["FALSE"] else []) ++
    (a.int.map fun b => [bound b]).getD [] ++ (if a.str then [a.renderStrs] else []) ++
    (if a.list then [list] else []) ++ (if a.struct then ["a struct"] else []) ++
    (if a.null then ["NULL"] else [])
  match parts with
  | [] => "nothing (no rows)"
  | [p] => p
  | ps => ", ".intercalate ps.dropLast ++ " or " ++ ps.getLast!

def _root_.Substrait.AVal.render (a : AVal) (dec : Option (Nat × Nat) := none) : String :=
  a.renderD 2 dec

/-- Machine-readable abstract value, so callers can display codes as doubles
or timestamps. -/
def _root_.Substrait.AVal.json (a : AVal) (dec : Option (Nat × Nat) := none) : Json :=
  let bound (o : Option Int) : Json := (o.map fun i => Json.str (toString i)).getD .null
  Json.mkObj ([("null", Lean.toJson a.null), ("true", Lean.toJson a.tt), ("false", Lean.toJson a.ff),
    ("string", Lean.toJson a.str),
    -- Every string is one of these (#708), or any string may be.
    ("strings", match a.strs with
      | some l => if a.str then Lean.toJson l else .null
      | none => .null),
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

/-- A column of `table` that must not be NULL. -/
def needNotNull (n : String × Nat) : Json :=
  Json.mkObj [("table", Lean.toJson n.1), ("col", Lean.toJson n.2), ("not_null", Lean.toJson true)]

def _root_.Substrait.Infer.Bounds.json (b : Infer.Bounds) : Json :=
  Json.mkObj [("needs",
      Json.arr (b.needs.map need ++ b.nes.map needNe ++ b.notNull.map needNotNull).toArray),
    ("split", Lean.toJson b.split),
    ("why", match b.why with | some w => Lean.toJson w | none => .null)]

structure Report where
  /-- For each postcondition plan, in the request's order, each column's
  name, whether the analysis proves it TRUE, and its abstract value
  (`Request.ensureResults`, `check_proved_sound`). -/
  ensures : List (List (String × Bool × String))
  /-- For each postcondition, the base-table ranges that would make it hold
  (`Infer.suggest`): untrusted, and only suggested. -/
  suggestions : List Infer.Bounds := []
  /-- For each postcondition: unproved, and proved where every window orders
  its rows totally, so only the order of ties leaves it open. Untrusted: it
  only spares the counterexample search (#691, #825). -/
  tiesOnly : List Bool := []
  /-- For each postcondition, the components of an observation its value
  depends on (`Expr.depends`): an observation that coarsens none of them
  keeps it TRUE (`Expr.robust_of_depends`). `none` where the plan is not a
  selection of conditions from the transformation. -/
  depends : List (Option (List String)) := []
  /-- For each postcondition, the components the request's observation
  ignores that its value depends on (#1071): `depends` filtered by the
  components the observation coarsens, but for `"zeros"`, which no
  comparison of reference codes sees (`Expr.robust_of_depends_canon`), and
  for `"floats"` under the plan's bound or an `approx` condition, with
  `"picks"` and `"elements"` for the open aggregate columns an unproved one
  reads (`Rel.openCol`; a proved one holds for every choice they leave,
  `contract_sound_all`). `none` where `depends` is, or without an
  observation in the request. -/
  ignores : List (Option (List String)) := []
  /-- For each postcondition: proved on every result the reference allows,
  every order and grouping of a double `SUM` or `AVG` among them
  (`contract_sound_allowed`, `postAllowed`), beside `proved`'s every order. -/
  allowed : List Bool := []
  facts : List (String × String × Json)
  /-- Requested output keys, and whether `Rel.keys_sound` proves them. -/
  keys : List (List Nat × Bool)
  /-- Does the transformation leave the engine no choice but the order of its
  rows (`Rel.detPlan`): then every result the reference allows is `Rel.eval`'s
  up to that order (`check_deterministic_sound`). -/
  deterministic : Bool := true
  /-- Does every window order its partitions totally? A `FETCH` over ties
  keeps every proof (it takes some rows of an allowed order) and the written
  SQL breaks its ties by input order; only a rerun may differ. -/
  windowsTotal : Bool := true
  /-- Where the transformation leaves its result open: each relation in the
  pre-order of `relations`, by its index, its operator and what is open
  (`tiesHere`). Empty exactly when `deterministic`
  (`Request.deterministicIn_eq`). -/
  tiePlaces : List (Nat × String × String) := []
  /-- Runtime errors and wrap-arounds `Rel.issuesCapped_sound` cannot rule
  out: an integer `SUM` the row caps or the bounds on rows per key keep
  within 64 bits is left out. -/
  issues : List (Issue × Expr) := []
  /-- The plan's constant errors (`Rel.constIssues`, #609, D21), also in
  `issues`: they raise on any data, so no precondition rules them out. -/
  constant : List (Issue × Expr) := []
  /-- The issues' expressions that sit inside an operand of an `AND` or `OR`
  (`Expr.underAndOr`): untrusted, for the report's suggestion (#604). -/
  underAndOr : List Expr := []
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
  /-- The base-table columns `bounds` need not NULL (a divisor's `COUNT`). -/
  inferredNotNull : List (String × Nat) := []
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

/-- Does `e` occur in `t`? -/
partial def _root_.Substrait.Expr.hasSub (e : Expr) (t : Expr) : Bool :=
  t == e || match t with
    | .un _ a => e.hasSub a
    | .bin _ a b => e.hasSub a || e.hasSub b
    | .ifThen c x y => e.hasSub c || e.hasSub x || e.hasSub y
    | .hof _ l b => e.hasSub l || e.hasSub b
    | _ => false

/-- Is `e` inside an operand of an `AND` or `OR` of `t`? Both operands are
evaluated (#604, D19), so a guard in the other operand does not keep `e`'s
error away: the report suggests a `CASE`. -/
partial def _root_.Substrait.Expr.underAndOr (e : Expr) (t : Expr) : Bool :=
  match t with
    | .bin .and a b | .bin .or a b => e.hasSub a || e.hasSub b
    | .un _ a => e.underAndOr a
    | .bin _ a b => e.underAndOr a || e.underAndOr b
    | .ifThen c x y => e.underAndOr c || e.underAndOr x || e.underAndOr y
    | .hof _ l b => e.underAndOr l || e.underAndOr b
    | _ => false

/-- Every expression of a plan. -/
partial def _root_.Substrait.Rel.allExprs : Rel → List Expr
  | .read _ | .values _ _ => []
  | .filter r c => c :: r.allExprs
  | .project r es => es ++ r.allExprs
  | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .unnest r _ | .window r _ _ _ =>
    r.allExprs
  | .cross a b | .unionAll a b => a.allExprs ++ b.allExprs
  | .join a b _ on | .semi a b _ on => on :: a.allExprs ++ b.allExprs
  | .aggregate r gs ms => gs ++ ms.flatMap Measure.exprs ++ r.allExprs

def Report.json (r : Report) : Json :=
  let ensures := r.ensures.flatten
  Json.mkObj [
    ("ensures", Json.arr (((((ensures.zip (r.suggestions ++
        List.replicate ensures.length ({ why := none } : Infer.Bounds))).zip
        (r.tiesOnly ++ List.replicate ensures.length false)).zip
        (r.depends ++ List.replicate ensures.length none)).zip
        ((r.allowed ++ List.replicate ensures.length false).zip
          (r.ignores ++ List.replicate ensures.length none))).map
          fun (((((n, ok, v), b), t), d), al, ig) =>
      Json.mkObj [("name", Lean.toJson n), ("proved", Lean.toJson ok),
        ("value", Lean.toJson v), ("suggest", if ok then .null else b.json),
        ("ties", Lean.toJson t), ("depends", match d with
          | some l => Lean.toJson l
          | none => .null), ("allowed", Lean.toJson (ok && al)), ("ignores", match ig with
          | some l => Lean.toJson l
          | none => .null)]).toArray),
    ("facts", Json.arr (r.facts.map fun (n, v, a) =>
      Json.mkObj [("name", Lean.toJson n), ("value", Lean.toJson v), ("abstract", a)]).toArray),
    ("keys", Json.arr (r.keys.map fun (k, ok) =>
      Json.mkObj [("cols", Lean.toJson k), ("proved", Lean.toJson ok)]).toArray),
    ("deterministic", Lean.toJson r.deterministic),
    ("windows_total", Lean.toJson r.windowsTotal),
    ("tie_places", Json.arr (r.tiePlaces.map fun (i, op, what) => Json.mkObj
      [("relation", Lean.toJson i), ("op", Lean.toJson op), ("what", Lean.toJson what)]).toArray),
    ("rows", match r.rows with | some n => Lean.toJson n | none => .null),
    ("relations", Json.arr (r.relations.map fun (op, d, n, g) =>
      Json.mkObj [("op", Lean.toJson op), ("depth", Lean.toJson d),
        ("rows", match n with | some n => Lean.toJson n | none => .null),
        ("group_rows", match g with | some n => Lean.toJson n | none => .null)]).toArray),
    ("issues", Json.arr (r.issues.map fun (i, e) =>
      Json.mkObj [("kind", Lean.toJson (Issue.name i)), ("error", Lean.toJson i.isError),
        ("assumed", Lean.toJson i.assumed),
        ("expr", Lean.toJson e.render),
        ("constant", Lean.toJson (r.constant.contains (i, e))),
        ("under_and_or", Lean.toJson (r.underAndOr.contains e)),
        ("bound", match r.bounds.find? (fun (i', e', _) => i' == i && e' == e) with
          | some (_, _, b) => b.json
          | none => .null)]).toArray),
    ("inferred", Json.arr (r.inferred.map need ++ r.inferredNes.map needNe ++
      r.inferredNotNull.map needNotNull).toArray),
    ("implied", Json.arr (r.implied.map fun (t, Es) =>
      Json.mkObj [("table", Lean.toJson t), ("any", Json.arr (Es.map fun E =>
        Json.arr (E.map fun (j, b) => need (t, j, b)).toArray).toArray)]).toArray),
    ("guard_free", Lean.toJson r.guardFree),
    ("unchecked", r.unchecked),
    ("optimized", r.optimized),
    ("rewrites", Lean.toJson r.rewrites)]

/-- Every postcondition and key proved, and every issue ruled out but the
assumed ones (`Issue.assumed`), which the data is checked against while the
job runs (`Report.assumed` in Python, #575). -/
def Report.allProved (r : Report) : Bool :=
  r.ensures.flatten.all (·.2.1) && r.keys.all (·.2) &&
    !r.issues.any fun (i, _) => i.isError && !i.assumed

def natLists (j : Json) : List (List Nat) :=
  ((j.getArr?).toOption.getD #[]).toList.map fun k =>
    ((k.getArr?).toOption.getD #[]).toList.filterMap fun c => (c.getNat?).toOption

def foreignKeys (j : Json) : ForeignKeys := fun t =>
  (((j.getObjVal? t).toOption.bind (·.getArr?.toOption)).getD #[]).toList.filterMap fun fk =>
    match fk.getArr?.toOption.map Array.toList with
    | some [c, s, p] => do
      pure ((← c.getNat?.toOption), (← s.getStr?.toOption), (← p.getNat?.toOption))
    | _ => none

variable [Boxes.Ambient]
/-- The predicates `r` implies on each base table it reads (`Rel.need` from
the root), as column bounds, one list per abstract row; tables where an
abstract row bounds no column are left out (their predicate is TRUE). -/
def impliedOf (cat : Catalog) (A : String → List AVal) (F : String → List Fact) (r : Rel) :
    List (String × List (List (Nat × Bound))) :=
  r.tables.eraseDups.filterMap fun t =>
    match Rel.need cat A F t (.lit (.bool true)) r with
    | some Es =>
      let bs := Es.map fun E => (envBounds E).map fun (j, _, b) => (j, b)
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

/-- The relations of `r` in pre-order, as `relationBounds` lists them. -/
def preorder (r : Rel) : List Rel :=
  r :: match r with
    | .read _ | .values _ _ => []
    | .filter i _ | .project i _ | .emit i _ | .fetch i _ _ | .window i _ _ _ | .orderBy i _
    | .distinct i | .aggregate i _ _ | .unnest i _ => preorder i
    | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => preorder a ++ preorder b

/-- What the measure `m` leaves open when `Measure.detIn` fails: rows that
tie in its order (`Measure.mode_signed_zero_open` for doubles that tie), a
double between two neighbours (`contAllowed`), or a function of its values
that is not proved (`AggFn.orderFree` lists the proved ones). -/
def measureTies (m : Measure) : String :=
  if m.fn.sorts then
    s!"{m.render} over rows that tie in its ORDER BY: no key among the group's and the " ++
      "order's columns, and its argument is not among the order's columns or holds doubles"
  else if m.fn matches .quantile true _ _ then
    s!"{m.render}: any double between the two neighbours"
  else s!"{m.render}: not proved a function of its values"

/-- Which member of a class of doubles (`0.0` and `-0.0`, the NaNs, D31). -/
def doublesTies (what : String) : String :=
  s!"{what} keeps any member of a class of doubles (0.0 and -0.0, the NaNs)"

/-- What the relation `r` leaves open beyond its inputs: each check of
`Rel.detPlan` at `r` that fails (`tiesIn_eq_nil`). -/
def tiesHere (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → List String
  | .distinct r => if (r.aeval cat A F .none).all AVal.noDoubles then [] else [doublesTies "DISTINCT"]
  | .window r part sort fns =>
    (if Rel.windowDetAt cat A F K r part sort fns then [] else
      let fs := ", ".intercalate ((fns.filter (!·.orderFree)).map WinFn.render)
      [s!"{fs} over rows that tie in PARTITION BY {part.map (s!"${·}")} ORDER BY " ++
        s!"{sort.map (s!"${·.col}")}, with no key among those columns"]) ++
      (fns.filter fun f => !WinFn.pickFixed cat A F r f).map fun f => doublesTies f.render
  | .aggregate r gs ms =>
    let env := r.aeval cat A F .none
    (gs.filter fun g => !(g.abs env).noDoubles).map (fun g => doublesTies s!"GROUP BY {g.render}") ++
      -- A measure that only picks a member of a class says so, its one open place.
      (ms.filter fun m => !Measure.detIn cat A F K r gs m && Measure.pickFixed cat A F r m).map
        measureTies ++
      (ms.filter fun m => !Measure.pickFixed cat A F r m).map fun m => doublesTies m.render
  | .fetch (.orderBy i keys) _ _ =>
    if Rel.fetchTotalAt cat A F K i keys then [] else
      if keys.any (·.clustered) then
        [s!"ORDER BY {keys.map (s!"${·.col}")} clusters its groups in any order"]
      else
        [s!"the rows it takes tie in ORDER BY {keys.map (s!"${·.col}")}, with no key among " ++
          "those columns"]
  | .fetch _ _ _ => ["the rows it takes have no ORDER BY"]
  | _ => []

/-- **The reasons are the flag's**: `r` leaves nothing open
(`Rel.detPlan`) exactly where no relation of it names a reason. -/
theorem tiesIn_eq_nil (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) :
    ∀ r : Rel, (preorder r).flatMap (tiesHere cat A F K) = [] ↔ r.detPlan cat A F K = true
  | .read _ | .values _ _ => by simp [preorder, tiesHere, Rel.detPlan]
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ | .unnest r _ => by
    simp [preorder, tiesHere, Rel.detPlan, tiesIn_eq_nil cat A F K r]
  | .distinct r => by
    cases h : (r.aeval cat A F .none).all AVal.noDoubles <;>
      simp [preorder, tiesHere, Rel.detPlan, tiesIn_eq_nil cat A F K r, h]
  | .window r part sort fns => by
    cases h : Rel.windowDetAt cat A F K r part sort fns <;>
      simp [preorder, tiesHere, Rel.detPlan, tiesIn_eq_nil cat A F K r, h, List.filter_eq_nil_iff,
        List.all_eq_true, and_comm]
  | .aggregate r gs ms => by
    simp only [preorder, tiesHere, Rel.detPlan, List.flatMap_cons, List.append_eq_nil_iff,
      List.map_eq_nil_iff, List.filter_eq_nil_iff, tiesIn_eq_nil cat A F K r, Bool.and_eq_true,
      List.all_eq_true, Bool.not_eq_true', Bool.not_eq_false]
    constructor
    · rintro ⟨⟨⟨hg, hm⟩, hmm⟩, hd⟩
      refine ⟨⟨⟨hd, fun m h => ?_⟩, hg⟩, hmm⟩
      cases hdm : Measure.detIn cat A F K r gs m
      · exact absurd ⟨hdm, hmm m h⟩ (hm m h)
      · rfl
    · rintro ⟨⟨⟨hd, hm⟩, hg⟩, hmm⟩
      exact ⟨⟨⟨hg, fun m h ⟨hf, _⟩ => by rw [hm m h] at hf; cases hf⟩, hmm⟩, hd⟩
  | .fetch (.orderBy i keys) _ _ => by
    cases h : Rel.fetchTotalAt cat A F K i keys <;> cases h' : keys.any (·.clustered) <;>
      simp [preorder, tiesHere, Rel.detPlan, tiesIn_eq_nil cat A F K i, h, h']
  | .fetch (.read _) _ _ | .fetch (.values _ _) _ _ | .fetch (.filter _ _) _ _
  | .fetch (.project _ _) _ _ | .fetch (.emit _ _) _ _ | .fetch (.cross _ _) _ _
  | .fetch (.join _ _ _ _) _ _ | .fetch (.fetch _ _ _) _ _ | .fetch (.unionAll _ _) _ _
  | .fetch (.window _ _ _ _) _ _ | .fetch (.semi _ _ _ _) _ _ | .fetch (.distinct _) _ _
  | .fetch (.aggregate _ _ _) _ _ | .fetch (.unnest _ _) _ _ => by
    simp [preorder, tiesHere, Rel.detPlan]
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => by
    simp [preorder, tiesHere, Rel.detPlan, tiesIn_eq_nil cat A F K a, tiesIn_eq_nil cat A F K b]

/-- Where `r` leaves the order of ties open: each relation's index in
`preorder r`, its operator and what is open. -/
def tiePlaces (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) : List (Nat × String × String) :=
  (preorder r).zipIdx.flatMap fun (n, i) => (tiesHere cat A F K n).map (i, opName n, ·)

theorem tiePlaces_eq_nil (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) :
    tiePlaces cat A F K r = [] ↔ r.detPlan cat A F K = true := by
  rw [← tiesIn_eq_nil]
  simp only [tiePlaces, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, Prod.forall]
  constructor
  · intro h n hn
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hn
    exact h n i (List.mem_zipIdx_iff_getElem?.mpr (by rw [List.getElem?_eq_getElem hi, he]))
  · intro h n i hi
    exact h n (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hi))

/-- A column's kind as an observation sees it (`ColKind`). -/
def colKindOf : Kind → ColKind
  | .float => .double
  | .time => .timestamp
  | .str => .string
  | .dec _ _ => .decimal
  | _ => .other

/-- The columns of a plan `T.select(c, …)`, as expressions over `T`'s
output, with `T`'s column kinds; `none` for another shape. -/
def postExprs (cat : Catalog) (tables : Tables) : Rel → Option (List Expr × List Kind)
  | .emit (.project t es) m =>
    let n := t.arity cat
    some (m.map fun j => if j < n then .field j else es.getD (j - n) (.lit .null), t.kinds tables)
  | .project t es => some ((List.range (t.arity cat)).map .field ++ es, t.kinds tables)
  | _ => none

/-- What each postcondition column's value depends on (`Expr.depends`). -/
def postDepends (cat : Catalog) (tables : Tables) (r : Rel) (n : Nat) :
    List (Option (List String)) :=
  match postExprs cat tables r with
  | some (es, ks) =>
    if es.length != n then List.replicate n none else
      let ctx : ObsCtx := { kind := fun i => colKindOf (ks.getD i .other) }
      es.map fun e => some (e.depends ctx).eraseDups
  | none => List.replicate n none

/-- Where the reference leaves column `j` of `r` open (D1): `"picks"` for
`FIRST`, `LAST` or `ARBITRARY` without an order, `"elements"` for `collect`
or `STRING_AGG` without one, traced through projections, emits, filters and
sorts to its aggregate. -/
def _root_.Substrait.Rel.openCol (cat : Catalog) : Rel → Nat → Option String
  | .aggregate _ gs ms, j =>
    if j < gs.length then none else
    match ms[j - gs.length]? with
    | some m =>
      if !m.sort.isEmpty then none else
      match m.fn with
      | .pick _ => some "picks"
      | .collect | .concat _ => some "elements"
      | _ => none
    | none => none
  | .project r es, j =>
    if j < r.arity cat then r.openCol cat j else
    match es[j - r.arity cat]? with
    | some (.field i) => r.openCol cat i
    | _ => none
  | .emit r m, j => match m[j]? with
    | some i => r.openCol cat i
    | none => none
  | .filter r _, j | .orderBy r _, j | .fetch r _ _, j | .distinct r, j => r.openCol cat j
  | _, _ => none

/-- The columns `e` reads other than through a function that ignores the
order of a list's elements (`cardinality`, `list_contains`, `any_match`,
`all_match`). -/
def _root_.Substrait.Expr.bareCols (guarded : Bool) : Expr → List Nat
  | .lit _ => []
  | .field i => if guarded then [] else [i]
  | .un f a => a.bareCols (guarded || f == .cardinality)
  | .bin f a b =>
    let g := guarded || f == .listFn .contains
    a.bareCols g ++ b.bareCols g
  | .ifThen c t e => c.bareCols guarded ++ t.bareCols guarded ++ e.bareCols guarded
  | .hof f l b =>
    let g := guarded || f == .anyMatch || f == .allMatch
    l.bareCols g ++ (b.bareCols g).filterMap fun i => if i = 0 then none else some (i - 1)

/-- For each postcondition column, its open components (`Rel.openCol` of
the columns it reads, `"elements"` only where it reads the list bare) and
the observation's ignored components it depends on, but for `"zeros"`
(`Expr.robust_of_depends_canon`), `"elements"` and `"floats"` under the
plan's bound or an `approx` condition (`floatsOk`). -/
def postIgnores (cat : Catalog) (tables : Tables) (r : Rel) (n : Nat) (coarsens : List String)
    (floatsOk : Bool) : List (Option (List String × List String)) :=
  match postExprs cat tables r with
  | some (es, ks) =>
    if es.length != n then List.replicate n none else
      let ctx : ObsCtx := { kind := fun i => colKindOf (ks.getD i .other) }
      let t := match r with
        | .emit (.project t _) _ | .project t _ => t
        | _ => r
      es.map fun e =>
        let bare := e.bareCols false
        let opened := (e.cols.filterMap fun c => match t.openCol cat c with
          | some "elements" => if bare.contains c then some "elements" else none
          | o => o).eraseDups
        let base := (e.depends ctx).eraseDups.filter fun c =>
          c != "zeros" && c != "elements" && coarsens.contains c && !(c == "floats" && floatsOk)
        some (opened, base)
  | none => List.replicate n none

/-- A postcondition's ignored components: its open ones first (none where
`noOpen`: windows order totally, or the transformation is SQL), then the
observation's. -/
def combineIgnores (noOpen : Bool) (pre : List (Option (List String × List String))) :
    List (Option (List String)) :=
  pre.map fun o => o.map fun p =>
    let op : List String := if noOpen then [] else p.1
    op ++ p.2.filter fun c => !op.contains c

/-- Where `contract_sound_allowed` carries a postcondition column of a plan
`T.select(…)` from every order to every allowed result: `T` is closed
(`Rel.closedB`, `contract_sound_allowed_closed`: no `VAR_*`, `STDDEV_*`,
`COVAR_*`, `CORR` or `QUANTILE_CONT`; a double `SUM` or `AVG` is order-free
since D25), or an aggregate whose open measures are double `SUM`s and `AVG`s
over a closed plan (`Rel.floatOpenSafe_aggregate`), and the column is robust
under that context without a tolerance (`Expr.robustB`), so it reads no open
measure. A comparison of an open sum needs
the shift of its tolerance (#929). -/
def postAllowed (cat : Catalog) (r : Rel) (n : Nat) : List Bool :=
  match r with
  | .emit (.project t es) m =>
    let ctx? : Option ObsCtx :=
      if t.closedB then some {} else match t with
        | .aggregate r gs ms =>
          if r.closedB && ms.all (fun m => m.closedB || m.openB) then some (aggCtx gs.length ms)
          else none
        | _ => none
    match ctx? with
    | some ctx =>
      if m.length != n then List.replicate n false
      else m.map fun j => (postExpr (t.arity cat) es j).robustB Obs.plan ctx (fun _ => none)
    | none => List.replicate n false
  | _ => List.replicate n false

/-- The issues' expressions under an `AND` or `OR` of the plan. -/
def issuesUnderAndOr (transform : Option Plan) (issues : List (Issue × Expr)) : List Expr :=
  match transform with
  | some p =>
    let all := p.root.allExprs
    issues.filterMap fun (_, e) => if all.any (e.underAndOr ·) then some e else none
  | none => []

/-- A postcondition as `parse` reads it from its plan in `ensures`: the
condition columns it projects over the transformation's output and the
columns it keeps (#1484, finding 2). The checker builds the postcondition's
plan over the transformation itself (`Post.plan`), so the plan it proves is
the transformation's by construction. -/
structure Post where
  exprs : List Expr
  mapping : List Nat
  names : List String

/-- Postcondition `p`'s plan over the transformation `T`: `p`'s conditions
projected over `T`'s output, `p`'s columns kept. -/
def Post.plan (T : Plan) (p : Post) : Plan :=
  { root := .emit (.project T.root p.exprs) p.mapping, names := p.names, tables := T.tables }

/-- The postcondition a plan of `ensures` states over the transformation `T`:
the plan must project its conditions over a relation equal to `T`'s root
(`==`; the checker then builds the plan from `T` itself, `Post.plan`, so no
law of `==` is trusted). `k` numbers it in messages. -/
def postOf (T : Plan) (k : Nat) (q : Plan) : Except String Post :=
  match q.root with
  | .emit (.project r es) m =>
    if r == T.root then .ok { exprs := es, mapping := m, names := q.names }
    else .error s!"postcondition {k} does not select from the transformation"
  | _ => .error s!"postcondition {k} is not a selection of conditions over the transformation"

/-- A postcondition's abstract values from the transformation's and the
facts its projections read (`Request.transformEnvIn`). -/
def Post.envFrom (p : Post) (t : List AVal × List Fact) : List AVal :=
  p.mapping.map ((t.1 ++ p.exprs.map (·.absF t.1 t.2)).getD · AVal.top)

/-- A `--contract` request as `parse` reads it: the transformation, the
postconditions over it, the precondition plans, the tables they read, and
each table's preconditions. Everything `Request.check` analyses is a function
of it (`check_proved_sound` reads it). -/
structure Request where
  input : Json
  posts : List Post
  requires : List Plan
  transform : Option Plan
  tables : Tables
  /-- Each precondition plan's table and conditions, last first. -/
  pre : List (String × List Expr)

/-- The tables' arities, without rows: the analyses read only the arities. -/
def tablesCatalog (tables : Tables) : Catalog := fun t => match tables.lookup t with
  | some (n, _) => ⟨n, []⟩
  | none => ⟨0, []⟩

/-- Read a request: its plans, their tables (one schema per table), and the
preconditions, each plan a selection of conditions from one table. -/
def parse (input : Json) : Except String Request := do
  let ensures ← ((input.getObjValAs? (Array Json) "ensures").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let transform ← match (input.getObjVal? "transform").toOption with
    | some j => some <$> parseJsonPlan j
    | none => pure none
  let posts ← match transform, ensures with
    | _, [] => pure []
    | some T, _ => (ensures.zip (List.range ensures.length)).mapM fun (q, k) => postOf T (k + 1) q
    | none, _ => throw "postconditions need the transformation (\"transform\")"
  let plans := ensures ++ requires ++ transform.toList
  let tables : Tables := plans.flatMap (·.tables)
  for (t, n, _) in tables do
    if tables.any fun (t', n', _) => t' == t && n' != n then
      throw s!"table {t} has different schemas in different plans"
  let mut pre : List (String × List Expr) := []
  for p in requires do
    let some (t, cs) := p.root.colExprs (tablesCatalog tables)
      | throw "a precondition plan must only select from one table"
    pre := (t, cs) :: pre
  return { input, posts, requires, transform, tables, pre }

namespace Request

variable (R : Request)

def cat : Catalog := tablesCatalog R.tables

/-- The postcondition plans, each built over the transformation (`Post.plan`). -/
def ensures : List Plan := match R.transform with
  | some T => R.posts.map (·.plan T)
  | none => []

/-- Each table's declared schema, as abstract values. -/
def schemas (t : String) : List AVal := match R.tables.lookup t with
  | some (_, s) => schemaEnv s
  | none => []

def preOf (t : String) : List Expr := (R.pre.filter (·.1 == t)).flatMap (·.2)

def keysOf (t : String) : List (List Nat) :=
  natLists (((R.input.getObjVal? "keys").toOption.bind (·.getObjVal? t |>.toOption)).getD
    (.arr #[]))

def caps : String → Option Nat := rowCaps ((R.input.getObjVal? "max_rows").toOption.getD (.obj {}))

/-- `knows` as a description of the inputs, `know` for a table it lacks. -/
@[noinline] def memoKnowledge (knows : List (String × Knowledge)) (know : String → Knowledge) :
    KnowledgeEnv :=
  fun t => (knows.lookup t).getD (know t)

/-- A table's knowledge: its schema, preconditions and keys. -/
def know (t : String) : Knowledge :=
  ⟨tableEnv (R.schemas t) (R.preOf t), (R.preOf t).flatMap Expr.factsOf, R.keysOf t, none⟩

/-- Every table's knowledge, as data. -/
def knowsTable : List (String × Knowledge) :=
  (R.tables.map (·.1) |>.eraseDups).map fun t => (t, R.know t)

/-- The description of the inputs the analyses start from
(`KnowledgeEnv.ofSpec`, sound by `KnowledgeEnv.ofSpec_sound`). A
`KnowledgeEnv` is a function, so the compiler gives `kenv` the table as a
second argument and evaluates its body at every call: `Request.check` builds
it once from `knowsTable`, a value, and passes it on (#825). -/
def kenv : KnowledgeEnv := memoKnowledge R.knowsTable R.know

/-- A postcondition plan's abstract values under the description `K` of the
inputs, the rows it reads capped. `Request.check` computes `K` once per
request (`kenv`) and passes it here and to the other analyses. -/
def ensureEnvIn (K : KnowledgeEnv) (q : Plan) : List AVal :=
  (q.root.capReads R.caps).aeval R.cat K.cols K.facts (K.windows R.cat)

/-- A postcondition plan's abstract values, the rows it reads capped. -/
def ensureEnv (q : Plan) : List AVal := R.ensureEnvIn R.kenv q

/-- The transformation's abstract values and the facts its projections read,
under `K`, its reads capped. Every postcondition's analysis starts from them
(`ensureEnvIn_plan`), so `check` computes them once per request rather than
once per postcondition. -/
def transformEnvIn (K : KnowledgeEnv) (T : Plan) : List AVal × List Fact :=
  let r := T.root.capReads R.caps
  (r.aeval R.cat K.cols K.facts (K.windows R.cat),
    r.facts R.cat K.facts (K.windows R.cat) ++ r.ratioPart R.cat K.cols K.facts (K.windows R.cat))

/-- Each postcondition's abstract values under `K`, the transformation
analysed once (`postEnvs_eq`). -/
def postEnvs (K : KnowledgeEnv) : List (List AVal) := match R.transform with
  | some T => let t := R.transformEnvIn K T; R.posts.map (·.envFrom t)
  | none => []

/-- A postcondition plan's columns, each with whether the analysis proves it
TRUE and its abstract value: proved for every order of the ties
(`contract_sound_all`, with `Rel.orderAllowed_capReads` and
`Rel.keyedWindows_soundAll`, D24). -/
def ensureResults (q : Plan) : List (String × Bool × String) :=
  resultsOf q (R.ensureEnv q)
where
  resultsOf (q : Plan) (env : List AVal) : List (String × Bool × String) :=
    let names := if q.names.length == env.length then q.names
      else (List.range env.length).map (s!"#{·}")
    names.zip (env.map fun a => (a.certainlyTrue, a.render))

end Request

/-- Is the transformation well-formed and without choices but the order of
its rows (`Rel.detPlan`) under the description `K` of the inputs: the report's
`deterministic` (`check_deterministic_sound`). -/
def Request.deterministicIn (R : Request) (K : KnowledgeEnv) : Bool := match R.transform with
  | some T => T.root.checkWF R.cat && T.root.detPlan R.cat K.cols K.facts K.keys
  | none => false

/-- Where the transformation leaves its result open (`tiePlaces`): the
report's `tie_places`. A transformation that is not well-formed is open
as a whole (`check` refuses it). -/
def Request.tiePlacesIn (R : Request) (K : KnowledgeEnv) : List (Nat × String × String) :=
  match R.transform with
  | some T => if T.root.checkWF R.cat then tiePlaces R.cat K.cols K.facts K.keys T.root
    else [(0, opName T.root, "the transformation plan is not well-formed")]
  | none => []

/-- **The transformation is determined exactly where the report names no
place that leaves it open**, so `check` reads the flag off the places and
analyses the plan once. -/
theorem Request.deterministicIn_eq (R : Request) (K : KnowledgeEnv) :
    R.deterministicIn K = (R.transform.isSome && (R.tiePlacesIn K).isEmpty) := by
  unfold Request.deterministicIn Request.tiePlacesIn
  cases R.transform with
  | none => rfl
  | some T =>
    cases hw : T.root.checkWF R.cat
    · simp [hw]
    · simp only [hw, Option.isSome_some, Bool.true_and, ↓reduceIte]
      exact Bool.eq_iff_iff.mpr (by rw [List.isEmpty_iff, tiePlaces_eq_nil])

/-- The analyses of a parsed request, given each postcondition's abstract
values (`ensureEnv`), but for the postconditions' verdicts (`Request.check`). -/
def Request.analyses (R : Request) (envs : List (List AVal)) (kenv : KnowledgeEnv := R.kenv) :
    Except String Report := do
  let input := R.input
  let ensures := R.ensures
  let transform := R.transform
  let tables := R.tables
  let cat := R.cat
  let A := kenv.cols
  let F := kenv.facts
  let inputKeys := kenv.keys
  let T := kenv.windows cat
  let implied : List (String × List (List (Nat × Bound))) :=
    ((transform.map (·.root)).filter (·.checkWF cat)).elim [] (impliedOf cat A F)
  let caps := R.caps
  let perKey := rowsPer ((input.getObjVal? "rows_per").toOption.getD (.obj {}))
  let mut suggestions : List Infer.Bounds := []
  let mut tiesOnly : List Bool := []
  let mut depends : List (Option (List String)) := []
  let mut allowed : List Bool := []
  -- The request's observation (#1071): the components it coarsens, whether
  -- doubles compare under the plan's bound, which postconditions are
  -- `approx`, and whether the transformation is SQL (whose open columns the
  -- report leaves to Python for now).
  let obsJ := (input.getObjVal? "observation").toOption
  let coarsens : List String :=
    ((obsJ.bind (·.getObjValAs? (Array String) "coarsens" |>.toOption)).getD #[]).toList
  let floatsPlan := (obsJ.bind (·.getObjValAs? Bool "floats_plan" |>.toOption)).getD false
  let approxs : List Bool :=
    ((obsJ.bind (·.getObjValAs? (Array Bool) "approx" |>.toOption)).getD #[]).toList
  let sqlT := (obsJ.bind (·.getObjValAs? Bool "sql" |>.toOption)).getD false
  let mut ignoresPre : List (Option (List String × List String)) := []
  let mut qi := 0
  for (q, env) in ensures.zip envs do
    depends := depends ++ postDepends cat tables q.root env.length
    allowed := allowed ++ postAllowed cat q.root env.length
    -- A proved column holds for every choice the plan leaves open (every
    -- order, `contract_sound_all`), so only an unproved one names them.
    ignoresPre := ignoresPre ++ ((postIgnores cat tables q.root env.length coarsens
      (floatsPlan || approxs.getD qi false)).zip env).map fun (o, a) =>
        if a.certainlyTrue then o.map fun p => ([], p.2) else o
    qi := qi + 1
    -- Suggestions only for what is unproved: the report drops the others.
    suggestions := suggestions ++ (List.range env.length).map fun i =>
      if (env.getD i AVal.top).certainlyTrue then ({ why := none } : Infer.Bounds) else
        let b := Infer.suggest cat A F T q.root i
        { b with needs := Infer.trim A b.needs }
    -- What every window ordering its rows totally would prove.
    let total : Option (List AVal) :=
      if env.all (·.certainlyTrue) then none
      else some ((q.root.capReads caps).aeval cat A F fun _ _ _ => true)
    tiesOnly := tiesOnly ++ (List.range env.length).map fun i =>
      !(env.getD i AVal.top).certainlyTrue &&
        (total.map fun t => (t.getD i AVal.top).certainlyTrue).getD false
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
  -- Windows that order their partitions totally: otherwise a rerun may give
  -- other rows (D10).
  let windowsDet := transform.all (·.root.windowsTotal cat A F inputKeys)
  let wanted := natLists ((input.getObjVal? "ensures_keys").toOption.getD (.arr #[]))
  let keys ← match transform with
    | some p =>
      if !p.root.checkWF cat then throw "the transformation plan is not well-formed"
      let derived := p.root.keys cat A F inputKeys
      -- A derived key holds on every order (`Rel.keys_sound_all`, D24).
      pure (wanted.map fun k => (k, derived.any fun k' => k'.all (k.contains ·)))
    | none => pure (wanted.map (·, false))
  let raw := match transform with
    | some p => if p.root.checkWF cat then p.root.mayIssues cat A F T false else []
    | none => []
  let constant := match transform with
    | some p => if p.root.checkWF cat then p.root.constIssues else []
    | none => []
  -- An overflow to `±∞` is the reference's error (#575): under another
  -- profile the request names, the engine gives `±∞`, and no precondition
  -- rules it out.
  let reference := ((input.getObjValAs? String "profile").toOption.getD "reference") == "reference"
  let issues := match transform with
    | some p =>
      if p.root.checkWF cat then
        ((p.root.issuesCapped cat A F T inputKeys caps perKey) ++ constant).eraseDups.filter
          fun (i, _) => reference || i != .infinite
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
  let ignores := if obsJ.isNone then [] else combineIgnores (sqlT || windowsDet) ignoresPre
  return {
    implied
    optimized
    rewrites
    ensures := []
    suggestions
    tiesOnly
    depends
    ignores
    allowed
    facts
    keys
    windowsTotal := windowsDet
    issues
    rows
    relations
    bounds
    -- Only for the issues the caps leave.
    inferred := Infer.merged A (bounds.filter fun (i, e, _) => i.isError && issues.contains (i, e))
    inferredNes :=
      Infer.mergedNes (bounds.filter fun (i, e, _) => i.isError && issues.contains (i, e))
    inferredNotNull :=
      Infer.mergedNotNull (bounds.filter fun (i, e, _) => i.isError && issues.contains (i, e))
    guardFree
    constant
    underAndOr := issuesUnderAndOr transform issues
    unchecked }

/-- The report of a parsed request. Each postcondition is analysed once
(`ensureEnv`); its verdicts are read from that analysis (`ensureResults`,
`check_ensures`), and so are the other analyses of the postconditions. -/
def Request.check (R : Request) : Except String Report :=
  -- `contract_sound` needs the postcondition plans to be well-formed (`check_wf`).
  if !R.ensures.all fun q => (q.root.capReads R.caps).checkWF R.cat then
    throw "a postcondition plan is not well-formed"
  else
    -- `R.kenv`, with every table's knowledge evaluated once (`knowsTable`):
    -- `R.kenv` itself would evaluate it again at each read.
    let K := memoKnowledge R.knowsTable R.know
    let envs := R.postEnvs K
    match R.analyses envs K with
    | .error e => .error e
    | .ok rep =>
      let ensures := (R.ensures.zip envs).map fun (q, env) => Request.ensureResults.resultsOf q env
      let tiePlaces := R.tiePlacesIn K
      .ok { rep with ensures, tiePlaces, deterministic := R.transform.isSome && tiePlaces.isEmpty }

/-- Check a `--contract` request. -/
def check (input : Json) : Except String Report := do
  (← parse input).check

/-- A postcondition's abstract values from the transformation's are those of
its plan. -/
theorem Request.ensureEnvIn_plan (R : Request) (K : KnowledgeEnv) (T : Plan) (p : Post) :
    R.ensureEnvIn K (p.plan T) = p.envFrom (R.transformEnvIn K T) := by
  simp only [Request.ensureEnvIn, Post.plan, Rel.capReads, Rel.aeval, Request.transformEnvIn,
    Post.envFrom]

theorem Request.postEnvs_eq (R : Request) (K : KnowledgeEnv) :
    R.postEnvs K = R.ensures.map (R.ensureEnvIn K) := by
  unfold Request.postEnvs Request.ensures
  split <;> simp [List.map_map, Function.comp_def, Request.ensureEnvIn_plan]

theorem Request.zip_results (R : Request) : ∀ qs : List Plan,
    ((qs.zip (qs.map R.ensureEnv)).map fun (q, env) => Request.ensureResults.resultsOf q env) =
      qs.map R.ensureResults
  | [] => rfl
  | q :: qs => by
    simp only [List.map_cons, List.zip_cons_cons, R.zip_results qs]
    rfl

theorem Request.check_ok {R : Request} {rep : Report} (hc : R.check = .ok rep) :
    (R.ensures.all fun q => (q.root.capReads R.caps).checkWF R.cat) = true ∧
      rep.ensures = R.ensures.map R.ensureResults ∧
      rep.deterministic = R.deterministicIn R.kenv ∧ rep.tiePlaces = R.tiePlacesIn R.kenv := by
  unfold Request.check at hc
  split at hc
  · cases hc
  · rename_i hwf
    refine ⟨by simpa using hwf, ?_⟩
    simp only at hc
    split at hc
    · cases hc
    · cases hc
      rw [Request.postEnvs_eq]
      exact ⟨R.zip_results R.ensures, (R.deterministicIn_eq _).symm, rfl⟩

theorem check_parse {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep) : R.check = .ok rep := by
  simpa [check, hR, bind, Except.bind] using hc

/-- The verdicts `check` reports are those of `ensureResults` on the parsed
postconditions, one list per postcondition plan. -/
theorem check_ensures {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep) :
    rep.ensures = R.ensures.map R.ensureResults :=
  (Request.check_ok (check_parse hR hc)).2.1

/-- The report's `deterministic` is `Request.deterministicIn`'s. -/
theorem check_deterministic {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep) :
    rep.deterministic = R.deterministicIn R.kenv :=
  (Request.check_ok (check_parse hR hc)).2.2.1

/-- The report's `tie_places` are `Request.tiePlacesIn`'s. -/
theorem check_tiePlaces {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep) :
    rep.tiePlaces = R.tiePlacesIn R.kenv :=
  (Request.check_ok (check_parse hR hc)).2.2.2

/-- The postcondition plans `check` analysed are well-formed. -/
theorem check_wf {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep) :
    ∀ q ∈ R.ensures, (q.root.capReads R.caps).checkWF R.cat = true := by
  have h := (Request.check_ok (check_parse hR hc)).1
  simpa only [List.all_eq_true] using h

/-! ### The checker's verdict is the contract theorem (#1088)

`check` parses the request (`parse`, trusted: the JSON reader and
`schemaEnv`) and analyses it on a catalog with the tables' arities and no rows
(`tablesCatalog`). `check_proved_sound` takes a postcondition the report marks
proved to the contract theorem on the data's catalog, through
`check_ensures` (the report's verdicts are `ensureResults`'), `check_wf`
(the analysed plans are well-formed), `Request.kenv_eq` (the description of
the inputs is `KnowledgeEnv.ofSpec`'s) and the analyses' congruence in the
catalog's arities (`AnalysisCongr.lean`). -/

omit [Boxes.Ambient] in
theorem lookup_map_self {β : Type} (f : String → β) (t : String) :
    ∀ l : List String, (l.map fun x => (x, f x)).lookup t = if t ∈ l then some (f t) else none
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.lookup_cons, List.mem_cons]
    by_cases h : t = x
    · subst h; simp
    · have : (t == x) = false := by simpa using h
      simp [this, h, lookup_map_self f t l]

omit [Boxes.Ambient] in
/-- The description of the inputs `check` computes once per table is
`KnowledgeEnv.ofSpec`'s. -/
theorem Request.kenv_eq (R : Request) :
    R.kenv = KnowledgeEnv.ofSpec R.schemas R.preOf R.keysOf := by
  funext t
  simp only [Request.kenv, memoKnowledge, Request.knowsTable, Request.know, KnowledgeEnv.ofSpec,
    lookup_map_self]
  split <;> rfl

omit [Boxes.Ambient] in
theorem Request.resultsOf_all (q : Plan) (env : List AVal)
    (h : ∀ e ∈ Request.ensureResults.resultsOf q env, e.2.1 = true) :
    env.all AVal.certainlyTrue = true := by
  simp only [Request.ensureResults.resultsOf] at h
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  split at h
  · rename_i hn
    have hn := (beq_iff_eq.mp hn)
    have hi' : i < (q.names.zip (env.map fun a => (a.certainlyTrue, a.render))).length := by
      simp [hn, hi]
    have := h _ (List.getElem_mem hi')
    simpa using this
  · have hi' : i < ((List.range env.length).map (s!"#{·}") |>.zip
        (env.map fun a => (a.certainlyTrue, a.render))).length := by simp [hi]
    have := h _ (List.getElem_mem hi')
    simpa using this

/-- **The data meets the request** (#1484): it has the request's tables with
their arities, and meets their schemas, their preconditions (those stated and
those sverify inferred and assumed, both in the request), their keys and their
row caps (`sv.max_rows`). The checker's theorems take it as their one
hypothesis on the data; the run-time checks of the preconditions decide it. -/
structure DataMeets (R : Request) (data : Catalog) : Prop where
  wf : data.WF
  arity : ∀ t, (data t).arity = (R.cat t).arity
  schemas : ∀ t, ∀ row ∈ (data t).rows, EnvMem (R.schemas t) row
  pre : ∀ t, ∀ row ∈ (data t).rows, ∀ e ∈ R.preOf t, (e.eval row).isTrue = true
  keys : ∀ t, ∀ k ∈ R.keysOf t, KeyOn k (data t).rows
  caps : ∀ t n, R.caps t = some n → (data t).rows.length ≤ n

/-- **The checker's verdict is the contract theorem** (#1088). When `check`
reports every column of the request's `k`-th postcondition proved, the
postcondition, its conditions projected over the request's transformation `T`
(#1484, finding 2: `parse` builds the plan from `T`, `Post.plan`), holds on
every row of every result the reference allows
(`Rel.OrderAllowed`: every order of the ties, D24), for any data that meets
the request (`DataMeets`).

`check` analyses under the reference whatever profile the request names: a
report under another one is the reference's, relabelled by `underProfile`
(`SubstraitCheck.lean`), a trusted step until #271 gives those engines
profiles of their own. A tolerance or an observation on the engine's doubles
belongs to the engine's soundness (`Engine.Sound`), which starts from this
conclusion.

The issues the report lists, the assumed ones among them (`Issue.assumed`: a
`SUM` that leaves its type, an overflow to `±∞`), are not hypotheses:
`Rel.OrderAllowed` gives a value at each, and the analysis is sound for that
value. Where the reference raises instead (`Profile.reference`, `raiseIf`),
it gives no result for the statement to speak of. An assumed issue is a
statement about the engine's run: whether it raises, whether it widens, and
whether its value means anything. It enters the engine's corollary as a
hypothesis through `Engine.Runs`, and leaves no hole in this lemma. -/
theorem check_proved_sound {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) :
    ∀ {out : Relation}, (Rel.emit (.project T.root p.exprs) p.mapping).OrderAllowed data out →
      ∀ row ∈ out, ∀ v ∈ row, v = .bool true := by
  intro out ho
  let q := p.plan T
  have hq : R.ensures[k]? = some q := by
    simp [Request.ensures, hT, hp, q]
  have hall : (R.ensureEnv q).all AVal.certainlyTrue = true := by
    rw [check_ensures hR hc, List.getD_eq_getElem?_getD, List.getElem?_map, hq] at hproved
    exact Request.resultsOf_all q _ hproved
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys
  have hQ : (q.root.capReads R.caps).WF data :=
    Rel.wf_congr hD.arity (Rel.checkWF_iff.mp (check_wf hR hc q (List.mem_of_getElem? hq)))
  have henv : R.ensureEnv q = ((q.root.capReads R.caps).analyse data R.kenv).cols := by
    simp only [Request.ensureEnv, Request.ensureEnvIn, Rel.analyse, KnowledgeEnv.windows,
      Rel.keyedWindows_congr hD.arity, (Rel.aeval_congr hD.arity _ _ _ false _).1]
  exact Knowledge.contract_sound_all hD.wf hK hQ (henv ▸ hall) (Rel.orderAllowed_capReads hD.caps ho)

/-- `p` keeps each of its conditions: over a transformation of arity `n`, the
column of every expression in `p.exprs` is among those `p.mapping` keeps.
The plans `sverify` sends keep exactly their conditions. -/
def Post.Selects (p : Post) (n : Nat) : Prop := ∀ i < p.exprs.length, n + i ∈ p.mapping

/-- **A proved postcondition over the transformation's own rows**: on every
result the reference allows for the transformation, every row makes each
column `p` keeps TRUE: the transformation's columns it keeps and its
conditions (`check_proved_sound`, through the `project` and `emit` cases of
`Rel.OrderAllowed`). `Expr.eval` is total: a condition that raises on a row
has no result in the reference (`raiseIf`) for this to speak of. -/
theorem check_proved_rows {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) :
    ∀ {out : Relation}, T.root.OrderAllowed data out → ∀ row ∈ out,
      ∀ j ∈ p.mapping, (row ++ p.exprs.map (·.eval row)).getD j .null = .bool true := by
  intro out ho row hrow j hj
  have h := check_proved_sound hR hc hD hT hp hproved
    (out := (out.map fun row => row ++ p.exprs.map (·.eval row)).map
      fun row => p.mapping.map (row.getD · .null))
    ⟨_, ⟨out, ho, rfl⟩, rfl⟩
  exact h _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨row, hrow, rfl⟩, rfl⟩) _
    (List.mem_map.mpr ⟨j, hj, rfl⟩)

/-- `check_proved_rows` for each condition of a postcondition that keeps
them all (`Post.Selects`): every row of every result the reference allows for
the transformation makes each of `p.exprs` TRUE. -/
theorem check_proved_conds {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hsel : p.Selects (T.root.arity R.cat))
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) :
    ∀ {out : Relation}, T.root.OrderAllowed data out → ∀ row ∈ out,
      ∀ e ∈ p.exprs, e.eval row = .bool true := by
  intro out ho row hrow e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hq : R.ensures[k]? = some (p.plan T) := by simp [Request.ensures, hT, hp]
  have hQ : ((p.plan T).root.capReads R.caps).WF data :=
    Rel.wf_congr hD.arity (Rel.checkWF_iff.mp (check_wf hR hc _ (List.mem_of_getElem? hq)))
  have hT' : (T.root.capReads R.caps).WF data := by
    simp only [Post.plan, Rel.capReads, Rel.WF] at hQ
    exact hQ.1.1
  have hlen : row.length = T.root.arity R.cat := by
    rw [← Rel.arity_congr hD.arity, ← Rel.capReads_arity R.caps]
    exact Rel.orderAllowed_arity hD.wf hT' (Rel.orderAllowed_capReads hD.caps ho) row hrow
  have h := check_proved_rows hR hc hD hT hp hproved ho row hrow _
    (hsel i hi)
  rw [← hlen] at h
  have hcol : (row ++ p.exprs.map (·.eval row)).getD (row.length + i) .null =
      p.exprs[i].eval row := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_eq_getElem hi]
  rwa [hcol] at h

/-- **The checker's `deterministic` is a theorem** (#1484, finding 9). When
`check` reports the transformation deterministic, every result the reference
allows for it, every order of the ties (`Rel.OrderAllowed`), is `Rel.eval`'s
up to the order of its rows, for any data that meets the request
(`DataMeets`): through `Rel.detPlan` (`check_deterministic`) and
`Rel.allowed_perm_eval`. -/
theorem check_deterministic_sound {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) (hdet : rep.deterministic = true) :
    ∀ {out : Relation}, T.root.OrderAllowed data out → out.Perm (T.root.eval data) := by
  intro out ho
  rw [check_deterministic hR hc] at hdet
  simp only [Request.deterministicIn, hT, Bool.and_eq_true] at hdet
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys
  have hwf : T.root.WF data := Rel.wf_congr hD.arity (Rel.checkWF_iff.mp hdet.1)
  have hd : T.root.detPlan data R.kenv.cols R.kenv.facts R.kenv.keys = true := by
    rw [Rel.detPlan_congr hD.arity]
    exact hdet.2
  exact Knowledge.allowed_perm_eval hD.wf hK hwf hd (Rel.orderAllowed_allowed ho)

end Substrait.ContractCheck
