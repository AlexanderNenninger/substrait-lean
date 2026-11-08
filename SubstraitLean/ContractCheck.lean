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
import SubstraitLean.Knowledge
import SubstraitLean.Implied
import SubstraitLean.Robust
import SubstraitLean.AllowedNear
import SubstraitLean.AllowedAnalysis

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

/-- What a column's declared type allows: a list's elements and a struct's
fields by their types (#925), `depth` levels down. -/
def typeEnvD : Nat → Json → AVal
  | 0, _ => AVal.top
  | depth + 1, ty =>
    -- Numbers: integers, doubles (by their codes, `SubstraitLean/Float.lean`), timestamps and dates.
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
  ensures : List (String × Bool × String)
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
  /-- Does every window order its partitions totally (`Rel.windowsTotal`), and
  every `FETCH` take rows an `ORDER BY` on a key fixes (`Rel.fetchesTotal`)? -/
  deterministic : Bool := true
  /-- Does every window order its partitions totally? A `FETCH` over ties
  keeps every proof (it takes some rows of an allowed order) and the written
  SQL breaks its ties by input order; only a rerun may differ. -/
  windowsTotal : Bool := true
  /-- Where the transformation leaves the order of ties open (D24): each
  relation in the pre-order of `relations`, by its index, its operator and
  what is open. Empty when `deterministic`. -/
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
  Json.mkObj [
    ("ensures", Json.arr (((((r.ensures.zip (r.suggestions ++
        List.replicate r.ensures.length ({ why := none } : Infer.Bounds))).zip
        (r.tiesOnly ++ List.replicate r.ensures.length false)).zip
        (r.depends ++ List.replicate r.ensures.length none)).zip
        ((r.allowed ++ List.replicate r.ensures.length false).zip
          (r.ignores ++ List.replicate r.ensures.length none))).map
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

/-- What the relation `r` leaves open of the order of ties, beyond its
inputs: the checks of `Rel.windowsTotal` and `Rel.fetchesTotal` at `r`. -/
def tiesHere (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) : Rel → List String
  | .window r part sort fns =>
    if Rel.windowTotalAt cat A F K r part sort fns then [] else
      let fs := ", ".intercalate ((fns.filter (!·.orderFree)).map WinFn.render)
      [s!"{fs} over rows that tie in PARTITION BY {part.map (s!"${·}")} ORDER BY " ++
        s!"{sort.map (s!"${·.col}")}, with no key among those columns"]
  | .aggregate r gs ms => (ms.filter fun m => !Measure.totalIn cat A F K r gs m).map fun m =>
      s!"{m.render} over rows that tie in its ORDER BY, with no key among the group's and " ++
        "the order's columns"
  | .fetch (.orderBy i keys) _ _ =>
    if Rel.fetchTotalAt cat A F K i keys then [] else
      [s!"the rows it takes tie in ORDER BY {keys.map (s!"${·.col}")}, with no key among " ++
        "those columns"]
  | .fetch _ _ _ => ["the rows it takes have no ORDER BY"]
  | _ => []

/-- Where `r` leaves the order of ties open: each relation's index in
`preorder r`, its operator and what is open. -/
def tiePlaces (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (K : String → List (List Nat)) (r : Rel) : List (Nat × String × String) :=
  (preorder r).zipIdx.flatMap fun (n, i) => (tiesHere cat A F K n).map (i, opName n, ·)

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
  -- Each table's description and facts, computed once: `A` and `F` are
  -- called at every read of every pass (#825).
  let names := tables.map (·.1) |>.eraseDups
  let keysJson := (input.getObjVal? "keys").toOption
  let keysOf (t : String) : List (List Nat) :=
    natLists (keysJson.bind (·.getObjVal? t |>.toOption) |>.getD (.arr #[]))
  -- One description of the inputs (`KnowledgeEnv.ofSpec`, sound by
  -- `KnowledgeEnv.ofSpec_sound`), computed once per table: the analyses
  -- read it at every read of every pass (#825). The window keys follow
  -- from it (`KnowledgeEnv.Sound.windows`).
  let know (t : String) : Knowledge :=
    ⟨tableEnv (schemas t) (preOf t), (preOf t).flatMap Expr.factsOf, keysOf t, none⟩
  let knows := names.map fun t => (t, know t)
  let kenv : KnowledgeEnv := fun t => (knows.lookup t).getD (know t)
  let A := kenv.cols
  let F := kenv.facts
  let inputKeys := kenv.keys
  let T := kenv.windows cat
  let implied : List (String × List (List (Nat × Bound))) :=
    ((transform.map (·.root)).filter (·.checkWF cat)).elim [] (impliedOf cat A F)
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let perKey := rowsPer ((input.getObjVal? "rows_per").toOption.getD (.obj {}))
  let mut results : List (String × Bool × String) := []
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
  for q in ensures do
    -- `contract_sound` needs the postcondition plan to be well-formed.
    if !(q.root.capReads caps).checkWF cat then throw "a postcondition plan is not well-formed"
    let env := (q.root.capReads caps).aeval cat A F T
    let names := if q.names.length == env.length then q.names
      else (List.range env.length).map (s!"#{·}")
    -- Proved for every order of the ties (`contract_sound_all`, with
    -- `Rel.orderAllowed_capReads` and `Rel.keyedWindows_soundAll`, D24).
    results := results ++ names.zip (env.map fun a => (a.certainlyTrue, a.render))
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
  -- Windows that order their partitions totally, and `FETCH`es below an
  -- `ORDER BY` on a key: otherwise a rerun may give other rows (D10).
  let windowsDet := transform.all (·.root.windowsTotal cat A F inputKeys)
  let deterministic := windowsDet && transform.all (·.root.fetchesTotal cat A F inputKeys)
  let tiePlaces := match transform with
    | some p => if p.root.checkWF cat then tiePlaces cat A F inputKeys p.root else []
    | none => []
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
  let ignores := if obsJ.isNone then [] else combineIgnores (sqlT || windowsDet) ignoresPre
  return {
    implied
    optimized
    rewrites
    ensures := results
    suggestions
    tiesOnly
    depends
    ignores
    allowed
    facts
    keys
    deterministic
    windowsTotal := windowsDet
    tiePlaces
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

end Substrait.ContractCheck
