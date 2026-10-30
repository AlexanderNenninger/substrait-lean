import SubstraitLean.Parse
import SubstraitLean.Weighted
import SubstraitLean.Terms

/-!
# Writing `Rel` back out as Substrait JSON

Like the parser, this is **trusted, unverified code**. The CLI checks that
every plan it writes parses back to the same `Rel` (a round trip), and the
golden tests run that check on every fixture.

Conventions:
* `Rel.emit` becomes `RelCommon.emit` on a `ProjectRel` (wrapping the child
  in an empty project if needed); directly nested emits are composed.
* Every modelled function is declared in `extensions` with a fixed anchor.
-/

namespace Substrait.Write

open Lean (Json toJson)

/-- `(anchor, Substrait name)` for every function the writer can emit.
DataFusion resolves functions by name and argument types, so the same `add`
serves integers, doubles and timestamps. -/
def functions : List (Nat × String) :=
  [(1, "not"), (2, "is_null"), (3, "negate"), (4, "add"), (5, "subtract"), (6, "multiply"),
   (7, "equal"), (8, "lt"), (9, "and"), (10, "or"), (11, "divide"),
   (12, "row_number"), (13, "lag"), (14, "lead")]

def UnFn.anchor : UnFn → Nat
  | .not => 1 | .isNull => 2 | .neg | .fneg => 3 | .itof => 0

def BinFn.anchor : BinFn → Nat
  | .add | .fadd => 4 | .sub | .fsub => 5 | .mul | .fmul => 6 | .eq => 7 | .lt => 8
  | .and => 9 | .or => 10 | .fdiv => 11

def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

def writeValue : Value → Json
  | .null => obj [("null", obj [("i64", obj [])])]
  | .bool b => obj [("boolean", toJson b)]
  | .int i => obj [("i64", toJson (toString i))]
  | .str s => obj [("string", toJson s)]

def fp64Type : Json := obj [("fp64", obj [("nullability", "NULLABILITY_NULLABLE")])]

/-- A double literal: exact, since `m · 2⁻¹⁰⁷⁴ = m · 5¹⁰⁷⁴ · 10⁻¹⁰⁷⁴`. -/
def writeDouble (c : Int) : Json :=
  if c == FloatCode.nan then "NaN"
  else if c == FloatCode.posInf then "Infinity"
  else if c == FloatCode.negInf then "-Infinity"
  else
    let (negative, m) := FloatCode.finiteParts c
    let mant : Int := m * 5 ^ 1074
    -- Lean renders a zero mantissa with a large exponent as `0.e-1064`.
    if m == 0 then Json.num 0 else Json.num ⟨if negative then -mant else mant, 1074⟩

def call (anchor : Nat) (args : List Json) : Json :=
  obj [("scalarFunction", obj [
    ("functionReference", toJson anchor),
    ("arguments", Json.arr (args.map fun a => obj [("value", a)]).toArray)])]

/-- An integer literal, written as the kind of value it stands for. -/
def writeLit (k : Parse.Kind) (v : Value) : Json :=
  let lit (kvs : List (String × Json)) := obj [("literal", obj kvs)]
  match k, v with
  -- JSON has no negative NaN or zero: write `negate(NaN)`, `negate(0.0)`, which fold back.
  | .float, .int c =>
    if c == FloatCode.negNan then call 3 [lit [("fp64", "NaN")]]
    else if c == FloatCode.ofMag true 0 then call 3 [lit [("fp64", writeDouble (FloatCode.ofMag false 0))]]
    else lit [("fp64", writeDouble c)]
  | .time, .int us =>
    lit [("precisionTimestamp", obj [("precision", toJson 6), ("value", toJson (toString us))])]
  | .date, .int d => lit [("date", toJson d)]
  | _, v => obj [("literal", writeValue v)]

/-- A day/second interval of `us` microseconds. -/
def writeInterval (us : Int) : Json :=
  obj [("literal", obj [("intervalDayToSecond", obj [
    ("seconds", toJson (us / 1_000_000)), ("subseconds", toJson (toString (us % 1_000_000))),
    ("precision", toJson 6)])])]

def isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- Write `e` over input columns of kinds `cols`; `ctx` is the kind a literal
at the top should be written as. -/
def writeExpr (cols : List Parse.Kind) (ctx : Parse.Kind) : Expr → Json
  | .lit v => writeLit ctx v
  | .field i => obj [("selection", obj [
      ("directReference", obj [("structField", obj [("field", toJson i)])]),
      ("rootReference", obj [])])]
  | .un .itof a => obj [("cast", obj [("type", fp64Type), ("input", writeExpr cols .int a)])]
  | .un .fneg a => call 3 [writeExpr cols .float a]
  | .un .neg a => call 3 [writeExpr cols ctx a]
  | .un f a => call (UnFn.anchor f) [writeExpr cols (a.kind cols) a]
  | .bin f a b =>
    let ka := if isLit a then b.kind cols else a.kind cols
    let kb := if isLit b then a.kind cols else b.kind cols
    match f with
    | .fadd | .fsub | .fmul | .fdiv =>
      call (BinFn.anchor f) [writeExpr cols .float a, writeExpr cols .float b]
    | .add | .sub =>
      -- `timestamp ± constant`: the constant is an interval in microseconds.
      match ka, b with
      | .time, .lit (.int us) => call (BinFn.anchor f) [writeExpr cols ka a, writeInterval us]
      | _, _ => call (BinFn.anchor f) [writeExpr cols ka a, writeExpr cols kb b]
    | _ => call (BinFn.anchor f) [writeExpr cols ka a, writeExpr cols kb b]
  | .ifThen c t e => obj [("ifThen", obj [
      ("ifs", Json.arr #[obj [("if", writeExpr cols .bool c), ("then", writeExpr cols ctx t)]]),
      ("else", writeExpr cols ctx e)])]

/-- `baseSchema` of each table: the parsed one, or a placeholder of `i64`
columns for tables the parser never saw. -/
abbrev Schemas := String → Nat → Json

def i64Type : Json := obj [("i64", obj [("nullability", "NULLABILITY_NULLABLE")])]

def placeholderSchema (n : Nat) : Json :=
  obj [("names", Json.arr ((List.range n).map fun i => toJson s!"c{i}").toArray),
       ("struct", obj [("types", Json.arr (List.replicate n i64Type).toArray),
                       ("nullability", "NULLABILITY_REQUIRED")])]

/-- Attach an output mapping. It is always put on a `ProjectRel` (other
relations get wrapped in a project with no expressions, which the parser reads
back as the identity), the form every consumer handles. -/
def withCommon (kind : String) (body : List (String × Json)) (emit : Option (List Nat)) : Json :=
  let common (m : List Nat) := ("common", obj [("emit", obj [("outputMapping", toJson m)])])
  match emit with
  | none => obj [(kind, obj body)]
  | some m =>
    if kind == "project" then obj [(kind, obj (common m :: body))]
    else obj [("project", obj [common m, ("input", obj [(kind, obj body)]),
      ("expressions", Json.arr #[])])]

/-- Column kinds, from the schemas the writer uses. -/
def relKinds (schemas : Schemas) (cat : Catalog) : Rel → List Parse.Kind
  | .read t => Parse.schemaKinds (schemas t (cat t).arity)
  | .values n _ => List.replicate n .other
  | .filter r _ | .fetch r _ _ => relKinds schemas cat r
  | .project r es =>
      let ks := relKinds schemas cat r
      ks ++ es.map (·.kind ks)
  | .emit r m =>
      let ks := relKinds schemas cat r
      m.map (ks.getD · .other)
  | .cross a b | .join a b _ _ => relKinds schemas cat a ++ relKinds schemas cat b
  | .unionAll a _ => relKinds schemas cat a
  | .window r _ _ fns =>
      let ks := relKinds schemas cat r
      ks ++ fns.map (WinFn.kind ks)

/-- A window function over input columns of kinds `cols`. -/
def writeWindow (cols : List Parse.Kind) (part : List Nat) (sort : List SortKey) (f : WinFn) : Json :=
  let col (i : Nat) := writeExpr cols .other (.field i)
  let (anchor, args) := match f with
    | .rowNumber => (12, [])
    | .lag c k d | .lead c k d =>
      let base := [col c, writeLit .int (.int k)]
      (if f matches .lag .. then 13 else 14,
        if d == Value.null then base else base ++ [writeLit (cols.getD c .other) d])
  let dir (k : SortKey) : Json := match k.desc, k.nullsFirst with
    | false, true => "SORT_DIRECTION_ASC_NULLS_FIRST"
    | false, false => "SORT_DIRECTION_ASC_NULLS_LAST"
    | true, true => "SORT_DIRECTION_DESC_NULLS_FIRST"
    | true, false => "SORT_DIRECTION_DESC_NULLS_LAST"
  obj [("windowFunction", obj [
    ("functionReference", toJson anchor),
    ("partitions", Json.arr (part.map col).toArray),
    ("sorts", Json.arr (sort.map fun (k : SortKey) => obj [("expr", col k.col), ("direction", dir k)]).toArray),
    ("arguments", Json.arr (args.map fun a => obj [("value", a)]).toArray),
    ("lowerBound", obj [("unbounded", obj [])]), ("upperBound", obj [("unbounded", obj [])]),
    ("boundsType", "BOUNDS_TYPE_ROWS")])]

/-- Write a relation; `emit` is an output mapping to put on its `RelCommon`. -/
def writeRel (schemas : Schemas) (cat : Catalog) : Rel → Option (List Nat) → Json
  | .emit r m, out => writeRel schemas cat r (some (match out with
      | none => m
      | some o => o.map (m.getD · 0)))
  | .read t, out => withCommon "read" [
      ("baseSchema", schemas t (cat t).arity),
      ("namedTable", obj [("names", toJson (t.splitOn "."))])] out
  | .values n rows, out => withCommon "read" [
      ("baseSchema", placeholderSchema n),
      ("virtualTable", obj [("expressions", Json.arr (rows.map fun row =>
        obj [("fields", Json.arr (row.map fun v => obj [("literal", writeValue v)]).toArray)]).toArray)])] out
  | .filter r c, out => withCommon "filter" [
      ("input", writeRel schemas cat r none),
      ("condition", writeExpr (relKinds schemas cat r) .bool c)] out
  | .project r es, out => withCommon "project" [
      ("input", writeRel schemas cat r none),
      ("expressions",
        let ks := relKinds schemas cat r
        Json.arr (es.map fun e => writeExpr ks (e.kind ks) e).toArray)] out
  | .cross a b, out => withCommon "cross" [
      ("left", writeRel schemas cat a none), ("right", writeRel schemas cat b none)] out
  | .join a b ty on, out => withCommon "join" [
      ("left", writeRel schemas cat a none), ("right", writeRel schemas cat b none),
      ("expression", writeExpr (relKinds schemas cat a ++ relKinds schemas cat b) .bool on),
      ("type", match ty with | .inner => "JOIN_TYPE_INNER" | .left => "JOIN_TYPE_LEFT")] out
  | .fetch r off cnt, out => withCommon "fetch" ([
      ("input", writeRel schemas cat r none), ("offset", toJson (toString off))] ++
      (cnt.map fun c => [("count", toJson (toString c))]).getD []) out
  | .unionAll a b, out => withCommon "set" [
      ("inputs", Json.arr #[writeRel schemas cat a none, writeRel schemas cat b none]),
      ("op", "SET_OP_UNION_ALL")] out
  | .window r part sort fns, out => withCommon "project" [
      ("input", writeRel schemas cat r none),
      ("expressions",
        let ks := relKinds schemas cat r
        Json.arr (fns.map (writeWindow ks part sort)).toArray)] out

def writePlan (schemas : Schemas) (cat : Catalog) (root : Rel) (names : List String) : Json :=
  obj [
    ("extensions", Json.arr (functions.map fun (a, n) => obj [("extensionFunction", obj [
      ("functionAnchor", toJson a), ("name", toJson n)])]).toArray),
    ("relations", Json.arr #[obj [("root", obj [
      ("input", writeRel schemas cat root none), ("names", toJson names)])]])]

/-- Schemas recorded by the parser, falling back to placeholders. -/
def planSchemas (p : Parse.Plan) : Schemas := fun t n =>
  match p.tables.lookup t with
  | some (_, s) => s
  | none => placeholderSchema n

/-- Does writing `p.root` and parsing it back give the same plan? -/
def roundtrips (p : Parse.Plan) : Bool :=
  let json := writePlan (planSchemas p) p.catalog p.root p.names
  match Parse.parsePlan json.compress with
  | .ok p' => p'.root == p.root && p'.names == p.names
  | .error _ => false

/-! ## Delta plans for an engine -/

def deltaName (t : String) : String := t ++ "$delta"

def isDeltaName (t : String) : Bool := t.endsWith "$delta"

/-- Change tables have the base table's columns plus a trailing `__weight`. -/
def deltaSchema (base : Json) : Json :=
  let names := match base.getObjValAs? (Array String) "names" with
    | .ok ns => ns.push "__weight" | .error _ => #["__weight"]
  let st := (base.getObjVal? "struct").toOption.getD (obj [])
  let types := match st.getObjValAs? (Array Json) "types" with
    | .ok ts => ts.push i64Type | .error _ => #[i64Type]
  obj [("names", toJson names),
       ("struct", obj [("types", Json.arr types), ("nullability", "NULLABILITY_REQUIRED")])]

/-- The arity catalog `Rel.weighted_eval` is stated over: change tables
have their base table's arity (the weight column is not counted). -/
def deltaCatalog (p : Parse.Plan) : Catalog := fun t =>
  if isDeltaName t then p.catalog (t.dropEnd 6).toString else p.catalog t

/-- The union-free terms of `Rel.delta` (`Rel.zeval_terms`); an engine runs
each one (after the weight-column encoding) and concatenates the results.
Union-free plans keep DataFusion's consumer from losing table qualifiers at a
union, which makes column names collide in a later join. -/
def deltaTerms (p : Parse.Plan) : List Rel := (p.root.delta deltaName).terms

def writeDeltaPlan (p : Parse.Plan) (term : Rel) : Json :=
  let schemas : Schemas := fun t n =>
    if isDeltaName t then deltaSchema (planSchemas p (t.dropEnd 6).toString (n - 1))
    else planSchemas p t n
  -- The engine's tables: change tables have one more (weight) column.
  let engineCat : Catalog := fun t =>
    let c := deltaCatalog p t
    if isDeltaName t then ⟨c.arity + 1, []⟩ else c
  writePlan schemas engineCat (term.weighted (deltaCatalog p) isDeltaName) (p.names ++ ["__weight"])

end Substrait.Write
