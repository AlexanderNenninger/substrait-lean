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
   (12, "row_number"), (13, "lag"), (14, "lead"), (15, "floor"), (16, "ceil"), (17, "round"),
   (18, "modulus"), (19, "power"), (20, "upper"), (21, "lower"), (22, "character_length"),
   (23, "regexp_match"), (24, "array_length"), (25, "date_part"), (26, "date_trunc"),
   (27, "str_concat"), (28, "strpos"), (29, "starts_with"), (30, "ends_with"), (31, "like"),
   (32, "substring"), (33, "btrim"), (34, "ltrim"), (35, "rtrim"),
   (36, "count"), (37, "sum"), (38, "avg"), (39, "min"), (40, "max"), (41, "nanvl"),
   (60, "date_diff")]

def AggFn.anchor : AggFn → Nat
  | .count => 36 | .sum | .fsum => 37 | .avg => 38 | .min => 39 | .max => 40

def UnFn.anchor : UnFn → Nat
  | .not => 1 | .isNull => 2 | .neg | .fneg => 3 | .ffloor => 15 | .fceil => 16
  | .fround | .froundTo _ => 17
  | .upper => 20 | .lower => 21 | .length => 22 | .datePart _ | .dayPart _ => 25
  | .dateTrunc _ | .dayTrunc _ => 26 | .addMonths _ _ => 4
  -- Casts are written as casts, not calls; `regexp_match` as two calls.
  | .itof | .ftoi | .narrow _ | .itos | .toDate | .regexMatch _ => 0

def BinFn.anchor : BinFn → Nat
  | .add | .fadd => 4 | .sub | .fsub => 5 | .mul | .fmul => 6 | .eq => 7 | .lt => 8
  | .and => 9 | .or => 10 | .fdiv | .idiv => 11 | .imod => 18 | .ipow | .fpow => 19
  | .concat => 27 | .strpos => 28 | .startsWith => 29 | .endsWith => 30 | .like => 31
  | .substr _ => 32 | .dateAdd => 4 | .dateDiff => 60
  | .trim true true => 33 | .trim true false => 34 | .trim false _ => 35

def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

def writeValue : Value → Json
  | .null => obj [("null", obj [("i64", obj [])])]
  | .bool b => obj [("boolean", toJson b)]
  | .int i => obj [("i64", toJson (toString i))]
  | .str s => obj [("string", toJson s)]

def fp64Type : Json := obj [("fp64", obj [("nullability", "NULLABILITY_NULLABLE")])]
def i64Type : Json := obj [("i64", obj [("nullability", "NULLABILITY_NULLABLE")])]

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
  | .float, .int c => lit [("fp64", writeDouble c)]
  | .time, .int us =>
    lit [("precisionTimestamp", obj [("precision", toJson 6), ("value", toJson (toString us))])]
  | .date, .int d => lit [("date", toJson d)]
  -- A typed `NULL`, so that e.g. `CASE … THEN NULL ELSE name END` type-checks.
  | .float, .null => lit [("null", fp64Type)]
  | .str, .null => lit [("null", obj [("string", obj [])])]
  | .bool, .null => lit [("null", obj [("bool", obj [])])]
  | .time, .null => lit [("null", obj [("precisionTimestamp", obj [("precision", toJson 6)])])]
  | .date, .null => lit [("null", obj [("date", obj [])])]
  | _, v => obj [("literal", writeValue v)]

/-- A day/second interval of `us` microseconds. -/
def writeInterval (us : Int) : Json :=
  obj [("literal", obj [("intervalDayToSecond", obj [
    ("seconds", toJson (us / 1_000_000)), ("subseconds", toJson (toString (us % 1_000_000))),
    ("precision", toJson 6)])])]

/-- An interval of `m` months. -/
def writeMonths (m : Int) : Json :=
  obj [("literal", obj [("intervalCompound", obj [
    ("intervalYearToMonth", obj [("months", toJson m)]),
    ("intervalDayToSecond", obj [("precision", toJson 6)])])])]

/-- A double the model has one zero and one NaN for, as IEEE engines compute
it: `nanvl(x + 0.0, NaN)` makes `-0.0` zero and every NaN the positive one.
Engines that compare by `f64::total_cmp` (DataFusion) need it after an
operation that can give `-0.0` or a negative NaN; the parser reads
`nanvl(x, NaN)` back as `x`. -/
def canonical (x : Json) : Json :=
  let lit (s : Json) := obj [("literal", obj [("fp64", s)])]
  call 41 [call 4 [x, lit (Json.num 0)], lit "NaN"]

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
  | .un .toDate a => obj [("cast", obj [("type", obj [("date", obj [("nullability", "NULLABILITY_NULLABLE")])]),
      ("input", writeExpr cols .time a)])]
  | .un .fneg a => canonical (call 3 [writeExpr cols .float a])
  | .un .ftoi a => obj [("cast", obj [("type", i64Type), ("input", writeExpr cols .float a),
      ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]
  | .un (.narrow n) a =>
    let ty := if n ≤ 8 then "i8" else if n ≤ 16 then "i16" else "i32"
    obj [("cast", obj [("type", obj [(ty, obj [("nullability", "NULLABILITY_NULLABLE")])]),
      ("input", writeExpr cols .int a), ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]
  | .un .itos a => obj [("cast", obj [("type", obj [("string", obj [("nullability", "NULLABILITY_NULLABLE")])]),
      ("input", writeExpr cols .int a), ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]
  | .un (.froundTo d) a =>
    canonical (call 17 [writeExpr cols .float a, obj [("literal", obj [("i64", toJson (toString d))])]])
  | .un .ffloor a => canonical (call 15 [writeExpr cols .float a])
  | .un .fceil a => canonical (call 16 [writeExpr cols .float a])
  | .un .fround a => canonical (call 17 [writeExpr cols .float a])
  | .un .neg a => call 3 [writeExpr cols ctx a]
  | .un (.regexMatch p) a =>
    call 24 [call 23 [writeExpr cols .str a, obj [("literal", writeValue (.str p))]]]
  | .un (.datePart p) a => call 25 [obj [("literal", writeValue (.str p.name))], writeExpr cols .time a]
  | .un (.dateTrunc u) a => call 26 [obj [("literal", writeValue (.str u.name))], writeExpr cols .time a]
  | .un (.dayPart p) a => call 25 [obj [("literal", writeValue (.str p.name))], writeExpr cols .date a]
  | .un (.dayTrunc u) a => call 26 [obj [("literal", writeValue (.str u.name))], writeExpr cols .date a]
  | .un (.addMonths m t) a => call 4 [writeExpr cols (if t then .time else .date) a, writeMonths m]
  | .un f a => call (UnFn.anchor f) [writeExpr cols (a.kind cols) a]
  | .bin f a b =>
    let ka := if isLit a then b.kind cols else a.kind cols
    let kb := if isLit b then a.kind cols else b.kind cols
    match f with
    -- A sum or difference of canonical doubles is `-0.0` never, NaN only
    -- as `inf - inf`, which IEEE engines may make negative.
    | .fadd | .fsub | .fmul | .fdiv | .fpow =>
      canonical (call (BinFn.anchor f) [writeExpr cols .float a, writeExpr cols .float b])
    | .add | .sub =>
      -- `timestamp ± constant`: the constant is an interval in microseconds.
      match ka, b with
      | .time, .lit (.int us) => call (BinFn.anchor f) [writeExpr cols ka a, writeInterval us]
      | _, _ => call (BinFn.anchor f) [writeExpr cols ka a, writeExpr cols kb b]
    -- Days added to a date: an interval of days, or a count of them.
    | .dateAdd => match b with
      | .lit (.int k) => call 4 [writeExpr cols .date a, writeInterval (k * Time.usPerDay)]
      | _ => call 4 [writeExpr cols .date a, call 6 [writeExpr cols .int b, writeInterval Time.usPerDay]]
    | .dateDiff => call 60 [writeExpr cols .date a, writeExpr cols .date b]
    | .substr (some n) =>
      call 32 [writeExpr cols .str a, writeExpr cols .int b, obj [("literal", writeValue (.int n))]]
    | .substr none => call 32 [writeExpr cols .str a, writeExpr cols .int b]
    | .concat | .strpos | .startsWith | .endsWith | .like | .trim _ _ =>
      call (BinFn.anchor f) [writeExpr cols .str a, writeExpr cols .str b]
    | _ => call (BinFn.anchor f) [writeExpr cols ka a, writeExpr cols kb b]
  | .ifThen c t e => obj [("ifThen", obj [
      ("ifs", Json.arr #[obj [("if", writeExpr cols .bool c), ("then", writeExpr cols ctx t)]]),
      ("else", writeExpr cols ctx e)])]

/-- `baseSchema` of each table: the parsed one, or a placeholder of `i64`
columns for tables the parser never saw. -/
abbrev Schemas := String → Nat → Json


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
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ => relKinds schemas cat r
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
  | .aggregate r gs ms =>
      let ks := relKinds schemas cat r
      gs.map (·.kind ks) ++ ms.map (·.kind ks)

def writeSortKey (cols : List Parse.Kind) (k : SortKey) : Json :=
  let dir : Json := match k.desc, k.nullsFirst with
    | false, true => "SORT_DIRECTION_ASC_NULLS_FIRST"
    | false, false => "SORT_DIRECTION_ASC_NULLS_LAST"
    | true, true => "SORT_DIRECTION_DESC_NULLS_FIRST"
    | true, false => "SORT_DIRECTION_DESC_NULLS_LAST"
  obj [("expr", writeExpr cols .other (.field k.col)), ("direction", dir)]

/-- A window function over input columns of kinds `cols`. -/
def writeWindow (cols : List Parse.Kind) (part : List Nat) (sort : List SortKey) (f : WinFn) : Json :=
  let col (i : Nat) := writeExpr cols .other (.field i)
  let (anchor, args) := match f with
    | .rowNumber => (12, [])
    | .lag c k d | .lead c k d =>
      let base := [col c, writeLit .int (.int k)]
      (if f matches .lag .. then 13 else 14,
        if d == Value.null then base else base ++ [writeLit (cols.getD c .other) d])
  obj [("windowFunction", obj [
    ("functionReference", toJson anchor),
    ("partitions", Json.arr (part.map col).toArray),
    ("sorts", Json.arr (sort.map (writeSortKey cols)).toArray),
    ("arguments", Json.arr (args.map fun a => obj [("value", a)]).toArray),
    ("lowerBound", obj [("unbounded", obj [])]), ("upperBound", obj [("unbounded", obj [])]),
    ("boundsType", "BOUNDS_TYPE_ROWS")])]

/-- An `AggregateRel` measure over input columns of kinds `cols`. -/
def writeMeasure (cols : List Parse.Kind) (m : Measure) : Json :=
  let measure := obj [
    ("functionReference", toJson (AggFn.anchor m.fn)),
    ("invocation", if m.distinct then "AGGREGATION_INVOCATION_DISTINCT" else "AGGREGATION_INVOCATION_ALL"),
    ("arguments", Json.arr #[obj [("value", writeExpr cols (m.arg.kind cols) m.arg)]])]
  obj ([("measure", measure)] ++
    (m.filter.map fun c => [("filter", writeExpr cols .bool c)]).getD [])

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
  | .semi a b anti on, out => withCommon "join" [
      ("left", writeRel schemas cat a none), ("right", writeRel schemas cat b none),
      ("expression", writeExpr (relKinds schemas cat a ++ relKinds schemas cat b) .bool on),
      ("type", if anti then "JOIN_TYPE_LEFT_ANTI" else "JOIN_TYPE_LEFT_SEMI")] out
  | .orderBy r keys, out => withCommon "sort" [
      ("input", writeRel schemas cat r none),
      ("sorts", Json.arr (keys.map (writeSortKey (relKinds schemas cat r))).toArray)] out
  -- Grouping by every column, with no measures.
  | .distinct r, out =>
      let ks := relKinds schemas cat r
      withCommon "aggregate" [
        ("input", writeRel schemas cat r none),
        ("groupingExpressions", Json.arr ((List.range ks.length).map fun i =>
          writeExpr ks .other (.field i)).toArray),
        ("groupings", Json.arr #[obj [("expressionReferences",
          Json.arr ((List.range ks.length).map toJson).toArray)]])] out
  | .aggregate r gs ms, out =>
      let ks := relKinds schemas cat r
      withCommon "aggregate" [
        ("input", writeRel schemas cat r none),
        ("groupingExpressions", Json.arr (gs.map fun g => writeExpr ks (g.kind ks) g).toArray),
        ("groupings", if gs.isEmpty then Json.arr #[] else
          Json.arr #[obj [("expressionReferences", toJson (List.range gs.length))]]),
        ("measures", Json.arr (ms.map (writeMeasure ks)).toArray)] out
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
