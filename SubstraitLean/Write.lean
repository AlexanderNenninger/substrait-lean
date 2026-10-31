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

/-! ## Function anchors

Every function the writer can emit has a fixed anchor, declared in one list
per area. A new function goes at the end of its area's list, with the next
free anchor of that area's range, so pull requests for different areas
touch different lines. Anchors below 100 predate the ranges and stay as they
are. The checks after `functions` reject a duplicate anchor or name, and an
anchor outside its area's range.

DataFusion resolves functions by name and argument types, so the same `add`
serves integers, doubles, dates and timestamps. -/

/-- Logic, comparison and arithmetic: new anchors 100–199. -/
def coreFns : List (Nat × String) := [
  (1, "not"), (2, "is_null"), (3, "negate"), (4, "add"), (5, "subtract"), (6, "multiply"),
  (7, "equal"), (8, "lt"), (9, "and"), (10, "or"), (11, "divide"),
  (15, "floor"), (16, "ceil"), (17, "round"), (18, "modulus"), (19, "power"), (41, "nanvl")]

/-- Strings: new anchors 200–299. -/
def stringFns : List (Nat × String) := [
  (20, "upper"), (21, "lower"), (22, "character_length"), (23, "regexp_match"),
  (27, "str_concat"), (28, "strpos"), (29, "starts_with"), (30, "ends_with"), (31, "like"),
  (32, "substring"), (33, "btrim"), (34, "ltrim"), (35, "rtrim")]

/-- Dates and times: new anchors 300–399. -/
def temporalFns : List (Nat × String) := [
  (25, "date_part"), (26, "date_trunc"), (60, "date_diff"), (61, "strftime"), (62, "date_bin")]

/-- Lists and structs: new anchors 400–499. -/
def nestedFns : List (Nat × String) := [
  (24, "array_length")]

/-- Aggregate functions: new anchors 500–599. -/
def aggregateFns : List (Nat × String) := [
  (36, "count"), (37, "sum"), (38, "avg"), (39, "min"), (40, "max"), (42, "array_agg")]

/-- Window functions: new anchors 600–699. -/
def windowFns : List (Nat × String) := [
  (12, "row_number"), (13, "lag"), (14, "lead"),
  (70, "rank"), (71, "dense_rank"), (72, "percent_rank"), (73, "cume_dist"), (74, "ntile"),
  (75, "first_value"), (76, "last_value"), (77, "nth_value")]

/-- Each area's functions and the range its new anchors come from. -/
def areas : List (List (Nat × String) × Nat) :=
  [(coreFns, 100), (stringFns, 200), (temporalFns, 300), (nestedFns, 400),
   (aggregateFns, 500), (windowFns, 600)]

/-- Every declared `(anchor, Substrait name)`, area by area. -/
def declared : List (Nat × String) := areas.flatMap (·.1)

/-- `(anchor, Substrait name)` for every function the writer can emit, by anchor. -/
def functions : List (Nat × String) := declared.mergeSort fun a b => a.1 ≤ b.1

example : (declared.map (·.1)).Nodup := by decide
example : (declared.map (·.2)).Nodup := by decide
example : areas.all fun (fs, lo) => fs.all fun (a, _) => a < 100 || (lo ≤ a && a < lo + 100) := by
  decide

def AggFn.anchor : AggFn → Nat
  | .count => 36 | .sum | .fsum => 37 | .avg => 38 | .min => 39 | .max => 40 | .collect => 42

def UnFn.anchor : UnFn → Nat
  -- Core
  | .not => 1 | .isNull => 2 | .neg | .fneg => 3 | .ffloor => 15 | .fceil => 16
  | .fround | .froundTo _ => 17
  -- Strings
  | .upper => 20 | .lower => 21 | .length => 22
  -- Dates and times
  | .datePart _ | .dayPart _ => 25 | .dateTrunc _ | .dayTrunc _ => 26 | .addMonths _ _ => 4
  | .strftime _ => 61 | .bucket _ _ => 62
  -- Casts are written as casts, not calls; `regexp_match` as two calls.
  | .itof | .ftoi | .narrow _ | .itos | .toDate | .regexMatch _ | .timeOfDay | .asTime => 0
  -- Not a function: the arithmetic inside is written at its width.
  | .wrap _ => 0

def BinFn.anchor : BinFn → Nat
  -- Core
  | .add | .fadd => 4 | .sub | .fsub => 5 | .mul | .fmul => 6 | .eq => 7 | .lt => 8
  | .and => 9 | .or => 10 | .fdiv | .idiv => 11 | .imod => 18 | .ipow | .fpow => 19
  -- Strings
  | .concat => 27 | .strpos => 28 | .startsWith => 29 | .endsWith => 30 | .like => 31
  | .substr _ => 32 | .trim true true => 33 | .trim true false => 34 | .trim false _ => 35
  -- Dates and times
  | .dateAdd => 4 | .dateDiff => 60

/-- Every anchor a function is written with is declared (0 marks no call). -/
theorem AggFn.anchor_declared (f : AggFn) : AggFn.anchor f ∈ declared.map (·.1) := by
  cases f <;> decide

theorem UnFn.anchor_declared (f : UnFn) :
    UnFn.anchor f = 0 ∨ UnFn.anchor f ∈ declared.map (·.1) := by
  cases f <;> exact of_decide_eq_true rfl

theorem BinFn.anchor_declared (f : BinFn) : BinFn.anchor f ∈ declared.map (·.1) := by
  cases f <;> first | exact of_decide_eq_true rfl | (rename_i a b; cases a <;> cases b <;> decide)

def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

def writeValue : Value → Json
  | .null => obj [("null", obj [("i64", obj [])])]
  | .bool b => obj [("boolean", toJson b)]
  | .int i => obj [("i64", toJson (toString i))]
  | .str s => obj [("string", toJson s)]
  | .list [] => obj [("emptyList", obj [("type", obj [("i64", obj [])])])]
  | .list vs => obj [("list", obj [("values", Json.arr (vs.attach.map fun ⟨v, _⟩ => writeValue v).toArray)])]

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

/-- The (nullable) Substrait type of a kind, `i64` where it is unknown. -/
def kindType : Parse.Kind → Json
  | .float => fp64Type
  | .str => obj [("string", nullable)]
  | .bool => obj [("bool", nullable)]
  | .time => obj [("precisionTimestamp", obj [("precision", toJson 6),
      ("nullability", "NULLABILITY_NULLABLE")])]
  | .timeTz => obj [("precisionTimestampTz", obj [("precision", toJson 6),
      ("nullability", "NULLABILITY_NULLABLE")])]
  | .date => obj [("date", nullable)]
  | .tod => obj [("precisionTime", obj [("precision", toJson 6), ("nullability", "NULLABILITY_NULLABLE")])]
  | .list k => obj [("list", obj [("type", kindType k), ("nullability", "NULLABILITY_NULLABLE")])]
  | .int | .other => i64Type
where nullable := obj [("nullability", "NULLABILITY_NULLABLE")]

/-- The kind of a column or expression as the writer sees it: the parser's
`Kind`, and day/second intervals. The model has both timestamps and intervals
as microseconds, and `Expr.kind` calls `ts - ts` a time; the writer must tell
them apart to write a literal compared with, or added to, an interval as an
interval (#65). -/
inductive WKind where
  | int | float | time | date | interval | str | bool | tod | other
  | list (elem : WKind)
  deriving BEq

def WKind.ofKind : Parse.Kind → WKind
  | .int => .int | .float => .float | .time => .time | .date => .date
  | .str => .str | .bool => .bool | .tod => .tod | .other => .other | .list k => .list (ofKind k)
  -- Zoned timestamps are only compared with each other (`checkArgKinds`).
  | .timeTz => .other

/-- The model's view: an interval is a time (`Expr.kind`). -/
def WKind.toKind : WKind → Parse.Kind
  | .int => .int | .float => .float | .time | .interval => .time | .date => .date
  | .str => .str | .bool => .bool | .tod => .tod | .other => .other | .list k => .list (toKind k)

/-- An expression without field references. -/
def isConst : Expr → Bool
  | .lit _ => true
  | .field _ => false
  | .un _ a => isConst a
  | .bin _ a b => isConst a && isConst b
  | .ifThen c t e => isConst c && isConst t && isConst e

/-- `Expr.kind`, telling intervals from times: `ts - ts` and an interval
column `± x` are intervals, `ts ± x` is a time. -/
def wkind (cols : List WKind) : Expr → WKind
  | .field i => cols.getD i .other
  | .un .neg a => wkind cols a
  | .bin .add a b | .bin .sub a b | .bin .mul a b =>
      match wkind cols a, wkind cols b, a with
      | .time, .time, _ => .interval
      | .interval, .time, _ | .time, _, _ => .time
      | _, kb, .lit _ => kb
      | ka, _, _ => ka
  | .ifThen _ (.lit v) e => match e with
    | .lit _ => .ofKind (Parse.litKind v)
    | _ => wkind cols e
  | .ifThen _ t _ => wkind cols t
  | e => .ofKind (e.kind (cols.map WKind.toKind))

/-- How to write the operands of `a ± b`, in a context of kind `ctx`: a
constant operand takes its kind from the other operand, or, if both are
constant, from the context (`ts < TIMESTAMP '…' - INTERVAL '15 minutes'`). -/
def sumKinds (sub : Bool) (cols : List WKind) (ctx : WKind) (a b : Expr) : WKind × WKind :=
  let ka := wkind cols a
  let kb := wkind cols b
  match isConst a, isConst b with
  | false, false => (ka, kb)
  | false, true => (ka, if ka == .time then .interval else ka)
  | true, false => match kb with
    | .time => (if sub then .time else .interval, kb)
    | .interval => (if ctx == .time then .time else .interval, kb)
    | _ => (kb, kb)
  | true, true => match ctx with
    | .time => (.time, .interval)
    | .interval => (.interval, .interval)
    | _ => (kb, ka)

/-- A day/second interval of `us` microseconds. -/
def writeInterval (us : Int) : Json :=
  obj [("literal", obj [("intervalDayToSecond", obj [
    ("seconds", toJson (us / 1_000_000)), ("subseconds", toJson (toString (us % 1_000_000))),
    ("precision", toJson 6)])])]

/-- A literal (the body of `Expression.literal`) of kind `k`: an integer is
written as the kind of value it stands for. -/
def writeLitBody (k : WKind) (v : Value) : Json :=
  match k, v with
  | .float, .int c => obj [("fp64", writeDouble c)]
  | .time, .int us =>
    obj [("precisionTimestamp", obj [("precision", toJson 6), ("value", toJson (toString us))])]
  | .interval, .int us => (writeInterval us).getObjValD "literal"
  | .date, .int d => obj [("date", toJson d)]
  | .tod, .int us =>
    obj [("precisionTime", obj [("precision", toJson 6), ("value", toJson (toString us))])]
  | .tod, .null => obj [("null", obj [("precisionTime", obj [("precision", toJson 6)])])]
  -- A typed `NULL`, so that e.g. `CASE … THEN NULL ELSE name END` type-checks.
  | .float, .null => obj [("null", fp64Type)]
  | .str, .null => obj [("null", obj [("string", obj [])])]
  | .bool, .null => obj [("null", obj [("bool", obj [])])]
  | .time, .null => obj [("null", obj [("precisionTimestamp", obj [("precision", toJson 6)])])]
  | .date, .null => obj [("null", obj [("date", obj [])])]
  | .interval, .null => obj [("null", obj [("intervalDayToSecond", obj [("precision", toJson 6)])])]
  | .list _, .null => obj [("null", kindType k.toKind)]
  | .list e, .list [] => obj [("emptyList", obj [("type", kindType e.toKind)])]
  | .list e, .list vs =>
    obj [("list", obj [("values", Json.arr (vs.attach.map fun ⟨v, _⟩ => writeLitBody e v).toArray)])]
  | _, v => writeValue v

def writeLit (k : WKind) (v : Value) : Json := obj [("literal", writeLitBody k v)]

/-- An interval of `m` months. -/
def writeMonths (m : Int) : Json :=
  obj [("literal", obj [("intervalCompound", obj [
    ("intervalYearToMonth", obj [("months", toJson m)]),
    ("intervalDayToSecond", obj [("precision", toJson 6)])])])]

/-- A constant of a virtual table, as a literal of its column's type `ty`
(integers of the column's width). -/
def valuesLit (ty : Json) (v : Value) : Json :=
  let narrow := ["i8", "i16", "i32"].find? fun k => (ty.getObjVal? k).toOption.isSome
  match narrow, v with
  | some k, .int i => obj [("literal", obj [(k, toJson i)])]
  | _, _ => writeLit (.ofKind (Parse.typeKind ty)) v

/-- A double the model has one zero and one NaN for, as IEEE engines compute
it: `nanvl(x + 0.0, NaN)` makes `-0.0` zero and every NaN the positive one.
Engines that compare by `f64::total_cmp` (DataFusion) need it after an
operation that can give `-0.0` or a negative NaN; the parser reads
`nanvl(x, NaN)` back as `x`. -/
def canonical (x : Json) : Json :=
  let lit (s : Json) := obj [("literal", obj [("fp64", s)])]
  call 41 [call 4 [x, lit (Json.num 0)], lit "NaN"]

/-- `x`, written as `j`, or as an integer literal of `n` bits. -/
def narrowLit (n : Nat) (x : Expr) (j : Json) : Json :=
  match x with
  | .lit (.int i) =>
    obj [("literal", obj [(if n ≤ 8 then "i8" else if n ≤ 16 then "i16" else "i32", toJson i)])]
  | _ => j

def isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- Write `e` over input columns of kinds `cols`; `ctx` is the kind a literal
at the top should be written as. -/
def writeExpr (cols : List WKind) (ctx : WKind) : Expr → Json
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
  -- Arithmetic at `n` bits: its integer literals are written at that width,
  -- which is what makes the engine compute at it.
  | .un (.wrap n) (.bin f x y) =>
    call (BinFn.anchor f) [narrowLit n x (writeExpr cols .int x), narrowLit n y (writeExpr cols .int y)]
  | .un (.wrap n) (.un .neg x) => call 3 [narrowLit n x (writeExpr cols .int x)]
  | .un (.wrap _) a => writeExpr cols ctx a
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
  | .un (.datePart p) a =>
    let k := if wkind cols a == .tod then .tod else .time
    call 25 [obj [("literal", writeValue (.str p.name))], writeExpr cols k a]
  | .un .timeOfDay a => obj [("cast", obj [("type", obj [("precisionTime", obj [("precision", toJson 6),
      ("nullability", "NULLABILITY_NULLABLE")])]), ("input", writeExpr cols .time a)])]
  | .un .asTime a => obj [("cast", obj [("type", obj [("precisionTimestamp", obj [("precision", toJson 6),
      ("nullability", "NULLABILITY_NULLABLE")])]), ("input", writeExpr cols .int a)])]
  | .un (.strftime fmt) a => call 61 [writeExpr cols .time a, obj [("literal", writeValue (.str fmt))]]
  | .un (.bucket k o) a => call 62 [writeInterval k, writeExpr cols .time a, writeLit .time (.int o)]
  | .un (.dateTrunc u) a => call 26 [obj [("literal", writeValue (.str u.name))], writeExpr cols .time a]
  | .un (.dayPart p) a => call 25 [obj [("literal", writeValue (.str p.name))], writeExpr cols .date a]
  | .un (.dayTrunc u) a => call 26 [obj [("literal", writeValue (.str u.name))], writeExpr cols .date a]
  | .un (.addMonths m t) a => call 4 [writeExpr cols (if t then .time else .date) a, writeMonths m]
  -- The argument's kind from the function, for a bare `NULL` (#96).
  | .un .not a => call (UnFn.anchor .not) [writeExpr cols .bool a]
  | .un .upper a => call (UnFn.anchor .upper) [writeExpr cols .str a]
  | .un .lower a => call (UnFn.anchor .lower) [writeExpr cols .str a]
  | .un .length a => call (UnFn.anchor .length) [writeExpr cols .str a]
  | .un f a => call (UnFn.anchor f) [writeExpr cols (wkind cols a) a]
  | .bin f a b =>
    let ka := if isConst a then wkind cols b else wkind cols a
    let kb := if isConst b then wkind cols a else wkind cols b
    match f with
    -- A sum or difference of canonical doubles is `-0.0` never, NaN only
    -- as `inf - inf`, which IEEE engines may make negative.
    | .fadd | .fsub | .fmul | .fdiv | .fpow =>
      canonical (call (BinFn.anchor f) [writeExpr cols .float a, writeExpr cols .float b])
    | .add | .sub =>
      -- `timestamp ± constant`: the constant is an interval in microseconds.
      let (ka, kb) := sumKinds (f matches .sub) cols ctx a b
      call (BinFn.anchor f) [writeExpr cols ka a, writeExpr cols kb b]
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
def relKinds (schemas : Schemas) (cat : Catalog) : Rel → List WKind
  | .read t => (Parse.schemaKinds (schemas t (cat t).arity)).map .ofKind
  | .values n rows => (Parse.schemaKinds (schemas (Parse.valuesKey n rows) n)).map .ofKind
  | .filter r _ | .fetch r _ _ | .orderBy r _ | .distinct r | .semi r _ _ _ => relKinds schemas cat r
  | .project r es =>
      let ks := relKinds schemas cat r
      ks ++ es.map (wkind ks)
  | .emit r m =>
      let ks := relKinds schemas cat r
      m.map (ks.getD · .other)
  | .cross a b | .join a b _ _ => relKinds schemas cat a ++ relKinds schemas cat b
  | .unionAll a _ => relKinds schemas cat a
  | .window r _ _ fns =>
      let ks := relKinds schemas cat r
      ks ++ fns.map fun
        | .rowNumber | .rank _ | .denseRank _ | .ntile _ => .int
        | .percentRank _ | .cumeDist _ => .float
        | .lag c _ _ | .lead c _ _ | .firstValue c _ _ | .lastValue c _ _ | .nthValue c _ _ _ =>
          ks.getD c .other
        | .agg m _ _ => match m.fn with
          | .count | .sum => .int
          | .fsum | .avg => .float
          | .min | .max => wkind ks m.arg
          | .collect => .list (wkind ks m.arg)
  | .aggregate r gs ms =>
      let ks := relKinds schemas cat r
      gs.map (wkind ks) ++ ms.map fun m => match m.fn with
        | .count | .sum => .int
        | .fsum | .avg => .float
        | .min | .max => wkind ks m.arg
        | .collect => .list (wkind ks m.arg)
  | .unnest r c =>
      let ks := relKinds schemas cat r
      ks.set c (match ks.getD c .other with | .list k => k | _ => .other)

def writeSortKey (cols : List WKind) (k : SortKey) : Json :=
  let dir : Json := match k.desc, k.nullsFirst with
    | false, true => "SORT_DIRECTION_ASC_NULLS_FIRST"
    | false, false => "SORT_DIRECTION_ASC_NULLS_LAST"
    | true, true => "SORT_DIRECTION_DESC_NULLS_FIRST"
    | true, false => "SORT_DIRECTION_DESC_NULLS_LAST"
  obj [("expr", writeExpr cols .other (.field k.col)), ("direction", dir)]

def writeBound : FrameBound → Json
  | .unboundedPreceding | .unboundedFollowing => obj [("unbounded", obj [])]
  | .preceding 0 => obj [("currentRow", obj [])]
  | .preceding k => obj [("preceding", obj [("offset", toJson (toString k))])]
  | .following k => obj [("following", obj [("offset", toJson (toString k))])]

/-- A window function over input columns of kinds `cols`. -/
def writeWindow (cols : List WKind) (part : List Nat) (sort : List SortKey) (f : WinFn) : Json :=
  let col (i : Nat) := writeExpr cols .other (.field i)
  let (anchor, args, fr) : Nat × List Json × Frame := match f with
    | .rowNumber => (12, [], .all)
    | .lag c k d | .lead c k d =>
      let base := [col c, writeLit .int (.int k)]
      (if f matches .lag .. then 13 else 14,
        if d == Value.null then base else base ++ [writeLit (cols.getD c .other) d], .all)
    | .rank _ => (70, [], .all)
    | .denseRank _ => (71, [], .all)
    | .percentRank _ => (72, [], .all)
    | .cumeDist _ => (73, [], .all)
    | .ntile k => (74, [writeLit .int (.int k)], .all)
    | .agg m _ fr => (Write.AggFn.anchor m.fn, [writeExpr cols (wkind cols m.arg) m.arg], fr)
    | .firstValue c _ fr => (75, [col c], fr)
    | .lastValue c _ fr => (76, [col c], fr)
    | .nthValue c n _ fr => (77, [col c, writeLit .int (.int n)], fr)
  obj [("windowFunction", obj [
    ("functionReference", toJson anchor),
    ("partitions", Json.arr (part.map col).toArray),
    ("sorts", Json.arr (sort.map (writeSortKey cols)).toArray),
    ("arguments", Json.arr (args.map fun a => obj [("value", a)]).toArray),
    ("lowerBound", writeBound fr.lo), ("upperBound", writeBound fr.hi),
    ("boundsType", if fr.range then "BOUNDS_TYPE_RANGE" else "BOUNDS_TYPE_ROWS")])]

/-- An `AggregateRel` measure over input columns of kinds `cols`. -/
def writeMeasure (df : Bool) (cols : List WKind) (m : Measure) : Json :=
  let arg := writeExpr cols (wkind cols m.arg) m.arg
  let decimal := obj [("decimal", obj [("precision", toJson 38), ("scale", toJson 0),
    ("nullability", "NULLABILITY_NULLABLE")])]
  let arg := if df && m.fn matches .sum then obj [("cast", obj [("type", decimal), ("input", arg)])]
    else arg
  let measure := obj [
    ("functionReference", toJson (AggFn.anchor m.fn)),
    ("invocation", if m.distinct then "AGGREGATION_INVOCATION_DISTINCT" else "AGGREGATION_INVOCATION_ALL"),
    ("arguments", Json.arr #[obj [("value", arg)]]),
    ("sorts", Json.arr (m.sort.map (writeSortKey cols)).toArray)]
  obj ([("measure", measure)] ++
    (m.filter.map fun c => [("filter", writeExpr cols .bool c)]).getD [])

/-- The conjuncts of a condition. -/
def conjunctsOf : Expr → List Expr
  | .bin .and a b => conjunctsOf a ++ conjunctsOf b
  | e => [e]

/-- The conjunction of `cs`, if any. -/
def andAll : List Expr → Option Expr
  | [] => none
  | c :: cs => some ((andAll cs).elim c (.bin .and c ·))

/-- Does `e` read a field, and only fields `p` holds of? -/
def readsOnly (p : Nat → Bool) (e : Expr) : Bool :=
  let rec go : Expr → Bool × Bool  -- (reads a field, all fields satisfy p)
    | .lit _ => (false, true)
    | .field i => (true, p i)
    | .un _ a => go a
    | .bin _ a b => let (x, y) := go a; let (z, w) := go b; (x || z, y && w)
    | .ifThen c t e =>
      let (x, y) := go c; let (z, w) := go t; let (u, v) := go e; (x || z || u, y && w && v)
  let (reads, all) := go e
  reads && all

/-- Write a relation; `emit` is an output mapping to put on its `RelCommon`.

With `df`, write it for DataFusion to run (`--write-datafusion`), compensating
for where DataFusion's semantics differ from `Rel.eval` (#24): an integer
`SUM` wraps around in DataFusion, so it is summed as `DECIMAL(38,0)` and cast
back, which fails outside 64 bits instead. Such a plan does not parse back to
the same `Rel`. -/
def writeRel (schemas : Schemas) (cat : Catalog) (df : Bool := false)
    (hint : List WKind := []) : Rel → Option (List Nat) → Json
  | .emit r m, out =>
    -- `hint` is for the emitted columns; `r`'s column `c` is emitted at `m.idxOf c`.
    let h := (List.range (relKinds schemas cat r).length).map fun c =>
      ((m.idxOf? c).bind (hint[·]?)).getD .other
    writeRel schemas cat df h r (some (match out with
      | none => m
      | some o => o.map (m.getD · 0)))
  | .read t, out => withCommon "read" [
      ("baseSchema", schemas t (cat t).arity),
      ("namedTable", obj [("names", toJson (t.splitOn "."))])] out
  | .values n rows, out =>
    -- The parsed `baseSchema`, and literals of its types: DataFusion checks
    -- the rows against the schema.
    let s := schemas (Parse.valuesKey n rows) n
    let tys := (s.getObjVal? "struct" >>= (·.getObjValAs? (Array Json) "types")).toOption.getD #[]
    withCommon "read" [
      ("baseSchema", s),
      ("virtualTable", obj [("expressions", Json.arr (rows.map fun row =>
        obj [("fields", Json.arr (row.zipIdx.map fun (v, i) =>
          valuesLit (tys.getD i i64Type) v).toArray)]).toArray)])] out
  | .filter r c, out => withCommon "filter" [
      ("input", writeRel schemas cat df [] r none),
      ("condition", writeExpr (relKinds schemas cat r) .bool c)] out
  | .project r es, out => withCommon "project" [
      ("input", writeRel schemas cat df [] r none),
      ("expressions",
        let ks := relKinds schemas cat r
        Json.arr (es.zipIdx.map fun (e, i) =>
          let k := wkind ks e
          writeExpr ks (if k == .other then hint.getD (ks.length + i) .other else k) e).toArray)] out
  | .cross a b, out => withCommon "cross" [
      ("left", writeRel schemas cat df [] a none), ("right", writeRel schemas cat df [] b none)] out
  | .join a b ty on, out =>
    -- For DataFusion, whose consumer takes every `=` of a join condition for
    -- a key pair across the inputs (#98), conjuncts over one input become a
    -- filter on it: the right input's, and in an inner join the left
    -- input's. In a left join those decide the padding, so they stay, as
    -- `CASE WHEN c THEN TRUE ELSE FALSE END`: the same in a join condition
    -- (NULL and FALSE both do not match), and not an `=`.
    let n := a.arity cat
    let cs := conjunctsOf on
    let left := if df && ty matches .inner then cs.filter (readsOnly (· < n)) else []
    let right := if df then cs.filter (readsOnly (n ≤ ·)) else []
    let rest := (cs.filter fun c => !left.contains c && !right.contains c).map fun c =>
      if df && readsOnly (· < n) c then .ifThen c (.lit (.bool true)) (.lit (.bool false)) else c
    let ka := relKinds schemas cat a
    let kb := relKinds schemas cat b
    let side (r : Json) (ks : List WKind) (cs : List Expr) : Json := match andAll cs with
      | none => r
      | some c => withCommon "filter" [("input", r), ("condition", writeExpr ks .bool c)] none
    withCommon "join" [
      ("left", side (writeRel schemas cat df [] a none) ka left),
      ("right", side (writeRel schemas cat df [] b none) kb (right.map (·.mapFields (· - n)))),
      ("expression", writeExpr (ka ++ kb) .bool
        (if !df then on else (andAll rest).getD (.lit (.bool true)))),
      ("type", match ty with | .inner => "JOIN_TYPE_INNER" | .left => "JOIN_TYPE_LEFT")] out
  -- The current encoding, `offsetExpr`/`countExpr`: DataFusion's protobuf no
  -- longer has the deprecated `offset`/`count`.
  | .fetch r off cnt, out => withCommon "fetch" ([
      ("input", writeRel schemas cat df [] r none),
      ("offsetExpr", obj [("literal", writeValue (.int off))])] ++
      (cnt.map fun c => [("countExpr", obj [("literal", writeValue (.int c))])]).getD []) out
  -- A branch's bare `NULL`s take the other branch's column kinds: a FULL
  -- JOIN's padding (#96).
  | .unionAll a b, out => withCommon "set" [
      ("inputs", Json.arr #[writeRel schemas cat df (relKinds schemas cat b) a none,
        writeRel schemas cat df (relKinds schemas cat a) b none]),
      ("op", "SET_OP_UNION_ALL")] out
  | .semi a b anti on, out => withCommon "join" [
      ("left", writeRel schemas cat df [] a none), ("right", writeRel schemas cat df [] b none),
      ("expression", writeExpr (relKinds schemas cat a ++ relKinds schemas cat b) .bool on),
      ("type", if anti then "JOIN_TYPE_LEFT_ANTI" else "JOIN_TYPE_LEFT_SEMI")] out
  | .orderBy r keys, out => withCommon "sort" [
      ("input", writeRel schemas cat df [] r none),
      ("sorts", Json.arr (keys.map (writeSortKey (relKinds schemas cat r))).toArray)] out
  -- Grouping by every column, with no measures.
  | .distinct r, out =>
      let ks := relKinds schemas cat r
      withCommon "aggregate" [
        ("input", writeRel schemas cat df [] r none),
        ("groupingExpressions", Json.arr ((List.range ks.length).map fun i =>
          writeExpr ks .other (.field i)).toArray),
        ("groupings", Json.arr #[obj [("expressionReferences",
          Json.arr ((List.range ks.length).map toJson).toArray)]])] out
  | .aggregate r gs ms, out =>
      let ks := relKinds schemas cat r
      let agg := withCommon "aggregate" [
        ("input", writeRel schemas cat df [] r none),
        ("groupingExpressions", Json.arr (gs.map fun g => writeExpr ks (wkind ks g) g).toArray),
        ("groupings", if gs.isEmpty then Json.arr #[] else
          Json.arr #[obj [("expressionReferences", toJson (List.range gs.length))]]),
        ("measures", Json.arr (ms.map (writeMeasure df ks)).toArray)]
      -- The DECIMAL sums (`writeMeasure`), cast back to `i64` by a project.
      let sums := (ms.zipIdx.filter fun (m, _) => df && m.fn matches .sum).map (gs.length + ·.2)
      if sums.isEmpty then agg out else
        let n := gs.length + ms.length
        let back := sums.map fun i => obj [("cast", obj [("type", i64Type),
          ("input", writeExpr [] .other (.field i)),
          ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]
        let cols := (List.range n).map fun j => match sums.idxOf? j with
          | some k => n + k
          | none => j
        withCommon "project" [("input", agg none), ("expressions", Json.arr back.toArray)]
          (some (match out with
            | none => cols
            | some o => o.map (cols.getD · 0)))
  | .unnest r c, out => withCommon "extensionSingle" [
      ("input", writeRel schemas cat df [] r none),
      ("detail", obj [("@type", "type.googleapis.com/sverify.Unnest"), ("column", toJson c)])] out
  | .window r part sort fns, out => withCommon "project" [
      ("input", writeRel schemas cat df [] r none),
      ("expressions",
        let ks := relKinds schemas cat r
        Json.arr (fns.map (writeWindow ks part sort)).toArray)] out

def writePlan (schemas : Schemas) (cat : Catalog) (root : Rel) (names : List String)
    (df : Bool := false) : Json :=
  obj [
    ("extensions", Json.arr (functions.map fun (a, n) => obj [("extensionFunction", obj [
      ("functionAnchor", toJson a), ("name", toJson n)])]).toArray),
    ("relations", Json.arr #[obj [("root", obj [
      ("input", writeRel schemas cat df [] root none), ("names", toJson names)])]])]

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
