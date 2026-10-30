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

/-- `(anchor, Substrait name)` for every function the writer can emit. -/
def functions : List (Nat × String) :=
  [(1, "not:bool"), (2, "is_null:any"), (3, "negate:i64"), (4, "add:i64_i64"),
   (5, "subtract:i64_i64"), (6, "multiply:i64_i64"), (7, "equal:any_any"),
   (8, "lt:any_any"), (9, "and:bool"), (10, "or:bool")]

def UnFn.anchor : UnFn → Nat
  | .not => 1 | .isNull => 2 | .neg => 3

def BinFn.anchor : BinFn → Nat
  | .add => 4 | .sub => 5 | .mul => 6 | .eq => 7 | .lt => 8 | .and => 9 | .or => 10

def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

def writeValue : Value → Json
  | .null => obj [("null", obj [("i64", obj [])])]
  | .bool b => obj [("boolean", toJson b)]
  | .int i => obj [("i64", toJson (toString i))]
  | .str s => obj [("string", toJson s)]

def call (anchor : Nat) (args : List Json) : Json :=
  obj [("scalarFunction", obj [
    ("functionReference", toJson anchor),
    ("arguments", Json.arr (args.map fun a => obj [("value", a)]).toArray)])]

def writeExpr : Expr → Json
  | .lit v => obj [("literal", writeValue v)]
  | .field i => obj [("selection", obj [
      ("directReference", obj [("structField", obj [("field", toJson i)])]),
      ("rootReference", obj [])])]
  | .un f a => call (UnFn.anchor f) [writeExpr a]
  | .bin f a b => call (BinFn.anchor f) [writeExpr a, writeExpr b]
  | .ifThen c t e => obj [("ifThen", obj [
      ("ifs", Json.arr #[obj [("if", writeExpr c), ("then", writeExpr t)]]),
      ("else", writeExpr e)])]

/-- `baseSchema` of each table: the parsed one, or a placeholder of `i64`
columns for tables the parser never saw. -/
abbrev Schemas := String → Nat → Json

def i64Type : Json := obj [("i64", obj [("nullability", "NULLABILITY_NULLABLE")])]

def placeholderSchema (n : Nat) : Json :=
  obj [("names", Json.arr ((List.range n).map fun i => toJson s!"c{i}").toArray),
       ("struct", obj [("types", Json.arr (List.replicate n i64Type).toArray),
                       ("nullability", "NULLABILITY_REQUIRED")])]

/-- Attach an output mapping. Only `ProjectRel` carries it (DuckDB ignores
`emit` elsewhere), so other relations get wrapped in a project with no
expressions, which the parser reads back as the identity. -/
def withCommon (kind : String) (body : List (String × Json)) (emit : Option (List Nat)) : Json :=
  let common (m : List Nat) := ("common", obj [("emit", obj [("outputMapping", toJson m)])])
  match emit with
  | none => obj [(kind, obj body)]
  | some m =>
    if kind == "project" then obj [(kind, obj (common m :: body))]
    else obj [("project", obj [common m, ("input", obj [(kind, obj body)]),
      ("expressions", Json.arr #[])])]

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
      ("input", writeRel schemas cat r none), ("condition", writeExpr c)] out
  | .project r es, out => withCommon "project" [
      ("input", writeRel schemas cat r none),
      ("expressions", Json.arr (es.map writeExpr).toArray)] out
  | .cross a b, out => withCommon "cross" [
      ("left", writeRel schemas cat a none), ("right", writeRel schemas cat b none)] out
  | .join a b ty on, out => withCommon "join" [
      ("left", writeRel schemas cat a none), ("right", writeRel schemas cat b none),
      ("expression", writeExpr on),
      ("type", match ty with | .inner => "JOIN_TYPE_INNER" | .left => "JOIN_TYPE_LEFT")] out
  | .fetch r off cnt, out => withCommon "fetch" ([
      ("input", writeRel schemas cat r none), ("offset", toJson (toString off))] ++
      (cnt.map fun c => [("count", toJson (toString c))]).getD []) out
  | .unionAll a b, out => withCommon "set" [
      ("inputs", Json.arr #[writeRel schemas cat a none, writeRel schemas cat b none]),
      ("op", "SET_OP_UNION_ALL")] out

def writePlan (schemas : Schemas) (cat : Catalog) (root : Rel) (names : List String) : Json :=
  obj [
    ("extensionUris", Json.arr #[obj [("extensionUriAnchor", toJson 1),
      ("uri", "https://github.com/substrait-io/substrait/blob/main/extensions/")]]),
    ("extensions", Json.arr (functions.map fun (a, n) => obj [("extensionFunction", obj [
      ("extensionUriReference", toJson 1), ("functionAnchor", toJson a), ("name", toJson n)])]).toArray),
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
each one after the weight-column encoding and concatenates the results. -/
def deltaTerms (p : Parse.Plan) : List Rel :=
  (p.root.delta deltaName).terms

def writeDeltaTerm (p : Parse.Plan) (term : Rel) : Json :=
  let schemas : Schemas := fun t n =>
    if isDeltaName t then deltaSchema (planSchemas p (t.dropEnd 6).toString (n - 1))
    else planSchemas p t n
  -- The engine's tables: change tables have one more (weight) column.
  let engineCat : Catalog := fun t =>
    let c := deltaCatalog p t
    if isDeltaName t then ⟨c.arity + 1, []⟩ else c
  writePlan schemas engineCat (term.weighted (deltaCatalog p) isDeltaName) (p.names ++ ["__weight"])

end Substrait.Write
