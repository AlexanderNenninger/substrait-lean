import Lean.Data.Json
import SubstraitLean.Rel

/-!
# Parsing Substrait JSON plans

Reads the protobuf-JSON encoding of a Substrait `Plan` (as produced by e.g.
DuckDB's `get_substrait_json`, Isthmus or `substrait-python`) into `Rel`.

The parser is **unverified, trusted code**: theorems about `Rel` say nothing
about whether this file translates a plan faithfully. Anything outside the
modelled fragment is rejected with an error rather than approximated.

Protobuf-JSON details that matter here:
* fields at their default value are omitted (e.g. `"field": 0` disappears);
* 64-bit integers are encoded as strings (`"i64": "42"`).
-/

namespace Substrait.Parse

open Lean (Json)

abbrev J := Except String

/-- Named tables seen while parsing: arity and the original `baseSchema`
JSON (kept so plans can be written back out). -/
abbrev Tables := List (String × Nat × Json)

abbrev P := StateT Tables J

/-- Present, non-null field. -/
def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def field (j : Json) (k : String) : J Json :=
  match field? j k with
  | some v => pure v
  | none => throw s!"missing field '{k}' in {j.compress}"

def arrD (j : Json) (k : String) : J (List Json) :=
  match field? j k with
  | some v => return (← v.getArr?).toList
  | none => pure []

def getInt (j : Json) : J Int :=
  match j with
  | .str s => match s.toInt? with
    | some i => pure i
    | none => throw s!"expected integer, got \"{s}\""
  | _ => j.getInt?

def getNat (j : Json) : J Nat := do
  let i ← getInt j
  if i < 0 then throw s!"expected non-negative integer, got {i}" else pure i.toNat

/-- Integer field that proto3 may omit when it is zero. -/
def natD (j : Json) (k : String) : J Nat :=
  (field? j k).elim (pure 0) getNat

/-- The member that is set in a protobuf `oneof`. -/
def oneof (what : String) (j : Json) (keys : List String) : J (String × Json) :=
  match keys.findSome? fun k => (field? j k).map (k, ·) with
  | some r => pure r
  | none =>
    let shown := j.compress
    let shown := if shown.length > 80 then (shown.take 80).toString ++ "…" else shown
    throw s!"unsupported {what}: {shown}"

/-- Function anchors declared in `extensions`, mapped to their base name
(`"lt:i64_i64"` ↦ `"lt"`). -/
def parseExtensions (plan : Json) : J (List (Nat × String)) := do
  let exts ← arrD plan "extensions"
  exts.filterMapM fun e => do
    match field? e "extensionFunction" with
    | none => pure none
    | some f =>
      let name ← (← field f "name").getStr?
      pure (some (← natD f "functionAnchor", (name.splitOn ":").head!))

def parseLiteral (j : Json) : J Value := do
  match ← oneof "literal" j ["boolean", "i8", "i16", "i32", "i64", "string", "null"] with
  | ("boolean", b) => return .bool (← b.getBool?)
  | ("string", s) => return .str (← s.getStr?)
  | ("null", _) => return .null
  | (_, n) => return .int (← getInt n)

/-- Maps Substrait standard-extension functions onto the modelled ones.
Comparisons are derived: `a > b := b < a`, `a ≤ b := ¬(b < a)`; under
null-propagation these agree with the direct definitions. -/
def mkCall : String → List Expr → J Expr
  | "not", [a] => pure (.un .not a)
  | "is_null", [a] => pure (.un .isNull a)
  | "is_not_null", [a] => pure (.un .not (.un .isNull a))
  | "negate", [a] => pure (.un .neg a)
  -- DuckDB writes unary minus as a one-argument `subtract`.
  | "subtract", [a] => pure (.un .neg a)
  | "add", [a, b] => pure (.bin .add a b)
  | "subtract", [a, b] => pure (.bin .sub a b)
  | "multiply", [a, b] => pure (.bin .mul a b)
  | "equal", [a, b] => pure (.bin .eq a b)
  | "not_equal", [a, b] => pure (.un .not (.bin .eq a b))
  | "lt", [a, b] => pure (.bin .lt a b)
  | "gt", [a, b] => pure (.bin .lt b a)
  | "lte", [a, b] => pure (.un .not (.bin .lt b a))
  | "gte", [a, b] => pure (.un .not (.bin .lt a b))
  -- `and` / `or` are variadic in Substrait.
  | "and", a :: as => pure (as.foldl (.bin .and) a)
  | "or", a :: as => pure (as.foldl (.bin .or) a)
  | name, args => throw s!"unsupported function {name}/{args.length}"

partial def parseExpr (fns : List (Nat × String)) (j : Json) : J Expr := do
  match ← oneof "expression" j ["literal", "selection", "scalarFunction", "ifThen", "cast"] with
  | ("literal", l) => return .lit (← parseLiteral l)
  | ("selection", s) =>
    if (field? s "outerReference").isSome then
      throw "outer references are not supported"
    let sf ← field (← field s "directReference") "structField"
    if (field? sf "child").isSome then
      throw "nested field references are not supported"
    return .field (← natD sf "field")
  | ("scalarFunction", f) =>
    let anchor ← natD f "functionReference"
    let some name := fns.lookup anchor
      | throw s!"function reference {anchor} is not declared in extensions"
    let args ← (← arrD f "arguments").mapM fun a => do parseExpr fns (← field a "value")
    mkCall name args
  | ("ifThen", t) =>
    let els ← parseExpr fns (← field t "else")
    (← arrD t "ifs").foldrM (init := els) fun clause acc => do
      return .ifThen (← parseExpr fns (← field clause "if"))
        (← parseExpr fns (← field clause "then")) acc
  | ("cast", c) =>
    -- Only integer literals cast to an integer type that can hold them
    -- (DuckDB emits `CAST(10 AS BIGINT)` for literals). Values are unbounded
    -- `Int`s, so such a cast is the identity.
    let (target, _) ← oneof "cast type" (← field c "type") ["i8", "i16", "i32", "i64"]
    let bits : Nat := match target with
      | "i8" => 8 | "i16" => 16 | "i32" => 32 | _ => 64
    match ← parseExpr fns (← field c "input") with
    | .lit (.int i) =>
      if -(2 ^ (bits - 1) : Int) ≤ i ∧ i < 2 ^ (bits - 1) then return .lit (.int i)
      else throw s!"cast of {i} to {target} overflows"
    | .lit .null => return .lit .null
    | _ => throw "only casts of integer literals are supported"
  | (k, _) => throw s!"unsupported expression: {k}"

def schemaArity (read : Json) : J Nat := do
  let schema ← field read "baseSchema"
  match field? schema "struct" with
  | some s => return (← arrD s "types").length
  | none => return (← arrD schema "names").length

/-- `ReadRel.projection` is a mask selecting top-level fields, in order. -/
def parseMask (mask : Json) : J (List Nat) := do
  let items ← arrD (← field mask "select") "structItems"
  items.mapM fun item => do
    if (field? item "child").isSome then
      throw "nested projection masks are not supported"
    natD item "field"

def parseRead (fns : List (Nat × String)) (r : Json) : P Rel := do
  let arity ← schemaArity r
  let base ← match ← oneof "read type" r ["namedTable", "virtualTable"] with
    | ("namedTable", t) =>
      let names ← (← arrD t "names").mapM (·.getStr?)
      let name := ".".intercalate names
      modify ((name, arity, ← field r "baseSchema") :: ·)
      pure (Rel.read name)
    | (_, v) =>
      -- Current encoding: `expressions`; deprecated encoding: `values` of literals.
      let rows ← match field? v "expressions" with
        | some _ => (← arrD v "expressions").mapM fun row => do
            (← arrD row "fields").mapM fun e => do pure ((← parseExpr fns e).eval [])
        | none => (← arrD v "values").mapM fun row => do
            (← arrD row "fields").mapM fun e => return (← parseLiteral e)
      pure (Rel.values arity rows)
  -- `ReadRel.filter` must be applied exactly (`bestEffortFilter` may be
  -- ignored). It refers to the base schema, so it comes before the mask.
  let filtered ← match field? r "filter" with
    | some c => pure (Rel.filter base (← parseExpr fns c))
    | none => pure base
  match field? r "projection" with
  | some m => return .emit filtered (← parseMask m)
  | none => return filtered

partial def parseRel (fns : List (Nat × String)) (j : Json) : P Rel := do
  let (kind, r) ← oneof "relation" j ["read", "filter", "project", "cross", "join", "fetch", "set"]
  let input := fun (k : String) => do parseRel fns (← field r k)
  let core ← match kind with
    | "read" => parseRead fns r
    | "filter" => pure (.filter (← input "input") (← parseExpr fns (← field r "condition")))
    | "project" =>
      let es ← (← arrD r "expressions").mapM fun e => do return (← parseExpr fns e)
      -- A project that appends nothing is the identity (used to carry `emit`).
      if es.isEmpty then input "input" else pure (.project (← input "input") es)
    | "cross" => pure (.cross (← input "left") (← input "right"))
    | "join" =>
      let ty ← match field? r "type" with
        | some (.str "JOIN_TYPE_INNER") => pure JoinType.inner
        | some (.str "JOIN_TYPE_LEFT") => pure JoinType.left
        | t => throw s!"unsupported join type: {(t.map (·.compress)).getD "unspecified"}"
      if (field? r "postJoinFilter").isSome then
        throw "JoinRel.postJoinFilter is not supported"
      let on ← (field? r "expression").elim (pure (Expr.lit (.bool true)))
        fun e => do return (← parseExpr fns e)
      pure (.join (← input "left") (← input "right") ty on)
    | "fetch" =>
      if (field? r "offsetExpr").isSome || (field? r "countExpr").isSome then
        throw "expression offsets/counts in FetchRel are not supported"
      -- An absent count, or the legacy `-1`, means "all remaining rows".
      let count ← match field? r "count" with
        | none => pure none
        | some c => do
          let n ← getInt c
          pure (if n < 0 then none else some n.toNat)
      pure (.fetch (← input "input") (← natD r "offset") count)
    | _ =>
      match field? r "op" with
      | some (.str "SET_OP_UNION_ALL") =>
        match ← (← arrD r "inputs").mapM (parseRel fns) with
        | a :: as => pure (as.foldl .unionAll a)
        | [] => throw "SetRel without inputs"
      | op => throw s!"unsupported set operation: {(op.map (·.compress)).getD "unspecified"}"
  match (field? r "common").bind (field? · "emit") with
  | some e => return .emit core (← (← arrD e "outputMapping").mapM fun i => return (← getNat i))
  | none => return core

structure Plan where
  root : Rel
  /-- Output column names from `RelRoot.names`. -/
  names : List String
  /-- Arity of every named table, taken from the plan's `baseSchema`s. -/
  tables : Tables

/-- The schema-only catalog a plan describes: each named table has the arity
its `baseSchema` declares and no rows. -/
def Plan.catalog (p : Plan) : Catalog := fun t =>
  match p.tables.lookup t with
  | some (n, _) => ⟨n, []⟩
  | none => ⟨0, []⟩

theorem Plan.catalog_wf (p : Plan) : p.catalog.WF := by
  intro t row h
  simp only [catalog] at h
  split at h <;> simp at h

def parsePlan (s : String) : J Plan := do
  let j ← Json.parse s
  let fns ← parseExtensions j
  let some root := (← arrD j "relations").findSome? (field? · "root")
    | throw "plan has no root relation"
  let (rel, tables) ← (parseRel fns (← field root "input")).run []
  let names ← (← arrD root "names").mapM (·.getStr?)
  return { root := rel, names, tables }

end Substrait.Parse
