import Lean.Data.Json
import Sverify.Frontend.Parse

/-!
# Substrait JSON, built (#1189)

Builders of Substrait's protobuf-JSON encoding: field references, types,
casts, literals, `NULL`s, `CASE`, calls and measures by anchor, the functions
the generated templates call with their anchors and extension URNs, and the
options a call may set with the preferences the parser accepts
(`Parse.optionAccepts`). Engine-free: the lift generator
(`engines/duckdb/Sverify/DuckDB/LiftSearch.lean`) builds its candidates with
them, and a SQL front door (#1362) may reuse them.
-/

namespace Substrait.SubstraitJson

open Lean

def fieldJ (i : Nat) : Json :=
  Json.mkObj [("selection", Json.mkObj [
    ("directReference", Json.mkObj [("structField", Json.mkObj [("field", toJson i)])]),
    ("rootReference", Json.mkObj [])])]

def typeJ (t : String) : Json := Json.mkObj [(t, Json.mkObj [("nullability", "NULLABILITY_NULLABLE")])]

def castJ (t : String) (e : Json) : Json :=
  Json.mkObj [("cast", Json.mkObj [("type", typeJ t), ("input", e),
    ("failureBehavior", "FAILURE_BEHAVIOR_THROW_EXCEPTION")])]

def litJ (t : String) (v : Json) : Json := Json.mkObj [("literal", Json.mkObj [(t, v)])]

def nullJ (t : String) : Json := Json.mkObj [("literal", Json.mkObj [("null", typeJ t)])]

/-- The extension URN of a Substrait function. -/
def urnOf (name : String) : String :=
  if name == "sverify_fmod" then "extension:io.sverify:functions"
  else if ["equal", "lt", "is_null", "is_not_null", "is_nan", "greatest", "least",
      "greatest_skip_null", "least_skip_null"].contains name then
    "extension:io.substrait:functions_comparison"
  else if ["and", "or", "not"].contains name then "extension:io.substrait:functions_boolean"
  else if ["sin", "cos", "tan", "asin", "acos", "atan"].contains name then
    "extension:io.substrait:functions_arithmetic"
  else if ["floor", "ceil", "round"].contains name then "extension:io.substrait:functions_rounding"
  else if name == "count" then "extension:io.substrait:functions_aggregate_generic"
  else "extension:io.substrait:functions_arithmetic"

/-- Functions of two arguments of one type that candidates call. -/
def binaryNames : List String :=
  ["divide", "modulus", "sverify_fmod", "power", "greatest_skip_null", "least_skip_null",
   "greatest", "least"]

/-- The functions candidates call, with their anchors, signatures and
extension URNs: each of `binaryNames` on `i64` and on `fp64`, the logarithms,
and the guards' comparisons and connectives. -/
def functions : List (Nat × String × String) :=
  let typed := binaryNames.flatMap fun n => ["i64", "fp64"].map fun t => s!"{n}:{t}_{t}"
  let unary := (FMath.all.map (·.name) ++ ["floor"]).map (· ++ ":fp64")
  let guards := ["equal:any_any", "lt:any_any", "is_null:any", "is_not_null:any", "is_nan:fp64",
    "and:bool", "or:bool", "not:bool"]
  let aggs := ["avg:i64", "avg:fp64", "sum:i64", "sum:fp64", "count:any"]
  -- Last, so the anchors before them stay: only seeded templates call them.
  let arith := ["add:fp64_fp64", "subtract:fp64_fp64", "multiply:fp64_fp64"]
  (typed ++ unary ++ guards ++ aggs ++ arith).zipIdx.map fun (n, i) => (i + 1, n, urnOf (Parse.baseName n))

def fns : List (Nat × String) := functions.map fun (a, n, _) => (a, n)

def anchorOf (full : String) : Option Nat :=
  (functions.find? fun (_, n, _) => n == full).map (·.1)

/-- A call of `full` (`name:signature`); `none` if it is not in `functions`. -/
def callJ? (full : String) (args : List Json) (opts : List (String × String)) (out : String) :
    Option Json := do
  let a ← anchorOf full
  return Json.mkObj [("scalarFunction", Json.mkObj [
    ("functionReference", toJson a),
    ("outputType", typeJ out),
    ("arguments", Json.arr (args.map fun a => Json.mkObj [("value", a)]).toArray),
    ("options", Json.arr (opts.map fun (o, p) =>
      Json.mkObj [("name", toJson o), ("preference", Json.arr #[toJson p])]).toArray)])]

/-- A guard's call (its function is always in `functions`). -/
def callJ (full : String) (args : List Json) : Json :=
  (callJ? full args [] "boolean").getD .null

/-- A template with each call naming its function (`"function"`), for the
cache (`LiftHint`); `anchored` turns it back. -/
partial def named : Json → Json
  | .obj kvs => Json.mkObj (kvs.toArray.toList.map fun (k, v) =>
      if k == "functionReference" then
        let name := (v.getNat?.toOption).bind fun a => fns.lookup a
        ("function", match name with | some n => toJson n | none => v)
      else (k, named v))
  | .arr vs => .arr (vs.map named)
  | j => j

partial def anchored : Json → Option Json
  | .obj kvs => do
    let kvs ← kvs.toArray.toList.mapM fun (k, v) => do
      if k == "function" then return ("functionReference", toJson (← anchorOf (← v.getStr?.toOption)))
      else return (k, ← anchored v)
    return Json.mkObj kvs
  | .arr vs => do return .arr (← vs.mapM anchored)
  | j => some j

def ifJ (c t e : Json) : Json :=
  Json.mkObj [("ifThen", Json.mkObj [
    ("ifs", Json.arr #[Json.mkObj [("if", c), ("then", t)]]), ("else", e)])]

/-- The options a call may set, each with the preferences the parser accepts. -/
def optionChoices (name : String) (float : Bool) : List (List (String × String)) :=
  ["overflow", "on_division_by_zero", "on_domain_error", "on_log_zero", "rounding",
   "division_type"].foldl (fun acc o =>
    match Parse.optionAccepts name float o with
    | some (some ps) => acc.flatMap fun a => a :: ps.map fun p => a ++ [(o, p)]
    | _ => acc) [[]]

/-- The functions a template's `functionReference`s point to, as JSON. -/
def functionsJson : Json :=
  Json.arr (functions.map fun (a, n, u) =>
    Json.mkObj [("anchor", toJson a), ("name", toJson n), ("urn", toJson u)]).toArray

def measureJ? (full : String) (arg : Json) (out : String) : Option Json := do
  let a ← anchorOf full
  return Json.mkObj [("measure", Json.mkObj [("functionReference", toJson a),
    ("outputType", typeJ out), ("arguments", Json.arr #[Json.mkObj [("value", arg)]]),
    ("phase", "AGGREGATION_PHASE_INITIAL_TO_RESULT"),
    ("invocation", "AGGREGATION_INVOCATION_ALL")])]

end Substrait.SubstraitJson
