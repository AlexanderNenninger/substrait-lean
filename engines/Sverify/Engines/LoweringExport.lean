import Sverify.Engines.LoweringSearch

/-!
# A generated lowering, exported (#241, #271)

`substrait-check --lowering-table` prints each engine's entries that are not
native as JSON (and the core's `FLOOR` templates under `"floor"`), for the
table interpreters that write each construct as its template says instead of
by hand: DuckDB's SQL printer (`sverify.sql.lowering`, #241), and Polars's
(#271). Shared by every engine's table.
-/

namespace Substrait


namespace LoweringExport

open Lean (Json)

/-- A function's name in the export: the model's, with its parameters. -/
def unName : UnFn → String
  | .isNum _ => "isNum" | .isNull => "isNull" | .not => "not" | .ffloor => "ffloor"
  | .raise _ => "raise" | .fmath f => s!"fmath:{f.name}"
  | .fit m w => s!"fit:{m.name}:{w.bits}"
  -- One name for every digit count: the translations write it themselves.
  | .froundTo _ => "Substrait.UnFn.froundTo"
  | f => reprStr f

def binName : BinFn → String
  | .eq => "eq" | .lt => "lt" | .and => "and" | .or => "or" | .add => "add" | .sub => "sub"
  | .dadd => "dadd" | .dsub => "dsub" | .dmul => "dmul" | .dmod => "dmod" | .imod => "imod"
  | .idiv => "idiv"
  | .fadd => "fadd" | .fsub => "fsub" | .fmul => "fmul" | .fdiv => "fdiv" | .fmod => "fmod"
  | .fdivIeee => "fdivIeee" | .fpow => "fpow" | .fatan2 => "fatan2" | .bit op => s!"bit:{op.name}"
  | f => reprStr f

/-- A literal: a double by its code (`core/Sverify/Core/Float.lean`), a date by
its days since 1970-01-01. -/
def litJson : Value → Json
  | .null => Json.mkObj [("null", true)]
  | .bool b => Json.mkObj [("bool", b)]
  | .int i => Json.mkObj [("int", toString i)]
  | .float c => Json.mkObj [("code", toString c)]
  | .date d => Json.mkObj [("date", toString d)]
  | v => Json.mkObj [("unsupported", reprStr v)]

/-- A template as JSON: fields, literals, calls and `CASE`s. -/
def exprJson : Expr → Json
  | .field i => Json.mkObj [("field", i)]
  | .lit v => litJson v
  | .un f a => Json.mkObj ([("fn", Json.str (unName f)), ("args", Json.arr #[exprJson a])] ++
      match f with | .raise m => [("message", Json.str m)] | _ => [])
  | .bin f a b => Json.mkObj [("fn", Json.str (binName f)),
      ("args", Json.arr #[exprJson a, exprJson b])]
  | .ifThen c t e => Json.mkObj [("if", exprJson c), ("then", exprJson t),
      ("else", exprJson e)]
  | .hof .. => Json.mkObj [("unsupported", "a higher-order function")]

/-- The `FLOOR` templates of the core (`Expr.floorDivOf`, `Expr.floorModOf`,
`Expr.floorFmodOf`), with the arguments as fields 0 and 1: the SQL writer's
`division_type: FLOOR` renders these (#1202). -/
def floorJson : Json :=
  Json.mkObj [("div", exprJson (Expr.floorDivOf (.field 0) (.field 1))),
    ("mod", exprJson (Expr.floorModOf (.field 0) (.field 1))),
    ("fmod", exprJson (Expr.floorFmodOf (.field 0) (.field 1)))]

/-- The constructs a table's export looks at: every function with finite
parameters, from the types themselves (`finite_values%`). A function with an
infinite parameter (a message, a decimal scale) is left out: native, refused, or
hand-built (Polars's decimal rescale, `Polars.droundEntry`), and the
translations write it themselves. -/
def unFns : List UnFn := finite_values% UnFn
def binFns : List BinFn := finite_values% BinFn

variable [Boxes.Ambient]
/-- The entries of a table that are not the native call. -/
def tableJson {p : Profile} (L : Lowering p) : Json :=
  let un := unFns.filterMap fun f => (L.un f).bind fun e =>
    let native := Expr.un f (.field 0)
    if e.tmpl == native then none
    else some (Json.mkObj [("fn", Json.str (unName f)), ("arity", (1 : Nat)),
      ("template", exprJson e.tmpl)])
  let bin := binFns.filterMap fun f => (L.bin f).bind fun e =>
    let native := Expr.bin f (.field 0) (.field 1)
    if e.tmpl == native then none
    else some (Json.mkObj [("fn", Json.str (binName f)), ("arity", (2 : Nat)),
      ("template", exprJson e.tmpl)])
  Json.arr (un ++ bin).toArray

end LoweringExport

end Substrait
