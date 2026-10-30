import Lean.Data.Json
import SubstraitLean.Rel

/-!
# Parsing Substrait JSON plans

Reads the protobuf-JSON encoding of a Substrait `Plan` (as produced by e.g.
DataFusion's Substrait producer) into `Rel`.

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
    | some f => pure (some (← natD f "functionAnchor", ← (← field f "name").getStr?))

/-- `"lt:i64_i64"` ↦ `"lt"` -/
def baseName (name : String) : String := (name.splitOn ":").head!

/-! ## Column kinds

Doubles, timestamps and dates all become integers in the model (see
`SubstraitLean/Float.lean`); the parser and the writer track which is which. -/

inductive Kind where
  | int | float | time | date | str | bool | other
  deriving Repr, BEq, DecidableEq

def typeKind (ty : Json) : Kind :=
  let has (k : String) := (ty.getObjVal? k).toOption.isSome
  if ["i8", "i16", "i32", "i64"].any has then .int
  else if ["fp32", "fp64"].any has then .float
  else if ["precisionTimestamp", "timestamp"].any has then .time
  else if has "date" then .date
  else if ["string", "varchar", "fixedChar"].any has then .str
  else if has "bool" then .bool
  else .other

def schemaKinds (schema : Json) : List Kind :=
  match (schema.getObjVal? "struct").toOption.bind (·.getObjValAs? (Array Json) "types" |>.toOption) with
  | some tys => tys.toList.map typeKind
  | none => []

def _root_.Substrait.Expr.kind (cols : List Kind) : Expr → Kind
  | .lit (.int _) => .int
  | .lit (.str _) => .str
  | .lit (.bool _) => .bool
  | .lit .null => .other
  | .field i => cols.getD i .other
  | .un .neg a => a.kind cols
  | .un .itof _ | .un .fneg _ => .float
  | .un _ _ => .bool
  | .bin .add a b | .bin .sub a b | .bin .mul a b =>
      match a with
      | .lit _ => b.kind cols
      | _ => a.kind cols
  | .bin .fadd _ _ | .bin .fsub _ _ | .bin .fmul _ _ | .bin .fdiv _ _ => .float
  | .bin _ _ _ => .bool
  | .ifThen _ t _ => t.kind cols

def _root_.Substrait.WinFn.kind (cols : List Kind) : WinFn → Kind
  | .rowNumber => .int
  | .lag c _ _ | .lead c _ _ => cols.getD c .other

def _root_.Substrait.Rel.kinds (tables : Tables) : Rel → List Kind
  | .read t => match tables.lookup t with
    | some (_, s) => schemaKinds s
    | none => []
  | .values n _ => List.replicate n .other
  | .filter r _ | .fetch r _ _ => r.kinds tables
  | .project r es =>
      let ks := r.kinds tables
      ks ++ es.map (·.kind ks)
  | .emit r m =>
      let ks := r.kinds tables
      m.map (ks.getD · .other)
  | .cross a b | .join a b _ _ => a.kinds tables ++ b.kinds tables
  | .unionAll a _ => a.kinds tables
  | .window r _ _ fns =>
      let ks := r.kinds tables
      ks ++ fns.map (WinFn.kind ks)

/-! ## Constants

Literals, and expressions built only from literals (`CAST('inf' AS DOUBLE)`,
`INTERVAL 60 SECOND` = `to_seconds(60.0)`), are folded into a single literal. -/

inductive Const where
  | int (i : Int)
  | flt (f : Float)
  /-- A double as its code; Lean's `Float` cannot hold a negative NaN. -/
  | code (c : Int)
  | dec (m : Int) (scale : Nat)
  | str (s : String)
  | bool (b : Bool)
  | null

def floatOfScientific (m : Int) (e : Nat) : Float :=
  let f := Float.ofScientific m.natAbs true e
  if m < 0 then -f else f

def Const.toFloat? : Const → Option Float
  | .int i => some (Float.ofInt i)
  | .flt f => some f
  | .code c => some (FloatCode.toFloat c)
  | .dec m s => some (floatOfScientific m s)
  | .str s =>
    match s.trimAscii.toString.toLower with
    | "inf" | "+inf" | "infinity" | "+infinity" => some (1.0 / 0.0)
    | "-inf" | "-infinity" => some (-1.0 / 0.0)
    | "nan" => some (0.0 / 0.0)
    | t => match Json.parse t with
      | .ok (.num n) => some (floatOfScientific n.mantissa n.exponent)
      | _ => none
  | _ => none

/-- Round half away from zero when casting a double to an integer. -/
def Const.toInt? : Const → Option Int
  | .int i => some i
  | .flt f => if f.isNaN || f.isInf then none else some f.round.toInt64.toInt
  | .dec m s =>
    let q := m.natAbs / 10 ^ s
    let r := m.natAbs % 10 ^ s
    let mag : Int := if 2 * r ≥ 10 ^ s then q + 1 else q
    some (if m < 0 then -mag else mag)
  | .str s => s.trimAscii.toString.toInt?
  | _ => none

def intBits (ty : Json) : Nat :=
  if (ty.getObjVal? "i8").toOption.isSome then 8
  else if (ty.getObjVal? "i16").toOption.isSome then 16
  else if (ty.getObjVal? "i32").toOption.isSome then 32
  else 64

def castConst (ty : Json) (c : Const) : J Const := do
  if let .null := c then return .null
  match typeKind ty with
  | .float =>
    let some f := c.toFloat? | throw "cannot cast this value to a double"
    return .flt f
  | .int =>
    let some i := c.toInt? | throw "cannot cast this value to an integer"
    let bits := intBits ty
    if -(2 ^ (bits - 1) : Int) ≤ i ∧ i < 2 ^ (bits - 1) then return .int i
    else throw s!"cast of {i} to a {bits}-bit integer overflows"
  | .time =>
    match c with
    | .str s => match Time.parseTimestamp? s.trimAscii.toString with
      | some us => return .int us
      | none => throw s!"cannot parse timestamp '{s}'"
    | .int us => return .int us
    | _ => throw "cannot cast this value to a timestamp"
  | .date =>
    match c with
    | .str s => match Time.parseDate? s.trimAscii.toString with
      | some d => return .int d
      | none => throw s!"cannot parse date '{s}'"
    | .int d => return .int d
    | _ => throw "cannot cast this value to a date"
  | .str =>
    match c with
    | .str s => return .str s
    | _ => throw "casts to strings are not supported"
  | _ => throw "unsupported cast type"

/-- A day/second interval in microseconds. -/
def intervalMicros (d : Json) : J Int := do
  let days ← (field? d "days").elim (pure 0) getInt
  let secs ← (field? d "seconds").elim (pure 0) getInt
  let sub ← (field? d "subseconds").elim (pure 0) getInt
  let p ← natD d "precision"
  let subUs : Int := if p ≥ 6 then sub / 10 ^ (p - 6) else sub * 10 ^ (6 - p)
  return (days * 86400 + secs) * 1_000_000 + subUs

def parseConstLiteral (j : Json) : J Const := do
  let keys := ["boolean", "i8", "i16", "i32", "i64", "fp32", "fp64", "string", "null", "decimal",
    "precisionTimestamp", "timestamp", "date", "intervalDayToSecond", "intervalCompound"]
  match ← oneof "literal" j keys with
  | ("boolean", b) => return .bool (← b.getBool?)
  | ("string", s) => return .str (← s.getStr?)
  | ("null", _) => return .null
  | ("fp32", n) | ("fp64", n) =>
    match n with
    | .num x => return .flt (floatOfScientific x.mantissa x.exponent)
    | .str s => match (Const.str s).toFloat? with
      | some f => return .flt f
      | none => throw s!"cannot parse double {s}"
    | _ => throw "malformed floating-point literal"
  | ("decimal", d) =>
    let some bytes := Base64.decode (← (← field d "value").getStr?)
      | throw "malformed decimal literal"
    return .dec (Base64.leSigned bytes) (← natD d "scale")
  | ("intervalDayToSecond", d) => return .int (← intervalMicros d)
  | ("intervalCompound", c) =>
    if let some ym := field? c "intervalYearToMonth" then
      if (← natD ym "years") != 0 || (← natD ym "months") != 0 then
        throw "month and year intervals are not supported"
    return .int (← (field? c "intervalDayToSecond").elim (pure 0) intervalMicros)
  | ("precisionTimestamp", t) =>
    if (← natD t "precision") != 6 then throw "only microsecond timestamps are supported"
    return .int (← getInt (← field t "value"))
  | (_, n) => return .int (← getInt n)

/-- `arrow_cast(value, '<Arrow type>')`, as Ibis writes casts for DataFusion. -/
def arrowCast (c : Const) (ty : String) : Option Const :=
  let dummy (k : String) : Json := Json.mkObj [(k, Json.mkObj [])]
  let target :=
    if ty.startsWith "Timestamp(" then some (dummy "precisionTimestamp")
    else if ty == "Float64" || ty == "Float32" then some (dummy "fp64")
    else if ty == "Date32" then some (dummy "date")
    else if ty.startsWith "Int" then some (dummy "i64")
    else if ty == "Utf8" then some (dummy "string")
    else none
  target >>= fun t => (castConst t c).toOption

/-- Fold a function applied to constants, if it is one the parser knows. -/
def foldCall : String → List Const → Option Const
  | "arrow_cast", [c, .str ty] => arrowCast c ty
  -- Negating a double negates its code, also for NaN.
  | "negate", [.int i] => some (.int (-i))
  | "negate", [.code c] => some (.code (FloatCode.neg c))
  | "negate", [c] => c.toFloat? >>= fun f => some (.code (FloatCode.neg (FloatCode.ofFloat f)))
  | "trunc", [c] => c.toFloat? >>= fun f => some (.flt (if f ≥ 0 then f.floor else f.ceil))
  | "to_seconds", [c] => c.toFloat? >>= fun f => (Const.flt (f * 1000000.0)).toInt? >>= (some ∘ .int)
  | "to_minutes", [c] => c.toInt? >>= fun i => some (.int (i * 60_000_000))
  | "to_hours", [c] => c.toInt? >>= fun i => some (.int (i * 3_600_000_000))
  | "to_days", [c] => c.toInt? >>= fun i => some (.int (i * 86_400_000_000))
  -- Intervals are plain microseconds here, so normalizing them changes nothing.
  | "normalized_interval", [c] => some c
  | _, _ => none

partial def constOf? (fns : List (Nat × String)) (j : Json) : J (Option Const) := do
  if let some l := field? j "literal" then
    return some (← parseConstLiteral l)
  if let some c := field? j "cast" then
    let some x ← constOf? fns (← field c "input") | return none
    return some (← castConst (← field c "type") x)
  if let some f := field? j "scalarFunction" then
    let anchor ← natD f "functionReference"
    let some name := fns.lookup anchor | return none
    let args ← (← arrD f "arguments").mapM fun a => do constOf? fns (← field a "value")
    let some cs := args.mapM id | return none
    return foldCall (baseName name) cs
  return none

def constExpr : Const → J Expr
  | .int i => pure (.lit (.int i))
  | .flt f => pure (.lit (.int (FloatCode.ofFloat f)))
  | .code c => pure (.lit (.int c))
  | .str s => pure (.lit (.str s))
  | .bool b => pure (.lit (.bool b))
  | .null => pure (.lit .null)
  | .dec _ _ => throw "DECIMAL values are not supported; cast them to DOUBLE"

/-- Maps Substrait standard-extension functions onto the modelled ones.
Comparisons are derived: `a > b := b < a`, `a ≤ b := ¬(b < a)`; under
null-propagation these agree with the direct definitions. -/
def mkCall : String → List Expr → J Expr
  | "not", [a] => pure (.un .not a)
  | "is_null", [a] => pure (.un .isNull a)
  | "is_not_null", [a] => pure (.un .not (.un .isNull a))
  | "negate", [a] => pure (.un .neg a)
  -- Some producers write unary minus as a one-argument `subtract`.
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
  -- Intervals are total microseconds, already normalized.
  | "normalized_interval", [a] => pure a
  -- NaN equals itself in DataFusion's total order; it may carry either sign.
  | "is_nan", [a] | "isnan", [a] =>
    pure (.bin .or (.bin .eq a (.lit (.int FloatCode.nan))) (.bin .eq a (.lit (.int FloatCode.negNan))))
  -- `and` / `or` are variadic in Substrait.
  | "and", a :: as => pure (as.foldl (.bin .and) a)
  | "or", a :: as => pure (as.foldl (.bin .or) a)
  | name, args => throw s!"unsupported function {name}/{args.length}"

/-- Arithmetic whose result is a double. -/
def mkFloatCall : String → List Expr → J Expr
  | "add", [a, b] => pure (.bin .fadd a b)
  | "subtract", [a, b] => pure (.bin .fsub a b)
  | "multiply", [a, b] => pure (.bin .fmul a b)
  | "divide", [a, b] => pure (.bin .fdiv a b)
  | "subtract", [a] | "negate", [a] => pure (.un .fneg a)
  | name, args => throw s!"unsupported double function {name}/{args.length}"

/-- Parse an expression over input columns of kinds `cols`. -/
partial def parseExpr (fns : List (Nat × String)) (cols : List Kind) (j : Json) : J Expr := do
  if let some c ← constOf? fns j then return ← constExpr c
  match ← oneof "expression" j ["selection", "scalarFunction", "ifThen", "cast"] with
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
    let argJs ← (← arrD f "arguments").mapM fun a => field a "value"
    let parsed ← argJs.mapM (parseExpr fns cols)
    -- An integer constant next to a double stands for that double (DataFusion
    -- leaves `bpm >= 30` uncast); give it the double's code.
    let hasFloat := parsed.any (·.kind cols == .float)
    let args ← (argJs.zip parsed).mapM fun (j, e) => do
      if hasFloat then
        if let some (.int i) ← constOf? fns j then return Expr.lit (.int (FloatCode.ofInt i))
      return e
    -- Arithmetic on doubles rounds, so it gets the float operators.
    let out := typeKind ((field? f "outputType").getD .null)
    let arith := ["add", "subtract", "multiply", "divide", "negate"].contains (baseName name)
    if arith && (out == .float || args.any (·.kind cols == .float)) then
      mkFloatCall (baseName name) args
    else mkCall (baseName name) args
  | ("ifThen", t) =>
    let els ← parseExpr fns cols (← field t "else")
    (← arrD t "ifs").foldrM (init := els) fun clause acc => do
      return .ifThen (← parseExpr fns cols (← field clause "if"))
        (← parseExpr fns cols (← field clause "then")) acc
  | ("cast", c) =>
    let e ← parseExpr fns cols (← field c "input")
    let target := typeKind (← field c "type")
    let k := e.kind cols
    if target == .float && k == .int then return .un .itof e
    if target == k && target != .other then return e
    throw s!"unsupported cast from {repr k} to {repr target}"
  | (k, _) => throw s!"unsupported expression: {k}"

/-! ## Window functions -/

def parseColumn (fns : List (Nat × String)) (cols : List Kind) (what : String) (j : Json) : J Nat := do
  match ← parseExpr fns cols j with
  | .field i => pure i
  | _ => throw s!"window {what} must be columns"

def parseSortKey (fns : List (Nat × String)) (cols : List Kind) (s : Json) : J SortKey := do
  let col ← parseColumn fns cols "sort keys" (← field s "expr")
  let (desc, nullsFirst) ← match field? s "direction" with
    | some (.str "SORT_DIRECTION_ASC_NULLS_FIRST") => pure (false, true)
    | some (.str "SORT_DIRECTION_ASC_NULLS_LAST") => pure (false, false)
    | some (.str "SORT_DIRECTION_DESC_NULLS_FIRST") => pure (true, true)
    | some (.str "SORT_DIRECTION_DESC_NULLS_LAST") => pure (true, false)
    | d => throw s!"unsupported sort direction: {(d.map (·.compress)).getD "unspecified"}"
  return { col, desc, nullsFirst }

/-- A `windowFunction` expression: its `PARTITION BY`, `ORDER BY` and function.
The frame is ignored: it doesn't affect `ROW_NUMBER`, `LAG` or `LEAD`. -/
def parseWindow (fns : List (Nat × String)) (cols : List Kind) (w : Json) :
    J (List Nat × List SortKey × WinFn) := do
  let anchor ← natD w "functionReference"
  let some name := fns.lookup anchor
    | throw s!"function reference {anchor} is not declared in extensions"
  let part ← (← arrD w "partitions").mapM (parseColumn fns cols "partitions")
  let sort ← (← arrD w "sorts").mapM (parseSortKey fns cols)
  let args ← (← arrD w "arguments").mapM fun a => field a "value"
  -- `LAG(c [, offset [, default]])`; a double column's default is a code.
  let shifted (args : List Json) : J (Nat × Nat × Value) := do
    let some c := args.head? | throw s!"{name} needs a column"
    let c ← parseColumn fns cols "function arguments" c
    let offset ← match args[1]? with
      | none => pure 1
      | some j => match ← constOf? fns j with
        | some (.int k) => if k ≥ 0 then pure k.toNat else throw s!"negative {name} offset"
        | _ => throw s!"{name} offsets must be integer constants"
    let dflt ← match args[2]? with
      | none => pure Value.null
      | some j => match ← constOf? fns j with
        | some (.int i) => pure (.int (if cols.getD c .other == .float then FloatCode.ofInt i else i))
        | some k => match ← constExpr k with
          | .lit v => pure v
          | _ => throw s!"{name} defaults must be constants"
        | none => throw s!"{name} defaults must be constants"
    return (c, offset, dflt)
  let f ← match baseName name with
    | "row_number" =>
      if args.isEmpty then pure WinFn.rowNumber else throw "row_number takes no arguments"
    | "lag" => do let (c, k, d) ← shifted args; pure (.lag c k d)
    | "lead" => do let (c, k, d) ← shifted args; pure (.lead c k d)
    | n => throw s!"unsupported window function: {n}"
  return (part, sort, f)

/-- A `ProjectRel` whose expressions include window functions. Windows with the
same `PARTITION BY` and `ORDER BY` share a `Rel.window` (stacked in order of
first use); an emit then restores Substrait's column order: input columns,
then each expression. -/
def parseWindowProject (fns : List (Nat × String)) (inp : Rel) (cols : List Kind)
    (es : List Json) : J Rel := do
  let n := cols.length
  let parsed ← es.mapM fun e => do
    match field? e "windowFunction" with
    | some w => return Sum.inl (← parseWindow fns cols w)
    | none => return Sum.inr (← parseExpr fns cols e)
  -- Group the windows: (partition, sort, functions), in order of first use.
  let groups := parsed.foldl (init := ([] : List (List Nat × List SortKey × List WinFn)))
    fun gs p => match p with
    | .inl (part, sort, f) =>
      if gs.any (fun (p', s', _) => p' == part && s' == sort) then
        gs.map fun (p', s', fs) => if p' == part && s' == sort then (p', s', fs ++ [f]) else (p', s', fs)
      else gs ++ [(part, sort, [f])]
    | .inr _ => gs
  let windowed := groups.foldl (fun r (part, sort, fs) => Rel.window r part sort fs) inp
  let width := (groups.map (·.2.2.length)).sum
  -- Where each window function's column ends up: the offset of its group plus
  -- its position (the n-th use of the same function in a group is its n-th copy).
  let column (part : List Nat) (sort : List SortKey) (f : WinFn) (seen : Nat) : Nat := Id.run do
    let mut off := n
    for (p', s', fs) in groups do
      if p' == part && s' == sort then
        let idxs := (fs.zipIdx.filter (·.1 == f)).map (·.2)
        return off + idxs.getD seen 0
      off := off + fs.length
    return off
  let scalars := parsed.filterMap fun p => match p with | .inr e => some e | .inl _ => none
  let (mapping, _, _) := parsed.foldl (init := (([] : List Nat), ([] : List (List Nat × List SortKey × WinFn)), 0))
    fun (m, seen, j) p => match p with
    | .inl w@(part, sort, f) =>
      (m ++ [column part sort f (seen.count w)], seen ++ [w], j)
    | .inr _ => (m ++ [n + width + j], seen, j + 1)
  let full := List.range n ++ mapping
  if scalars.isEmpty && full == List.range (n + width) then return windowed
  let core := if scalars.isEmpty then windowed else Rel.project windowed scalars
  return .emit core full

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
            (← arrD row "fields").mapM fun e => do pure ((← parseExpr fns [] e).eval [])
        | none => (← arrD v "values").mapM fun row => do
            (← arrD row "fields").mapM fun e => do
              return (← constExpr (← parseConstLiteral e)).eval []
      pure (Rel.values arity rows)
  -- `ReadRel.filter` must be applied exactly (`bestEffortFilter` may be
  -- ignored). It refers to the base schema, so it comes before the mask.
  let filtered ← match field? r "filter" with
    | some c => pure (Rel.filter base (← parseExpr fns (schemaKinds (← field r "baseSchema")) c))
    | none => pure base
  match field? r "projection" with
  | some m => return .emit filtered (← parseMask m)
  | none => return filtered

partial def parseRel (fns : List (Nat × String)) (j : Json) : P Rel := do
  let (kind, r) ← oneof "relation" j ["read", "filter", "project", "cross", "join", "fetch", "set"]
  let input := fun (k : String) => do parseRel fns (← field r k)
  let core ← match kind with
    | "read" => parseRead fns r
    | "filter" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      pure (.filter inp (← parseExpr fns cols (← field r "condition")))
    | "project" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      let ejs ← arrD r "expressions"
      if ejs.any (fun e => (field? e "windowFunction").isSome) then
        parseWindowProject fns inp cols ejs
      else
        let es ← ejs.mapM fun e => do return (← parseExpr fns cols e)
        -- A project that appends nothing is the identity (used to carry `emit`).
        if es.isEmpty then pure inp else pure (.project inp es)
    | "cross" => pure (.cross (← input "left") (← input "right"))
    | "join" =>
      let ty ← match field? r "type" with
        | some (.str "JOIN_TYPE_INNER") => pure JoinType.inner
        | some (.str "JOIN_TYPE_LEFT") => pure JoinType.left
        | t => throw s!"unsupported join type: {(t.map (·.compress)).getD "unspecified"}"
      if (field? r "postJoinFilter").isSome then
        throw "JoinRel.postJoinFilter is not supported"
      let left ← input "left"
      let right ← input "right"
      let cols := left.kinds (← get) ++ right.kinds (← get)
      let on ← (field? r "expression").elim (pure (Expr.lit (.bool true)))
        fun e => do return (← parseExpr fns cols e)
      pure (.join left right ty on)
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
  | some e =>
    let m ← (← arrD e "outputMapping").mapM fun i => return (← getNat i)
    -- Compose with an emit the relation itself produced, as the writer does.
    match core with
    | .emit r' m' => return .emit r' (m.map (m'.getD · 0))
    | _ => return .emit core m
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
