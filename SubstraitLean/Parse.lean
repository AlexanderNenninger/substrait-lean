import Lean.Data.Json
import SubstraitLean.Keys

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
JSON (kept so plans can be written back out). Virtual tables are recorded
too, under `valuesKey`, so that their column kinds are known. -/
abbrev Tables := List (String × Nat × Json)

/-- The entry of a virtual table in `Tables`; no table name starts with `$`
in a plan the parser reads. -/
def valuesKey (n : Nat) (rows : Relation) : String := s!"$values {n} {reprStr rows}"

def isValuesKey (t : String) : Bool := t.startsWith "$values "

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

/-- The argument types of a signature, `"add:date_iday"` ↦ `["date", "iday"]`;
empty for a bare name (DataFusion's producer and sverify's write those). -/
def sigTokens (name : String) : List String :=
  match name.splitOn ":" with
  | [_, sig] => if sig.isEmpty then [] else sig.splitOn "_"
  | _ => []

/-! ## Column kinds

Doubles, timestamps and dates all become integers in the model (see
`SubstraitLean/Float.lean`); the parser and the writer track which is which. -/

inductive Kind where
  /-- `tod`: a time of day (`TIME`), in microseconds since midnight. -/
  | int | float | time | date | str | bool | tod | other
  /-- A list of values of the element kind. -/
  | list (elem : Kind)
  deriving Repr, BEq, DecidableEq, Inhabited

partial def typeKind (ty : Json) : Kind :=
  let has (k : String) := (ty.getObjVal? k).toOption.isSome
  if ["i8", "i16", "i32", "i64"].any has then .int
  else if ["fp32", "fp64"].any has then .float
  -- Times are microseconds; a coarser precision (Calcite's `TIMESTAMP` is
  -- seconds) would truncate, which is not modelled.
  else if has "timestamp" then .time
  else if let some t := (ty.getObjVal? "precisionTimestamp").toOption then
    if 6 ≤ ((t.getObjValAs? Nat "precision").toOption.getD 0) then .time else .other
  else if has "date" then .date
  else if has "time" then .tod
  else if let some t := (ty.getObjVal? "precisionTime").toOption then
    if 6 ≤ ((t.getObjValAs? Nat "precision").toOption.getD 0) then .tod else .other
  else if ["string", "varchar", "fixedChar"].any has then .str
  else if has "bool" then .bool
  else if let some l := (ty.getObjVal? "list").toOption then
    .list (typeKind ((l.getObjVal? "type").toOption.getD .null))
  else .other

def schemaKinds (schema : Json) : List Kind :=
  match (schema.getObjVal? "struct").toOption.bind (·.getObjValAs? (Array Json) "types" |>.toOption) with
  | some tys => tys.toList.map typeKind
  | none => []

/-- An argument type of a function signature (Substrait's short type names). -/
inductive ArgSig where
  | kind (k : Kind)
  /-- A day/second interval; the parser folds interval literals to microseconds. -/
  | interval
  | any
  | unknown (t : String)

def argSig : String → ArgSig
  | "i8" | "i16" | "i32" | "i64" => .kind .int
  | "fp32" | "fp64" => .kind .float
  | "ts" | "pts" => .kind .time
  | "date" => .kind .date
  | "str" | "vchar" | "fchar" => .kind .str
  | "bool" => .kind .bool
  | "iday" => .interval
  | "any" | "any1" | "any2" => .any
  | t => .unknown t

def litKind : Value → Kind
  | .int _ => .int
  | .str _ => .str
  | .bool _ => .bool
  | .null => .other
  | .list [] => .list .other
  | .list (v :: _) => .list (litKind v)

def _root_.Substrait.Expr.kind (cols : List Kind) : Expr → Kind
  | .lit v => litKind v
  | .field i => cols.getD i .other
  | .un .neg a => a.kind cols
  | .un .itof _ | .un .fneg _ | .un .ffloor _ | .un .fceil _ | .un .fround _
  | .un (.froundTo _) _ => .float
  | .un .ftoi _ | .un (.narrow _) _ => .int
  | .un .itos _ | .un .upper _ | .un .lower _ => .str
  | .un .length _ | .un (.regexMatch _) _ | .un (.datePart _) _ | .un (.dayPart _) _ => .int
  | .un (.dateTrunc _) _ => .time
  | .un .toDate _ | .un (.dayTrunc _) _ => .date
  | .un (.addMonths _ true) _ | .un .asTime _ => .time
  | .un .timeOfDay _ => .tod
  | .un (.strftime _) _ => .str
  | .un (.addMonths _ false) _ => .date
  | .un _ _ => .bool
  | .bin .add a b | .bin .sub a b | .bin .mul a b =>
      match a with
      | .lit _ => b.kind cols
      | _ => a.kind cols
  | .bin .fadd _ _ | .bin .fsub _ _ | .bin .fmul _ _ | .bin .fdiv _ _ | .bin .fpow _ _ => .float
  | .bin .idiv _ _ | .bin .imod _ _ | .bin .ipow _ _ | .bin .strpos _ _ | .bin .dateDiff _ _ => .int
  | .bin .dateAdd _ _ => .date
  | .bin .concat _ _ | .bin (.substr _) _ _ | .bin (.trim _ _) _ _ => .str
  | .bin _ _ _ => .bool
  -- A literal branch (`NULLIF`'s `NULL`, `GREATEST(x, 0)`'s `0`) says less
  -- than the other one.
  | .ifThen _ (.lit v) e => match e with
    | .lit _ => litKind v
    | _ => e.kind cols
  | .ifThen _ t _ => t.kind cols

/-- Renumber field references. -/
def _root_.Substrait.Expr.mapFields (f : Nat → Nat) : Expr → Expr
  | .lit v => .lit v
  | .field i => .field (f i)
  | .un g a => .un g (a.mapFields f)
  | .bin g a b => .bin g (a.mapFields f) (b.mapFields f)
  | .ifThen c t e => .ifThen (c.mapFields f) (t.mapFields f) (e.mapFields f)

def _root_.Substrait.WinFn.kind (cols : List Kind) : WinFn → Kind
  | .rowNumber => .int
  | .lag c _ _ | .lead c _ _ => cols.getD c .other

def _root_.Substrait.Measure.kind (cols : List Kind) (m : Measure) : Kind :=
  match m.fn with
  | .count | .sum => .int
  | .fsum | .avg => .float
  | .min | .max => m.arg.kind cols
  | .collect => .list (m.arg.kind cols)

def _root_.Substrait.Rel.kinds (tables : Tables) : Rel → List Kind
  | .read t => match tables.lookup t with
    | some (_, s) => schemaKinds s
    | none => []
  | .values n rows => match tables.lookup (valuesKey n rows) with
    | some (_, s) => schemaKinds s
    | none => List.replicate n .other
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
  | .semi a _ _ _ => a.kinds tables
  | .orderBy r _ | .distinct r => r.kinds tables
  | .unnest r c =>
      let ks := r.kinds tables
      ks.set c (match ks.getD c .other with | .list k => k | _ => .other)
  | .aggregate r gs ms =>
      let ks := r.kinds tables
      gs.map (·.kind ks) ++ ms.map (·.kind ks)

/-! ## Constants

Literals, and expressions built only from literals (`CAST('inf' AS DOUBLE)`,
`INTERVAL 60 SECOND` = `to_seconds(60.0)`), are folded into a single literal. -/

inductive Const where
  | int (i : Int)
  | flt (f : Float)
  /-- A double as its code (zero `0`, one NaN). -/
  | code (c : Int)
  | dec (m : Int) (scale : Nat)
  | str (s : String)
  | bool (b : Bool)
  | null

def floatOfScientific (m : Int) (e : Nat) : Float :=
  let f := Float.ofScientific m.natAbs true e
  if m < 0 then -f else f

/-- `CAST(c AS DOUBLE)` of a constant. A string is read as DataFusion reads it,
with no spaces around the number (DataFusion fails on those). -/
def Const.toFloat? : Const → Option Float
  | .int i => some (Float.ofInt i)
  | .flt f => some f
  | .code c => some (FloatCode.toFloat c)
  | .dec m s => some (floatOfScientific m s)
  | .str s =>
    -- `Json.parse` skips surrounding spaces, so refuse them first.
    if s.trimAscii.toString != s then none else
    match s.toLower with
    | "inf" | "+inf" | "infinity" | "+infinity" => some (1.0 / 0.0)
    | "-inf" | "-infinity" => some (-1.0 / 0.0)
    | "nan" => some (0.0 / 0.0)
    | t => match Json.parse t with
      | .ok (.num n) => some (floatOfScientific n.mantissa n.exponent)
      | _ => none
  | _ => none

/-- An integer written as DataFusion's casts accept one: an optional sign
and ASCII digits, nothing else (no spaces, no `_` separators). -/
def parseInt? (s : String) : Option Int :=
  let (neg, ds) := match s.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let n : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0
    some (if neg then -(n : Int) else n)

/-- `CAST(c AS BIGINT)` of a constant, as DataFusion casts a column
(`FloatCode.toInt?`): doubles and decimals truncate toward zero, and NaN, ±∞
and doubles outside 64 bits have no value. -/
def Const.toInt? : Const → Option Int
  | .int i => some i
  | .flt f =>
    if f.isNaN || f < -9223372036854775808.0 || f ≥ 9223372036854775808.0 then none
    else some f.toInt64.toInt
  | .dec m s =>
    let q : Int := (m.natAbs / 10 ^ s : Nat)
    some (if m < 0 then -q else q)
  | .str s => parseInt? s
  | _ => none

/-- Microseconds from seconds, rounded to the nearest (`f * 10⁶` is rarely
exact: `0.3 * 10⁶` is just below 300000). -/
def roundMicros? (f : Float) : Option Int :=
  if f.isNaN || f.isInf then none else some f.round.toInt64.toInt

#guard (Const.dec 27 1).toInt? == some 2 && (Const.dec (-25) 1).toInt? == some (-2)
#guard (Const.flt 2.7).toInt? == some 2 && (Const.flt (-2.7)).toInt? == some (-2)
#guard (Const.flt 1e30).toInt? == none && (Const.flt (-9223372036854775808.0)).toInt? == some (-2 ^ 63)
#guard (Const.str "+12").toInt? == some 12 && (Const.str "-012").toInt? == some (-12)
#guard [" 12", "12 ", "1_000", "", "-", "١٢"].all fun s => (Const.str s).toInt? == none
#guard (Const.str " 1.5").toFloat? == none && (Const.str "1.5\n").toFloat? == none
#guard (Time.parseTimestamp? " 2024-01-01").isNone && (Time.parseDate? "2024-01-01 ").isNone
#guard roundMicros? (0.3 * 1000000.0) == some 300000

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
    | .str s => match Time.parseTimestamp? s with
      | some us => return .int us
      | none => throw s!"cannot parse timestamp '{s}'"
    | .int us => return .int us
    | _ => throw "cannot cast this value to a timestamp"
  | .date =>
    match c with
    | .str s => match Time.parseDate? s with
      | some d => return .int d
      | none => throw s!"cannot parse date '{s}'"
    | .int d => return .int d
    | _ => throw "cannot cast this value to a date"
  | .str =>
    match c with
    | .str s => return .str s
    | _ => throw "casts to strings are not supported"
  | .tod =>
    match c with
    | .int us =>
      if 0 ≤ us ∧ us < Time.usPerDay then return .int us
      else throw "a time of day outside 00:00 to 24:00"
    | _ => throw "cannot cast this value to a time of day"
  | _ =>
    -- A constant cast to a timestamp coarser than microseconds: only where it
    -- truncates nothing (`CAST('2024-01-15 00:00:00' AS TIMESTAMP)` in Calcite).
    if let some t := (ty.getObjVal? "precisionTimestamp").toOption then
      let p := (t.getObjValAs? Nat "precision").toOption.getD 0
      let us ← match c with
        | .str s => match Time.parseTimestamp? s with
          | some us => pure us
          | none => throw s!"cannot parse timestamp '{s}'"
        | _ => throw "cannot cast this value to a timestamp"
      if us % 10 ^ (6 - p) == 0 then return .int us
      else throw s!"cast to a timestamp of precision {p} truncates"
    throw "unsupported cast type"

/-- A day/second interval in microseconds. -/
def intervalMicros (d : Json) : J Int := do
  let days ← (field? d "days").elim (pure 0) getInt
  let secs ← (field? d "seconds").elim (pure 0) getInt
  let sub ← (field? d "subseconds").elim (pure 0) getInt
  let p ← natD d "precision"
  let subUs : Int := if p ≥ 6 then sub / 10 ^ (p - 6) else sub * 10 ^ (6 - p)
  return (days * 86400 + secs) * 1_000_000 + subUs

/-- The months of a year/month interval. -/
def yearMonths (ym : Json) : J Int := do
  let years ← (field? ym "years").elim (pure 0) getInt
  let months ← (field? ym "months").elim (pure 0) getInt
  return 12 * years + months

/-- An interval literal as months and microseconds; `none` for other
expressions. -/
def intervalLit? (j : Json) : J (Option (Int × Int)) := do
  let some l := field? j "literal" | return none
  if let some d := field? l "intervalDayToSecond" then return some (0, ← intervalMicros d)
  if let some ym := field? l "intervalYearToMonth" then return some (← yearMonths ym, 0)
  if let some c := field? l "intervalCompound" then
    let m ← (field? c "intervalYearToMonth").elim (pure 0) yearMonths
    let us ← (field? c "intervalDayToSecond").elim (pure 0) intervalMicros
    return some (m, us)
  return none

/-- An interval literal with days or months. DataFusion compares a duration
(`ts - ts`, `d - d`) with an interval as `(months, days, nanoseconds)`, so
`d - e > INTERVAL '3 days'` is false for any `d - e`: comparisons with these
are refused. Written in hours or seconds, it compares as a number. -/
def calendarInterval (l : Json) : J Bool := do
  let days (d : Json) : J Bool := do return (← (field? d "days").elim (pure 0) getInt) != 0
  if let some d := field? l "intervalDayToSecond" then return ← days d
  if let some ym := field? l "intervalYearToMonth" then return (← yearMonths ym) != 0
  if let some c := field? l "intervalCompound" then
    let m ← (field? c "intervalYearToMonth").elim (pure 0) yearMonths
    return m != 0 || (← (field? c "intervalDayToSecond").elim (pure false) days)
  return false

def parseConstLiteral (j : Json) : J Const := do
  let keys := ["boolean", "i8", "i16", "i32", "i64", "fp32", "fp64", "string", "fixedChar",
    "varChar", "null", "decimal",
    "precisionTimestamp", "timestamp", "date", "precisionTime", "time", "intervalDayToSecond",
    "intervalYearToMonth",
    "intervalCompound"]
  match ← oneof "literal" j keys with
  | ("boolean", b) => return .bool (← b.getBool?)
  | ("string", s) => return .str (← s.getStr?)
  -- `CHAR(n)` literals (Calcite types `'abc'` as `CHAR(3)`) hold exactly their
  -- `n` characters. Engines disagree on what trailing blanks mean (PAD SPACE
  -- comparisons, casts that strip them), so those are refused; without them a
  -- CHAR literal is its string. Comparisons with one are refused in
  -- `parseExpr`, since PAD SPACE also ignores the other side's trailing blanks.
  | ("fixedChar", s) =>
    let s ← s.getStr?
    if s.endsWith " " then throw "CHAR literals with trailing blanks are not supported (blank padding)"
    return .str s
  | ("varChar", v) =>
    let s ← (← field v "value").getStr?
    if s.length > (← natD v "length") then throw "VARCHAR literal longer than its type"
    return .str s
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
      if (← yearMonths ym) != 0 then
        throw "month and year intervals are only supported added to a date or timestamp"
    return .int (← (field? c "intervalDayToSecond").elim (pure 0) intervalMicros)
  | ("intervalYearToMonth", ym) =>
    if (← yearMonths ym) != 0 then
      throw "month and year intervals are only supported added to a date or timestamp"
    return .int 0
  -- A time of day, in units of 10⁻ᵖ s since midnight.
  | ("precisionTime", t) =>
    let p ← natD t "precision"
    let v ← getInt (← field t "value")
    if p ≤ 6 then return .int (v * 10 ^ (6 - p))
    else if v % 10 ^ (p - 6) == 0 then return .int (v / 10 ^ (p - 6))
    else throw "times finer than microseconds are not supported"
  -- Precision `p` counts units of 10⁻ᵖ s (Isthmus writes `TIMESTAMP '…'` at 0).
  | ("precisionTimestamp", t) =>
    let p ← natD t "precision"
    let v ← getInt (← field t "value")
    if p ≤ 6 then return .int (v * 10 ^ (6 - p))
    else if v % 10 ^ (p - 6) == 0 then return .int (v / 10 ^ (p - 6))
    else throw "timestamps finer than microseconds are not supported"
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

/-- Negation of a double constant: NaN stays NaN. -/
def fneg (c : Int) : Int := if c == FloatCode.nan then c else FloatCode.neg c

/-- Fold a function applied to constants, if it is one the parser knows. -/
def foldCall : String → List Const → Option Const
  | "arrow_cast", [c, .str ty] => arrowCast c ty
  -- Negating a double negates its code; zero and NaN stay as they are.
  | "negate", [.int i] => some (.int (-i))
  | "negate", [.code c] => some (.code (fneg c))
  | "negate", [c] => c.toFloat? >>= fun f => some (.code (fneg (FloatCode.ofFloat f)))
  | "trunc", [c] => c.toFloat? >>= fun f => some (.flt (if f ≥ 0 then f.floor else f.ceil))
  | "to_seconds", [c] => c.toFloat? >>= fun f => roundMicros? (f * 1000000.0) >>= (some ∘ .int)
  | "to_minutes", [c] => c.toInt? >>= fun i => some (.int (i * 60_000_000))
  | "to_hours", [c] => c.toInt? >>= fun i => some (.int (i * 3_600_000_000))
  | "to_days", [c] => c.toInt? >>= fun i => some (.int (i * 86_400_000_000))
  -- Intervals are plain microseconds here, so normalizing them changes nothing.
  | "normalized_interval", [c] => some c
  | _, _ => none

partial def constOf? (fns : List (Nat × String)) (j : Json) : J (Option Const) := do
  if let some l := field? j "literal" then
    -- Months are not microseconds: `temporalArith` reads these.
    if let some (m, _) ← intervalLit? j then
      if m != 0 then return none
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

/-! ## Argument kinds

The parser dispatches on a function's base name, and the model has one
integer type for integers, doubles (as codes), timestamps (µs), dates (days)
and intervals (µs). So the arguments' kinds must be checked: `add:date_iday`
would otherwise add days and microseconds. A signature suffix (`date_iday`, as
Isthmus writes) is checked against the arguments the parser sees; a literal
argument (or one built only from literals) has no kind of its own (a
timestamp literal is an integer), so only the signature speaks for it. -/

/-- Functions whose arguments are numbers, timestamps or intervals. -/
def arithmeticFns : List String :=
  ["add", "subtract", "multiply", "divide", "modulus", "power", "negate", "abs"]

/-- Functions that compare their arguments: these must have one kind. -/
def comparisonFns : List String :=
  ["equal", "not_equal", "lt", "gt", "lte", "gte", "is_distinct_from", "is_not_distinct_from"]

/-- Does the expression read a column? One that doesn't is built from
literals, whose kinds say nothing (a timestamp literal is an integer). -/
def _root_.Substrait.Expr.readsField : Expr → Bool
  | .lit _ => false
  | .field _ => true
  | .un _ a => a.readsField
  | .bin _ a b => a.readsField || b.readsField
  | .ifThen c t e => c.readsField || t.readsField || e.readsField

def checkArgKinds (name : String) (cols : List Kind) (args : List Expr) : J Unit := do
  let base := baseName name
  let sigs := (sigTokens name).map argSig
  -- `none` for expressions of literals.
  let ks := args.map fun e => if e.readsField then some (e.kind cols) else none
  let strict := arithmeticFns.contains base || comparisonFns.contains base
  if strict then
    if let some t := sigs.findSome? (fun | .unknown t => some t | _ => none) then
      throw s!"{name}: argument type '{t}' is not supported"
  if arithmeticFns.contains base then
    if sigs.any (· matches .kind .date) || ks.any (· == some .date) then
      throw s!"{name}: date arithmetic is not in the Lean model (dates are days, intervals microseconds)"
  if comparisonFns.contains base then
    let known := ((ks.filterMap id).filter (· != .other)) ++
      sigs.filterMap (fun | .kind k => some k | _ => none)
    if let k :: rest := known then
      if rest.any (· != k) then throw s!"{name}: compares values of different types"
  -- A variadic signature (`and:bool`) names the type of every argument once.
  let sigs := match sigs.getLast? with
    | some s => sigs ++ List.replicate (args.length - sigs.length) s
    | none => sigs
  for (s, k) in sigs.zip ks do
    match s, k with
    | .kind want, some k =>
      if k != .other && k != want then
        throw s!"{name}: argument of kind {repr k} where the signature says {repr want}"
    | .interval, some k =>
      if k != .other && k != .int && k != .time then
        throw s!"{name}: argument of kind {repr k} where the signature says an interval"
    | _, _ => pure ()

#guard (checkArgKinds "add:date_iday" [.date] [.field 0, .lit (.int 86400000000)]).toBool == false
#guard (checkArgKinds "add" [.date] [.field 0, .lit (.int 86400000000)]).toBool == false
#guard (checkArgKinds "lt:date_date" [.date] [.field 0, .field 0]).toBool
#guard (checkArgKinds "lt:date_pts" [.date] [.field 0, .lit (.int 0)]).toBool == false
#guard (checkArgKinds "lt" [.date, .time] [.field 0, .field 1]).toBool == false
#guard (checkArgKinds "lt" [.time] [.field 0, .bin .sub (.lit (.int 9)) (.lit (.int 1))]).toBool
#guard (checkArgKinds "add:pts_iday" [.time] [.field 0, .lit (.int 1)]).toBool
#guard (checkArgKinds "add:i64_i64" [.float] [.field 0, .lit (.int 1)]).toBool == false
#guard (checkArgKinds "and:bool" [.bool, .bool, .int] [.field 0, .field 1, .field 2]).toBool == false

/-! ## Dates and intervals

Intervals of days and seconds are microseconds in the model, so they add to
timestamps as integers. Month intervals, and anything added to a DATE (which
is days), are read here instead: `x + INTERVAL '1 month 2 days'` adds the
months first, then the days, as DataFusion does. -/

/-- The kind of an argument: its expression's, or for a literal, its type's
(a date or timestamp literal is an integer in the model). -/
def argKind (cols : List Kind) (j : Json) (e : Expr) : Kind :=
  if e.readsField then e.kind cols else
  match field? j "literal", field? j "cast" with
  | some l, _ =>
    if (field? l "date").isSome then .date
    else if (field? l "precisionTimestamp").isSome || (field? l "timestamp").isSome then .time
    else .other
  -- A constant cast (`DATE '2024-01-31'` is a cast of a string).
  | none, some c => match typeKind ((field? c "type").getD .null) with
    | .date => .date
    | .time => .time
    | _ => .other
  | none, none => .other

/-- `x ± interval` where `x` is a DATE, or a timestamp and the interval has
months. `none` for other calls, which `mkCall` reads. -/
def temporalArith (parse : Json → J Expr) (cols : List Kind) (name : String) (argJs : List Json)
    (out : Kind) : J (Option Expr) := do
  let [aj, bj] := argJs | return none
  if name != "add" && name != "subtract" then return none
  let sub := name == "subtract"
  let a ← parse aj
  let ka := argKind cols aj a
  if ka != .date && ka != .time then return none
  -- Calcite types `DATE + INTERVAL` as a timestamp; under a cast to DATE
  -- (`parseExpr` retypes it) that is the date.
  if ka == .date && out == .time then
    throw "a date plus an interval typed as a timestamp is not supported"
  let iv ← intervalLit? bj
  -- A month interval literal is not an expression of its own.
  let b ← match iv with
    | some (_, us) => pure (Expr.lit (.int us))
    | none => parse bj
  -- DataFusion's `d - e` is a duration, which it compares with intervals as
  -- `(months, days, nanoseconds)` and fails to beyond ±2⁶³ ns; `date_diff`
  -- is the number of days.
  if ka == .date && argKind cols bj b == .date then
    throw "date - date is not supported (DataFusion compares the duration wrongly); use date_diff"
  let (months, rest) := match iv with
    | some (m, us) => (if sub then -m else m, if us == 0 then none else some (Expr.lit (.int us)))
    | none => (0, some b)
  if ka == .time then
    if months == 0 then return none
    let x := Expr.un (.addMonths months true) a
    return some (match rest with
      | none => x
      | some r => .bin (if sub then .sub else .add) x r)
  let x := if months == 0 then a else Expr.un (.addMonths months false) a
  let some r := rest | return some x
  -- The days: a constant, or a count times a constant interval of whole days.
  let days ← match r with
    | .lit (.int us) =>
      if us % Time.usPerDay != 0 then throw "a date plus a part of a day is not supported"
      pure (Expr.lit (.int (us / Time.usPerDay)))
    | .bin .mul n (.lit (.int us)) =>
      if us % Time.usPerDay != 0 || us == 0 then
        throw "a date plus a part of a day is not supported"
      if n.kind cols != .int && n.readsField then
        throw "a date plus an interval is only supported with an integer count of days"
      pure (if us == Time.usPerDay then n else .bin .mul n (.lit (.int (us / Time.usPerDay))))
    | _ => throw "a date plus an interval is only supported for constants, or a count of days"
  let days := if !sub then days else match days with
    | .lit (.int k) => .lit (.int (-k))
    | e => .un .neg e
  return some (.bin .dateAdd x days)

/-- Maps Substrait standard-extension functions onto the modelled ones.
Comparisons are derived: `a > b := b < a`, `a ≤ b := ¬(b < a)`; under
null-propagation these agree with the direct definitions. -/
def mkCall : String → List Expr → J Expr
  | "not", [a] => pure (.un .not a)
  | "is_null", [a] => pure (.un .isNull a)
  | "is_not_null", [a] => pure (.un .not (.un .isNull a))
  -- `x IS TRUE`, `x IS NOT FALSE`, …: never `NULL`.
  | "is_true", [a] => pure (.ifThen a (.lit (.bool true)) (.lit (.bool false)))
  | "is_not_true", [a] => pure (.ifThen a (.lit (.bool false)) (.lit (.bool true)))
  | "is_false", [a] => pure (.ifThen (.un .not a) (.lit (.bool true)) (.lit (.bool false)))
  | "is_not_false", [a] => pure (.ifThen (.un .not a) (.lit (.bool false)) (.lit (.bool true)))
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
  -- There is one NaN, equal to itself.
  | "is_nan", [a] | "isnan", [a] => pure (.bin .eq a (.lit (.int FloatCode.nan)))
  -- `nanvl(x, NaN)` is `x` with one NaN, and `x + 0.0` is `x` with one
  -- zero: the writer's `canonical`, read back as it was.
  | "nanvl", [a, .lit (.int c)] =>
    if c != FloatCode.nan then throw "nanvl is only supported with NaN as its fallback"
    else match a with
      | .bin .fadd x (.lit (.int 0)) => pure x
      | _ => pure a
  -- `and` / `or` are variadic in Substrait.
  | "and", a :: as => pure (as.foldl (.bin .and) a)
  | "or", a :: as => pure (as.foldl (.bin .or) a)
  -- Null handling and `GREATEST`/`LEAST`, as conditionals. These duplicate
  -- their arguments, which is harmless: expressions have no side effects.
  | "coalesce", a :: as => pure (coalesce a as)
  | "nullif", [a, b] => pure (.ifThen (.bin .eq a b) (.lit .null) a)
  | "greatest", a :: as | "greatest_skip_null", a :: as =>
    pure (as.foldl (pick fun x y => .bin .lt x y) a)
  | "least", a :: as | "least_skip_null", a :: as =>
    pure (as.foldl (pick fun x y => .bin .lt y x) a)
  | "abs", [a] => pure (.ifThen (.bin .lt a (.lit (.int 0))) (.un .neg a) a)
  -- Equality where `NULL` equals `NULL`: never `NULL` itself.
  | "is_not_distinct_from", [a, b] => pure (notDistinct a b)
  | "is_distinct_from", [a, b] => pure (.un .not (notDistinct a b))
  -- Integer division and remainder truncate; doubles go to `mkFloatCall`.
  | "divide", [a, b] => pure (.bin .idiv a b)
  | "modulus", [a, b] => pure (.bin .imod a b)
  | "power", [a, b] => pure (.bin .ipow a b)
  -- Strings (`SubstraitLean/Text.lean`).
  | "upper", [a] => pure (.un .upper a)
  | "lower", [a] => pure (.un .lower a)
  | "character_length", [a] | "char_length", [a] | "length", [a] => pure (.un .length a)
  | "str_concat", [a, b] => pure (.bin .concat a b)
  | "concat", a :: as => pure (as.foldl (.bin .concat) a)
  | "strpos", [a, b] => pure (.bin .strpos a b)
  | "starts_with", [a, b] => pure (.bin .startsWith a b)
  | "ends_with", [a, b] => pure (.bin .endsWith a b)
  -- The third argument is the escape character; `NULL` means a backslash.
  | "like", [a, b] | "like", [a, b, .lit .null] => pure (.bin .like a b)
  | "like", [_, _, _] => throw "LIKE … ESCAPE is not supported (DataFusion only allows a backslash)"
  | "substring", [s, a] => pure (.bin (.substr none) s a)
  | "substring", [s, a, .lit (.int n)] =>
    if n < 0 then throw "a negative substring length always fails"
    else pure (.bin (.substr (some n.toNat)) s a)
  | "substring", [_, _, _] => throw "substring lengths must be constants"
  | "btrim", [a] => pure (.bin (.trim true true) a (.lit (.str " ")))
  | "ltrim", [a] => pure (.bin (.trim true false) a (.lit (.str " ")))
  | "rtrim", [a] => pure (.bin (.trim false true) a (.lit (.str " ")))
  | "btrim", [a, b] => pure (.bin (.trim true true) a b)
  | "ltrim", [a, b] => pure (.bin (.trim true false) a b)
  | "rtrim", [a, b] => pure (.bin (.trim false true) a b)
  | "regexp_match", _ => throw "regexp_match is only supported as array_length(regexp_match(s, p))"
  -- Timestamps (`SubstraitLean/Time.lean`).
  | "date_part", [.lit (.str p), a] | "datepart", [.lit (.str p), a] =>
    match Time.DatePart.ofName? p with
    | some p => pure (.un (.datePart p) a)
    | none => throw s!"unsupported date part '{p}'"
  | "date_trunc", [.lit (.str u), a] | "datetrunc", [.lit (.str u), a] =>
    match Time.TimeUnit.ofName? u with
    | some u => pure (.un (.dateTrunc u) a)
    | none => throw s!"unsupported date_trunc unit '{u}'"
  -- chrono's formats; DataFusion's `to_char`.
  | "strftime", [a, .lit (.str fmt)] | "to_char", [a, .lit (.str fmt)]
  | "date_format", [a, .lit (.str fmt)] =>
    match Time.parseFormat fmt.toList with
    | some _ => pure (.un (.strftime fmt) a)
    | none => throw s!"strftime format '{fmt}' is not supported (only %Y %m %d %H %M %S %j %F %T %%)"
  -- sverify's own: the days from `e` to `d` (Lean writes it for `UnFn.dateDiff`).
  | "date_diff", [d, e] => pure (.bin .dateDiff d e)
  | name, args => throw s!"unsupported function {name}/{args.length}"
where
  notDistinct (a b : Expr) : Expr :=
    .ifThen (.un .isNull a) (.un .isNull b)
      (.ifThen (.un .isNull b) (.lit (.bool false)) (.bin .eq a b))
  /-- `COALESCE(a, as…)`: the first argument that is not `NULL`. -/
  coalesce (a : Expr) : List Expr → Expr
    | [] => a
    | b :: bs => .ifThen (.un .not (.un .isNull a)) a (coalesce b bs)
  /-- `GREATEST`/`LEAST` of two values, where `better x y` says `y` wins. Like
  DataFusion (whose producer writes them as bare `greatest`/`least`), they skip
  `NULL`s: the result is `NULL` only if both are. Substrait's typed
  `greatest`/`least` propagate `NULL`s instead (`parseExpr`). -/
  pick (better : Expr → Expr → Expr) (a b : Expr) : Expr :=
    .ifThen (.un .isNull a) b (.ifThen (.un .isNull b) a (.ifThen (better a b) b a))

/-- Arithmetic whose result is a double. -/
def mkFloatCall : String → List Expr → J Expr
  | "add", [a, b] => pure (.bin .fadd a b)
  | "subtract", [a, b] => pure (.bin .fsub a b)
  | "multiply", [a, b] => pure (.bin .fmul a b)
  | "divide", [a, b] => pure (.bin .fdiv a b)
  -- Code negation would make NaN the smallest code; SQL's one NaN stays NaN.
  | "subtract", [a] | "negate", [a] =>
    pure (.ifThen (.bin .eq a (.lit (.int FloatCode.nan))) a (.un .fneg a))
  -- `ABS` negates the codes below zero (negatives and `-∞`).
  | "abs", [a] => pure (.ifThen (.bin .lt a (.lit (.int 0))) (.un .fneg a) a)
  | "power", [a, b] => pure (.bin .fpow a b)
  | "floor", [a] => pure (.un .ffloor a)
  | "ceil", [a] => pure (.un .fceil a)
  | "round", [a] => pure (.un .fround a)
  | "round", [a, .lit (.int 0)] => pure (.un .fround a)
  | "round", [a, .lit (.int d)] => pure (.un (.froundTo d) a)
  | name, args => throw s!"unsupported double function {name}/{args.length}"

/-- Parse an expression over input columns of kinds `cols`. -/
partial def parseExpr (fns : List (Nat × String)) (cols : List Kind) (j : Json) : J Expr := do
  -- List literals: their elements are literals (without the `literal` key).
  if let some l := field? j "literal" then
    if let some lj := field? l "list" then
      let vs ← (← arrD lj "values").mapM fun e => do
        return (← parseExpr fns [] (Json.mkObj [("literal", e)])).eval []
      return .lit (.list vs)
    if (field? l "emptyList").isSome then return .lit (.list [])
  if let some c ← constOf? fns j then return ← constExpr c
  if (field? j "literal").isSome then
    throw "month and year intervals are only supported added to a date or timestamp"
  match ← oneof "expression" j ["selection", "scalarFunction", "ifThen", "cast", "singularOrList"] with
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
    -- `array_length(regexp_match(s, p))`: NULL if `p` does not match.
    if baseName name == "array_length" then
      if let [j] := argJs then
        if let some g := field? j "scalarFunction" then
          if (fns.lookup (← natD g "functionReference")).map baseName == some "regexp_match" then
            let gargs ← (← arrD g "arguments").mapM fun a => field a "value"
            let [sj, pj] := gargs | throw "regexp_match with flags is not supported"
            let some (.str p) ← constOf? fns pj | throw "regular expressions must be constants"
            return .un (.regexMatch p) (← parseExpr fns cols sj)
    let out := typeKind ((field? f "outputType").getD .null)
    if let some e ← temporalArith (parseExpr fns cols) cols (baseName name) argJs out then return e
    if comparisonFns.contains (baseName name) then
      for a in argJs do
        if let some l := field? a "literal" then
          if ← calendarInterval l then
            throw s!"{baseName name} with an interval of days or months is not supported: \
              DataFusion compares durations with it as (months, days, nanoseconds); \
              write it in hours or seconds"
    let parsed ← argJs.mapM (parseExpr fns cols)
    if baseName name == "date_diff" then
      if (argJs.zip parsed).any fun (j, e) => argKind cols j e != .date then
        throw "date_diff takes two dates"
    checkArgKinds name cols parsed
    -- Substrait's `greatest`/`least` are `NULL` if any argument is; DataFusion
    -- writes its `NULL`-skipping ones untyped (`mkCall`).
    if ["greatest", "least"].contains (baseName name) && !(sigTokens name).isEmpty then
      let call ← mkCall (baseName name) parsed
      return parsed.foldr (fun a acc => .ifThen (.un .isNull a) (.lit .null) acc) call
    if (comparisonFns ++ ["like", "starts_with", "ends_with"]).contains (baseName name) &&
        argJs.any (fun j => ((field? j "literal").bind (field? · "fixedChar")).isSome) then
      throw s!"{baseName name} with a CHAR literal is not supported (blank-padded comparison)"
    -- Substrait's `concat` is `NULL` if any argument is, unless it is asked to
    -- skip them (as DataFusion's `concat` does): only the former is modelled.
    if baseName name == "concat" then
      let opts ← arrD f "options"
      let accepts ← opts.anyM fun o => do
        if (field? o "name") != some (.str "null_handling") then return false
        return (← arrD o "preference").head? == some (.str "ACCEPT_NULLS")
      if !accepts then throw "concat is only supported with null_handling ACCEPT_NULLS"
    if ["strftime", "to_char", "date_format"].contains (baseName name) then
      if (parsed.getD 0 (.lit .null)).kind cols != .time then
        throw s!"{baseName name} is only supported on timestamps"
    if ["date_part", "datepart", "date_trunc", "datetrunc"].contains (baseName name) then
      match (parsed.getD 1 (.lit .null)).kind cols with
      | .time => pure ()
      | .tod =>
        -- A time of day is a timestamp on 1970-01-01, for its clock parts.
        match ← mkCall (baseName name) parsed with
        | e@(.un (.datePart p) _) =>
          if [.hour, .minute, .second, .millisecond, .microsecond].contains p then return e
          throw s!"date_part '{p.name}' of a time of day is not supported"
        | _ => throw s!"{baseName name} of a time of day is not supported"
      | .date =>
        -- The same function of a DATE (days).
        match ← mkCall (baseName name) parsed with
        | .un (.datePart p) a => return .un (.dayPart p) a
        | .un (.dateTrunc u) a =>
          if !([.day, .week, .month, .quarter, .year].contains u) then
            throw s!"date_trunc of a date to a {u.name} is not supported"
          return .un (.dayTrunc u) a
        | e => return e
      | _ => throw s!"{baseName name} is only supported on timestamps and dates"
    -- Arithmetic on doubles rounds, so it gets the float operators; integer
    -- arguments of a double function are converted, as DataFusion does
    -- (Isthmus types `POWER` of integers as a double).
    let floats := ["add", "subtract", "multiply", "divide", "negate", "abs", "power", "floor",
      "ceil", "round"]
    let hasFloat := parsed.any (·.kind cols == .float)
    let floatCall := floats.contains (baseName name) && (out == .float || hasFloat)
    -- An integer constant next to a double, or in a double function, stands
    -- for that double (DataFusion leaves `bpm >= 30` uncast); give it the
    -- double's code.
    -- `ROUND(x, d)`: the digits stay an integer.
    let keepInt (k : Nat) : Bool := baseName name == "round" && k == 1
    let args ← ((argJs.zip parsed).zipIdx).mapM fun ((j, e), k) => do
      if (hasFloat || floatCall) && !keepInt k then
        if let some (.int i) ← constOf? fns j then return Expr.lit (.int (FloatCode.ofInt i))
      return e
    if floatCall then
      let args := args.zipIdx.map fun (e, k) =>
        if e.kind cols == .int && !keepInt k && !(e matches .lit _) then Expr.un .itof e else e
      mkFloatCall (baseName name) args
    else mkCall (baseName name) args
  | ("ifThen", t) =>
    -- A `CASE` without `ELSE` is `ELSE NULL`.
    let els ← match field? t "else" with
      | some e => parseExpr fns cols e
      | none => pure (.lit .null)
    (← arrD t "ifs").foldrM (init := els) fun clause acc => do
      return .ifThen (← parseExpr fns cols (← field clause "if"))
        (← parseExpr fns cols (← field clause "then")) acc
  | ("cast", c) =>
    let input ← field c "input"
    -- `CAST(d + INTERVAL '1' DAY AS DATE)` (Calcite types the sum as a
    -- timestamp, at midnight): the date arithmetic itself.
    let dateType := Json.mkObj [("date", Json.mkObj [])]
    let target ← field c "type"
    let input := match field? input "scalarFunction" with
      | some f =>
        if typeKind target == .date &&
            typeKind ((field? f "outputType").getD .null) == .time then
          Json.mkObj [("scalarFunction", f.setObjVal! "outputType" dateType)]
        else input
      | none => input
    let e ← parseExpr fns cols input
    let target := typeKind (← field c "type")
    let k := e.kind cols
    if target == .float && k == .int then return .un .itof e
    -- Fails on NaN, ±∞ and out-of-range values (`SubstraitLean/Safety.lean`).
    if target == .int && k == .float then return .un .ftoi e
    if target == .str && k == .int then return .un .itos e
    if target == .date && k == .time then return .un .toDate e
    if target == .tod && k == .time then return .un .timeOfDay e
    -- Microseconds since 1970-01-01 (arrow's cast of an integer).
    if target == .time && k == .int then return .un .asTime e
    -- Fails where the value does not fit (`SubstraitLean/Safety.lean`).
    if target == .int && k == .int then
      let bits := intBits (← field c "type")
      return if bits < 64 then .un (.narrow bits) e else e
    if target == k && target != .other then return e
    throw s!"unsupported cast from {repr k} to {repr target}"
  | ("singularOrList", l) =>
    -- `x IN (a, b)` is `x = a OR x = b`, which has SQL's null semantics.
    let v ← parseExpr fns cols (← field l "value")
    let opts ← (← arrD l "options").mapM fun o => do
      if v.kind cols == .float then
        if let some (.int i) ← constOf? fns o then return Expr.lit (.int (FloatCode.ofInt i))
      parseExpr fns cols o
    match opts.map (.bin .eq v) with
    | [] => return .lit (.bool false)
    | e :: es => return es.foldl (.bin .or) e
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

/-- The nodes under `key` inside an expression, in the order `replaceNodes`
visits them. A node's own contents are not searched. -/
partial def nodesIn (key : String) : Json → List Json
  | .arr a => a.toList.flatMap (nodesIn key)
  | j@(.obj kvs) => match field? j key with
    | some w => [w]
    | none => kvs.toList.flatMap (nodesIn key ·.2)
  | _ => []

/-- Replace the `k`-th node under `key` (from `k₀`) by `col k`. -/
partial def replaceNodes (key : String) (col : Nat → Json) : Json → StateM Nat Json
  | .arr a => return .arr (← a.mapM (replaceNodes key col))
  | j@(.obj kvs) => do
    if (field? j key).isSome then
      let k ← get
      set (k + 1)
      return col k
    let kvs' ← kvs.toList.mapM fun (k, v) => do return (k, ← replaceNodes key col v)
    return Json.mkObj kvs'
  | j => return j

/-- The window functions inside an expression. -/
def windowsIn : Json → List Json := nodesIn "windowFunction"

def replaceWindows (col : Nat → Json) : Json → StateM Nat Json := replaceNodes "windowFunction" col

/-- A reference to input column `i`. -/
def fieldJson (i : Nat) : Json :=
  Json.mkObj [("selection", Json.mkObj [("directReference", Json.mkObj
    [("structField", Json.mkObj [("field", (i : Int))])])])]

/-- A `ProjectRel` whose expressions use window functions, at the top or
nested (`ROW_NUMBER() OVER (…) - 1`). The windows are hoisted into
`Rel.window`s: those with the same `PARTITION BY` and `ORDER BY` share one
(stacked in order of first use), each use getting its own column. The
expressions then read those columns; an emit restores Substrait's column
order: input columns, then each expression. -/
def parseWindowProject (fns : List (Nat × String)) (inp : Rel) (cols : List Kind)
    (es : List Json) : J Rel := do
  let n := cols.length
  let uses ← (es.flatMap windowsIn).mapM (parseWindow fns cols)
  -- Group the uses: (partition, sort, functions), in order of first use.
  let groups := uses.foldl (init := ([] : List (List Nat × List SortKey × List WinFn)))
    fun gs (part, sort, f) =>
      if gs.any (fun (p', s', _) => p' == part && s' == sort) then
        gs.map fun (p', s', fs) => if p' == part && s' == sort then (p', s', fs ++ [f]) else (p', s', fs)
      else gs ++ [(part, sort, [f])]
  let windowed := groups.foldl (fun r (part, sort, fs) => Rel.window r part sort fs) inp
  let width := (groups.map (·.2.2.length)).sum
  -- The column of the k-th use: its group's offset plus its position there
  -- (the uses of a group come in order).
  let column (k : Nat) : Nat := Id.run do
    let some (part, sort, _) := uses[k]? | return 0
    let before := ((uses.take k).filter fun (p', s', _) => p' == part && s' == sort).length
    let mut off := n
    for (p', s', fs) in groups do
      if p' == part && s' == sort then return off + before
      off := off + fs.length
    return off
  let (rewritten, _) := (es.mapM (replaceWindows (fieldJson ∘ column))).run 0
  let wcols := cols ++ (windowed.kinds []).drop n
  -- Bare window functions are their columns; other expressions are computed
  -- after the windows.
  let parsed ← rewritten.mapM fun e => do
    match ← parseExpr fns wcols e with
    | .field i => if n ≤ i then pure (Sum.inl i) else pure (Sum.inr (Expr.field i))
    | e => pure (Sum.inr e)
  let scalars := parsed.filterMap fun p => match p with | .inr e => some e | .inl _ => none
  let (mapping, _) := parsed.foldl (init := (([] : List Nat), 0))
    fun (m, j) p => match p with
    | .inl i => (m ++ [i], j)
    | .inr _ => (m ++ [n + width + j], j + 1)
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
  -- The model's times are microseconds (`typeKind`).
  for ty in ← arrD ((field? (← field r "baseSchema") "struct").getD .null) "types" do
    if let some t := field? ty "precisionTimestamp" then
      if (← natD t "precision") < 6 then
        throw "timestamp columns coarser than microseconds are not supported"
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
      -- Virtual tables with the same rows share an entry (`Rel.values` has no
      -- schema): where their kinds differ, the column's kind is unknown.
      let key := valuesKey arity rows
      let schema ← field r "baseSchema"
      let schema := match (← get).lookup key with
        | some (_, prev) =>
          let types := ((schema.getObjVal? "struct").bind (·.getObjValAs? (Array Json) "types")).toOption.getD #[]
          let prevKinds := schemaKinds prev
          let merged := types.toList.zipIdx.map fun (ty, i) =>
            if prevKinds[i]? == some (typeKind ty) then ty else Json.mkObj []
          Json.mkObj [("struct", Json.mkObj [("types", Json.arr merged.toArray)])]
        | none => schema
      modify ((key, arity, schema) :: ·)
      pure (Rel.values arity rows)
  -- `ReadRel.filter` must be applied exactly (`bestEffortFilter` may be
  -- ignored). It refers to the base schema, so it comes before the mask.
  let filtered ← match field? r "filter" with
    | some c => pure (Rel.filter base (← parseExpr fns (schemaKinds (← field r "baseSchema")) c))
    | none => pure base
  match field? r "projection" with
  | some m => return .emit filtered (← parseMask m)
  | none => return filtered

/-- One `AggregateRel` measure. `AVG` of integers averages their conversions
to double; `COUNT(*)` may come with no argument. -/
def parseMeasure (fns : List (Nat × String)) (cols : List Kind) (mj : Json) : J Measure := do
  let m ← field mj "measure"
  let anchor ← natD m "functionReference"
  let some name := fns.lookup anchor
    | throw s!"function reference {anchor} is not declared in extensions"
  let name := baseName name
  -- Only `ARRAY_AGG` depends on the order of its rows.
  let sort ← (← arrD m "sorts").mapM fun k => (parseSortKey fns cols k : J SortKey)
  if !sort.isEmpty && name != "array_agg" then
    throw s!"ordered aggregates are not supported: {name}"
  let distinct ← match field? m "invocation" with
    | none | some (.str "AGGREGATION_INVOCATION_ALL")
    | some (.str "AGGREGATION_INVOCATION_UNSPECIFIED") => pure false
    | some (.str "AGGREGATION_INVOCATION_DISTINCT") => pure true
    | some i => throw s!"unsupported aggregate invocation: {i.compress}"
  let filter ← (field? mj "filter").mapM fun c => (parseExpr fns cols c : J Expr)
  let args ← (← arrD m "arguments").mapM fun a => field a "value"
  let arg ← match args with
    | [a] => parseExpr fns cols a
    | [] => if name == "count" then pure (.lit (.int 1)) else throw s!"{name} needs an argument"
    | _ => throw s!"{name} takes one argument"
  let k := arg.kind cols
  -- `AVG` is modelled as a double; Calcite's `AVG` of integers is an integer
  -- (`avg:i64` with an `i64` result), which it is not.
  if name == "avg" then
    if let some ty := field? m "outputType" then
      if typeKind ty != .float then throw "avg with a non-double result is not supported"
  let minMax (k : Kind) := k == .int || k == .str || k == .bool || k == .time || k == .date
  let (fn, arg) ← match name, k with
    | "count", _ => pure (AggFn.count, arg)
    | "sum", .int => pure (.sum, arg)
    | "sum", .float => pure (.fsum, arg)
    | "avg", .int => pure (.avg, .un .itof arg)
    | "avg", .float => pure (.avg, arg)
    -- DataFusion's grouped `MIN`/`MAX` of doubles compares like IEEE 754 from
    -- ±f64::MAX: a group of +∞ has `MIN` f64::MAX, and NaN is skipped next
    -- to other values.
    | "min", .float | "max", .float => throw s!"{name} of doubles is not supported"
    | "min", _ => if minMax k then pure (.min, arg) else throw "min of this type is not supported"
    | "max", _ => if minMax k then pure (.max, arg) else throw "max of this type is not supported"
    | "sum", _ | "avg", _ => throw s!"{name} of this type is not supported"
    -- NULLs are skipped (`Measure.inputs`), as with Ibis's
    -- `ARRAY_AGG(x) FILTER (WHERE x IS NOT NULL)`, so the filter must say so.
    | "array_agg", _ => pure (.collect, arg)
    | n, _ => throw s!"unsupported aggregate function: {n}"
  if fn == .collect then
    if distinct then throw "array_agg(DISTINCT …) is not supported"
    let skipsNull := match filter with
      | some f => f == .un .not (.un .isNull arg) ||
          (match f with | .bin .and _ (.un .not (.un .isNull a)) => a == arg | _ => false)
      | none => false
    if !skipsNull then
      throw "array_agg keeps NULLs; only array_agg(x) FILTER (WHERE x IS NOT NULL) is supported"
  return { fn, arg, distinct, filter, sort }

/-! ## Subqueries

A subquery expression (`Expression.subquery`) in a filter or a projection
becomes a column appended to the input, computed by joining the subquery's
relation; the expression then reads that column. Outer references are
refused, so only uncorrelated subqueries get here. -/

/-- Does `r` have at most one row, on every catalog with the tables' arities?
`Rel.keys` derives the empty key (`Rel.keys_sound`, `KeyOn.nil_iff`). -/
def atMostOneRow (tables : Tables) (r : Rel) : Bool :=
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  (r.keys cat (fun _ => []) (fun _ => []) (fun _ => [])).contains []

/-- `inp` with one more column: the value of the subquery `sq` on each row.

* `(SELECT …)`: a left join on `TRUE`. DataFusion fails when the subquery
  has several rows, so it must provably have at most one (`atMostOneRow`);
  with none, the value is `NULL`.
* `x IN (SELECT y …)`: `TRUE` if some `y = x`; otherwise `NULL` if `x` is
  `NULL` (and there are `y`s) or some `y` is, else `FALSE`. A left join with
  the distinct non-`NULL` `y`s finds the match (at most one per row), and a
  cross join with `COUNT(*)` and `COUNT(y)` (one row) says the rest.
* `EXISTS (…)`: a cross join with its `COUNT(*)` (one row), compared with 0. -/
def liftSubquery (fns : List (Nat × String)) (parse : Json → P Rel) (inp : Rel) (sq : Json) :
    P Rel := do
  let cols := inp.kinds (← get)
  let n := cols.length
  let oneColumn (what : String) (q : Rel) : P Unit := do
    if (q.kinds (← get)).length != 1 then throw s!"{what} must return one column"
  let count (e : Expr) : Measure := { fn := .count, arg := e }
  match ← oneof "subquery" sq ["scalar", "inPredicate", "setPredicate"] with
  | ("scalar", s) =>
    let q ← parse (← field s "input")
    oneColumn "a scalar subquery" q
    if !atMostOneRow (← get) q then
      throw "a scalar subquery must have at most one row (DataFusion fails on more), \
        and the checker cannot prove it (it can for an aggregate without groups, or LIMIT 1)"
    return .join inp q .left (.lit (.bool true))
  | ("inPredicate", ip) =>
    let [nj] ← arrD ip "needles" | throw "IN with several needles is not supported"
    let x ← parseExpr fns cols nj
    let hay ← parse (← field ip "haystack")
    oneColumn "an IN subquery" hay
    let ys := Rel.distinct (.filter hay (.un .not (.un .isNull (.field 0))))
    let counts := Rel.aggregate hay [] [count (.lit (.int 1)), count (.field 0)]
    let both := Rel.cross (.join inp ys .left (.bin .eq x (.field n))) counts
    let (y, c, cy) := (Expr.field n, Expr.field (n + 1), Expr.field (n + 2))
    let value := Expr.ifThen (.un .not (.un .isNull y)) (.lit (.bool true))
      (.ifThen (.bin .eq c (.lit (.int 0))) (.lit (.bool false))
        (.ifThen (.bin .or (.un .isNull x) (.bin .lt cy c)) (.lit .null) (.lit (.bool false))))
    return .emit (.project both [value]) (List.range n ++ [n + 3])
  | (_, sp) =>
    if field? sp "predicateOp" != some (.str "PREDICATE_OP_EXISTS") then
      throw "only EXISTS set predicates are supported"
    let q ← parse (← field sp "tuples")
    let exists_ := Expr.bin .lt (.lit (.int 0)) (.field n)
    return .emit (.project (.cross inp (.aggregate q [] [count (.lit (.int 1))])) [exists_])
      (List.range n ++ [n + 1])

/-- Parse the expressions `es` over `inp`, lifting their subqueries
(`liftSubquery`): the lifted input, and the expressions over it. -/
def parseLifted (fns : List (Nat × String)) (parse : Json → P Rel) (inp : Rel) (es : List Json) :
    P (Rel × List Expr) := do
  let n := (inp.kinds (← get)).length
  let lifted ← (es.flatMap (nodesIn "subquery")).foldlM (liftSubquery fns parse) inp
  let (rewritten, _) := (es.mapM (replaceNodes "subquery" (fieldJson ∘ (n + ·)))).run 0
  let cols := lifted.kinds (← get)
  return (lifted, ← rewritten.mapM fun e => (parseExpr fns cols e : J Expr))

/-- The conjuncts of a condition, splitting top-level `and` calls. -/
partial def conjuncts (fns : List (Nat × String)) (j : Json) : J (List Json) := do
  if let some f := field? j "scalarFunction" then
    if (fns.lookup (← natD f "functionReference")).map baseName == some "and" then
      let args ← (← arrD f "arguments").mapM fun a => field a "value"
      return (← args.mapM (conjuncts fns)).flatten
  return [j]

partial def parseRel (fns : List (Nat × String)) (j : Json) : P Rel := do
  let (kind, r) ← oneof "relation" j
    ["read", "filter", "project", "cross", "join", "fetch", "set", "sort", "aggregate",
      "extensionSingle"]
  let input := fun (k : String) => do parseRel fns (← field r k)
  let core ← match kind with
    | "read" => parseRead fns r
    | "filter" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      -- `x IN (subquery)` conjuncts become semi joins; the rest stays a filter,
      -- with other subqueries lifted into columns that an emit drops after.
      let mut base := inp
      let mut rest : List Json := []
      for c in ← conjuncts fns (← field r "condition") do
        match (field? c "subquery").bind (field? · "inPredicate") with
        | some ip =>
          let [nj] ← arrD ip "needles" | throw "IN with several needles is not supported"
          let needle ← parseExpr fns cols nj
          let hay ← parseRel fns (← field ip "haystack")
          if (hay.kinds (← get)).length != 1 then throw "IN subquery must return one column"
          base := .semi base hay false (.bin .eq needle (.field cols.length))
        | none => rest := rest ++ [c]
      let (lifted, conds) ← parseLifted fns (parseRel fns) base rest
      let filtered := match conds with
        | [] => lifted
        | e :: es => .filter lifted (es.foldl (.bin .and) e)
      if (rest.flatMap (nodesIn "subquery")).isEmpty then pure filtered
      else pure (.emit filtered (List.range cols.length))
    | "project" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      let ejs ← arrD r "expressions"
      let k := (ejs.flatMap (nodesIn "subquery")).length
      if !(ejs.flatMap windowsIn).isEmpty then
        if k != 0 then throw "a projection with window functions and subqueries is not supported"
        parseWindowProject fns inp cols ejs
      else if k != 0 then
        let (lifted, es) ← parseLifted fns (parseRel fns) inp ejs
        let n := cols.length
        pure (.emit (.project lifted es) (List.range n ++ (List.range es.length).map (n + k + ·)))
      else
        let es ← ejs.mapM fun e => do return (← parseExpr fns cols e)
        -- A project that appends nothing is the identity (used to carry `emit`).
        if es.isEmpty then pure inp else pure (.project inp es)
    | "cross" => pure (.cross (← input "left") (← input "right"))
    | "join" =>
      let ty := match field? r "type" with
        | some (.str t) => t
        | _ => "unspecified"
      if (field? r "postJoinFilter").isSome then
        throw "JoinRel.postJoinFilter is not supported"
      let left ← input "left"
      let right ← input "right"
      let (n, m) := ((left.kinds (← get)).length, (right.kinds (← get)).length)
      let cols := left.kinds (← get) ++ right.kinds (← get)
      let on ← (field? r "expression").elim (pure (Expr.lit (.bool true)))
        fun e => do return (← parseExpr fns cols e)
      -- The condition with the sides swapped: a's columns `i < n` move to
      -- `m + i`, b's columns `n + j` to `j`.
      let swapped := on.mapFields fun i => if i < n then m + i else i - n
      -- `b`'s columns, then `a`'s: put back in order.
      let back := (List.range n).map (m + ·) ++ List.range m
      match ty with
      | "JOIN_TYPE_INNER" => pure (.join left right .inner on)
      | "JOIN_TYPE_LEFT" => pure (.join left right .left on)
      | "JOIN_TYPE_RIGHT" => pure (.emit (.join right left .left swapped) back)
      | "JOIN_TYPE_LEFT_SEMI" => pure (.semi left right false on)
      | "JOIN_TYPE_LEFT_ANTI" => pure (.semi left right true on)
      | "JOIN_TYPE_RIGHT_SEMI" => pure (.semi right left false swapped)
      | "JOIN_TYPE_RIGHT_ANTI" => pure (.semi right left true swapped)
      -- The left join, plus the right rows nothing matches, padded with NULLs.
      | "JOIN_TYPE_OUTER" =>
        let unmatched := Rel.project (.semi right left true swapped) (List.replicate n (.lit .null))
        pure (.unionAll (.join left right .left on) (.emit unmatched ((List.range n).map (m + ·) ++ List.range m)))
      | t => throw s!"unsupported join type: {t}"
    | "fetch" =>
      -- Current encoding: `offsetExpr`/`countExpr` (constants only here);
      -- deprecated encoding: `offset`/`count`.
      let constInt (key : String) : J (Option Int) := do
        match field? r (key ++ "Expr") with
        | some e => match ← constOf? fns e with
          | some (.int i) => pure (some i)
          | some .null => pure none
          | _ => throw s!"FetchRel.{key}Expr must be an integer constant"
        | none => (field? r key).mapM getInt
      let offset ← match ← constInt "offset" with
        | some i => if i < 0 then throw "negative FetchRel offset" else pure i.toNat
        | none => pure 0
      -- An absent count, or the legacy `-1`, means "all remaining rows".
      let count := (← constInt "count").bind fun n => if n < 0 then none else some n.toNat
      pure (.fetch (← input "input") offset count)
    | "sort" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      pure (.orderBy inp (← (← arrD r "sorts").mapM fun k => (parseSortKey fns cols k : J SortKey)))
    | "aggregate" =>
      let inp ← input "input"
      let cols := inp.kinds (← get)
      let measures ← arrD r "measures"
      let groups ← match ← arrD r "groupings" with
        | [] => pure (some [])
        | [g] =>
          -- DataFusion writes `DISTINCT` as one empty grouping (which its own
          -- consumer rejects); without measures it can only mean all columns.
          if (field? g "expressionReferences").isNone && (field? g "groupingExpressions").isNone then
            pure (if measures.isEmpty then none else some [])
          else
            let top ← arrD r "groupingExpressions"
            let exprs ← match field? g "expressionReferences" with
              | some _ => (← arrD g "expressionReferences").mapM fun i => do
                  let k ← getNat i
                  match top[k]? with
                  | some e => pure e
                  | none => throw s!"grouping expression {k} does not exist"
              | none => arrD g "groupingExpressions"
            pure (some (← exprs.mapM fun e => (parseExpr fns cols e : J Expr)))
        | _ => throw "grouping sets are not supported"
      let columns (gs : List Expr) : Option (List Nat) :=
        gs.mapM fun | .field i => some i | _ => none
      match groups, measures with
      | none, _ => pure (.distinct inp)
      | some [], [] => throw "an aggregate without groupings needs measures"
      | some gs, [] => match columns gs with
        | some keys =>
          if keys == List.range cols.length then pure (.distinct inp)
          else pure (.distinct (.emit inp keys))
        | none => pure (.aggregate inp gs [])
      | some gs, ms =>
        pure (.aggregate inp gs (← ms.mapM fun m => (parseMeasure fns cols m : J Measure)))
    | "extensionSingle" =>
      -- `UNNEST`, our own extension (`docs/nested-values.md`).
      let d ← field r "detail"
      if field? d "@type" != some (.str "type.googleapis.com/sverify.Unnest") then
        throw "unsupported ExtensionSingleRel"
      if field? d "keepEmpty" == some (.bool true) then
        throw "UNNEST keeping empty lists is not supported"
      let inp ← input "input"
      let c ← natD d "column"
      match (inp.kinds (← get)).getD c .other with
      | .list _ => pure (.unnest inp c)
      | _ => throw s!"UNNEST of column {c}, which is not a list"
    | _ =>
      let inputs ← (← arrD r "inputs").mapM (parseRel fns)
      let union ← match inputs with
        | a :: as => pure (as.foldl .unionAll a)
        | [] => throw "SetRel without inputs"
      match field? r "op" with
      | some (.str "SET_OP_UNION_ALL") => pure union
      | some (.str "SET_OP_UNION_DISTINCT") => pure (.distinct union)
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
