import SubstraitLean.Rel
import SubstraitLean.Functions

/-! # Human-readable rendering of values, expressions and plans -/

namespace Substrait

/-- `i · 10⁻ˢ` in decimal digits (`decimalString 2 (-5)` is `-0.05`). -/
def _root_.decimalString (s : Nat) (i : Int) : String :=
  if s = 0 then toString i else
    let digits := (toString i.natAbs).toList
    let digits := List.replicate (s + 1 - digits.length) '0' ++ digits
    let k := digits.length - s
    (if i < 0 then "-" else "") ++ String.ofList (digits.take k) ++ "." ++ String.ofList (digits.drop k)

#guard decimalString 2 (-5) == "-0.05" && decimalString 2 1234 == "12.34" && decimalString 0 7 == "7"
#guard decimalString 3 1000 == "1.000" && decimalString 1 0 == "0.0"

/-- A value by its kind (#923): a double as a double with a `d`, a decimal
in its digits, dates and times as their integers (days, microseconds). -/
def Value.render : Value → String
  | .null => "NULL"
  | .bool b => toString b
  | .int i | .date i | .ts i | .tod i => toString i
  | .float c => s!"{FloatCode.toFloat c}d"
  | .dec s i => decimalString s i
  | .str s => s.quote
  | .list vs | .struct vs => "[" ++ ", ".intercalate (vs.attach.map fun ⟨v, _⟩ => v.render) ++ "]"

#guard Value.render (.int (-(2 ^ 63))) == "-9223372036854775808"
#guard Value.render (.int (2 ^ 63)) == "9223372036854775808"
#guard Value.render (.list [.dec 1 10, .null, .dec 1 25]) == "[1.0, NULL, 2.5]"

def Row.render (row : Row) : String :=
  "(" ++ ", ".intercalate (row.map Value.render) ++ ")"

/-! Constructors without parameters render as their row of
`SubstraitLean/Functions.lean` says (`Functions.prettyOf`); the others, and
those without a row (casts), by an arm of their own. -/

def UnFn.render : UnFn → String
  | .itof => "DOUBLE" | .froundTo d => s!"ROUND_{d}"
  | .ftoi => "BIGINT" | .narrow n => s!"INT{n}" | .ftoiOrNull => "TRY_BIGINT"
  | .narrowOrNull n => s!"TRY_INT{n}" | .wrap n => s!"WRAP{n}" | .itos => "VARCHAR" | .widen => "DOUBLE"
  | .replace p r => s!"REPLACE_{p.quote}_{r.quote}" | .regexMatch p => s!"REGEXP_MATCH_{p.quote}"
  | .regexExtract p g => s!"REGEXP_EXTRACT_{p.quote}_{g}"
  | .regexReplace p r g => s!"REGEXP_REPLACE_{p.quote}_{r.quote}{if g then "_G" else ""}"
  | .datePart p => s!"DATE_PART_{p.name}" | .dateTrunc u => s!"DATE_TRUNC_{u.name}"
  | .toDate => "DATE" | .dayPart p => s!"DAY_PART_{p.name}" | .dayTrunc u => s!"DAY_TRUNC_{u.name}"
  | .addMonths m _ => s!"ADD_MONTHS_{m}" | .timeOfDay => "TIME" | .asTime => "TIMESTAMP"
  | .dateTime => "DATE_TIMESTAMP" | .epochUs => "EPOCH_US"
  | .strftime fmt => s!"STRFTIME_{fmt.quote}" | .bucket k o => s!"BUCKET_{k}_{o}"
  | .decimal p s => s!"DECIMAL_{p}_{s}" | .dkind p s => s!"AS_DECIMAL_{p}_{s}" | .dround k => s!"DROUND_{k}" | .dtrunc k => s!"DTRUNC_{k}"
  | .ftod s => s!"TO_DECIMAL_{s}" | .dtof s => s!"DECIMAL_TO_DOUBLE_{s}"
  | .structField i => s!"FIELD_{i}" | .listElement off => s!"ELEMENT_{off}"
  | .raise msg => s!"RAISE_{msg.quote}"
  | .fit m w => s!"{m.name}{w.bits}"
  | .bbox n => n.toUpper
  | f => Functions.prettyOf (.un f)

def BinFn.render : BinFn → String
  | .substr n wrap =>
    s!"SUBSTRING_FOR_{(n.map toString).getD "ALL"}{if wrap then "" else "_LEFT_OF_BEGINNING"}"
  | .bbox2 n => n.toUpper
  | f => Functions.prettyOf (.bin f)

def HoFn.name (f : HoFn) : String := Functions.prettyOf (.hof f)

/-- An expression under `d` lambdas: their parameters are `x0` (the
outermost) to `x{d-1}`, and the row's column `i` is `$i` (D28). -/
def Expr.renderAt (d : Nat) : Expr → String
  | .lit v => v.render
  | .field i => if i < d then s!"x{d - 1 - i}" else s!"${i - d}"
  | .un f a => s!"{f.render}({a.renderAt d})"
  | .bin f a b => s!"({a.renderAt d} {f.render} {b.renderAt d})"
  | .ifThen c t e => s!"IF {c.renderAt d} THEN {t.renderAt d} ELSE {e.renderAt d}"
  | .hof f l b => s!"{f.name}({l.renderAt d}, x{d} -> {b.renderAt (d + 1)})"

def Expr.render (e : Expr) : String := e.renderAt 0

def AggFn.name : AggFn → String
  | .bit op => s!"BIT_{op.name.toUpper}"
  | .concat sep => s!"STRING_AGG_{sep.quote}"
  | .quantile cont num scale =>
    s!"QUANTILE_{if cont then "CONT" else "DISC"}_{num}E-{scale}"
  | .bbox n => n.toUpper
  | f => Functions.prettyOf (.agg f)

def Measure.render (m : Measure) : String :=
  let filter := match m.filter with
    | some c => s!" FILTER (WHERE {c.render})"
    | none => ""
  let sort := if m.sort.isEmpty then "" else
    " ORDER BY " ++ ", ".intercalate (m.sort.map fun k => s!"${k.col}{if k.desc then " DESC" else ""}")
  s!"{m.fn.name}({if m.distinct then "DISTINCT " else ""}{m.arg.render}{sort}){filter}"

def FrameBound.render : FrameBound → String
  | .unboundedPreceding => "UNBOUNDED PRECEDING" | .unboundedFollowing => "UNBOUNDED FOLLOWING"
  | .preceding 0 => "CURRENT ROW" | .preceding k => s!"{k} PRECEDING" | .following k => s!"{k} FOLLOWING"

def Frame.render (fr : Frame) : String :=
  s!"{if fr.range then "RANGE" else "ROWS"} BETWEEN {fr.lo.render} AND {fr.hi.render}"

def WinFn.render : WinFn → String
  | .rowNumber => "ROW_NUMBER()"
  | .lag c k d => s!"LAG(${c}, {k}, {d.render})"
  | .lead c k d => s!"LEAD(${c}, {k}, {d.render})"
  | .rank _ => "RANK()" | .denseRank _ => "DENSE_RANK()" | .percentRank _ => "PERCENT_RANK()"
  | .cumeDist _ => "CUME_DIST()" | .ntile k => s!"NTILE({k})"
  | .agg m _ fr => s!"{m.render} {fr.render}"
  | .firstValue c _ fr => s!"FIRST_VALUE(${c}) {fr.render}"
  | .lastValue c _ fr => s!"LAST_VALUE(${c}) {fr.render}"
  | .nthValue c n _ fr => s!"NTH_VALUE(${c}, {n}) {fr.render}"

def Rel.renderLines : Rel → List String
  | .read t => [s!"Read {t}"]
  | .values n rows => [s!"Values[{n}] {rows.length} row(s)"]
  | .filter r c => s!"Filter {c.render}" :: indent r.renderLines
  | .project r es => s!"Project +[{", ".intercalate (es.map Expr.render)}]" :: indent r.renderLines
  | .emit r m => s!"Emit {m}" :: indent r.renderLines
  | .cross a b => "Cross" :: indent a.renderLines ++ indent b.renderLines
  | .join a b ty on =>
      let t := match ty with | .inner => "Inner" | .left => "Left"
      s!"{t}Join {on.render}" :: indent a.renderLines ++ indent b.renderLines
  | .fetch r off cnt =>
      s!"Fetch offset={off} count={(cnt.map toString).getD "all"}" :: indent r.renderLines
  | .unionAll a b => "UnionAll" :: indent a.renderLines ++ indent b.renderLines
  | .window r part sort fns =>
      s!"Window +[{", ".intercalate (fns.map WinFn.render)}] PARTITION BY {part.map (s!"${·}")} ORDER BY {sort.map key}"
        :: indent r.renderLines
  | .semi a b anti on =>
      s!"{if anti then "Anti" else "Semi"}Join {on.render}" :: indent a.renderLines ++ indent b.renderLines
  | .orderBy r keys => s!"OrderBy {keys.map key}" :: indent r.renderLines
  | .distinct r => "Distinct" :: indent r.renderLines
  | .unnest r c => s!"Unnest ${c}" :: indent r.renderLines
  | .aggregate r gs ms =>
      s!"Aggregate +[{", ".intercalate (ms.map Measure.render)}] GROUP BY [{", ".intercalate (gs.map Expr.render)}]"
        :: indent r.renderLines
where
  indent (ls : List String) : List String := ls.map ("  " ++ ·)
  key (k : SortKey) : String :=
    if k.clustered then s!"${k.col} CLUSTERED" else
    s!"${k.col}{if k.desc then " DESC" else ""}{if k.firstNulls then " NULLS FIRST" else ""}{if k.nullsOpen then " NULLS ANY" else ""}"

def Rel.render (r : Rel) : String := "\n".intercalate r.renderLines

end Substrait
