import SubstraitLean.Rel

/-! # Human-readable rendering of values, expressions and plans -/

namespace Substrait

def Value.render : Value → String
  | .null => "NULL"
  | .bool b => toString b
  -- Too large for a 64-bit integer: a double's code (SubstraitLean/Float.lean).
  | .int i => if i.natAbs ≥ 2 ^ 63 then s!"{FloatCode.toFloat i}d" else toString i
  | .str s => s.quote

def Row.render (row : Row) : String :=
  "(" ++ ", ".intercalate (row.map Value.render) ++ ")"

def UnFn.render : UnFn → String
  | .not => "NOT" | .isNull => "IS_NULL" | .neg => "-" | .itof => "DOUBLE" | .fneg => "-."
  | .ffloor => "FLOOR" | .fceil => "CEIL" | .fround => "ROUND" | .froundTo d => s!"ROUND_{d}"
  | .ftoi => "BIGINT" | .narrow n => s!"INT{n}" | .itos => "VARCHAR" | .upper => "UPPER" | .lower => "LOWER"
  | .length => "LENGTH" | .regexMatch p => s!"REGEXP_MATCH_{p.quote}"
  | .datePart p => s!"DATE_PART_{p.name}" | .dateTrunc u => s!"DATE_TRUNC_{u.name}"
  | .toDate => "DATE"

def BinFn.render : BinFn → String
  | .add => "+" | .sub => "-" | .mul => "*" | .eq => "=" | .lt => "<"
  | .and => "AND" | .or => "OR" | .fadd => "+." | .fsub => "-." | .fmul => "*." | .fdiv => "/."
  | .idiv => "/" | .imod => "%" | .ipow => "^" | .fpow => "^."
  | .concat => "||" | .strpos => "STRPOS" | .startsWith => "STARTS_WITH"
  | .endsWith => "ENDS_WITH" | .like => "LIKE"
  | .substr n => s!"SUBSTRING_FOR_{(n.map toString).getD "ALL"}"
  | .trim l r => if l && r then "BTRIM" else if l then "LTRIM" else "RTRIM"

def Expr.render : Expr → String
  | .lit v => v.render
  | .field i => s!"${i}"
  | .un f a => s!"{f.render}({a.render})"
  | .bin f a b => s!"({a.render} {f.render} {b.render})"
  | .ifThen c t e => s!"IF {c.render} THEN {t.render} ELSE {e.render}"

def AggFn.name : AggFn → String
  | .count => "COUNT" | .sum | .fsum => "SUM" | .avg => "AVG" | .min => "MIN" | .max => "MAX"

def Measure.render (m : Measure) : String :=
  let filter := match m.filter with
    | some c => s!" FILTER (WHERE {c.render})"
    | none => ""
  s!"{m.fn.name}({if m.distinct then "DISTINCT " else ""}{m.arg.render}){filter}"

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
  | .aggregate r gs ms =>
      s!"Aggregate +[{", ".intercalate (ms.map Measure.render)}] GROUP BY [{", ".intercalate (gs.map Expr.render)}]"
        :: indent r.renderLines
where
  indent (ls : List String) : List String := ls.map ("  " ++ ·)
  key (k : SortKey) : String :=
    s!"${k.col}{if k.desc then " DESC" else ""}{if k.nullsFirst then " NULLS FIRST" else ""}"

def Rel.render (r : Rel) : String := "\n".intercalate r.renderLines

end Substrait
