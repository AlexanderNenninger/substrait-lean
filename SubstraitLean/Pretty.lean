import SubstraitLean.Rel

/-! # Human-readable rendering of values, expressions and plans -/

namespace Substrait

def Value.render : Value → String
  | .null => "NULL"
  | .bool b => toString b
  | .int i => toString i
  | .str s => s.quote

def Row.render (row : Row) : String :=
  "(" ++ ", ".intercalate (row.map Value.render) ++ ")"

def UnFn.render : UnFn → String
  | .not => "NOT" | .isNull => "IS_NULL" | .neg => "-"

def BinFn.render : BinFn → String
  | .add => "+" | .sub => "-" | .mul => "*" | .eq => "=" | .lt => "<"
  | .and => "AND" | .or => "OR"

def Expr.render : Expr → String
  | .lit v => v.render
  | .field i => s!"${i}"
  | .un f a => s!"{f.render}({a.render})"
  | .bin f a b => s!"({a.render} {f.render} {b.render})"
  | .ifThen c t e => s!"IF {c.render} THEN {t.render} ELSE {e.render}"

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
where
  indent (ls : List String) : List String := ls.map ("  " ++ ·)

def Rel.render (r : Rel) : String := "\n".intercalate r.renderLines

end Substrait
