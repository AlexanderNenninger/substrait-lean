import Sverify.Core.Robust
import Sverify.Core.Float
import Sverify.Core.Rel

/-!
# The margin check of a threshold on a double `SUM` (#929)

A filter `SUM(x) > t` over an aggregate keeps a group on an engine as on the
reference when the engine's sum is far enough from `t`, which the data
decides, not the plan. `Rel.marginCheck` writes the check as a plan of its
own: the filter's input aggregate with each group's `SUM(x)` (or `AVG(x)`), `COUNT(x)` and
`SUM(ABS(x))`, the groups that fail

  `|fl(v − t)| > fl(cₙ · fl(A + n · tiny))`, `cₙ = (8n + 16) · 2⁻⁵³`,

or have more than `2³²` values, and their count. A group with no values has a
NULL sum, which the filter drops on the reference and on every engine; the
check decides the others, whose `n ≥ 1` gives `mag xs ≥ tiny`, as
`StdModel.check_sound` needs. On an engine whose sums are
`StdModel.Summed` (its `sum_order` row), a count of `0` puts every group's
sum, in the check and in the sink alike, on the reference's side of `t`
(`StdModel.margin_check` in `float-bounds/FloatBounds/Margin.lean`): the
filter keeps the reference's groups.

The check runs on the same engine and the same inputs as the sink, before
it (`Report.run`). Its constants are an integer times a power of two, exact
in doubles; `|·|` is written with `fneg`, also exact. Which plan computes the
check is trusted, as the `epsilon` formulas are (`Epsilon.lean`): the
theorem is about the doubles, and `tests/test_margin.py` runs the check
against Python's arithmetic.
-/

namespace Substrait

/-- `|e|` of a double, exact. -/
def Expr.fabs (e : Expr) : Expr := .ifThen (.bin .lt e (.lit (.float (FloatCode.ofFloat 0.0)))) (.un .fneg e) e

/-- A double literal. -/
def Expr.dlit (f : Float) : Expr := .lit (.float (FloatCode.ofFloat f))

/-- A comparison of an aggregate's column `j` with a constant `t`, the
condition of a threshold filter: `(j, t)`. -/
def Expr.thresholdOf : Expr → Option (Nat × Expr)
  | .bin .lt (.field j) t | .bin .lt t (.field j) | .bin .eq (.field j) t | .bin .eq t (.field j) =>
    if t.cols.isEmpty then some (j, t) else none
  | .un .not c => c.thresholdOf
  | _ => none

/-- The check over `inner`, whose columns `s`, `s + 1`, `s + 2` hold the sum
or mean, `COUNT(x)` and `SUM(ABS(x))`, and whose arity is `k`: the difference
`v − t` and the margin are projected once, at `k` and `k + 1`, so that an
engine's SQL computes each once (a window's aggregate is not repeated), then
the groups (or rows) with a value whose sum or mean is within the margin of
`t`, or that have more than `2³²` values, are counted. A group with no values
(`n = 0`, its sum NULL) is not flagged: the filter drops it everywhere. -/
def marginCount (inner : Rel) (k s : Nat) (t : Expr) (avg : Bool) : Rel :=
  let n := Expr.un .itof (.field (s + 1))
  let c := Expr.bin .fmul (.bin .fadd (.bin .fmul (Expr.dlit 8.0) n) (Expr.dlit (if avg then 32.0 else 16.0)))
    (Expr.dlit (Float.scaleB 1.0 (-53)))
  let p := Expr.bin .fadd (.field (s + 2)) (.bin .fmul n (Expr.dlit (Float.scaleB 1.0 (-1022))))
  let m := Expr.bin .fmul c (if avg then .bin .fdiv p n else p)
  let d := Expr.bin .fsub (.field s) t
  let pass := Expr.bin .or (.bin .lt (.field (k + 1)) (.field k))
    (.bin .lt (.field (k + 1)) (.un .fneg (.field k)))
  let some := Expr.un .not (.bin .lt (.field (s + 1)) (.lit (.int 1)))
  let flag := Expr.bin .or (.bin .and some (.un .not pass))
    (.bin .lt (.lit (.int (2 ^ 32))) (.field (s + 1)))
  .aggregate (.filter (.project inner [d, m]) flag) [] [{ fn := .count, arg := .lit (.int 1) }]

/-- A threshold filter the margin check covers (#929): the check, the
filter input's column of the double aggregate (`col`), the threshold in the
filter input's columns (`thr`, a constant or an exact column), and whether
the aggregate is a window's (`win`, which needs `window_sum_algo` too). -/
structure MarginSite where
  check : Rel
  col : Nat
  thr : Expr
  win : Bool

/-- The two sides of a comparison. -/
def Expr.cmpSides : Expr → Option (Expr × Expr)
  | .bin .lt a b | .bin .eq a b => some (a, b)
  | .un .not c => c.cmpSides
  | _ => none

/-- Where column `j` of `r` comes from through emits, projections of
fields, filters and sorts: a window node and its output column. -/
def Rel.traceWin (cat : Catalog) : Rel → Nat → Option (Rel × Nat)
  | w@(.window ..), j => some (w, j)
  | .emit r m, j => m[j]?.bind (r.traceWin cat)
  | .project r es, j =>
    if j < r.arity cat then r.traceWin cat j
    else match es[j - r.arity cat]? with
      | some (.field k) => r.traceWin cat k
      | _ => none
  | .filter r _, j | .orderBy r _, j => r.traceWin cat j
  | _, _ => none

/-- The check of `x` against `y` in a filter over `i`: `x` a window's `SUM` or
`AVG` of a column over the whole partition, `y` a column of the window's
input. Per row, the partition's sum or mean against the row's `y`. -/
def marginWin (cat : Catalog) (i : Rel) (x y : Expr) : Option MarginSite := do
  let jx ← match x with | .field j => some j | _ => none
  let jy ← match y with | .field j => some j | _ => none
  let (w, a) ← i.traceWin cat jx
  let (w', b) ← i.traceWin cat jy
  guard (w == w')
  let (r, part, sort, fns) ← match w with
    | .window r part sort fns => some (r, part, sort, fns)
    | _ => none
  let n := r.arity cat
  guard (n ≤ a && b < n)
  let (m, s, frame) ← match fns[a - n]? with
    | some (.agg m s frame) => some (m, s, frame)
    | _ => none
  guard (frame.lo == .unboundedPreceding && frame.hi == .unboundedFollowing)
  guard ((m.fn == .fsum || m.fn == .avg) && !m.distinct && m.filter.isNone)
  let xi ← match m.arg with | .field xi => some xi | _ => none
  -- The frame is the whole partition, so any order gives its values; one by the
  -- partition's keys where the window has none (Spark's windows need one).
  let sort' := if sort.isEmpty then part.map fun p => ({ col := p } : SortKey) else sort
  let w2 := Rel.window r part sort' [.agg m s frame, .agg { fn := .count, arg := .field xi } s frame,
    .agg { fn := .fsum, arg := (Expr.field xi).fabs } s frame]
  some ⟨marginCount w2 (n + 3) n (.field b) (m.fn == .avg), jx, y, true⟩

/-- **The margin check of a threshold filter**: the count of the groups (or
rows, for a window's aggregate) that fail it, a plan of one row and one
column. A filter over an aggregate whose condition compares a double `SUM`
or `AVG` of a column (not `DISTINCT`, no `FILTER`) with a constant, or a
filter comparing a window's `SUM` or `AVG` over the whole partition with a
column of the window's input. `none` otherwise. -/
def Rel.marginSite (cat : Catalog) : Rel → Option MarginSite
  | .filter (.aggregate r gs ms) c => do
    let (j, t) ← c.thresholdOf
    guard (gs.length ≤ j)
    let m ← ms[j - gs.length]?
    guard ((m.fn == .fsum || m.fn == .avg) && !m.distinct && m.filter.isNone)
    let i ← match m.arg with
      | .field i => some i
      | _ => none
    let inner := Rel.aggregate r gs
      [m, { fn := .count, arg := .field i }, { fn := .fsum, arg := (Expr.field i).fabs }]
    some ⟨marginCount inner (gs.length + 3) gs.length t (m.fn == .avg), j, t, false⟩
  | .filter i c => do
    let (x, y) ← c.cmpSides
    (marginWin cat i x y).orElse fun _ => marginWin cat i y x
  | _ => none

/-- The check alone. -/
def Rel.marginCheck (cat : Catalog) (r : Rel) : Option Rel := (r.marginSite cat).map (·.check)

/-- What the margin check decides, for the report (#929): the conditions of
`StdModel.margin_check` it checks on each group. -/
def marginConditions : List String :=
  ["|SUM(x) − t| > (8n + 16) · 2⁻⁵³ · (SUM(|x|) + n · 2⁻¹⁰²²), computed in doubles",
   "n ≤ 2³² values", "n ≥ 1, or the group's sum is NULL and the filter drops it everywhere"]

/-- A double as a report prints it: an integer without its `.0`. -/
def fmtDouble (f : Float) : String :=
  if f == f.round && f.abs < 1.0e15 then
    (if f < 0 then "-" else "") ++ toString f.abs.toUInt64
  else toString f

/-- The margin checks of a plan's threshold filters, outermost first. -/
def Rel.marginChecks (cat : Catalog) : Rel → List Rel
  | r@(.filter i _) => (r.marginCheck cat).toList ++ i.marginChecks cat
  | .project i _ | .emit i _ | .fetch i _ _ | .window i .. | .orderBy i _ | .distinct i
  | .aggregate i _ _ | .unnest i _ => i.marginChecks cat
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ =>
    a.marginChecks cat ++ b.marginChecks cat
  | .read _ | .values _ _ => []

/-! ## Examples -/

private def exCat : Catalog := fun _ => ⟨2, []⟩

private def having (c : Expr) : Rel :=
  .filter (.aggregate (.read "orders") [.field 0] [{ fn := .fsum, arg := .field 1 }]) c

-- An `AVG` threshold has one too.
#guard (Rel.filter (.aggregate (.read "orders") [.field 0] [{ fn := .avg, arg := .field 1 }])
  (.bin .lt (Expr.dlit 50.0) (.field 1))).marginCheck exCat |>.isSome
-- `SUM(amount) > 1000`, `>=` and `=` have a check; a threshold on the key,
-- a `COUNT`, or a column on both sides has none.
#guard (having (.bin .lt (.un .itof (.lit (.int 1000))) (.field 1))).marginCheck exCat |>.isSome
#guard (having (.un .not (.bin .lt (.field 1) (Expr.dlit 1000.0)))).marginCheck exCat |>.isSome
#guard (having (.bin .eq (.field 1) (Expr.dlit 1000.0))).marginCheck exCat |>.isSome
#guard (having (.bin .lt (.lit (.int 3)) (.field 0))).marginCheck exCat |>.isNone
#guard (Rel.filter (.aggregate (.read "orders") [.field 0] [{ fn := .count, arg := .field 1 }])
  (.bin .lt (.lit (.int 3)) (.field 1))).marginCheck exCat |>.isNone
#guard (having (.bin .lt (.field 0) (.field 1))).marginCheck exCat |>.isNone
-- A row's value against its partition's mean, through the projection and
-- emit that put them side by side (`readings`: sensor, value).
#guard (Rel.filter (.emit (.window (.read "r") [0] []
  [.agg { fn := .avg, arg := .field 1 } [] ⟨false, .unboundedPreceding, .unboundedFollowing⟩]) [0, 1, 2])
  (.bin .lt (.field 2) (.field 1))).marginCheck exCat |>.isSome
-- A running mean (a frame that ends at the row) has none.
#guard (Rel.filter (.window (.read "r") [0] []
  [.agg { fn := .avg, arg := .field 1 } [] ⟨false, .unboundedPreceding, .preceding 0⟩])
  (.bin .lt (.field 2) (.field 1))).marginCheck exCat |>.isNone
-- A check for each threshold filter, nested ones included.
#guard ((Rel.project (having (.bin .lt (Expr.dlit 1.0) (.field 1))) []).marginChecks exCat).length == 1

end Substrait
