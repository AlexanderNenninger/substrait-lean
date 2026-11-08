import SubstraitLean.Robust
import SubstraitLean.Float
import SubstraitLean.Rel

/-!
# The margin check of a threshold on a double `SUM` (#929)

A filter `SUM(x) > t` over an aggregate keeps a group on an engine as on the
reference when the engine's sum is far enough from `t`, which the data
decides, not the plan. `Rel.marginCheck` writes the check as a plan of its
own: the filter's input aggregate with each group's `SUM(x)`, `COUNT(x)` and
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

/-- The check over `inner`, whose columns `s`, `s + 1`, `s + 2` hold the sum,
`COUNT(x)` and `SUM(ABS(x))`, and whose arity is `k`: the difference `v − t`
and the margin are projected once, at `k` and `k + 1`, so that an engine
computes each once, then the groups with a value whose sum is within the
margin of `t`, or that have more than `2³²` values, are counted. A group with
no values (`n = 0`, its sum NULL) is not flagged: the filter drops it
everywhere. -/
def marginCount (inner : Rel) (k s : Nat) (t : Expr) : Rel :=
  let n := Expr.un .itof (.field (s + 1))
  let c := Expr.bin .fmul (.bin .fadd (.bin .fmul (Expr.dlit 8.0) n) (Expr.dlit 16.0))
    (Expr.dlit (Float.scaleB 1.0 (-53)))
  let m := Expr.bin .fmul c (.bin .fadd (.field (s + 2)) (.bin .fmul n (Expr.dlit (Float.scaleB 1.0 (-1022)))))
  let d := Expr.bin .fsub (.field s) t
  let pass := Expr.bin .or (.bin .lt (.field (k + 1)) (.field k))
    (.bin .lt (.field (k + 1)) (.un .fneg (.field k)))
  let some := Expr.un .not (.bin .lt (.field (s + 1)) (.lit (.int 1)))
  let flag := Expr.bin .or (.bin .and some (.un .not pass))
    (.bin .lt (.lit (.int (2 ^ 32))) (.field (s + 1)))
  .aggregate (.filter (.project inner [d, m]) flag) [] [{ fn := .count, arg := .lit (.int 1) }]

/-- **The margin check of a threshold filter** over an aggregate: the count
of the groups that fail it, a plan of one row and one column. `none` where
the filter is not a comparison of a double `SUM` of a column (not `DISTINCT`,
no `FILTER`) with a constant. -/
def Rel.marginCheck : Rel → Option Rel
  | .filter (.aggregate r gs ms) c => do
    let (j, t) ← c.thresholdOf
    guard (gs.length ≤ j)
    let m ← ms[j - gs.length]?
    guard (m.fn == .fsum && !m.distinct && m.filter.isNone)
    let i ← match m.arg with
      | .field i => some i
      | _ => none
    let inner := Rel.aggregate r gs
      [m, { fn := .count, arg := .field i }, { fn := .fsum, arg := (Expr.field i).fabs }]
    some (marginCount inner (gs.length + 3) gs.length t)
  | _ => none

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
def Rel.marginChecks : Rel → List Rel
  | r@(.filter i _) => r.marginCheck.toList ++ i.marginChecks
  | .project i _ | .emit i _ | .fetch i _ _ | .window i .. | .orderBy i _ | .distinct i
  | .aggregate i _ _ | .unnest i _ => i.marginChecks
  | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => a.marginChecks ++ b.marginChecks
  | .read _ | .values _ _ => []

/-! ## Examples -/

private def having (c : Expr) : Rel :=
  .filter (.aggregate (.read "orders") [.field 0] [{ fn := .fsum, arg := .field 1 }]) c

-- `SUM(amount) > 1000`, `>=` and `=` have a check; a threshold on the key,
-- a `COUNT`, or a column on both sides has none.
#guard (having (.bin .lt (.un .itof (.lit (.int 1000))) (.field 1))).marginCheck.isSome
#guard (having (.un .not (.bin .lt (.field 1) (Expr.dlit 1000.0)))).marginCheck.isSome
#guard (having (.bin .eq (.field 1) (Expr.dlit 1000.0))).marginCheck.isSome
#guard (having (.bin .lt (.lit (.int 3)) (.field 0))).marginCheck.isNone
#guard (Rel.filter (.aggregate (.read "orders") [.field 0] [{ fn := .count, arg := .field 1 }])
  (.bin .lt (.lit (.int 3)) (.field 1))).marginCheck.isNone
#guard (having (.bin .lt (.field 0) (.field 1))).marginCheck.isNone
-- A check for each threshold filter, nested ones included.
#guard (Rel.project (having (.bin .lt (Expr.dlit 1.0) (.field 1))) []).marginChecks.length == 1

end Substrait
