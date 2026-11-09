import Sverify.Analysis.Keys

/-!
# The values an open order allows, on concrete data (#679, D24)

A test oracle beside `Rel.eval`. Where a plan leaves the order of ties open
in an ordered aggregate (`FIRST`, `LAST`, `ARG_MIN`/`ARG_MAX`, `STRING_AGG`,
`collect`), `Rel.evalChoices` gives, for each cell such a measure makes, the
values every order allows (`Rel.OrderAllowed`): for a pick, the values of the
rows that tie at its end of the order; for `STRING_AGG` and `collect`, the
tie classes, each of which may come in any order. Comparisons of an
engine's rows (`sverify.testing.allows_rows`) then accept any of them.

Elsewhere it computes `Rel.eval`'s rows, where the data leaves no choice: a
window whose partitions have no ties, a `FETCH` that takes every row or
rows that do not tie. Where the data does leave a choice it cannot list
(ties in a window or at a `FETCH`, `MODE`, a `DISTINCT` measure, an
expression over an open cell), it gives `none`, and the caller compares
with `Rel.eval`'s rows.

Untrusted: no theorem connects it to `Rel.OrderAllowed`; the comparisons
it serves are tests.
-/

namespace Substrait

/-- What one cell of a result may be. -/
inductive TieChoice where
  /-- This value. -/
  | val (v : Value)
  /-- Any one of these values. -/
  | anyOf (vs : List Value)
  /-- `STRING_AGG` with this separator: the strings of each class, the
  classes in order, each class's strings in any order. -/
  | concat (sep : String) (classes : List (List Value))
  /-- `collect`: as `concat`, as a list. -/
  | collect (classes : List (List Value))
  deriving Inhabited

def TieChoice.exact? : TieChoice → Option Value
  | .val v => some v
  | _ => none

/-- Rows whose every cell is exact. -/
def exactRows (rows : List (List TieChoice)) : Option Relation :=
  rows.mapM (·.mapM TieChoice.exact?)

def toChoices (rows : Relation) : List (List TieChoice) := rows.map (·.map .val)

/-- The runs of rows that tie under `le` both ways, in order. -/
def tieRuns (le : Row → Row → Bool) : List Row → List (List Row)
  | [] => []
  | x :: xs =>
    match tieRuns le xs with
    | (y :: ys) :: rest => if le x y && le y x then (x :: y :: ys) :: rest else [x] :: (y :: ys) :: rest
    | _ => [[x]]

variable [Boxes.Ambient]
/-- The kept rows of a group in the measure's order, in classes of rows that
tie, each mapped to its non-NULL arguments; empty classes dropped. -/
def Measure.classes (m : Measure) (grp : Relation) : List (List Value) :=
  ((tieRuns (sortLe m.sort) ((m.kept grp).mergeSort (sortLe m.sort))).map fun run =>
    (run.map m.arg.eval).filter (· != .null)).filter (!·.isEmpty)

/-- What the measure may give over the group `grp`, for every order. -/
def Measure.choice (m : Measure) (grp : Relation) : Option TieChoice :=
  if m.fn.sorts = false then some (.val (m.eval grp)) else
  let cs := m.classes grp
  if cs.all (·.length ≤ 1) then some (.val (m.eval grp)) else
  if m.distinct then none else
  match m.fn with
  | .pick last => some (.anyOf ((if last then cs.getLast? else cs.head?).getD []))
  | .concat sep => some (.concat sep cs)
  | .collect => some (.collect cs)
  | _ => none

/-- Do two rows of one partition tie in the window's order? -/
def windowTies (part : List Nat) (sort : List SortKey) (rows : Relation) : Bool :=
  rows.any fun x =>
    (rows.filter fun y => samePart part x y && sortLe sort x y && sortLe sort y x).length > 1

/-- The rows of `r` on `cat`, with every choice its ordered aggregates leave
open on this data; `none` where the data leaves another choice. -/
def Rel.evalChoices (cat : Catalog) : Rel → Option (List (List TieChoice))
  | .aggregate r gs ms => do
    let rows ← exactRows (← r.evalChoices cat)
    let groups := if gs.isEmpty then [([], rows)] else
      (dedup (rows.map (groupKey gs))).map fun k => (k, groupRows gs rows k)
    groups.mapM fun (k, grp) => do
      let cells ← ms.mapM (·.choice grp)
      pure (k.map .val ++ cells)
  | .emit r m => do
    let rows ← r.evalChoices cat
    pure (rows.map fun row => m.map (row.getD · (.val .null)))
  | .project r es => do
    let rows ← r.evalChoices cat
    rows.mapM fun row =>
      match row.mapM TieChoice.exact? with
      | some vs => some (row ++ es.map fun e => .val (e.eval vs))
      | none => do
        -- A copied column keeps its choice; an expression over one has none.
        let extra ← es.mapM fun
          | .field i => some (row.getD i (.val .null))
          | _ => none
        pure (row ++ extra)
  -- The order of the rows is the caller's to compare.
  | .orderBy r keys => do
    let rows ← r.evalChoices cat
    match exactRows rows with
    | some vs => pure (toChoices (vs.mergeSort (sortLe keys)))
    | none => pure rows
  | .fetch r off cnt => do
    let rows ← exactRows (← r.evalChoices cat)
    let all := off = 0 && cnt.all (rows.length ≤ ·)
    let fixed := match r with
      | .orderBy _ keys => !(tieRuns (sortLe keys) rows).any (·.length > 1)
      | _ => false
    if all || fixed then pure (toChoices ((Rel.fetch (.values 0 rows) off cnt).eval cat)) else none
  | .window r part sort fns => do
    let rows ← exactRows (← r.evalChoices cat)
    if fns.all (WinFn.tieFree sort) || !windowTies part sort rows then
      pure (toChoices (windowEval part sort fns rows))
    else none
  | .filter r c => do
    let rows ← exactRows (← r.evalChoices cat)
    pure (toChoices (rows.filter fun row => (c.eval row).isTrue))
  | .distinct r => do
    pure (toChoices (dedup (← exactRows (← r.evalChoices cat))))
  | .unnest r c => do
    pure (toChoices ((← exactRows (← r.evalChoices cat)).flatMap (unnestRow c)))
  | .cross a b => do
    pure (toChoices (crossRows (← exactRows (← a.evalChoices cat)) (← exactRows (← b.evalChoices cat))))
  | .join a b .inner on => do
    let x ← exactRows (← a.evalChoices cat)
    let y ← exactRows (← b.evalChoices cat)
    pure (toChoices ((crossRows x y).filter fun row => (on.eval row).isTrue))
  | .join a b .left on => do
    let x ← exactRows (← a.evalChoices cat)
    let y ← exactRows (← b.evalChoices cat)
    pure (toChoices (x.flatMap (leftJoinRow on (b.arity cat) y)))
  | .unionAll a b => do
    pure (toChoices ((← exactRows (← a.evalChoices cat)) ++ (← exactRows (← b.evalChoices cat))))
  | .semi a b anti on => do
    let x ← exactRows (← a.evalChoices cat)
    let y ← exactRows (← b.evalChoices cat)
    pure (toChoices (x.filter fun row => hasMatch on y row != anti))
  | .read t => some (toChoices (cat t).rows)
  | .values _ rows => some (toChoices rows)

end Substrait
