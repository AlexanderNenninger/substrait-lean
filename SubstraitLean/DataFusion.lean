import SubstraitLean.Write

/-!
# DataFusion's writer

DataFusion is a tier-3 engine: sverify runs a plan there when its
Substrait consumer computes what `Rel.eval` computes, and refuses the plan
otherwise, naming DataFusion's bug (`upstream/bugs/DF-*.json`). This module is
DataFusion's whole path in Lean: what it refuses (`refusal`), the rewrite
its consumer needs (`Rel.splitJoins`), and the plan `--write-datafusion`
prints (`writePlan`). The core writer (`SubstraitLean/Write.lean`) knows
nothing of it. `python/src/sverify/datafusion_engine.py` does the rest: the
function names DataFusion's consumer knows, and the refusals that read the
written plan.

Such a plan does not parse back to the same `Rel`: `splitJoins` moves join
conjuncts, and integer sums are written over `DECIMAL(38,0)`.
-/

namespace Substrait

/-- Does the plan take a `MIN` or `MAX` of doubles (#371)? DataFusion's
grouped ones compare like IEEE 754 from `±f64::MAX` (a group of `+∞` has
`MIN` `f64::MAX`, and NaN is skipped). -/
def _root_.Substrait.Rel.floatExtremes (tables : Parse.Tables) : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => r.floatExtremes tables
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ =>
    a.floatExtremes tables || b.floatExtremes tables
  | .window r _ _ fns =>
    r.floatExtremes tables || fns.any fun
      | .agg m _ _ => (m.fn == .min || m.fn == .max) && m.arg.kind (r.kinds tables) == .float
      | _ => false
  | .aggregate r _ ms =>
    r.floatExtremes tables ||
      ms.any fun m => (m.fn == .min || m.fn == .max) && m.arg.kind (r.kinds tables) == .float

/-- Does the plan take a double `SUM`, an `AVG` or a `MIN` over a sliding
frame (one not from UNBOUNDED PRECEDING)? DataFusion slides a frame by
retracting the rows that leave it: a sum of doubles then rounds differently
from adding up the frame, an average of a frame that has become empty is NaN,
and a `MIN` of one with only NULLs left is the last minimum. -/
def _root_.Substrait.Rel.slidingFrames : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ | .aggregate r _ _ => r.slidingFrames
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => a.slidingFrames || b.slidingFrames
  | .window r _ _ fns =>
    r.slidingFrames || fns.any fun
      | .agg m _ fr => [AggFn.fsum, .avg, .iavg, .min].contains m.fn && fr.lo != .unboundedPreceding
      | _ => false

/-- Does the expression have a double operation that IEEE arithmetic lets
give `-0.0` or a negative NaN? DataFusion orders those apart from `0.0` and
NaN (`f64::total_cmp`, upstream/bugs/DF-13.json), so it gets no plans with
these. -/
def _root_.Substrait.Expr.signedDoubles : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a =>
    (match f with
      | .fneg | .ffloor | .fceil | .fround | .froundTo _ | .fmath _ => true
      | _ => false) || a.signedDoubles
  | .bin f a b =>
    (match f with
      | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow | .fatan2 | .flogb => true
      | _ => false) || a.signedDoubles || b.signedDoubles
  | .ifThen c t e => c.signedDoubles || t.signedDoubles || e.signedDoubles
  | .hof _ l b => l.signedDoubles || b.signedDoubles

/-- Does the expression wrap around or clamp (`overflow` = `SILENT` or
`SATURATE`, `UnFn.fit`, #241)? -/
def _root_.Substrait.Expr.fits : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a => (f matches .fit _ _) || a.fits
  | .bin _ a b => a.fits || b.fits
  | .ifThen c t e => c.fits || t.fits || e.fits
  | .hof _ l b => l.fits || b.fits

/-- Does the expression reach into a struct or a list, count a list, or take
a lambda (#94)? DataFusion 51 reads a reference into a value as a reference
into the row, its `cardinality([])` is NULL, and its consumer has no lambdas,
so it gets no plans with these. -/
def _root_.Substrait.Expr.nestedAccess : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a =>
    (match f with | .structField _ | .listElement _ | .cardinality | .flatten => true | _ => false) ||
      a.nestedAccess
  | .bin f a b =>
    (match f with | .listFn _ => true | _ => false) || a.nestedAccess || b.nestedAccess
  | .ifThen c t e => c.nestedAccess || t.nestedAccess || e.nestedAccess
  | .hof _ _ _ => true

namespace DataFusion

open Write (relKinds)

/-- The conjuncts of a condition. -/
def conjunctsOf : Expr → List Expr
  | .bin .and a b => conjunctsOf a ++ conjunctsOf b
  | e => [e]

/-- The conjunction of `cs`, if any. -/
def andAll : List Expr → Option Expr
  | [] => none
  | c :: cs => some ((andAll cs).elim c (.bin .and c ·))

/-- Does `e` read a field, and only fields `p` holds of? -/
def readsOnly (p : Nat → Bool) (e : Expr) : Bool :=
  -- (reads a field, all fields satisfy p), past `k` lambda parameters
  let rec go (k : Nat) : Expr → Bool × Bool
    | .lit _ => (false, true)
    | .field i => if i < k then (false, true) else (true, p (i - k))
    | .un _ a => go k a
    | .bin _ a b => let (x, y) := go k a; let (z, w) := go k b; (x || z, y && w)
    | .ifThen c t e =>
      let (x, y) := go k c; let (z, w) := go k t; let (u, v) := go k e; (x || z || u, y && w && v)
    -- A lambda's body reads its parameter, then the row (D28).
    | .hof _ l b => let (x, y) := go k l; let (z, w) := go (k + 1) b; (x || z, y && w)
  let (reads, all) := go 0 e
  reads && all

/-- `r`, filtered by the conjunction of `cs` (none: `r`). -/
def filterBy (r : Rel) (cs : List Expr) : Rel := match andAll cs with
  | none => r
  | some c => .filter r c

/-- The plan with each join's conjuncts over one input moved onto that input,
for DataFusion's consumer, which takes every `=` of a join condition for a key
pair across the inputs (#98, upstream/bugs/DF-19.json). The right input's
conjuncts become a filter on it, and in an inner join the left input's too.
In a left join the left input's decide the padding, so they stay, as
`CASE WHEN c THEN TRUE ELSE FALSE END`: the same in a join condition (NULL
and FALSE both do not match), and not an `=`. Each rewrite gives the rows
the join gives. -/
def splitJoins (cat : Catalog) : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (splitJoins cat r) c
  | .project r es => .project (splitJoins cat r) es
  | .emit r m => .emit (splitJoins cat r) m
  | .fetch r o c => .fetch (splitJoins cat r) o c
  | .window r p s f => .window (splitJoins cat r) p s f
  | .orderBy r ks => .orderBy (splitJoins cat r) ks
  | .distinct r => .distinct (splitJoins cat r)
  | .aggregate r gs ms => .aggregate (splitJoins cat r) gs ms
  | .unnest r c => .unnest (splitJoins cat r) c
  | .cross a b => .cross (splitJoins cat a) (splitJoins cat b)
  | .unionAll a b => .unionAll (splitJoins cat a) (splitJoins cat b)
  | .semi a b anti on => .semi (splitJoins cat a) (splitJoins cat b) anti on
  | .join a b ty on =>
    let n := a.arity cat
    let cs := conjunctsOf on
    let left := if ty matches .inner then cs.filter (readsOnly (· < n)) else []
    let right := cs.filter (readsOnly (n ≤ ·))
    let rest := (cs.filter fun c => !left.contains c && !right.contains c).map fun c =>
      if readsOnly (· < n) c then .ifThen c (.lit (.bool true)) (.lit (.bool false)) else c
    .join (filterBy (splitJoins cat a) left)
      (filterBy (splitJoins cat b) (right.map (·.mapFields (· - n)))) ty
      ((andAll rest).getD (.lit (.bool true)))

/-- Why DataFusion does not get the plan, if it does not: each refusal names
DataFusion's bug or the issue that tracks it. -/
def refusal (plan : Parse.Plan) : Option String :=
  let r := plan.root
  if r.anyExpr Expr.fits then
    some "overflow = SILENT or SATURATE is not supported on DataFusion (#241)"
  else if r.decimalOps then
    some "DataFusion does not compute decimals as the reference does (#27)"
  else if r.floatExtremes plan.tables then
    some "MIN and MAX of doubles are not supported on DataFusion (upstream/bugs/DF-15.json)"
  else if r.slidingFrames then
    some ("SUM of doubles, AVG and MIN over a sliding frame are not supported on DataFusion " ++
      "(upstream/bugs/DF-16.json); use a frame from UNBOUNDED PRECEDING")
  else if r.anyExpr Expr.signedDoubles then
    some ("DataFusion orders the -0.0 and NaN a double operation can give apart from 0.0 " ++
      "and NaN (upstream/bugs/DF-13.json)")
  else if r.anyExpr Expr.nestedAccess then
    some ("DataFusion does not run struct fields, list elements or cardinality as the " ++
      "reference does (#94, upstream/bugs/DF-20.json)")
  else none

/-- The plan as DataFusion runs it (`--write-datafusion`): join conjuncts
split (`splitJoins`), and integer sums over `DECIMAL(38,0)`, so that one
leaving 64 bits fails where DataFusion's own would wrap around
(upstream/bugs/DF-14.json). -/
def writePlan (plan : Parse.Plan) : Lean.Json :=
  Write.writePlan (Write.planSchemas plan) plan.catalog (splitJoins plan.catalog plan.root)
    plan.names (wideSums := true)

end DataFusion

end Substrait
