import SubstraitLean.Write

/-!
# DataFusion's writer

DataFusion is a tier-3 engine: sverify runs a plan there when its
Substrait consumer computes what `Rel.eval` computes, and refuses the plan
otherwise, naming DataFusion's bug (`upstream/bugs/DF-*.json`). This module is
DataFusion's whole path in Lean: what it refuses (`refusal`), the rewrites its
consumer needs (`splitJoins`, `wideSums`), and the plan `--write-datafusion`
prints (`writePlan`). The core writer (`SubstraitLean/Write.lean`) knows
nothing of it. `python/src/sverify/datafusion_engine.py` does the rest: the
function names DataFusion's consumer knows, and the refusals that read the
written plan.

Each hook names its expiry: the upstream issue whose fix removes it, or the
DataFusion bug (`DF-*`) until one is filed, or sverify's issue that will
replace a refusal with a shim.

Such a plan does not parse back to the same `Rel`: `splitJoins` moves join
conjuncts, and `wideSums` sums integers as decimals.
-/

namespace Substrait.DataFusion

open Write (relKinds)

variable [Boxes.Ambient]
/-- Does the plan take a `MIN` or `MAX` of doubles (#371)? DataFusion's
grouped ones compare like IEEE 754 from `±f64::MAX` (a group of `+∞` has
`MIN` `f64::MAX`, and NaN is skipped; DF-15). Expires when DF-15 is fixed
upstream (not filed yet). -/
def floatExtremes (tables : Parse.Tables) : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => floatExtremes tables r
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ =>
    floatExtremes tables a || floatExtremes tables b
  | .window r _ _ fns =>
    floatExtremes tables r || fns.any fun
      | .agg m _ _ => (m.fn == .min || m.fn == .max) && m.arg.kind (r.kinds tables) == .float
      | _ => false
  | .aggregate r _ ms =>
    floatExtremes tables r ||
      ms.any fun m => (m.fn == .min || m.fn == .max) && m.arg.kind (r.kinds tables) == .float

/-- Does the plan take a double `SUM`, an `AVG` or a `MIN` over a sliding
frame (one not from UNBOUNDED PRECEDING)? DataFusion slides a frame by
retracting the rows that leave it, so a sum keeps an infinity that has left
(DF-16). Expires with apache/datafusion#26222. -/
def slidingFrames : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _ | .distinct r
  | .unnest r _ | .aggregate r _ _ => slidingFrames r
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => slidingFrames a || slidingFrames b
  | .window r _ _ fns =>
    slidingFrames r || fns.any fun
      | .agg m _ fr => [AggFn.fsum, .avg, .iavg, .min].contains m.fn && fr.lo != .unboundedPreceding
      | _ => false

/-- Does the expression have a double operation that IEEE arithmetic lets
give `-0.0` or a negative NaN? DataFusion orders those apart from `0.0` and
NaN (`f64::total_cmp`, DF-13). Expires with apache/datafusion#26138. -/
def signedDoubles : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a =>
    (match f with
      | .fneg | .ffloor | .fceil | .fround | .froundTo _ | .fmath _ => true
      | _ => false) || signedDoubles a
  | .bin f a b =>
    (match f with
      | .fadd | .fsub | .fmul | .fdiv | .fmod | .fpow | .fatan2 | .flogb => true
      | _ => false) || signedDoubles a || signedDoubles b
  | .ifThen c t e => signedDoubles c || signedDoubles t || signedDoubles e
  | .hof _ l b => signedDoubles l || signedDoubles b

/-- Does the expression truncate to a week or longer, truncate a date, or bin
timestamps? DataFusion computes those in nanoseconds, which fail (or, on 51,
give a wrong date) outside ±2⁶³ ns (DF-17), where the reference's timestamps
reach 0001 to 9999 (D32). Expires when DF-17 is fixed upstream (not filed
yet). -/
def nanoCalendar : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a =>
    (match f with
      | .dateTrunc u => u.calendar
      | .dayTrunc _ | .bucket _ _ => true
      | _ => false) || nanoCalendar a
  | .bin _ a b => nanoCalendar a || nanoCalendar b
  | .ifThen c t e => nanoCalendar c || nanoCalendar t || nanoCalendar e
  | .hof _ l b => nanoCalendar l || nanoCalendar b

/-- Does the expression wrap around or clamp (`overflow` = `SILENT` or
`SATURATE`, `UnFn.fit`)? Expires with #241, the shim that writes them. -/
def fits : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a => (f matches .fit _ _) || fits a
  | .bin _ a b => fits a || fits b
  | .ifThen c t e => fits c || fits t || fits e
  | .hof _ l b => fits l || fits b

/-- Does the expression reach into a struct or a list, count a list, or take
a lambda? DataFusion's consumer has no `ListElement` reference and no lambdas
(DF-20), and on 51 its `cardinality([])` is NULL. Expires when DF-20 is fixed
upstream (not filed yet) and sverify pins DataFusion 55 (#94). -/
def nestedAccess : Expr → Bool
  | .lit _ | .field _ => false
  | .un f a =>
    (match f with | .structField _ | .listElement _ | .cardinality | .flatten => true | _ => false) ||
      nestedAccess a
  | .bin f a b =>
    (match f with | .listFn _ => true | _ => false) || nestedAccess a || nestedAccess b
  | .ifThen c t e => nestedAccess c || nestedAccess t || nestedAccess e
  | .hof _ _ _ => true

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
the join gives. Expires when DF-19 is fixed upstream (not filed yet). -/
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

/-- The plan with each aggregate's integer `SUM` summed as `DECIMAL(38,0)` and
cast back to `BIGINT` by a project above it: DataFusion's integer `SUM` wraps
around past 64 bits (DF-14), and the cast back fails there, where the
reference raises. The sum is the same (38 digits hold any sum of 64-bit
integers that fits back). Expires with apache/datafusion#3520. -/
def wideSums : Rel → Rel
  | .read t => .read t
  | .values n rows => .values n rows
  | .filter r c => .filter (wideSums r) c
  | .project r es => .project (wideSums r) es
  | .emit r m => .emit (wideSums r) m
  | .fetch r o c => .fetch (wideSums r) o c
  | .window r p s f => .window (wideSums r) p s f
  | .orderBy r ks => .orderBy (wideSums r) ks
  | .distinct r => .distinct (wideSums r)
  | .unnest r c => .unnest (wideSums r) c
  | .cross a b => .cross (wideSums a) (wideSums b)
  | .unionAll a b => .unionAll (wideSums a) (wideSums b)
  | .join a b ty on => .join (wideSums a) (wideSums b) ty on
  | .semi a b anti on => .semi (wideSums a) (wideSums b) anti on
  | .aggregate r gs ms =>
    let sums := (ms.zipIdx.filter fun (m, _) => m.fn matches .sum).map (gs.length + ·.2)
    if sums.isEmpty then .aggregate (wideSums r) gs ms else
      let ms' := ms.map fun m =>
        if m.fn matches .sum then { m with arg := .un (.decimal 38 0) m.arg } else m
      let n := gs.length + ms.length
      let cols := (List.range n).map fun j => match sums.idxOf? j with
        | some k => n + k
        | none => j
      .emit (.project (.aggregate (wideSums r) gs ms') (sums.map (.un (.dtrunc 0) <| .field ·))) cols

/-- Why DataFusion does not get the plan, if it does not: each refusal names
DataFusion's bug or the issue that tracks it. -/
def refusal (plan : Parse.Plan) : Option String :=
  let r := plan.root
  if r.anyExpr fits then
    some "overflow = SILENT or SATURATE is not supported on DataFusion (#241)"
  else if r.decimalOps then
    -- Expires with #27's decimal facts for DataFusion.
    some "DataFusion does not compute decimals as the reference does (#27)"
  else if floatExtremes plan.tables r then
    some "MIN and MAX of doubles are not supported on DataFusion (upstream/bugs/DF-15.json)"
  else if slidingFrames r then
    some ("SUM of doubles, AVG and MIN over a sliding frame are not supported on DataFusion " ++
      "(upstream/bugs/DF-16.json); use a frame from UNBOUNDED PRECEDING")
  else if r.anyExpr signedDoubles then
    some ("DataFusion orders the -0.0 and NaN a double operation can give apart from 0.0 " ++
      "and NaN (upstream/bugs/DF-13.json)")
  else if r.anyExpr nanoCalendar then
    some ("DataFusion truncates to a week or longer, truncates dates and bins timestamps in " ++
      "nanoseconds, outside the reference's timestamps (upstream/bugs/DF-17.json)")
  else if r.anyExpr nestedAccess then
    some ("DataFusion does not run struct fields, list elements or cardinality as the " ++
      "reference does (#94, upstream/bugs/DF-20.json)")
  else none

/-- The plan as DataFusion runs it (`--write-datafusion`): join conjuncts
split (`splitJoins`) and integer sums over decimals (`wideSums`), written by
the core writer. -/
def writePlan (plan : Parse.Plan) : Lean.Json :=
  let cat := plan.catalog
  Write.writePlan (Write.planSchemas plan) cat (wideSums (splitJoins cat plan.root)) plan.names

end Substrait.DataFusion
