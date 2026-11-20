import Sverify.Analysis.Safety

/-!
# The check of the assumed issues, as a plan (#2018, ruling 195)

An assumed issue (`Issue.assumed`: a `SUM` that leaves its type, an operation
on finite doubles that gives `±∞`) is a precondition on the data the job
checks before it runs (`Report.assumed`, `Rel.AssumedHold`). The reference
raises wherever the plan as written evaluates such an operation, whatever
sits above it (`Rel.HasIssue`). An engine evaluates lazily: it prunes a column
nothing reads, pushes a filter or a limit below a projection and skips one
side of a join whose other side is empty, so a guard inside the plan the
engine runs is a side effect it may never take.

The check is therefore a plan of its own, whose result is the verdict: one
row, with one column per site of an assumed issue, `1` where the issue occurs
on some row the site evaluates and `0` otherwise. Each column is an aggregate
without groups at the root, which every engine computes and returns.

* `Expr.assumedFlag p e`: a condition on a row that is `TRUE` exactly where
  evaluating `e` runs into the issue `p` (`Expr.issues`): a `CASE` counts the
  branch it takes, a lambda every element.
* `Rel.assumedSites p u r`: the sites where `Rel.HasIssue` looks for `p`, each a
  plan of rows and the flag over them: an operator's input (its loose input
  under a filter or join, `Rel.loose`), the groups of a `SUM` (summed in
  38 digits, which hold any 64-bit sum of fewer than `10¹⁹` rows), and the
  frames the plan's windows compute.
* `assumedCheck`: the sites of a list of issues as one plan, and the issue
  each column checks.

A theorem (the check passes only where `Rel.AssumedHold` holds) can follow;
the report and `Report._check_assumed` rest on the plan's output values,
never on an optimizer setting.
-/

namespace Substrait

variable [Boxes.Ambient]

/-- `TRUE` where `x` is a finite double: between `-∞` and `+∞` by canonical
codes, as `isFiniteCode (canon x)` (NaN's code is above `+∞`). -/
def Expr.finiteE (x : Expr) : Expr :=
  .bin .and (.bin .lt (.lit (.float FloatCode.negInf)) x) (.bin .lt x (.lit (.float FloatCode.posInf)))

/-- `TRUE` where `x` is `+∞` or `-∞` (`Value.isInf`). -/
def Expr.infE (x : Expr) : Expr :=
  .bin .or (.bin .eq x (.lit (.float FloatCode.posInf))) (.bin .eq x (.lit (.float FloatCode.negInf)))

/-- `TRUE` where every element of the list `x` is a finite double (a pair,
`covar`'s and `corr`'s input), as `finiteValue` has it. -/
def Expr.finitePairE (x : Expr) : Expr := .hof .allMatch x (Expr.field 0).finiteE

/-- `p ∨ q`, of optional conditions. -/
def orFlag : Option Expr → Option Expr → Option Expr
  | some p, some q => some (.bin .or p q)
  | some p, none | none, some p => some p
  | none, none => none

/-- The condition under which the call `e` (its operands already evaluated)
runs into the overflow to `±∞` itself (`UnFn.infIssue`, `BinFn.infIssue`,
`issueAll`: an error of the call comes first, so a double divided by zero is
not an overflow). None where `e` cannot overflow. -/
def Expr.infFlag : Expr → Option Expr
  | e@(.un (.fmath .exp) a) => some (.bin .and a.finiteE e.infE)
  | e@(.bin f a b) =>
    if f.makesInf then
      let base := Expr.bin .and (.bin .and a.finiteE b.finiteE) e.infE
      -- `fdiv` by a zero is a division by zero; IEEE division by a zero is
      -- `±∞` by the option's choice (D39), not an overflow.
      if f == .fdiv || f == .fdivIeee then
        some (.bin .and base (.un .not (.bin .eq b (.lit (.float 0)))))
      else some base
    else none
  | _ => none

/-- **Where evaluating `e` runs into `p`**, as `Expr.issues` finds it: the
operands' conditions, and the call's own where the call is `p`'s expression.
A `CASE` evaluates its condition and the branch it takes; a lambda's body runs
on every element of its list. Only overflows to `±∞` arise in an expression;
a `SUM` that leaves its type arises in an aggregate (`Rel.assumedSites`). -/
def Expr.assumedFlag (p : Issue × Expr) : Expr → Option Expr
  | .lit _ | .field _ => none
  | e@(.un _ a) => orFlag (a.assumedFlag p) (if p == (.infinite, e) then e.infFlag else none)
  | e@(.bin _ a b) =>
    orFlag (orFlag (a.assumedFlag p) (b.assumedFlag p))
      (if p == (.infinite, e) then e.infFlag else none)
  | .ifThen c t e => orFlag (c.assumedFlag p) <|
      match t.assumedFlag p, e.assumedFlag p with
      | none, none => none
      | ft, fe => some (.ifThen c (ft.getD (.lit (.bool false))) (fe.getD (.lit (.bool false))))
  | .hof _ l b => orFlag (l.assumedFlag p) ((b.assumedFlag p).map (.hof .anyMatch l ·))

/-- The scale of `m`'s argument (0 for an integer) and its unscaled integer. -/
def Measure.unscaledArg (m : Measure) : Nat × Expr :=
  match m.arg with
  | .un (.decimal _ sc) x => (sc, x)
  | a => (0, a)

/-- Can `m`'s `SUM` be summed in more digits than its own type has: an
integer `SUM` (64 bits), or a decimal one of fewer than 38 digits? A decimal
`SUM` of 38 digits cannot: the engines' widest decimal has 38, and the
engine's own sum of it raises where it leaves them. -/
def Measure.widens (m : Measure) : Bool :=
  match m.sumDigits with
  | some q => q < 38
  | none => true

/-- `m` summed in 38 digits where it widens (`Measure.widens`): its argument
as a `DECIMAL(38, s + 1)` of the same value (one more digit of scale, so that
no reader takes a wide decimal of scale 0 for the integer it holds,
`Parse.wideIntDecimal`). No `SUM` of fewer than `10¹⁸` 64-bit values leaves
it. -/
def Measure.wide (m : Measure) : Measure :=
  if m.widens then
    let (sc, x) := m.unscaledArg
    { m with arg := .un (.decimal 38 (sc + 1)) (.bin .dmul x (.lit (.int 10))) }
  else m

/-- `TRUE` where `s`, `m.wide`'s `SUM`, leaves the type of `m`'s own `SUM`
(`Measure.sumOk`): 64 bits for integers, the result's digits for decimals. -/
def Measure.sumOutE (m : Measure) (s : Expr) : Expr :=
  let up : Nat := if m.widens then 1 else 0
  let sc := m.unscaledArg.1 + up
  let (lo, hi) : Int × Int := match m.sumDigits with
    | some _ => (-m.sumMax, m.sumMax)
    | none => (FloatCode.minI64, FloatCode.maxI64)
  .bin .or (.bin .lt s (.lit (.dec sc (10 ^ up * lo)))) (.bin .lt (.lit (.dec sc (10 ^ up * hi))) s)

/-- `1` where none of `m`'s inputs is anything but a finite double (or a pair
of them), `0` where one is; NULL on a row the measure does not read. -/
def Measure.nonFiniteE (m : Measure) : Expr :=
  let fin := match m.fn with
    | .cov _ | .corr => m.arg.finitePairE
    | _ => m.arg.finiteE
  .ifThen (.un .isNull m.arg) (.lit .null) (.ifThen fin (.lit (.int 0)) (.lit (.int 1)))

/-- A site: rows, and the condition on each that says the issue occurs. -/
abbrev Site := Rel × Expr

/-- The site of the expressions `es` evaluated on the rows of `r`. -/
def exprSite (p : Issue × Expr) (r : Rel) (es : List Expr) : List Site :=
  match es.foldl (fun acc e => orFlag acc (e.assumedFlag p)) none with
  | some f => [(r, f)]
  | none => []

/-- The sites of the aggregates of `r` grouped by `gs` (`n` group columns,
the aggregate's output starting there): a `SUM` that leaves its type, summed
in 38 digits per group, and an aggregate of finite doubles that is `±∞`. -/
def aggSites (p : Issue × Expr) (r : Rel) (gs : List Expr) (ms : List Measure) : List Site :=
  let n := gs.length
  ms.flatMap fun m =>
    (if m.fn = .sum ∧ p = (.sumWraps, m.arg) then
      [(Rel.aggregate r gs [m.wide], m.sumOutE (.field n))] else []) ++
    (if m.fn.infAgg ∧ p = (.infinite, m.arg) then
      [(Rel.aggregate r gs [m, { fn := .max, arg := m.nonFiniteE, filter := m.filter }],
        .bin .and (Expr.field n).infE (.un .not (.bin .eq (.field (n + 1)) (.lit (.int 1)))))]
    else [])

/-- The same for a window's aggregates, per frame the plan computes (`k`
columns before the window's). The value a measure checks is projected as a
column below the window first, as the writers take a window's arguments. -/
def winSites (p : Issue × Expr) (r : Rel) (k : Nat) (part : List Nat) (sort : List SortKey) :
    List WinFn → List Site
  | [] => []
  | .agg m s fr :: fns =>
    (if m.fn = .sum ∧ p = (.sumWraps, m.arg) then
      [(Rel.window (.project r [m.wide.arg]) part sort [.agg { m with arg := .field k } s fr],
        m.sumOutE (.field (k + 1)))] else []) ++
    (if m.fn.infAgg ∧ p = (.infinite, m.arg) then
      [(Rel.window (.project r [m.arg, m.nonFiniteE]) part sort
          [.agg { m with arg := .field k } s fr,
            .agg { fn := .max, arg := .field (k + 1), filter := m.filter } s fr],
        .bin .and (Expr.field (k + 2)).infE (.un .not (.bin .eq (.field (k + 3)) (.lit (.int 1)))))]
    else []) ++ winSites p r k part sort fns
  | _ :: fns => winSites p r k part sort fns

/-- **The sites of `p` in `r`**, as `Rel.HasIssue` looks for it: filter and
join conditions on the loose input, projections on their input (its loose
input under a filter or a join, `u`), an aggregate's grouping expressions,
arguments and filters like a projection's, and its `SUM`s and aggregates of
doubles per group; a window's per frame. -/
def Rel.assumedSites (cat : Catalog) (p : Issue × Expr) : Bool → Rel → List Site
  | _, .read _ | _, .values _ _ => []
  | _, .filter r c => r.assumedSites cat p true ++ exprSite p r.loose [c]
  | u, .project r es =>
    r.assumedSites cat p u ++ exprSite p (if u then r.loose else r) es
  | u, .emit r _ | u, .fetch r _ _ | u, .orderBy r _ | u, .distinct r | u, .unnest r _ =>
    r.assumedSites cat p u
  | u, .window r part sort fns =>
    r.assumedSites cat p u ++ winSites p r (r.arity cat) part sort fns
  | u, .cross a b | u, .unionAll a b => a.assumedSites cat p u ++ b.assumedSites cat p u
  | _, .join a b _ on | _, .semi a b _ on =>
    a.assumedSites cat p true ++ b.assumedSites cat p true ++
      exprSite p (.cross a.loose b.loose) [on]
  | u, .aggregate r gs ms =>
    r.assumedSites cat p u ++
      exprSite p (if u then r.loose else r) (gs ++ ms.flatMap Measure.exprs) ++
      aggSites p r gs ms

/-- A site as one row: `1` where its condition holds on some row, else `0`
(`MAX` of nothing is NULL: no row, no issue). -/
def Site.verdict (s : Site) : Rel :=
  .aggregate s.1 [] [{ fn := .max, arg := .ifThen s.2 (.lit (.int 1)) (.lit (.int 0)) }]

/-- **The check of the issues `ps`** in the plan `r` as written: one row, one
column per site (`Site.verdict`), and for each column the index in `ps` of
the issue it checks. None where no issue has a site. -/
def assumedCheck (cat : Catalog) (r : Rel) (ps : List (Issue × Expr)) : Option (Rel × List Nat) :=
  match ps.zipIdx.flatMap fun (p, i) => (r.assumedSites cat p false).map (·, i) with
  | [] => none
  | (s, i) :: rest =>
    some (rest.foldl (fun acc (s', _) => .cross acc s'.verdict) s.verdict, i :: rest.map (·.2))

/-! ## Checks of the flags

`Expr.finiteE` and `Expr.infE` say what `isFiniteCode` and `Value.isInf` say,
on the reference's comparisons; a product that overflows is flagged, one of
`+∞` is not (no finite operands), nor one of finite doubles that stays
finite; a `CASE` flags the branch a row takes. -/

section
local instance : Boxes.Ambient := Boxes.Ambient.none

private def big : Value := .float (FloatCode.ofFloat 1e308)
private def ten : Expr := .lit (.float (FloatCode.ofFloat 10.0))
private def prod : Expr := .bin .fmul (.field 0) ten
private def flagOn (e : Expr) (row : Row) : Bool :=
  match e.assumedFlag (.infinite, prod) with
  | some f => (f.eval row).isTrue
  | none => false

#guard [big, .float FloatCode.posInf, .float FloatCode.negInf, .float FloatCode.nan, .null].map
  (fun v => ((Expr.field 0).finiteE.eval [v]).isTrue) == [true, false, false, false, false]
#guard [big, .float FloatCode.posInf, .float FloatCode.negInf, .float FloatCode.nan].map
  (fun v => ((Expr.field 0).infE.eval [v]).isTrue) == [false, true, true, false]
#guard flagOn prod [big] && !flagOn prod [.float FloatCode.posInf] &&
  !flagOn prod [.float (FloatCode.ofFloat 2.0)] && !flagOn prod [.null]
-- `CASE WHEN x < 1 THEN x * 10 ELSE 0`: the product is in the branch not taken.
#guard !flagOn (.ifThen (.bin .lt (.field 0) (.lit (.float (FloatCode.ofFloat 1.0)))) prod
  (.lit (.float 0))) [big]
#guard flagOn (.ifThen (.bin .lt (.lit (.float (FloatCode.ofFloat 1.0))) (.field 0)) prod
  (.lit (.float 0))) [big]

end

end Substrait
