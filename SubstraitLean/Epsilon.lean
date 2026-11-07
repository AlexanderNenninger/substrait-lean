import SubstraitLean.ShardCheck
import SubstraitLean.Transfer

/-!
# The float tolerance of a plan's outputs (#444, #85)

A double `SUM` or `AVG` whose order an engine picks (`sum_order`, a choice
the reference leaves open, with the observation `{"floats": {"bound":
"plan"}}`) is within a per-plan bound of a result the reference allows. This
computes that bound per output column, from what the contract's
preconditions and row caps give (`Measure.abs`, `floatBound`):

* every order the reference allows (`FloatSums`: trees of additions in any
  order) and every order the engine profiles allow (`SEQUENTIAL`, `ANY`,
  `PAIRWISE`, DuckDB's constant run `fl(k · x)` as `SCALED_CONSTANT`, Kahan's
  compensated sum as `COMPENSATED`) gives a result within
  `sumTolScaled n B` (`avgTolScaled` for an `AVG`) of the exact one, for at
  most `n` values in `[-B, B]`;
* so the engine's result is within twice the bound of one the reference
  allows: `"abs"`, as a double, rounded up. `StdModel.epsilon_sum` and
  `StdModel.epsilon_avg` in `float-bounds/FloatBounds/Epsilon.lean` prove it;
* where the argument's values have one sign nothing cancels, and the bound
  is also relative (`relEps`): `"rel"`, `StdModel.epsilon_sum_rel` and, for a
  mean of values at least `2⁻¹⁰²²` in magnitude, `StdModel.epsilon_avg_rel`.

`"proved"` marks a bound those theorems cover (`provedEps`): the engines'
`sum_order` behaviours are among the proved ones, the plan has no
single-precision column (Polars sums `Float32` in single precision,
polars-sum-float), and the argument, its rows and its groups are the same on
every engine (`colEps`). That an engine's algorithm is the one its
behaviour names rests on its characterization (duckdb-sum-double,
polars-sum-float, polars-sum-float-streaming).

A column the bound does not carry over to (computed from a double measure
by an expression) has `"abs": null`, as has a measure whose argument or row
count is not bounded. -/

namespace Substrait.Epsilon

open Lean (Json toJson)
open ContractCheck ShardCheck Parse

/-- The aggregate under filters, projections, emits and sorts. -/
def findAggregate : Rel → Option (Rel × List Expr × List Measure)
  | .aggregate r gs ms => some (r, gs, ms)
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => findAggregate r
  | _ => none

/-- `n` scaled units (`FloatCode.scaled`: the value times `2¹⁰⁷⁴`) as a
double, rounded up: its top 53 bits, plus one where bits are dropped. -/
def unscale (n : Nat) : Float :=
  let k := n.log2
  if k ≤ 52 then Float.scaleB (Float.ofNat n) (-1074)
  else
    let sh := k - 52
    let m := n >>> sh
    let m := if m <<< sh == n then m else m + 1
    Float.scaleB (Float.ofNat m) ((sh : Int) - 1074)

/-- `n` scaled units as a double, rounded down: its top 53 bits. -/
def unscaleDown (n : Nat) : Float :=
  let k := n.log2
  if k ≤ 52 then Float.scaleB (Float.ofNat n) (-1074)
  else
    let sh := k - 52
    Float.scaleB (Float.ofNat (n >>> sh)) ((sh : Int) - 1074)

/-- A positive double as JSON, rounded up to 17 significant digits (Lean's
`toJson` of a `Float` keeps six decimals, which would round a bound down). -/
def upJson (f : Float) : Json :=
  if f ≤ 0 || f.isNaN || f.isInf then toJson f else
  let e : Int := (Float.floor (Float.log10 f)).toInt64.toInt
  let k : Int := 16 - e
  let scaled := if k ≥ 0 then f * Float.ofNat (10 ^ k.toNat) else f / Float.ofNat (10 ^ (-k).toNat)
  let m : Nat := (Float.ceil scaled).toUInt64.toNat + 1
  if k ≥ 0 then .num ⟨m, k.toNat⟩ else .num ⟨m * 10 ^ (-k).toNat, 0⟩

/-- A relative bound where the values cannot cancel (all `≥ 0`, or all `≤ 0`):
each order's result is within `γ = k·u/(1 − k·u)` of the exact one,
relatively, with `u = 2⁻⁵³` and `k` the number of roundings (Higham, §4.2), so
two results are within `2γ/(1 − γ)` of each other relative to either
(`StdModel.epsilon_sum_rel`, `epsilon_avg_rel`). Evaluated in doubles, the
formula's few roundings are covered by the factor `1.000001`. -/
def relEps (k : Nat) : Float :=
  let u : Float := Float.scaleB 1.0 (-53)
  let ku := Float.ofNat k * u
  let γ := ku / (1.0 - ku)
  2.0 * γ / (1.0 - γ) * 1.000001

/-- As `upJson`, `0` for zero. -/
def upJsonZ (f : Float) : Json := if f == 0.0 then toJson (0 : Nat) else upJson f

/-- The bound for a double measure over rows described by `env`, at most
`rows` of them: absolute, and relative where the values have one sign, with
whether the relative bound is one `epsilon_avg_rel` covers (an `AVG`'s
values at least `2⁻¹⁰²¹` in magnitude, so its decoded doubles and mean at
least `2⁻¹⁰²²`). -/
def measureEps (env : List AVal) (m : Measure) (rows : Option Nat) :
    Option (Float × Option (Float × Bool)) := do
  let a := m.arg.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let n ← rows
  let bs := max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs
  guard (n ≤ 2 ^ 32 ∧ bs ≤ 2 ^ 1474)
  let t := if m.fn = .avg then FloatCode.avgTolScaled n bs else FloatCode.sumTolScaled n bs
  let oneSign := 0 ≤ FloatCode.scaled lo || FloatCode.scaled hi ≤ 0
  let normal := (2 ^ 53 : Int) ≤ FloatCode.scaled lo || FloatCode.scaled hi ≤ -(2 ^ 53 : Int)
  let rel := if oneSign && n < 2 ^ 40 then
      some (relEps (if m.fn = .avg then n + 2 else n), m.fn ≠ .avg || normal)
    else none
  return (unscale (2 * t), rel)

/-! ## Per engine: the error carried through arithmetic

`epsilon` below is the summation order's share, the same for every engine.
`epsilonByEngine` carries it, and each engine's own per-operation error,
through the double arithmetic between the aggregates and the output, from
the ranges the preconditions give (#568's propagation, forward mode). With
`|a| ≤ ma`, `|b| ≤ mb`, the inputs' errors `εa`, `εb` and `t = 2⁻¹⁰²²`, the
rules of `float-bounds/FloatBounds/Propagate.lean`:

* `+`, `-`: `(εa + εb)(1 + u) + 2u (ma + mb + t)` (`rule_add`, `rule_sub`);
* `*`: `(ma εb + mb εa + εa εb)(1 + u) + 2u (ma mb + t)` (`rule_mul`);
* `/` by a divisor the same on both sides, `|b| ≥ lb > 0`:
  `(εa / lb)(1 + u) + 2u (ma / lb + t)` (`rule_div`); Polars's `/` by a
  literal multiplies by the reciprocal (`fl(x · fl(1/y))`,
  polars-scalar-divisor): `(εa / lb)(1 + u)² + (3u + u²)(ma / lb) +
  (u (1 + u)(ma + εa) + 2u) t` (`rule_div_recip`);
* `abs`, negation: `εa` (`rule_abs`); `FLOOR`, `CEIL`, `ROUND`: `εa + 1`
  (`rule_floor`, `rule_ceil`, `rule_round`); a cast to an integer: `εa + 2`
  (`rule_trunc`); `sqrt` of `a ≥ εa`: `Δ (1 + u) + 2u (√ha + t)`,
  `Δ = min(√εa, εa / (√(la − εa) + √la))` (`rule_sqrt`);
* a comparison is exact where the ranges, widened by `ε`, do not straddle
  (`rule_threshold`): a filter, `CASE` or key on it keeps the same rows;
* `exp a`, `a ≤ ha`: `εa · exp(ha + εa)(1 + 2u) + 4u (exp ha + t)`
  (`rule_exp`): the platform's `libm` on both sides, trusted to one ulp
  (`NativeLink.exp`);
* `+ - * /` and `sqrt` are correctly rounded on both engines, as are
  integer-to-double conversions (the characterization's round 5), so an
  operation on exact inputs is exact there, Polars's literal division aside;
* each engine's logarithms that differ from the reference's (Polars's
  `log10`, `log2` and `log(b)` are `ln / ln`, 2.1 ulp; DuckDB's `log(b, x)`
  1.4 ulp) are probed, not modelled, and the other elementary functions but `exp` are
  the platform's `libm` (macOS `tan` up to 2.4 ulp, glibc `cos` and `tan` far
  more near zeros of `cos`): unbounded here where an input is off, and their
  bounds are not proved.

Each rule holds where the exact results do not overflow, which `fits`
checks. A column's bound is proved (its flag) where every step is one of
these rules, the `SUM`s and `AVG`s it reads are proved (`provedOrders`), and
no filter, sort key, `DISTINCT` or group key reads a value that may differ
between engines. The formulas are evaluated in doubles: every term is
nonnegative, so each rounding is relative and the factor `1 + 2⁻⁴⁰` covers
them. -/

/-- The unit roundoff of a double. -/
def unitRound : Float := Float.scaleB 1.0 (-53)

/-- `2⁻¹⁰²²`, the least normal double: the underflow term of a rounding. -/
def tinyF : Float := Float.scaleB 1.0 (-1022)

/-- Below the largest finite double, with room: an exact result this large
does not overflow. -/
def fits (x : Float) : Bool := x ≤ 1.0e308

/-- The `sum_order` behaviours `float-bounds` proves the bound for:
`TreeSum` and Kahan's sum (`StdModel.Summed`). -/
def provedOrders : List String := ["SEQUENTIAL", "ANY", "PAIRWISE", "SCALED_CONSTANT", "COMPENSATED"]

/-- The engines `epsilon_by_engine` reports on, with their tables. -/
def epsEngines : List (String × ProfileTable) :=
  [("duckdb", Profile.duckdb.table {}), ("polars", Profile.polars.table)]

/-- Does every engine's `sum_order` give one of the proved orders? -/
def ordersProved : Bool :=
  epsEngines.all fun (_, t) => (t.allows "agg.fsum" "sum_order" []).all (provedOrders.contains ·)

/-- A bound on `|e|` from the preconditions, for a double expression. -/
def magOf (env : List AVal) (e : Expr) : Option Float := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  return unscale (max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs)

/-- An upper bound on `e` from the preconditions (`0` where it is negative). -/
def hiOf (env : List AVal) (e : Expr) : Option Float := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let hi ← b.hi
  let s := FloatCode.scaled hi
  return if s ≤ 0 then 0.0 else unscale s.natAbs

/-- The range of `e` from the preconditions, as doubles: the low end rounded
down, the high end up. -/
def rangeOf (env : List AVal) (e : Expr) : Option (Float × Float) := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let (l, h) := (FloatCode.scaled lo, FloatCode.scaled hi)
  let lf := if 0 ≤ l then unscaleDown l.natAbs else -unscale l.natAbs
  let hf := if 0 ≤ h then unscale h.natAbs else -unscaleDown h.natAbs
  return (lf, hf)

/-- `x < y` with room for the doubles' own rounding of both. -/
def clearlyBelow (x y : Float) : Bool :=
  x + (x.abs + y.abs) * Float.scaleB 1.0 (-40) + tinyF < y

/-- The least `|e|` from the preconditions, where `0` is outside its range. -/
def minAbsOf (env : List AVal) (e : Expr) : Option Float := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let (l, h) := (FloatCode.scaled lo, FloatCode.scaled hi)
  if 0 < l then return unscale l.natAbs
  else if h < 0 then return unscale h.natAbs
  else none

/-- A bound on `|e|`: from the preconditions, else from its operation (a
quotient by a divisor bounded away from 0, a logarithm of a finite double). -/
def resultMag (env : List AVal) (e : Expr) : Option Float :=
  (magOf env e).orElse fun _ => match e with
    | .bin .fdiv a b => do return (← magOf env a) / (← minAbsOf env b)
    | .un (.fmath .log10) _ => some 309.0
    | .un (.fmath .log2) _ => some 1075.0
    | _ => none

/-- An engine's own error at one call, beyond the reference's, relative to
`u` and the result's bound: its logarithms by `ln / ln` (Polars), DuckDB's
`log(b, x)`. Polars's `/` by a literal has its own rule (`exprEps`). -/
def opExtra (engine : String) : Expr → Option Float
  | .un (.fmath .log10) _ | .un (.fmath .log2) _ =>
    if engine == "polars" then some (2.0 * (2.1 + 1.0)) else some 0.0
  | .bin .flogb _ _ =>
    some (2.0 * ((if engine == "polars" then 2.1 else 1.4) + 1.0))
  | _ => some 0.0

/-- An operation the engines may compute otherwise than the reference, on
the same inputs, with no rule here: the platform's `libm` (`pow`, `atan2`,
`log(b, x)`, every elementary function but `sqrt` and `exp`), rounding to
decimals, decimal conversions and black boxes. Its error is probed or not
known, never proved. -/
def inexact : Expr → Bool
  | .bin .fpow _ _ | .bin .fatan2 _ _ | .bin .flogb _ _ | .bin (.bbox2 _) _ _ => true
  | .un (.fmath f) _ => f != .sqrt && f != .exp
  | .un (.froundTo _) _ | .un (.ftod _) _ | .un (.dtof _) _ | .un (.bbox _) _ => true
  | _ => false

/-- Exact on this engine, with a proof: the same value as the reference's. -/
def exactP : Option (Float × Bool) → Bool
  | some (e, p) => e == 0.0 && p
  | none => false

/-- How far an engine's value of `e` may be from the reference's, from the
columns' errors `cols` (`none`: not bounded), and whether a rule of
`Propagate.lean` proves it. -/
def exprEps (engine : String) (env : List AVal) (cols : List (Option (Float × Bool))) :
    Expr → Option (Float × Bool)
  | .lit _ => some (0.0, true)
  | .field i => cols.getD i none
  | .un .fneg a => exprEps engine env cols a
  | .un .itof a => (exprEps engine env cols a).bind fun (x, p) =>
    if x == 0.0 then some (0.0, p) else none
  | .bin .lt a b | .bin .eq a b => do
    -- `rule_threshold`: where the ranges, widened by `ε`, do not straddle, the
    -- comparison has one outcome on both sides.
    let (ea, pa) ← exprEps engine env cols a
    let (eb, pb) ← exprEps engine env cols b
    if ea == 0.0 && eb == 0.0 then return (0.0, pa && pb)
    let (la, ha) ← rangeOf env a
    let (lb, hb) ← rangeOf env b
    guard (clearlyBelow (ha + ea) (lb - eb) || clearlyBelow (hb + eb) (la - ea))
    return (0.0, pa && pb)
  | e@(.bin f a b) => do
    let (ea, pa) ← exprEps engine env cols a
    let (eb, pb) ← exprEps engine env cols b
    let u := unitRound
    let recip := engine == "polars" && (match f, b with | .fdiv, .lit _ => true | _, _ => false)
    match f with
    | .fadd | .fsub =>
      if ea == 0.0 && eb == 0.0 then return (0.0, pa && pb)
      let ma ← magOf env a
      let mb ← magOf env b
      guard (fits (ma + mb + ea + eb))
      return ((ea + eb) * (1.0 + u) + 2.0 * u * (ma + mb + tinyF), pa && pb)
    | .fmul =>
      if ea == 0.0 && eb == 0.0 then return (0.0, pa && pb)
      let ma ← magOf env a
      let mb ← magOf env b
      let d := ma * eb + mb * ea + ea * eb
      guard (fits (ma * mb + d))
      return (d * (1.0 + u) + 2.0 * u * (ma * mb + tinyF), pa && pb)
    | .fdiv =>
      guard (eb == 0.0)
      if ea == 0.0 && !recip then return (0.0, pa && pb)
      let lb ← minAbsOf env b
      match magOf env a with
      | some ma =>
        guard (fits (ma / lb + ea / lb))
        if recip then
          return (ea / lb * (1.0 + u) * (1.0 + u) + (3.0 * u + u * u) * (ma / lb)
            + (u * (1.0 + u) * (ma + ea) + 2.0 * u) * tinyF, pa && pb)
        return (ea / lb * (1.0 + u) + 2.0 * u * (ma / lb + tinyF), pa && pb)
      | none =>
        -- From the quotient's own bound: not a proved rule.
        let mq ← resultMag env e
        return (ea / lb + 2.0 * u * mq + (if recip then 3.0 * u * mq else 0.0), false)
    | _ =>
      let extra ← opExtra engine e
      if ea == 0.0 && eb == 0.0 && extra == 0.0 then return (0.0, pa && pb && !inexact e)
      guard (ea == 0.0 && eb == 0.0)
      return (extra * u * (← resultMag env e), false)
  | .un (.fmath .sqrt) a => do
    -- `rule_sqrt`: correctly rounded on both sides.
    let (ea, pa) ← exprEps engine env cols a
    if ea == 0.0 then return (0.0, pa)
    let (la, ha) ← rangeOf env a
    guard (la - ea ≥ 0.0)
    let s := Float.sqrt (la - ea) + Float.sqrt la
    let d1 := Float.sqrt ea
    let d := if s > 0.0 then min d1 (ea / s) else d1
    let u := unitRound
    return (d * (1.0 + u) + 2.0 * u * (Float.sqrt ha + tinyF), pa)
  | .un .ffloor a | .un .fceil a | .un .fround a => do
    -- `rule_floor`, `rule_ceil`, `rule_round`: a step of one.
    let (ea, pa) ← exprEps engine env cols a
    if ea == 0.0 then return (0.0, pa)
    return (ea + 1.0, pa)
  | .un .ftoi a => do
    -- `rule_trunc`: each side within one of its input.
    let (ea, pa) ← exprEps engine env cols a
    if ea == 0.0 then return (0.0, pa)
    return (ea + 2.0, pa)
  | .un (.fmath .exp) a => do
    -- `rule_exp`: the platform's `libm` on both sides, one ulp each.
    let (ea, pa) ← exprEps engine env cols a
    let ha ← hiOf env a
    let u := unitRound
    guard (ha + ea ≤ 709.0)
    return (ea * Float.exp (ha + ea) * (1.0 + 2.0 * u) + 4.0 * u * (Float.exp ha + tinyF), pa)
  | e@(.un _ a) => do
    let (ea, pa) ← exprEps engine env cols a
    let extra ← opExtra engine e
    if ea == 0.0 && extra == 0.0 then return (0.0, pa && !inexact e)
    if ea == 0.0 then return (extra * unitRound * (← resultMag env e), false)
    none
  | .ifThen c@(.bin .lt a (.lit (.int 0))) t@(.un .fneg a₁) f => do
    -- `abs` as the parser writes it: `rule_abs`, whatever the sign of `a`.
    if a₁ == a && f == a then
      let (ea, pa) ← exprEps engine env cols a
      return (ea, pa)
    let et ← exprEps engine env cols t
    let ef ← exprEps engine env cols f
    return (max et.1 ef.1, et.2 && ef.2 && exactP (exprEps engine env cols c))
  | .ifThen c t f => do
    let et ← exprEps engine env cols t
    let ef ← exprEps engine env cols f
    -- A condition that may differ between engines may pick the other branch.
    return (max et.1 ef.1, et.2 && ef.2 && exactP (exprEps engine env cols c))
  | .hof _ _ _ => none

/-- `cs` with every flag cleared where `ok` fails: rows or groups that may
differ between engines. -/
def keepIf (ok : Bool) (cs : List (Option (Float × Bool))) : List (Option (Float × Bool)) :=
  if ok then cs else cs.map (·.map fun (e, _) => (e, false))

/-- Each column's error on `engine`, and whether it is proved, for plans of
projections, filters, sorts and one aggregate over reads. -/
def colEps (engine : String) (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) : Rel → Option (List (Option (Float × Bool)))
  | .read t => some ((List.range (cat t).arity).map fun _ => some (0.0, true))
  | .values n _ => some ((List.range n).map fun _ => some (0.0, true))
  | .filter r c => (colEps engine cat A F T r).map fun cs =>
      keepIf (exactP (exprEps engine (r.aeval cat A F T) cs c)) cs
  | .orderBy r keys => (colEps engine cat A F T r).map fun cs =>
      keepIf (keys.all fun k => exactP (cs.getD k.col none)) cs
  | .distinct r => (colEps engine cat A F T r).map fun cs => keepIf (cs.all exactP) cs
  | .fetch r _ _ => colEps engine cat A F T r
  | .emit r m => (colEps engine cat A F T r).map fun cs => m.map (cs.getD · none)
  | .cross a b => do
    return (← colEps engine cat A F T a) ++ (← colEps engine cat A F T b)
  | .join a b _ on => do
    let cs := (← colEps engine cat A F T a) ++ (← colEps engine cat A F T b)
    let env := a.aeval cat A F T ++ b.aeval cat A F T
    return keepIf (exactP (exprEps engine env cs on)) cs
  | .semi a b _ on => do
    let ca ← colEps engine cat A F T a
    let cs := ca ++ (← colEps engine cat A F T b)
    let env := a.aeval cat A F T ++ b.aeval cat A F T
    return keepIf (exactP (exprEps engine env cs on)) ca
  | .unionAll a b => do
    let ca ← colEps engine cat A F T a
    let cb ← colEps engine cat A F T b
    return (ca.zip cb).map fun
      | (some (x, p), some (y, q)) => some (max x y, p && q)
      | _ => none
  | .window r part sort fns => (colEps engine cat A F T r).map fun cs =>
      -- The window functions' values are not bounded here; the input's are kept.
      keepIf ((part.all fun i => exactP (cs.getD i none)) &&
          sort.all fun k => exactP (cs.getD k.col none)) cs ++
        fns.map fun _ => none
  | .project r es => (colEps engine cat A F T r).map fun cs =>
      cs ++ es.map (exprEps engine (r.aeval cat A F T) cs)
  | .aggregate r gs ms => (colEps engine cat A F T r).map fun cs =>
      let env := r.aeval cat A F T
      let keys := gs.all fun g => exactP (exprEps engine env cs g)
      keepIf keys <| gs.map (fun _ => some (0.0, true)) ++ ms.map fun m => do
        let (ea, pa) ← exprEps engine env cs m.arg
        let pf := m.filter.all fun c => exactP (exprEps engine env cs c)
        match m.fn with
        | .fsum | .avg =>
          let (order, _) ← measureEps env m r.maxRows
          let n ← r.maxRows
          -- The order's bound is proved for the same doubles on both sides.
          return (order + (if m.fn = .avg then ea else Float.ofNat n * ea),
            ea == 0.0 && pa && pf && ordersProved)
        | .count => return (0.0, pf)
        | .min | .max => return (ea, pa && pf)
        | _ => if ea == 0.0 then some (0.0, false) else none
  | _ => none

/-- Does every filter, sort key, `DISTINCT`, grouping key and measure filter
of the plan read values that are the same on `engine` as on the reference,
or a comparison whose outcome is (`rule_threshold`)? Then the engine keeps
the same rows and groups, and the columns' bounds compare like with like. -/
def rowsExact (engine : String) (cat : Catalog) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) : Rel → Bool
  | .read _ | .values _ _ => true
  | .filter r c => rowsExact engine cat A F T r &&
      (colEps engine cat A F T r).any fun cs => exactP (exprEps engine (r.aeval cat A F T) cs c)
  | .orderBy r keys => rowsExact engine cat A F T r &&
      (colEps engine cat A F T r).any fun cs => keys.all fun k => exactP (cs.getD k.col none)
  | .distinct r => rowsExact engine cat A F T r &&
      (colEps engine cat A F T r).any fun cs => cs.all exactP
  | .fetch r _ _ | .emit r _ | .project r _ | .window r _ _ _ | .unnest r _ =>
    rowsExact engine cat A F T r
  | .cross a b | .unionAll a b => rowsExact engine cat A F T a && rowsExact engine cat A F T b
  | .join a b _ on | .semi a b _ on =>
    rowsExact engine cat A F T a && rowsExact engine cat A F T b &&
      match colEps engine cat A F T a, colEps engine cat A F T b with
      | some ca, some cb =>
        exactP (exprEps engine (a.aeval cat A F T ++ b.aeval cat A F T) (ca ++ cb) on)
      | _, _ => false
  | .aggregate r gs ms => rowsExact engine cat A F T r &&
      (colEps engine cat A F T r).any fun cs =>
        let env := r.aeval cat A F T
        gs.all (fun g => exactP (exprEps engine env cs g)) &&
          ms.all fun m => m.filter.all fun c => exactP (exprEps engine env cs c)

/-- Does the plan read or write a single-precision column? Polars sums
`Float32` in single precision (polars-sum-float), which no bound here covers. -/
def hasFp32 (tj : Json) : Bool := (tj.compress.splitOn "\"fp32\"").length > 1

/-- A computed bound as JSON, with the factor that covers its evaluation in
doubles. -/
def epsJson (e : Float) : Json := upJsonZ (e * (1.0 + Float.scaleB 1.0 (-40)))

/-- `"epsilon_by_engine"` of a `--contract` request: per engine and double
output column, how far the engine's value may be from one the reference
allows, `{"abs": …, "rel"?: …, "proved": {"abs": …, "rel"?: …}}` (`null`:
not bounded). `rel` is `abs` over the least magnitude the reference's value
may have, where its range leaves out zero: a difference of nearly equal
values loses it, as cancellation loses relative accuracy. -/
def epsilonByEngine (input : Json) (engines : List String) : Except String Json := do
  let some tj := (input.getObjVal? "transform").toOption | return Json.mkObj []
  let plan ← parseJsonPlan tj
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let tables : Tables := (plan :: requires).flatMap (·.tables)
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  let schemas : String → List AVal := fun t => match tables.lookup t with
    | some (_, s) => schemaEnv s
    | none => []
  let pre : List (String × List Expr) := requires.filterMap (·.root.colExprs cat)
  let preOf (t : String) : List Expr := (pre.filter (·.1 == t)).flatMap (·.2)
  let A := fun t => tableEnv (schemas t) (preOf t)
  let F := fun t => (preOf t).flatMap Expr.factsOf
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let root := plan.root.capReads caps
  let T := Rel.keyedWindows cat A F (fun _ => [])
  let kinds := (Write.relKinds (Write.planSchemas plan) cat plan.root).map Write.WKind.toKind
  let names := if plan.names.length == kinds.length then plan.names
    else (List.range kinds.length).map (s!"#{·}")
  let f32 := hasFp32 tj
  -- The least magnitude of each column, for the relative bound.
  let mins : List (Option Float) := (root.aeval cat A F T).map fun a => do
    guard a.intsOnly
    let b ← a.int
    let (l, h) := (FloatCode.scaled (← b.lo), FloatCode.scaled (← b.hi))
    if 0 < l then some (unscaleDown l.natAbs)
    else if h < 0 then some (unscaleDown h.natAbs) else none
  return Json.mkObj <| engines.map fun engine =>
    let cols := colEps engine cat A F T root
    (engine, Json.mkObj <| ((names.zip kinds).zipIdx.filter (·.1.2 == .float)).map
      fun ((name, _), i) => match cols.bind (·.getD i none) with
        | some (e, p) =>
          let p := p && !f32
          -- Relative to the reference's value, at least `m` in magnitude: a value
          -- near zero (cancellation) has no relative bound.
          match mins.getD i none with
          | some m => (name, Json.mkObj [("abs", epsJson e), ("rel", epsJson (e / m)),
              ("proved", Json.mkObj [("abs", toJson p), ("rel", toJson p)])])
          | none => (name, Json.mkObj [("abs", epsJson e),
              ("proved", Json.mkObj [("abs", toJson p)])])
        | none => (name, Json.mkObj [("abs", Json.null),
            ("proved", Json.mkObj [("abs", toJson false)])]))

/-- `"rows_exact"` of a `--contract` request: per engine, whether the plan
keeps the same rows and groups under each column's `ε` (`rowsExact`). Where
it may not, a route needs a shim or a precondition on the threshold. -/
def rowsExactByEngine (input : Json) (engines : List String) : Except String Json := do
  let some tj := (input.getObjVal? "transform").toOption | return Json.mkObj []
  let plan ← parseJsonPlan tj
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let tables : Tables := (plan :: requires).flatMap (·.tables)
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  let schemas : String → List AVal := fun t => match tables.lookup t with
    | some (_, s) => schemaEnv s
    | none => []
  let pre : List (String × List Expr) := requires.filterMap (·.root.colExprs cat)
  let preOf (t : String) : List Expr := (pre.filter (·.1 == t)).flatMap (·.2)
  let A := fun t => tableEnv (schemas t) (preOf t)
  let F := fun t => (preOf t).flatMap Expr.factsOf
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let root := plan.root.capReads caps
  let T := Rel.keyedWindows cat A F (fun _ => [])
  return Json.mkObj <| engines.map fun e => (e, toJson (rowsExact e cat A F T root))

/-- Why a window aggregate of doubles has no bound, and what lifts it. -/
def windowUnbounded : String :=
  "a window aggregate of doubles: no bound yet (#1032)"

/-- Does a window function give a double that may differ between engines: a
`SUM`, `AVG` or statistical aggregate of doubles over a frame (#1032)? -/
def openDouble : WinFn → Bool
  | .agg m _ _ => match m.fn with
    | .fsum | .avg | .var _ _ | .cov _ | .corr | .quantile true _ _ => true
    | _ => false
  | _ => false

/-- The output columns that read a window aggregate of doubles: a copy of
one, or a value computed from one (#1032). They have no bound here. -/
def windowCols (cat : Catalog) : Rel → List Bool
  | .read t => List.replicate (cat t).arity false
  | .values n _ => List.replicate n false
  | .filter r _ | .orderBy r _ | .fetch r _ _ | .distinct r | .unnest r _ => windowCols cat r
  | .emit r m => let s := windowCols cat r; m.map (s.getD · false)
  | .project r es => let s := windowCols cat r; s ++ es.map (reading s)
  | .window r _ _ fns => let s := windowCols cat r
    s ++ fns.map fun f => openDouble f || match f with
      | .agg m _ _ => reading s m.arg
      | .lag c _ _ | .lead c _ _ | .firstValue c _ _ | .lastValue c _ _ | .nthValue c _ _ _ =>
        s.getD c false
      | _ => false
  | .cross a b | .join a b _ _ => windowCols cat a ++ windowCols cat b
  | .semi a _ _ _ => windowCols cat a
  | .unionAll a b => (windowCols cat a).zipWith (· || ·) (windowCols cat b)
  | .aggregate r gs ms => let s := windowCols cat r
    gs.map (reading s) ++ ms.map fun m => reading s m.arg
where
  reading (s : List Bool) (e : Expr) : Bool := (ShardCheck.reads e).any (s.getD · false)

/-- `"epsilon"` of a `--contract` request: per output column of the
transformation that is a double `SUM` or `AVG`,
`{"abs": …, "rel"?: …, "proved": {"abs": …, "rel"?: …}}`.

The bounds are a conjunction: each holds on its own, so the engine's result
is within `abs` of a result the reference allows and also within `rel` of
it, and a tolerance that either bound meets is met.

`proved` says which bounds Lean proves (`StdModel.epsilon_sum`,
`epsilon_avg`, `epsilon_sum_rel`, `epsilon_avg_rel`): those whose measure
reads, on every engine, the same values in the same rows and groups as the
reference (`colEps`), in a plan without single-precision columns, where
every engine's `sum_order` is a proved order (`ordersProved`). -/
def epsilon (input : Json) : Except String Json := do
  let some tj := (input.getObjVal? "transform").toOption | return Json.mkObj []
  let plan ← parseJsonPlan tj
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let tables : Tables := (plan :: requires).flatMap (·.tables)
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  let schemas : String → List AVal := fun t => match tables.lookup t with
    | some (_, s) => schemaEnv s
    | none => []
  let pre : List (String × List Expr) := requires.filterMap (·.root.colExprs cat)
  let preOf (t : String) : List Expr := (pre.filter (·.1 == t)).flatMap (·.2)
  let A := fun t => tableEnv (schemas t) (preOf t)
  let F := fun t => (preOf t).flatMap Expr.factsOf
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let root := plan.root.capReads caps
  -- A column that reads a window aggregate of doubles has no bound (#1032).
  let wins := windowCols cat root
  let winNames := if plan.names.length == wins.length then plan.names
    else (List.range wins.length).map (s!"#{·}")
  let winCols := (winNames.zip wins).filterMap fun (name, w) =>
    if w then some (name, Json.mkObj [("abs", Json.null), ("why", toJson windowUnbounded)])
    else none
  let some (r, gs, ms) := findAggregate root | return Json.mkObj winCols
  let some (srcs, _) := colSrcs plan.root | return Json.mkObj winCols
  let T := Rel.keyedWindows cat A F (fun _ => [])
  let env := r.aeval cat A F T
  -- The measure's values, rows and groups are the same on every engine.
  let same (m : Measure) : Bool := !hasFp32 tj && ordersProved &&
    epsEngines.all fun (engine, _) => match colEps engine cat A F T r with
      | some cs => (m.arg :: gs ++ m.filter.toList).all fun e => exactP (exprEps engine env cs e)
      | none => false
  let doubles := (doubleIdx ms).filterMap (ms[·]?)
  let names := if plan.names.length == srcs.length then plan.names
    else (List.range srcs.length).map (s!"#{·}")
  let cols := (names.zip srcs).filterMap fun (name, src) => match src with
    | .bounded j => some (name, match doubles[j]?.bind fun m =>
          (measureEps env m r.maxRows).map (·, same m) with
        | some ((e, rel), p) => Json.mkObj ([("abs", upJson e)] ++
            (match rel with | some (r, _) => [("rel", upJson r)] | none => []) ++
            [("proved", Json.mkObj ([("abs", toJson p)] ++
              match rel with | some (_, pr) => [("rel", toJson (p && pr))] | none => []))])
        | none => Json.mkObj [("abs", Json.null)])
    | .unbounded => some (name, Json.mkObj [("abs", Json.null)])
    | _ => none
  return Json.mkObj (cols.filter (fun (n, _) => !winCols.any (·.1 == n)) ++ winCols)

/-! ## The dependency report of a contract

`Rel.reads` lists every option a plan's calls, aggregates, sorts and keys
meet, by syntax: it is what `Rel.transfer_of_transferB` covers. A contract
knows more, the columns' types and what the preconditions rule out, and its
`"depends"` leaves out the options the plan cannot meet:

* the keys' NaN and zeros (`rel.keys`), where no grouping or `DISTINCT` key
  is a double and no join compares doubles;
* `empty_group_aggregates`, where every `SUM` and `AVG` is grouped, without a
  filter, over an argument that cannot be NULL (a group then has a value);
* `avg_int_result`, where no `AVG` has an integer result (`AggFn.iavg`);
* a comparison's NaN and zeros options (`cmp`), where no comparison has a
  double side;
* `min_mod_neg_one`, where every integer `%`'s dividend is bounded above
  `-2⁶³` by the preconditions;
* a value-side or open option of an expression whose result reaches neither
  the output nor the rows kept (`liveReads`): a projected column nothing reads.
  An error-side option counts wherever it is met, since an engine may still
  compute such a column and raise. -/

/-- Every aggregate of a plan: its input, keys and measures. -/
def aggNodes : Rel → List (Rel × List Expr × List Measure)
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .distinct r | .unnest r _ => aggNodes r
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => aggNodes a ++ aggNodes b
  | .aggregate r gs ms => (r, gs, ms) :: aggNodes r

/-- The subexpressions of an expression (a lambda's body aside: its column is not the row's). -/
def subExprs : Expr → List Expr
  | e@(.lit _) | e@(.field _) => [e]
  | e@(.un _ a) => e :: subExprs a
  | e@(.bin _ a b) => e :: (subExprs a ++ subExprs b)
  | e@(.ifThen c t f) => e :: (subExprs c ++ subExprs t ++ subExprs f)
  | e@(.hof _ l _) => e :: subExprs l

/-- Does a comparison (`cmp`) compare doubles? -/
def cmpDouble (cols : List Kind) : Expr → Bool
  | .un f a => (Functions.rowOf (.un f)).any (·.group == "cmp") && a.kind cols == .float
  | .bin f a b => (Functions.rowOf (.bin f)).any (·.group == "cmp") &&
      (a.kind cols == .float || b.kind cols == .float)
  | _ => false

/-- Does a grouping, `DISTINCT` or join compare doubles as keys? -/
def doubleKeys (schemas : Write.Schemas) (cat : Catalog) : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _
  | .unnest r _ => doubleKeys schemas cat r
  | .distinct r => (kinds r).any (· == .float) || doubleKeys schemas cat r
  | .cross a b | .unionAll a b => doubleKeys schemas cat a || doubleKeys schemas cat b
  | .join a b _ on | .semi a b _ on =>
    (subExprs on).any (cmpDouble (kinds a ++ kinds b)) || doubleKeys schemas cat a ||
      doubleKeys schemas cat b
  | .aggregate r gs _ =>
    gs.any (fun g => g.kind (kinds r) == .float) || doubleKeys schemas cat r
where kinds (r : Rel) : List Kind := (Write.relKinds schemas cat r).map Write.WKind.toKind

/-- Each expression of a plan with its input columns' kinds and description. -/
def exprCtx (schemas : Write.Schemas) (cat : Catalog) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) : Rel → List (Expr × List Kind × List AVal)
  | .read _ | .values _ _ => []
  | .filter r c => (c, kinds r, r.aeval cat A F T) :: exprCtx schemas cat A F T r
  | .project r es => es.map (·, kinds r, r.aeval cat A F T) ++ exprCtx schemas cat A F T r
  | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r | .unnest r _ =>
    exprCtx schemas cat A F T r
  | .cross a b | .unionAll a b => exprCtx schemas cat A F T a ++ exprCtx schemas cat A F T b
  | .join a b _ on | .semi a b _ on =>
    (on, kinds a ++ kinds b, a.aeval cat A F T ++ b.aeval cat A F T) ::
      (exprCtx schemas cat A F T a ++ exprCtx schemas cat A F T b)
  | .aggregate r gs ms =>
    (gs ++ ms.flatMap fun m => m.arg :: m.filter.toList).map (·, kinds r, r.aeval cat A F T) ++
      exprCtx schemas cat A F T r
where kinds (r : Rel) : List Kind := (Write.relKinds schemas cat r).map Write.WKind.toKind

/-- May an integer `%` see `MIN % -1`: a dividend not bounded above `-2⁶³`? -/
def minModPossible (env : List AVal) : Expr → Bool
  | .bin .imod a _ => match ((a.absD env []).int).bind (·.lo) with
    | some lo => lo ≤ -(2 ^ 63 : Int)
    | none => true
  | _ => false

/-- The column a expression reads, by `ShardCheck.reads`. -/
abbrev colRefs (e : Expr) : List Nat := ShardCheck.reads e

/-- The options whose behaviour can reach the plan's output columns `live` or
decide which rows it keeps: those of the expressions computing live columns,
filters, join conditions, grouping keys, sort keys and `DISTINCT`; not those
of a projected column nothing reads. -/
def liveReads (cat : Catalog) : Rel → List Nat → List Read
  | .read _, _ | .values _ _, _ => []
  | .filter r c, live => c.reads ++ liveReads cat r (live ++ colRefs c)
  | .project r es, live =>
    let n := r.arity cat
    let used := es.zipIdx.filter fun (_, i) => live.contains (n + i)
    used.flatMap (·.1.reads) ++
      liveReads cat r (live.filter (· < n) ++ used.flatMap (colRefs ·.1))
  | .emit r m, live => liveReads cat r (live.filterMap (m[·]?))
  | .cross a b, live =>
    let na := a.arity cat
    liveReads cat a (live.filter (· < na)) ++ liveReads cat b ((live.filter (na ≤ ·)).map (· - na))
  | .unionAll a b, live => liveReads cat a live ++ liveReads cat b live
  | .join a b _ on, live | .semi a b _ on, live =>
    let na := a.arity cat
    let refs := live ++ colRefs on
    on.reads ++ joinReads ++ liveReads cat a (refs.filter (· < na)) ++
      liveReads cat b ((refs.filter (na ≤ ·)).map (· - na))
  | .fetch r _ _, live => liveReads cat r live
  | .window r _ _ fns, _ => fns.flatMap WinFn.reads ++ liveReads cat r (List.range (r.arity cat))
  | .orderBy r keys, live => sortReads keys ++ liveReads cat r (live ++ keys.map (·.col))
  | .distinct r, _ => keyReads ++ liveReads cat r (List.range (r.arity cat))
  | .unnest r c, live => liveReads cat r (live ++ [c])
  | .aggregate r gs ms, live =>
    let k := gs.length
    let used := ms.zipIdx.filter fun (_, i) => live.contains (k + i)
    gs.flatMap Expr.reads ++ (if gs.isEmpty then [] else keyReads) ++
      used.flatMap (Measure.reads ·.1) ++
      liveReads cat r (gs.flatMap colRefs ++
        used.flatMap fun (m, _) => colRefs m.arg ++ (m.filter.map colRefs).getD [])

/-- `"depends"` of a `--contract` request. -/
def depends (input : Json) : Except String Json := do
  let some tj := (input.getObjVal? "transform").toOption | return .null
  let plan ← parseJsonPlan tj
  let requires ← ((input.getObjValAs? (Array Json) "requires").toOption.getD #[]).toList.mapM
    parseJsonPlan
  let tables : Tables := (plan :: requires).flatMap (·.tables)
  let cat : Catalog := fun t => match tables.lookup t with
    | some (n, _) => ⟨n, []⟩
    | none => ⟨0, []⟩
  let schemas : String → List AVal := fun t => match tables.lookup t with
    | some (_, s) => schemaEnv s
    | none => []
  let pre : List (String × List Expr) := requires.filterMap (·.root.colExprs cat)
  let preOf (t : String) : List Expr := (pre.filter (·.1 == t)).flatMap (·.2)
  let A := fun t => tableEnv (schemas t) (preOf t)
  let F := fun t => (preOf t).flatMap Expr.factsOf
  let T := Rel.keyedWindows cat A F (fun _ => [])
  let aggs := aggNodes plan.root
  let keys := doubleKeys (Write.planSchemas plan) cat plan.root
  let empty := aggs.any fun (r, gs, ms) => ms.any fun m =>
    (m.fn = .sum || m.fn = .fsum || m.fn = .avg) &&
      (gs.isEmpty || m.filter.isSome || (m.arg.absD (r.aeval cat A F T) []).null)
  let iavg := aggs.any fun (_, _, ms) => ms.any (·.fn = .iavg)
  let ctx := exprCtx (Write.planSchemas plan) cat A F T plan.root
  let cmp := ctx.any fun (e, cols, _) => (subExprs e).any (cmpDouble cols)
  let minMod := ctx.any fun (e, _, env) => (subExprs e).any (minModPossible env)
  -- Error-side options count wherever they are met (an engine may evaluate a
  -- column nothing reads, and raise); the others where they reach the output.
  let live := liveReads cat plan.root (List.range (plan.root.arity cat))
  let raises (o : String) : Bool :=
    (Profile.reference.tools.find? (·.option == o)).any (·.tool == .raise)
  let reads := (plan.root.reads.filter fun p => raises p.2.1 || live.contains p).filter
    fun (g, o, _) =>
    !(g == "rel.keys" && !keys) && !(o == "empty_group_aggregates" && !empty) &&
      !(o == "avg_int_result" && !iavg) && !(g == "cmp" && !cmp) &&
      !(o == "min_mod_neg_one" && !minMod)
  return readsJson reads

end Substrait.Epsilon
