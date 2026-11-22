import SubstraitLean.ShardCheck
import SubstraitLean.EngineTables
import Sverify.Core.MarginCheck
import Sverify.Analysis.AsofExact
import Sverify.Core.ExactBound

/-!
# The float tolerance of a plan's outputs (#444, #85)

A double `SUM` or `AVG` is, in the reference, the exact sum or mean rounded
once (D25, `floatSumCR`). An engine adds in an order of its own
(`sum_order`, with the observation `{"floats": {"bound": "plan"}}`), so its
result is within a per-plan bound of the reference's. This computes that
bound per output column, from what the contract's preconditions and row caps
give (`Measure.abs`, `floatBound`):

* every order the engine profiles allow (`SEQUENTIAL`, `ANY`, `PAIRWISE`,
  DuckDB's constant run `fl(k · x)` as `SCALED_CONSTANT`, Kahan's
  compensated sum as `COMPENSATED`) gives a result within
  `sumTolScaled n B` (`avgTolScaled` for an `AVG`) of the exact one, for at
  most `n` values in `[-B, B]`;
* the reference's value is within `u = 2⁻⁵³` of the exact one, relatively
  (`FloatCode.ofExact_rel`), so at most `u · n · B` (`u · B` for a mean);
* so the engine's result is within the sum of the two: `"abs"`, as a
  double, rounded up. `StdModel.epsilon_sum_cr` and `StdModel.epsilon_avg_cr`
  in `float-bounds/FloatBounds/Epsilon.lean` prove it;
* a `SUM` or `AVG` of converted integers (`itof e`) with `N · max M 1 ≤ 2⁵²`
  adds exactly on every engine and in every order, and a mean divides once
  as the reference does: tolerance `0`, proved (`intMeanExact`,
  `SumOrder.int_exact`, `AvgOrder.int_exact`; D35 amended 2026-11-19);
* an integer or decimal `SUM` whose argument's range and proved row cap keep
  it inside its type (`Measure.sumFits`) is outside the `overflow` option's
  scope (D34), so every engine gives the reference's exact value: tolerance
  `0`, proved by `Measure.sumFits_sound` (ruling 197);
* where the argument's values have one sign nothing cancels, and the bound
  is also relative (`relEps`): `"rel"`, `StdModel.epsilon_sum_rel` and, for a
  mean of values at least `2⁻¹⁰²²` in magnitude, `StdModel.epsilon_avg_rel`,
  between two orders, which covers the reference's value too (`u ≤ γ n`).

`"proved"` marks a bound those theorems cover (`provedEps`): the engines'
`sum_order` behaviours are among the proved ones, the plan has no
single-precision column (Polars sums `Float32` in single precision,
polars-sum-float-streaming), and the argument, its rows and its groups are the same on
every engine (`colEps`). That an engine's algorithm is the one its
behaviour names rests on its characterization (duckdb-sum-double,
polars-sum-float, polars-sum-float-streaming).

A column the bound does not carry over to (computed from a double measure
by an expression) has `"abs": null`, as has a measure whose argument or row
count is not bounded. -/

namespace Substrait.Epsilon

open Lean (Json toJson)
open ContractCheck ShardCheck Parse ExactBound

/-- The aggregate under filters, projections, emits and sorts. -/
def findAggregate : Rel → Option (Rel × List Expr × List Measure)
  | .aggregate r gs ms => some (r, gs, ms)
  | .filter r _ | .project r _ | .emit r _ | .orderBy r _ => findAggregate r
  | _ => none

/-- A relative bound where the values cannot cancel (all `≥ 0`, or all `≤ 0`):
each order's result is within `γ = k·u/(1 − k·u)` of the exact one,
relatively, with `u = 2⁻⁵³` and `k` the number of roundings (Higham, §4.2), so
two results are within `2γ/(1 − γ)` of each other relative to either
(`StdModel.epsilon_sum_rel`, `epsilon_avg_rel`). -/
def relEps (k : Nat) : Rat :=
  let ku := (k : Rat) * unitRound
  let γ := ku / (1 - ku)
  2 * γ / (1 - γ)

variable [Boxes.Ambient]
/-- A `SUM` or `AVG` of converted integers that every engine computes
exactly (#1608 12b-1): the argument is `itof e`, `e`'s values at most `M`
in magnitude, at most `N` rows, and `N · max M 1 ≤ 2⁵²`. Then the values'
`Σ |xᵢ| ≤ 2⁵³` and every order adds exactly (`SumOrder.int_exact`), and a
mean divides once as the reference does (`AvgOrder.int_exact`), whatever
the engine's `sum_order` behaviour. -/
def intMeanExact (env : List AVal) (m : Measure) (rows : Option Nat) : Bool :=
  match m.arg, rows with
  | .un .itof e, some n => match (e.absD env []).int with
    | some ⟨some lo, some hi⟩ => n * max (max lo.natAbs hi.natAbs) 1 ≤ 2 ^ 52
    | _ => false
  | _, _ => false

/-- The bound for a double measure over rows described by `env`, at most
`rows` of them: absolute, and relative where the values have one sign, with
whether the relative bound is one `epsilon_avg_rel` covers (an `AVG`'s
values at least `2⁻¹⁰²¹` in magnitude, so its decoded doubles and mean at
least `2⁻¹⁰²²`). Outside `intMeanExact`'s case it gives no bound over more than
`2³²` rows: a `SUM` or `AVG` of a double column under a larger row cap is
unbounded (`test_a_double_sum_over_more_than_2_32_rows_has_no_bound`). -/
def measureEps (env : List AVal) (m : Measure) (rows : Option Nat) :
    Option (Rat × Option (Rat × Bool)) := do
  if intMeanExact env m rows then return (0, some (0, true))
  let a := m.arg.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let n ← rows
  let bs := max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs
  guard (n ≤ 2 ^ 32 ∧ bs ≤ 2 ^ 1474)
  -- The engine's order from the exact value, then the reference's rounding.
  let t := if m.fn = .avg then FloatCode.avgTolScaled n bs + FloatCode.ceilDiv bs (2 ^ 53)
    else FloatCode.sumTolScaled n bs + FloatCode.ceilDiv (n * bs) (2 ^ 53)
  let oneSign := 0 ≤ FloatCode.scaled lo || FloatCode.scaled hi ≤ 0
  let normal := (2 ^ 53 : Int) ≤ FloatCode.scaled lo || FloatCode.scaled hi ≤ -(2 ^ 53 : Int)
  let rel := if oneSign && n < 2 ^ 40 then
      some (relEps (if m.fn = .avg then n + 2 else n), m.fn ≠ .avg || normal)
    else none
  return (unscale t, rel)

/-- The largest magnitude `B ≤ 2³⁹⁸` of the doubles `e` gives, from its range. -/
def doubleMag (env : List AVal) (e : Expr) : Option Rat := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  -- Finite codes only (`FloatCode.IsFin`): an infinite end has no magnitude.
  guard (FloatCode.negInf < lo && lo < FloatCode.posInf && FloatCode.negInf < hi && hi < FloatCode.posInf)
  let x := max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs
  guard (x ≤ 2 ^ (398 + 1074))
  return unscale x

/-- The bound of a statistical aggregate over at most `rows` values (D30),
`n` of them, `d` the divisor (`n − 1` of a sample, `n` of a population),
`u = 2⁻⁵³`, `t = 2⁻¹⁰²²`:

* `VAR_*` of doubles in `[-B, B]`: an engine's algorithm is within `varTol`
  of the exact `V = S / d` (`core_var_chan`), the reference's value within
  `u · V` of it (`epsilon_var_cr`). With `Q' ≤ n (B + t)²`,
  `√(Q' S) ≤ n (B + t) B` and `V ≤ n B² / d`.
* `STDDEV_*`: an engine's `fl(√v̂)` within `√τ + u (√V + √τ) + 2u t + u √V`
  of the reference's root rounded once (`epsilon_stddev_cr`), `τ` the
  variance's bound above, since `|√a − √b| ≤ √|a − b|`.
* `COVAR_*` of pairs in `[-Bx, Bx] × [-By, By]` (the pair's two sides): an
  engine is within `covTol` of `C / d` (`core_cov_chan`), the reference
  within `u · |C / d|` (`epsilon_cov_cr`), with `r₁ = n (Bx + t) By`,
  `r₂ = n (By + t) Bx`, `r_s = n Bx By ≥ |C|`, `r_q = n (Bx + t)(By + t)`.
* `CORR`: none, by D30's decision. Its error grows as a side's variance
  shrinks, and the ranges give no lower bound on it; `core_corr_chan` bounds
  it under a stated lower bound `L` on both co-moments, which waits for
  preconditions on aggregates (#918). `[-1, 1]` holds regardless.

`COVAR_*`'s constants are `t` (`Stat.StatTol`, ruling 271), `VAR_*`'s the
same for every algorithm. Evaluated exactly (`ExactBound`), the square roots
rounded up. -/
def statEps (t : Stat.StatTol) (env : List AVal) (m : Measure) (rows : Option Nat) :
    Option Rat := do
  let n ← rows
  guard (n ≤ 2 ^ 32)
  let u := unitRound
  let nf : Rat := n
  let dOf (sample : Bool) : Nat := if sample then max 1 (n - 1) else max 1 n
  match m.fn, m.arg with
  | .var sample sqrt, arg =>
    let x ← doubleMag env arg
    let d := dOf sample
    let q := nf * (x + tiny) * (x + tiny)
    let r := nf * (x + tiny) * x
    let varTol := Stat.varTol n d r q
    let v := nf * x * x / d
    let tv := varTol + u * v
    if sqrt then
      let st := sqrtUp tv
      return st + u * (sqrtUp v + st) + 2 * u * tiny + u * sqrtUp v
    else return tv
  | .cov sample, .bin .pair a b =>
    let bx ← doubleMag env a
    let byy ← doubleMag env b
    let d := dOf sample
    let r1 := nf * (bx + tiny) * byy
    let r2 := nf * (byy + tiny) * bx
    let rs := nf * bx * byy
    let rq := nf * (bx + tiny) * (byy + tiny)
    return Stat.covTol t n d r1 r2 rs rq + u * rs / d
  | _, _ => none

/-- Is `statEps` of `m` a theorem (`epsilon_var_cr`, `epsilon_stddev_cr`,
`epsilon_cov_cr`)? For `VAR_*`, `STDDEV_*` and `COVAR_*`, not for `CORR`. -/
def statProvedFn (m : Measure) : Bool :=
  match m.fn with
  | .var _ _ | .cov _ => true
  | _ => false

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
  divisor with no column reference (a literal, a constant expression) multiplies by the
  reciprocal (`fl(x · fl(1/y))`, polars-scalar-divisor): `(εa / lb)(1 + u)² +
  (3u + u²)(ma / lb) + (u (1 + u)(ma + εa) + 2u) t` (`rule_div_recip`), stated only where
  `lb ≥ t`, so `1 / y` is finite. It is at least `rule_div`'s term by term
  (`rule_div_le_recip`), so a plan Polars divides exactly (a frame shorter than its
  threads) is covered too;
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
between engines. The formulas are evaluated exactly (`ExactBound`, #660),
square roots rounded outward and `exp` bounded above. -/

/-- Below the largest finite double, with room: an exact result this large
does not overflow. -/
def fits (x : Rat) : Bool := x ≤ 1.0e308

/-- The `sum_order` behaviours `float-bounds` proves the bound for:
`TreeSum` and Kahan's sum (`StdModel.Summed`). -/
def provedOrders : List String := ["SEQUENTIAL", "ANY", "PAIRWISE", "SCALED_CONSTANT", "COMPENSATED"]

/-- Does every engine of `es` sum doubles in one of the proved orders? -/
def ordersProved (es : List EngineProfile) : Bool :=
  es.all fun e => (e.table.allows "agg.fsum" "sum_order" []).all (provedOrders.contains ·)

/-- The `stat_algo` behaviours `core_var_chan`, `core_cov_chan`,
`core_var_polars` and `core_cov_polars` cover: the reference's own, Welford's
update with Chan's merge, and two-pass blocks with Schubert and Gertz's merge. -/
def provedStatAlgos : List String := ["EXACT", "WELFORD_CHAN", "SCHUBERT_GERTZ"]

/-- The group whose `stat_algo` row a statistic reads, as the plan does
(`AggFn.reads`): `agg.var` for `VAR_*` and `STDDEV_*`, `agg.stat` for
`COVAR_*` and `CORR`. -/
def statGroup (m : Measure) : String :=
  match (AggFn.reads m.fn).find? (·.2.1 == "stat_algo") with
  | some (g, _, _) => g
  | none => "agg.stat"

/-- The engines whose statistics of `group` a theorem bounds: the group's
`stat_algo` choices are ones the theorems cover, and the `stat_algo` row the
plan reads for the group (`ObsTable.row?`: the group's own, else the
option's) is proved on facts about the engine's algorithm (`core_var_chan`,
`core_var_polars`). An engine whose algorithm no fact settles, or whose row is
only tested, is not among them: its statistics' columns are tested
(`Report.epsilon[col].proved_on`). -/
def statsProvedOn (group : String) (es : List EngineProfile) : List String :=
  es.filterMap fun e =>
    let algos := e.table.allows group "stat_algo" []
    let proved := match e.obs.row? group "stat_algo" with
      | some r => match r.evidence with | .proved _ _ => true | _ => false
      | none => false
    if algos.all (provedStatAlgos.contains ·) && proved then some e.name else none

/-- The constants of the loosest `stat_algo` the engines `es` allow for
`group`: Schubert and Gertz's where one allows `SCHUBERT_GERTZ`, else Chan's. -/
def statTolOn (group : String) (es : List EngineProfile) : Stat.StatTol :=
  if es.any fun e => (e.table.allows group "stat_algo" []).contains "SCHUBERT_GERTZ" then .sg
  else .chan

-- Every engine's `VAR_*` and `STDDEV_*` is proved. Polars's `COVAR_*` is too
-- (`core_cov_polars`), but its `agg.stat` row, which `CORR` shares, stays tested
-- until Polars's `CORR` is proved (ruling 271, #1808).
#guard statsProvedOn "agg.var" builtinEngines == ["duckdb", "polars", "spark"]
#guard statsProvedOn "agg.stat" builtinEngines == ["duckdb", "spark"]
#guard (statTolOn "agg.stat" builtinEngines).cov == 107
#guard (statTolOn "agg.stat" (builtinEngines.filter (·.name != "polars"))).cov == 71

/-- Why a `CORR` column has no bound, and what lifts it (D30). -/
def corrWhy : String :=
  "CORR has no data-free bound: its distance to the reference is bounded only under a stated lower bound on both sides' variances, a precondition the run checks; without one only [-1, 1] holds, and a tolerance on it is tested (D30, #918)"

/-- A bound on `|e|` from the preconditions, for a double expression. -/
def magOf (env : List AVal) (e : Expr) : Option Rat := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  return unscale (max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs)

/-- An upper bound on `e` from the preconditions (`0` where it is negative). -/
def hiOf (env : List AVal) (e : Expr) : Option Rat := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let hi ← b.hi
  let s := FloatCode.scaled hi
  return if s ≤ 0 then 0 else unscale s.natAbs

/-- The range of `e` from the preconditions, exactly. -/
def rangeOf (env : List AVal) (e : Expr) : Option (Rat × Rat) := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let (l, h) := (FloatCode.scaled lo, FloatCode.scaled hi)
  return ((l : Rat) / ((2 ^ 1074 : Nat) : Rat), (h : Rat) / ((2 ^ 1074 : Nat) : Rat))

/-- The least `|e|` from the preconditions, where `0` is outside its range. -/
def minAbsOf (env : List AVal) (e : Expr) : Option Rat := do
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
def resultMag (env : List AVal) (e : Expr) : Option Rat :=
  (magOf env e).orElse fun _ => match e with
    | .bin .fdiv a b => do return (← magOf env a) / (← minAbsOf env b)
    | .un (.fmath .log10) _ => some 324
    | .un (.fmath .log2) _ => some 1075
    | .un (.fmath .ln) _ => some 745
    | .un (.fmath .sin) _ | .un (.fmath .cos) _ => some 1
    | .un (.fmath .asin) _ | .un (.fmath .atan) _ => some 1.5707963267948968
    | .un (.fmath .acos) _ => some 3.1415926535897936
    | _ => none

/-- The key of an elementary function in `EngineProfile.elemUlps`. `sqrt` and `exp` have none:
`sqrt` is correctly rounded everywhere, and `exp` has its own rule in `exprEps` (`rule_exp`, one
ulp on each side, which Java's specification gives `exp` too), so neither reaches `opExtra`. -/
def elemKey : Expr → Option String
  | .un (.fmath .sqrt) _ | .un (.fmath .exp) _ => none
  | .un (.fmath f) _ => some f.name
  | .bin .flogb _ _ => some "logb"
  | .bin .fpow _ _ => some "pow"
  | .bin .fatan2 _ _ => some "atan2"
  | _ => none

/-- An engine's own error at one call, beyond the reference's, relative to `u`
and the result's bound: twice its `elemUlps` entry. An elementary function
without an entry is the reference's on an engine that calls its `libm`
(`sameLibm`), and has no bound on one that does not. -/
def opExtra (es : List EngineProfile) (engine : String) (e : Expr) : Option Rat :=
  match elemKey e with
  | none => some 0
  | some k =>
    let ep := engineNamed? es engine
    match ep.bind (·.elemUlps.lookup k) with
    | some v => some (2 * v)
    | none => if ep.all (·.sameLibm) then some 0 else none

/-- The largest `|x|` for which an engine's `sin`, `cos` and `tan` are bounded:
Java gives them one ulp for every argument, where glibc's large-argument
reduction, the reference's side, errs by more (ruling 132). -/
def trigArgMax : Rat := 1048576

/-- `sin`, `cos` and `tan`, which carry the guard `trigArgMax` on an engine
whose own values they are. -/
def trigArg? : Expr → Option Expr
  | .un (.fmath .sin) a | .un (.fmath .cos) a | .un (.fmath .tan) a => some a
  | _ => none

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
def exactP : Option (Rat × Bool) → Bool
  | some (e, p) => e == 0 && p
  | none => false

/-- The columns' values where a `CASE` takes its `THEN` branch: refined by the
condition where it has the same outcome on every engine (`ec` exact), so
that, say, a mean guarded by `0 < count` reads a count of at least one. -/
def thenEnv (env : List AVal) (ec : Option (Rat × Bool)) (c : Expr) : List AVal :=
  if exactP ec then c.refine env else env

/-- How far an engine's value of `e` may be from the reference's, from the
columns' errors `cols` (`none`: not bounded), and whether a rule of
`Propagate.lean` proves it. -/
def exprEps (es : List EngineProfile) (engine : String) (env : List AVal) (cols : List (Option (Rat × Bool))) :
    Expr → Option (Rat × Bool)
  | .lit _ => some (0, true)
  | .field i => cols.getD i none
  | .un .fneg a => exprEps es engine env cols a
  | .un .itof a => (exprEps es engine env cols a).bind fun (x, p) =>
    if x == 0 then some (0, p) else none
  -- D52: a source mark. The source's construct is within `k · 2⁻⁵³` of the
  -- plan's value, relatively (`DuckAgg.avgBigint_nearRel` for `avg(BIGINT)`):
  -- that band over the argument's range, exactly, and `2⁻¹⁰⁷⁴` beside it, where
  -- the argument is exact; no bound otherwise. It does not test `engine`: one
  -- bound, whoever runs the SQL (ruling 82).
  -- Proved by the theorem that states the band (ruling 85) where the argument
  -- is exact with a proof (`exactP`).
  | .un (.approx k) a => (exprEps es engine env cols a).bind fun (x, p) => do
    guard (x == 0)
    let m ← doubleMag env a
    return ((k : Rat) * unitRound * m + pow2 (-1074), p)
  | .bin .lt a b | .bin .eq a b => do
    -- `rule_threshold`: where the ranges, widened by `ε`, do not straddle, the
    -- comparison has one outcome on both sides.
    let (ea, pa) ← exprEps es engine env cols a
    let (eb, pb) ← exprEps es engine env cols b
    if ea == 0 && eb == 0 then return (0, pa && pb)
    let (la, ha) ← rangeOf env a
    let (lb, hb) ← rangeOf env b
    guard (ha + ea < lb - eb || hb + eb < la - ea)
    return (0, pa && pb)
  | e@(.bin f a b) => do
    let (ea, pa) ← exprEps es engine env cols a
    let (eb, pb) ← exprEps es engine env cols b
    let u := unitRound
    -- Polars multiplies by the reciprocal for any length-1 divisor, one with no column
    -- reference included (polars-scalar-divisor); `rule_div_le_recip` says the bound also
    -- covers the exact kernel it takes for a short frame.
    let recip := engine == "polars" && f == .fdiv && b.cols.isEmpty
    match f with
    | .fadd | .fsub =>
      if ea == 0 && eb == 0 then return (0, pa && pb)
      let ma ← magOf env a
      let mb ← magOf env b
      guard (fits (ma + mb + ea + eb))
      return ((ea + eb) * (1 + u) + 2 * u * (ma + mb + tiny), pa && pb)
    | .fmul =>
      if ea == 0 && eb == 0 then return (0, pa && pb)
      let ma ← magOf env a
      let mb ← magOf env b
      let d := ma * eb + mb * ea + ea * eb
      guard (fits (ma * mb + d))
      return (d * (1 + u) + 2 * u * (ma * mb + tiny), pa && pb)
    | .fdiv =>
      guard (eb == 0)
      if ea == 0 && !recip then return (0, pa && pb)
      let lb ← minAbsOf env b
      -- Below the smallest normal `1 / y` overflows and Polars gives inf or NaN where the
      -- rule would state a finite bound: no bound there (the row's precondition, ruling 157).
      guard (!recip || tiny ≤ lb)
      match magOf env a with
      | some ma =>
        guard (fits (ma / lb + ea / lb))
        if recip then
          return (ea / lb * (1 + u) * (1 + u) + (3 * u + u * u) * (ma / lb)
            + (u * (1 + u) * (ma + ea) + 2 * u) * tiny, pa && pb)
        return (ea / lb * (1 + u) + 2 * u * (ma / lb + tiny), pa && pb)
      | none =>
        -- From the quotient's own bound: not a proved rule.
        let mq ← resultMag env e
        return (ea / lb + 2 * u * mq + (if recip then 3 * u * mq else 0), false)
    | _ =>
      let extra ← opExtra es engine e
      if ea == 0 && eb == 0 && extra == 0 then return (0, pa && pb && !inexact e)
      guard (ea == 0 && eb == 0)
      return (extra * u * (← resultMag env e), false)
  | .un (.fmath .sqrt) a => do
    -- `rule_sqrt`: correctly rounded on both sides.
    let (ea, pa) ← exprEps es engine env cols a
    if ea == 0 then return (0, pa)
    let (la, ha) ← rangeOf env a
    guard (la - ea ≥ 0)
    -- The roots rounded outward: `s` divides, `d1` and `√ha` add.
    let s := sqrtDown (la - ea) + sqrtDown la
    let d1 := sqrtUp ea
    let d := if s > 0 then min d1 (ea / s) else d1
    let u := unitRound
    return (d * (1 + u) + 2 * u * (sqrtUp ha + tiny), pa)
  | .un .ffloor a | .un .fceil a | .un .fround a => do
    -- `rule_floor`, `rule_ceil`, `rule_round`: a step of one.
    let (ea, pa) ← exprEps es engine env cols a
    if ea == 0 then return (0, pa)
    return (ea + 1, pa)
  | .un .ftoi a => do
    -- `rule_trunc`: each side within one of its input.
    let (ea, pa) ← exprEps es engine env cols a
    if ea == 0 then return (0, pa)
    return (ea + 2, pa)
  | .un (.fmath .exp) a => do
    -- `rule_exp`: the platform's `libm` on both sides, one ulp each.
    let (ea, pa) ← exprEps es engine env cols a
    let ha ← hiOf env a
    let u := unitRound
    guard (ha + ea ≤ 709)
    return (ea * expUp (ha + ea) * (1 + 2 * u) + 4 * u * (expUp ha + tiny), pa)
  | e@(.un _ a) => do
    let (ea, pa) ← exprEps es engine env cols a
    let extra ← opExtra es engine e
    -- Spark's `sin`, `cos` and `tan` are bounded for arguments up to `trigArgMax`.
    if extra != 0 then
      match trigArg? e with
      | some a' => guard ((magOf env a').any (· ≤ trigArgMax))
      | none => pure ()
    if ea == 0 && extra == 0 then return (0, pa && !inexact e)
    if ea == 0 then return (extra * unitRound * (← resultMag env e), false)
    none
  | .ifThen c@(.bin .lt a (.lit (.float 0))) t@(.un .fneg a₁) f => do
    -- `abs` as the parser writes it: `rule_abs`, whatever the sign of `a`.
    if a₁ == a && f == a then
      let (ea, pa) ← exprEps es engine env cols a
      return (ea, pa)
    let ec := exprEps es engine env cols c
    let et ← exprEps es engine (thenEnv env ec c) cols t
    let ef ← exprEps es engine env cols f
    return (max et.1 ef.1, et.2 && ef.2 && exactP ec)
  | .ifThen c t f => do
    let ec := exprEps es engine env cols c
    let et ← exprEps es engine (thenEnv env ec c) cols t
    let ef ← exprEps es engine env cols f
    -- A condition that may differ between engines may pick the other branch.
    return (max et.1 ef.1, et.2 && ef.2 && exactP ec)
  | .hof _ _ _ => none

/-- `cs` with every flag cleared where `ok` fails: rows or groups that may
differ between engines. -/
def keepIf (ok : Bool) (cs : List (Option (Rat × Bool))) : List (Option (Rat × Bool)) :=
  if ok then cs else cs.map (·.map fun (e, _) => (e, false))

/-- The window algorithms that sum the frame's own values, so that the
aggregate's bound holds of the frame (`window_sum_algo`, #1032). -/
def windowSumAlgos : List String := ["RECOMPUTE", "TREE", "RUNNING_ADD"]

/-- Does every engine sum a window's frame by one of `windowSumAlgos`? -/
def windowSumsBounded (es : List EngineProfile) : Bool :=
  es.all fun e =>
    (e.table.allows "win.agg" "window_sum_algo" []).all (windowSumAlgos.contains ·)

/-- A threshold filter the margin check decides on `engine` (#929): one the
check covers (`Rel.marginCheck`), on an engine whose sums are in the orders
`StdModel.margin_check` covers. The check runs on the data before the plan. -/
def marginCovered (es : List EngineProfile) (engine : String) (cat : Catalog) (env : List AVal)
    (cs : List (Option (Rat × Bool))) (r : Rel) (c : Expr) : Bool :=
  let on := es.filter (·.name == engine)
  match (Rel.filter r c).marginSite cat with
  | some s => ordersProved on && (!s.win || windowSumsBounded on) && exactP (exprEps es engine env cs s.thr)
  | none => false

/-- Each column's error on `engine`, and whether it is proved, for plans of
projections, filters, sorts and one aggregate over reads. A threshold filter
the margin check covers keeps the reference's rows (`marginCovered`). -/
def colEps (es : List EngineProfile) (engine : String) (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) : Rel → Option (List (Option (Rat × Bool)))
  | .read t => some ((List.range (cat t).arity).map fun _ => some (0, true))
  | .values n _ => some ((List.range n).map fun _ => some (0, true))
  | .filter r c => (colEps es engine cat A F T r).map fun cs =>
      keepIf (exactP (exprEps es engine (r.aeval cat A F T) cs c) ||
        marginCovered es engine cat (r.aeval cat A F T) cs r c) cs
  | .orderBy r keys => (colEps es engine cat A F T r).map fun cs =>
      keepIf (keys.all fun k => exactP (cs.getD k.col none)) cs
  | .distinct r => (colEps es engine cat A F T r).map fun cs => keepIf (cs.all exactP) cs
  | .fetch r _ _ => colEps es engine cat A F T r
  | .emit r m => (colEps es engine cat A F T r).map fun cs => m.map (cs.getD · none)
  | .cross a b => do
    return (← colEps es engine cat A F T a) ++ (← colEps es engine cat A F T b)
  | .join a b _ on => do
    let cs := (← colEps es engine cat A F T a) ++ (← colEps es engine cat A F T b)
    let env := a.aeval cat A F T ++ b.aeval cat A F T
    return keepIf (exactP (exprEps es engine env cs on)) cs
  | .semi a b _ on => do
    let ca ← colEps es engine cat A F T a
    let cs := ca ++ (← colEps es engine cat A F T b)
    let env := a.aeval cat A F T ++ b.aeval cat A F T
    return keepIf (exactP (exprEps es engine env cs on)) ca
  | .unionAll a b => do
    let ca ← colEps es engine cat A F T a
    let cb ← colEps es engine cat A F T b
    return (ca.zip cb).map fun
      | (some (x, p), some (y, q)) => some (max x y, p && q)
      | _ => none
  | .window r part sort fns => (colEps es engine cat A F T r).map fun cs =>
      -- The window functions' values are not bounded here; the input's are kept.
      keepIf ((part.all fun i => exactP (cs.getD i none)) &&
          sort.all fun k => exactP (cs.getD k.col none)) cs ++
        fns.map fun _ => none
  | .project r xs => (colEps es engine cat A F T r).map fun cs =>
      cs ++ xs.map (exprEps es engine (r.aeval cat A F T) cs)
  | .aggregate r gs ms => (colEps es engine cat A F T r).map fun cs =>
      let env := r.aeval cat A F T
      let keys := gs.all fun g => exactP (exprEps es engine env cs g)
      keepIf keys <| gs.map (fun _ => some (0, true)) ++ ms.map fun m => do
        let (ea, pa) ← exprEps es engine env cs m.arg
        let pf := m.filter.all fun c => exactP (exprEps es engine env cs c)
        match m.fn with
        | .fsum | .avg =>
          -- Outside `intMeanExact`'s case, no bound over more than `2³²` rows
          -- (`measureEps`).
          let (order, _) ← measureEps env m r.maxRows
          let n ← r.maxRows
          -- The order's bound is proved for the same doubles on both sides.
          return (order + (if m.fn = .avg then ea else (n : Rat) * ea),
            ea == 0 && pa && pf && (intMeanExact env m r.maxRows || ordersProved es))
        | .count => return (0, pf)
        -- An integer or decimal `SUM` the argument's range and the proved row
        -- cap keep inside its type (`Measure.sumFits_sound`) is outside the
        -- `overflow` option's scope, so every profile gives the reference's
        -- value (D34, ruling 197).
        | .sum => if ea == 0 then return (0, pa && pf && m.sumFits (·.absD env []) r.maxRows) else none
        | .min | .max => return (ea, pa && pf)
        -- D30: an engine's statistic is within the plan's bound of the
        -- reference's exact moments rounded once.
        | .var _ _ => if ea == 0 && pf then return (← statEps .chan env m r.maxRows, false) else none
        | .cov _ | .corr => none
        | _ => if ea == 0 then some (0, false) else none
  | _ => none

/-! ### Decisions on a marked value (D52, ruling 104)

A source mark (`.un (.approx k) _`) says the lifted source computes a value
within a band of the plan's. A row decision (a filter, sort key, `DISTINCT`,
join condition, grouping key or measure filter) that reads such a value has
one outcome over the band only where `rowsExact`'s check clears it; elsewhere
the source may keep other rows than the verified plan. -/

/-- Does `e` contain a mark at any depth, or read a column `d` marks? A
lambda's body reads the row shifted by one, so a lambda over a marked row
counts as marked. -/
def Expr.markDep (d : List Bool) : Expr → Bool
  | .lit _ => false
  | .field i => d.getD i true
  | .un (.approx _) _ => true
  | .un _ a => Expr.markDep d a
  | .bin _ a b => Expr.markDep d a || Expr.markDep d b
  | .ifThen c t e => Expr.markDep d c || Expr.markDep d t || Expr.markDep d e
  -- The body runs on `x :: row`: the element is as tainted as the list, an
  -- outer column as itself.
  | .hof _ l body => Expr.markDep d l || Expr.markDep (Expr.markDep d l :: d) body

/-- Does `e` contain a mark? -/
def Expr.hasMark : Expr → Bool
  | .lit _ | .field _ => false
  | .un (.approx _) _ => true
  | .un _ a => Expr.hasMark a
  | .bin _ a b => Expr.hasMark a || Expr.hasMark b
  | .ifThen c t e => Expr.hasMark c || Expr.hasMark t || Expr.hasMark e
  | .hof _ l body => Expr.hasMark l || Expr.hasMark body

/-- Does a measure's argument or filter contain a mark? -/
def Measure.hasMark (m : Measure) : Bool := Expr.hasMark m.arg || m.filter.any Expr.hasMark

/-- Does any expression of the plan contain a mark? Without one no column,
row decision or postcondition is tainted, and `sourceIssues` stops early. -/
def Rel.hasMark : Rel → Bool
  | .read _ | .values _ _ => false
  | .filter r c => Rel.hasMark r || Expr.hasMark c
  | .project r es => Rel.hasMark r || es.any Expr.hasMark
  | .emit r _ | .orderBy r _ | .fetch r _ _ | .distinct r | .unnest r _ => Rel.hasMark r
  | .aggregate r gs ms => Rel.hasMark r || gs.any Expr.hasMark || ms.any Measure.hasMark
  | .window r _ _ fns => Rel.hasMark r || fns.any fun
    | .agg m _ _ => Measure.hasMark m
    | _ => false
  | .cross a b | .unionAll a b => Rel.hasMark a || Rel.hasMark b
  | .join a b _ on | .semi a b _ on => Rel.hasMark a || Rel.hasMark b || Expr.hasMark on

/-- Which columns of `r` depend on a mark (M1, M2): every constructor has a
rule, and an operator whose columns this does not trace taints them all. -/
def Rel.markDeps (cat : Catalog) : Rel → List Bool
  | .read t => List.replicate (cat t).arity false
  | .values n _ => List.replicate n false
  | .filter r _ | .orderBy r _ | .fetch r _ _ | .distinct r | .unnest r _ => Rel.markDeps cat r
  | .project r es => let d := Rel.markDeps cat r; d ++ es.map (Expr.markDep d)
  | .emit r m => let d := Rel.markDeps cat r; m.map (d.getD · true)
  | .aggregate r gs ms =>
    let d := Rel.markDeps cat r
    gs.map (Expr.markDep d) ++
      ms.map fun m => Expr.markDep d m.arg || m.filter.any (Expr.markDep d) ||
        m.sort.any fun k => d.getD k.col true
  | .window r _ _ fns => let d := Rel.markDeps cat r; d ++ fns.map fun _ => d.any id
  | .cross a b | .join a b _ _ => Rel.markDeps cat a ++ Rel.markDeps cat b
  | .semi a _ _ _ => Rel.markDeps cat a
  | .unionAll a b => List.zipWith (· || ·) (Rel.markDeps cat a) (Rel.markDeps cat b)

/-- Every row decision of the plan on `engine`: whether `rowsExact`'s check
passes there, whether it reads a value a mark taints, and what it is.
`rowsExact` is that every site passes. -/
def rowSites (es : List EngineProfile) (engine : String) (cat : Catalog) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) : Rel → List (Bool × Bool × String)
  | .read _ | .values _ _ => []
  | .filter r c => rowSites es engine cat A F T r ++
      [((colEps es engine cat A F T r).any fun cs =>
        exactP (exprEps es engine (r.aeval cat A F T) cs c) ||
          marginCovered es engine cat (r.aeval cat A F T) cs r c,
        Expr.markDep (Rel.markDeps cat r) c, s!"the filter {c.render}")]
  | .orderBy r keys => rowSites es engine cat A F T r ++
      [((colEps es engine cat A F T r).any fun cs => keys.all fun k => exactP (cs.getD k.col none),
        keys.any (fun k => (Rel.markDeps cat r).getD k.col true), "a sort key")]
  | .distinct r => rowSites es engine cat A F T r ++
      [((colEps es engine cat A F T r).any fun cs => cs.all exactP, (Rel.markDeps cat r).any id,
        "DISTINCT")]
  | .fetch r _ _ | .emit r _ | .project r _ | .window r _ _ _ | .unnest r _ =>
    rowSites es engine cat A F T r
  | .cross a b | .unionAll a b => rowSites es engine cat A F T a ++ rowSites es engine cat A F T b
  | .join a b _ on | .semi a b _ on =>
    rowSites es engine cat A F T a ++ rowSites es engine cat A F T b ++
      [(match colEps es engine cat A F T a, colEps es engine cat A F T b with
        | some ca, some cb =>
          exactP (exprEps es engine (a.aeval cat A F T ++ b.aeval cat A F T) (ca ++ cb) on)
        | _, _ => false,
        Expr.markDep (Rel.markDeps cat a ++ Rel.markDeps cat b) on, s!"the join condition {on.render}")]
  | .aggregate r gs ms => rowSites es engine cat A F T r ++
      [((colEps es engine cat A F T r).any fun cs =>
        let env := r.aeval cat A F T
        gs.all (fun g => exactP (exprEps es engine env cs g)) &&
          ms.all fun m => m.filter.all fun c => exactP (exprEps es engine env cs c),
        gs.any (Expr.markDep (Rel.markDeps cat r)) ||
          ms.any (fun m => m.filter.any (Expr.markDep (Rel.markDeps cat r))),
        "a grouping key or measure filter")]

/-- Does every filter, sort key, `DISTINCT`, grouping key and measure filter
of the plan read values that are the same on `engine` as on the reference,
or a comparison whose outcome is (`rule_threshold`)? Then the engine keeps
the same rows and groups, and the columns' bounds compare like with like. -/
def rowsExact (es : List EngineProfile) (engine : String) (cat : Catalog) (A : String → List AVal)
    (F : String → List Fact) (T : WindowKeys) (r : Rel) : Bool :=
  (rowSites es engine cat A F T r).all (·.1)

/-- Does the plan read or write a single-precision column? Polars sums
`Float32` in single precision (polars-sum-float-streaming), which no bound here covers. -/
def hasFp32 (tj : Json) : Bool := (tj.compress.splitOn "\"fp32\"").length > 1

/-- What `"epsilon"` says of a double `SUM` of exact values with no row cap,
grouped by exact keys, on engines whose orders `StdModel.Summed` covers
(#929): each group's sum is within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the
reference's, from its own `n ≤ 2³²` values (`StdModel.epsilon_group`); an
`AVG` within `(γₙ + 4u)` of that over `n` (`StdModel.epsilon_group_avg`). No
number bounds every group, so a stated tolerance is not met by it; the plan's
bound is. -/
def perGroupJson (avg : Bool) : Json := Json.mkObj [("abs", Json.null),
  ("per_group", toJson (if avg then "(γₙ + 4u) · Σ(|xᵢ| + 2⁻¹⁰²²) / n, n ≤ 2³² the group's values"
    else "(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²), n ≤ 2³² the group's values")),
  ("theorem", toJson (if avg then "FloatBounds.StdModel.epsilon_group_avg"
    else "FloatBounds.StdModel.epsilon_group")),
  ("proved", Json.mkObj [("abs", toJson false), ("per_group", toJson true)])]

/-- A computed bound as JSON, rounded up (`ExactBound.toJsonUp`). -/
def epsJson (e : Rat) : Json := toJsonUp e

/-- What `epsilonByEngine`, `rowsExactByEngine`, `marginChecksJson` and
`epsilon` start from: a request's transformation (`tj`, `plan`), the tables'
arities (`cat`), each table's columns and facts under its preconditions (`A`,
`F`), the row caps, the plan with its reads capped (`root`) and the window
keys (`T`). -/
structure Inputs where
  tj : Json
  plan : Plan
  cat : Catalog
  A : String → List AVal
  F : String → List Fact
  caps : String → Option Nat
  root : Rel
  T : WindowKeys

/-- A request's `Inputs`, or `none` without a transformation. Each table's
columns and facts are computed once, as data: the analyses read them at every
read of every engine's pass, and computed there each read would parse the
table's schema again. -/
def inputs? (input : Json) : Except String (Option Inputs) := do
  let some tj := (input.getObjVal? "transform").toOption | return none
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
  let byTable := (tables.map (·.1) |>.eraseDups).map fun t =>
    (t, tableEnv (schemas t) (preOf t), (preOf t).flatMap Expr.factsOf)
  let A : String → List AVal := fun t => match byTable.find? (·.1 == t) with
    | some (_, a, _) => a
    | none => tableEnv (schemas t) (preOf t)
  let F : String → List Fact := fun t => match byTable.find? (·.1 == t) with
    | some (_, _, f) => f
    | none => (preOf t).flatMap Expr.factsOf
  let caps := rowCaps ((input.getObjVal? "max_rows").toOption.getD (.obj {}))
  let root := plan.root.capReads caps
  let T := Rel.keyedWindows cat A F { keys := fun _ => [] }
  return some ⟨tj, plan, cat, A, F, caps, root, T⟩

/-- `"epsilon_by_engine"` of a `--contract` request: per engine and double
output column, how far the engine's value may be from one the reference
allows, `{"abs": …, "rel"?: …, "proved": {"abs": …, "rel"?: …}}` (`null`:
not bounded). `rel` is `abs` over the least magnitude the reference's value
may have, where its range leaves out zero: a difference of nearly equal
values loses it, as cancellation loses relative accuracy. -/
def epsilonByEngine (es : List EngineProfile) (input : Json) : Except String Json := do
  let some ⟨tj, plan, cat, A, F, _, root, T⟩ ← inputs? input | return Json.mkObj []
  let kinds := (Write.relKinds (Write.planSchemas plan) cat plan.root).map Write.WKind.toKind
  let names := if plan.names.length == kinds.length then plan.names
    else (List.range kinds.length).map (s!"#{·}")
  let f32 := hasFp32 tj
  -- The least magnitude of each column, for the relative bound.
  let mins : List (Option Rat) := (root.aeval cat A F T).map fun a => do
    guard a.intsOnly
    let b ← a.int
    let (l, h) := (FloatCode.scaled (← b.lo), FloatCode.scaled (← b.hi))
    if 0 < l then some (unscale l.natAbs)
    else if h < 0 then some (unscale h.natAbs) else none
  return Json.mkObj <| (es.map (·.name)).map fun engine =>
    let cols := colEps es engine cat A F T root
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
def rowsExactByEngine (es : List EngineProfile) (input : Json) : Except String Json := do
  let some ⟨_, _, cat, A, F, _, root, T⟩ ← inputs? input | return Json.mkObj []
  return Json.mkObj <| es.map fun e => (e.name, toJson (rowsExact es e.name cat A F T root))

/-- `"margin_checks"` of a `--contract` request (#929): the margin check of
each threshold filter on a double `SUM` that no static bound decides, as a
plan of its own (`Rel.marginCheck`), with the column it reads. `Report.run`
runs each on the engine before the plan and counts the groups it flags. -/
def marginChecksJson (es : List EngineProfile) (input : Json) : Except String Json := do
  let some ⟨_, plan, cat, A, F, caps, _, T⟩ ← inputs? input | return Json.arr #[]
  -- The filters no static bound decides on some engine, judged on the plan
  -- with its reads capped (`Rel.capReads`); the check reads the data as it is.
  let rec sites : Rel → List (Rel × MarginSite)
    | r@(.filter i c) =>
      let ic := i.capReads caps
      let static := es.all fun e => (colEps es e.name cat A F T ic).any fun cs =>
        exactP (exprEps es e.name (ic.aeval cat A F T) cs c)
      (if static then [] else (r.marginSite cat).toList.map (r, ·)) ++ sites i
    | .project i _ | .emit i _ | .fetch i _ _ | .window i .. | .orderBy i _ | .distinct i
    | .aggregate i _ _ | .unnest i _ => sites i
    | .cross a b | .join a b _ _ | .unionAll a b | .semi a b _ _ => sites a ++ sites b
    | .read _ | .values _ _ => []
  let schemaOf := Write.planSchemas plan
  return Json.arr <| (sites plan.root).toArray.map fun (node, site) =>
    let chk := site.check
    let j := site.col
    let t := site.thr
    -- The threshold, and the columns' names where the filter is the plan's output.
    let root := node == plan.root
    let tf : Option Float := match t.eval [] with
      | .float code => some (FloatCode.toFloat code)
      | _ => none
    let col := if root then plan.names.getD j "the SUM" else "the SUM"
    let atT := match tf, t with
      | some f, _ => " " ++ fmtDouble f
      | none, .field k => if root then " " ++ plan.names.getD k "" else ""
      | _, _ => ""
    let what := if site.win then "row(s)" else "group(s)"
    -- Per engine whose sums `StdModel.margin_check` covers: the facts behind
    -- its order, and the message of a run whose check flags `{k}` groups.
    let engines := (es.filter fun e => ordersProved [e] && (!site.win || windowSumsBounded [e])).map fun e =>
      let facts := e.obs.factsAt none "sum_order"
      let factsTxt := if facts.isEmpty then "its sum_order row" else ", ".intercalate facts
      (e.name, Json.mkObj [("facts", toJson facts), ("message", toJson (
        "{k} " ++ what ++ " have " ++ col ++ " within its bound of the threshold" ++ atT ++
        (if site.win then " (the bound per partition" else " (the bound per group") ++
        " from its count and Σ|x|), or more than 2³² values: " ++ e.name ++
        "'s SUM adds in an order of its own (" ++ factsTxt ++ "), so " ++ e.name ++
        " may keep other groups than the reference there. A group with no values has a NULL " ++
        "sum, which the filter drops on every engine. Widen the threshold's margin, sum in " ++
        "DECIMAL, or verify with on_inferred=\"warn\" to keep them, the contract holding up " ++
        "to the bound"))])
    Json.mkObj [("plan", Write.writePlan schemaOf plan.catalog chk ["flagged"]),
      ("column", if root then toJson (plan.names.getD j "") else Json.null),
      ("threshold", match tf with | some f => toJson f | none => Json.null),
      ("label", toJson (col ++ " is farther than its bound from the threshold" ++ atT ++
        (if site.win then " in every row, so the engine keeps the reference's rows (the bound " ++
          "per partition from its count and Σ|x|)"
        else " in every group with a value, so the engine keeps the reference's groups (the " ++
          "bound per group from its count and Σ|x|)"))),
      ("conditions", toJson marginConditions),
      ("engines", Json.mkObj engines)]

/-- A path of child indices over `Rel` nodes (`Rel.asofSitesAt`) as a path in
the JSON `Write.writeRel` writes, from `relations[0].root.input`: the key of
each step (`input`, `left`, `right`, or `inputs` and an index), and none for
an `EMIT`, which `Write` puts on its input's `RelCommon`, nor for the
projection of an `EMIT` of a projection of an aggregate with decimal `AVG`s,
which `Write` writes as one aggregate node. -/
def _root_.Substrait.Rel.jsonPath : Rel → List Nat → List Json
  | _, [] => []
  | .emit p@(.project (.aggregate r gs ms) qs) m, 0 :: ps =>
    -- `Write` writes the three as one aggregate node where they hold decimal `AVG`s.
    match Write.decimalAvgsOf gs.length ms qs m, ps with
    | some _, 0 :: 0 :: ps' => "input" :: r.jsonPath ps'
    | some _, _ => []
    | none, _ => p.jsonPath ps
  | .emit r _, 0 :: ps => r.jsonPath ps
  | .filter r _, 0 :: ps | .project r _, 0 :: ps | .fetch r _ _, 0 :: ps
  | .orderBy r _, 0 :: ps | .distinct r, 0 :: ps | .aggregate r _ _, 0 :: ps
  | .unnest r _, 0 :: ps | .window r .., 0 :: ps => "input" :: r.jsonPath ps
  | .join a _ _ _, 0 :: ps | .cross a _, 0 :: ps | .semi a _ _ _, 0 :: ps => "left" :: a.jsonPath ps
  | .join _ b _ _, 1 :: ps | .cross _ b, 1 :: ps | .semi _ b _ _, 1 :: ps =>
    "right" :: b.jsonPath ps
  | .unionAll a _, 0 :: ps => "inputs" :: toJson 0 :: a.jsonPath ps
  | .unionAll _ b, 1 :: ps => "inputs" :: toJson 1 :: b.jsonPath ps
  | _, _ => []

/-- `"asof_checks"` of a `--contract` request (#1447, ruling 162 A2 and A7):
per as-of join of the plan (`Rel.asofSites`), the count of the pairs its
range join compares (`AsofSite.pairs`), as a plan of its own, and where and
what the site is for a writer: the path to its node (child indices from the
root, 0 for an input or a join's left side, 1 for the right; `json_path` the
same in the written JSON, `Rel.jsonPath`), its shape
(`AsofForm`), the keys as (left column, right column) pairs, `lon` and
`ron` (the left columns are the join's left input's, the right ones the
right input's own), whether it is a LEFT join, whether it has more
conjuncts (a tolerance) and whether it has the shape that keeps one row per
left row (`left_exact`, `AsofSite.left_exactly_one`). `Report.run` evaluates the count on the engine
before the plan and refuses the run above the cap `asof_join` states,
whatever the rows come from. -/
def asofChecksJson (input : Json) : Except String Json := do
  let some ⟨_, plan, cat, _, _, _, _, _⟩ ← inputs? input | return Json.arr #[]
  let schemaOf := Write.planSchemas plan
  return Json.arr <| (plan.root.asofSites cat).toArray.map fun (path, s) =>
    Json.mkObj [("plan", Write.writePlan schemaOf plan.catalog s.pairs ["pairs"]),
      ("path", toJson path), ("json_path", Json.arr (plan.root.jsonPath path).toArray),
      ("form", toJson s.form.name),
      ("keys", toJson (s.keys.map fun (l, r) => [l, r])), ("lon", toJson s.lon),
      ("ron", toJson s.ron), ("outer", toJson (s.type == .left)),
      ("tolerance", toJson !s.rest.isEmpty), ("left_exact", toJson (s.leftExact cat))]

/-- Where an output column comes from, as far as window aggregates of doubles
go (#1032): a window's double `SUM` or `AVG` over its input `r`, a value that
reads another window aggregate of doubles or one (no bound), or neither. -/
inductive WinSrc where
  | other
  | bounded (r : Rel) (m : Measure) (part : List Nat) (sort : List SortKey)
  /-- No bound, with what lifts it. -/
  | unbounded (why : String)

-- DuckDB, Polars and Spark each sum a window's own values (duckdb-window-sum-order,
-- polars-window-agg, spark-window-agg).
#guard windowSumsBounded builtinEngines

/-- Why a window statistic of doubles, or a value computed from a window
aggregate of doubles, has no bound, and what lifts it. -/
def windowStatWhy : String := "a window statistic of doubles: no bound yet (#918)"
def derivedWhy : String := "computed from a window aggregate of doubles: no bound carries over"
def slidingWhy : String :=
  "a window sum on an engine whose window algorithm no fact bounds (window_sum_algo, #1032)"

def WinSrc.window : WinSrc → Bool
  | .other => false
  | _ => true

/-- Does a window function's value differ between engines? A double `SUM` or
`AVG` is within `measureEps` of the reference's, a statistical aggregate or
`QUANTILE_CONT` of doubles has no bound here, and a function that copies or
aggregates such a column has none either. -/
def winFnSrc (es : List EngineProfile) (r : Rel) (part : List Nat) (srcs : List WinSrc) : WinFn → WinSrc
  | .agg m sort _ =>
    if (ShardCheck.reads m.arg).any (fun i => (srcs.getD i .other).window) then .unbounded derivedWhy
    else match m.fn with
      | .fsum | .avg => if windowSumsBounded es then .bounded r m part sort else .unbounded slidingWhy
      | .var _ _ | .cov _ | .corr | .quantile true _ _ => .unbounded windowStatWhy
      | _ => .other
  | .lag c _ _ | .lead c _ _ | .firstValue c _ _ | .lastValue c _ _ | .nthValue c _ _ _ =>
    if (srcs.getD c .other).window then .unbounded derivedWhy else .other
  | _ => .other

/-- Each output column's `WinSrc`. -/
def winSrcs (es : List EngineProfile) (cat : Catalog) : Rel → List WinSrc
  | .read t => List.replicate (cat t).arity .other
  | .values n _ => List.replicate n .other
  | .filter r _ | .orderBy r _ | .fetch r _ _ | .distinct r | .unnest r _ => winSrcs es cat r
  | .emit r m => let s := winSrcs es cat r; m.map (s.getD · .other)
  | .project r xs => let s := winSrcs es cat r; s ++ xs.map (reading s)
  | .window r part _ fns => let s := winSrcs es cat r; s ++ fns.map (winFnSrc es r part s)
  | .cross a b | .join a b _ _ => winSrcs es cat a ++ winSrcs es cat b
  | .semi a _ _ _ => winSrcs es cat a
  | .unionAll a b => (winSrcs es cat a).zipWith (fun x y =>
      if x.window || y.window then .unbounded derivedWhy else .other) (winSrcs es cat b)
  | .aggregate r gs ms => let s := winSrcs es cat r
    -- An aggregate of, or grouped by, such a column has no bound here.
    let any (e : Expr) : WinSrc :=
      if (ShardCheck.reads e).any (fun i => (s.getD i .other).window) then .unbounded derivedWhy
      else .other
    gs.map any ++ ms.map fun m => any m.arg
where
  /-- A copy of a column keeps its source; anything computed from a window
  aggregate of doubles has no bound here. -/
  reading (s : List WinSrc) : Expr → WinSrc
    | .field i => s.getD i .other
    | e => if (ShardCheck.reads e).any (fun i => (s.getD i .other).window) then
        .unbounded derivedWhy else .other

/-- A bound as `"epsilon"` gives it, proved or not. -/
def boundJson (e : Rat) (rel : Option (Rat × Bool)) (p : Bool) : Json :=
  Json.mkObj ([("abs", toJsonUp e)] ++
    (match rel with | some (r, _) => [("rel", toJsonUp r)] | none => []) ++
    [("proved", Json.mkObj ([("abs", toJson p)] ++
      match rel with | some (_, pr) => [("rel", toJson (p && pr))] | none => []))])

/-- Whether a measure is a statistical aggregate (D30): its engine's value is
within the plan's bound of the reference's, not equal to it. -/
def isStat (m : Measure) : Bool :=
  match m.fn with
  | .var _ _ | .cov _ | .corr => true
  | _ => false

/-- The output columns that read a statistical aggregate, above the
aggregate: `some (some m)` for the measure `m`'s own column, `some none` for
a column computed from one (no bound carries over), `none` for the rest. -/
def statCols : Rel → Option (List (Option (Option Measure)))
  | .aggregate _ gs ms =>
    some (gs.map (fun _ => none) ++ ms.map fun m => if isStat m then some (some m) else none)
  | .filter r _ | .orderBy r _ => statCols r
  | .project r es => (statCols r).map fun cs => cs ++ es.map fun e =>
      match e with
      | .field i => cs.getD i none
      | _ => if (reads e).any (fun i => (cs.getD i none).isSome) then some none else none
  | .emit r m => (statCols r).map fun cs => m.map (cs.getD · none)
  | _ => none


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
def epsilon (es : List EngineProfile) (input : Json) : Except String Json := do
  let some ⟨tj, plan, cat, A, F, _, root, T⟩ ← inputs? input | return Json.mkObj []
  let wins := winSrcs es cat root
  let winNames := if plan.names.length == wins.length then plan.names
    else (List.range wins.length).map (s!"#{·}")
  -- A window's double `SUM` or `AVG`: each frame is some of the input's rows,
  -- so the aggregate's bound for the input's row cap holds of every frame.
  let winCols := (winNames.zip wins).filterMap fun (name, w) => match w with
    | .bounded r m part sort =>
      let reads := m.arg :: part.map .field ++ sort.map (.field ·.col) ++ m.filter.toList
      let p := !hasFp32 tj && ordersProved es && (es.map (·.name)).all fun engine =>
        match colEps es engine cat A F T r with
        | some cs => reads.all fun e => exactP (exprEps es engine (r.aeval cat A F T) cs e)
        | none => false
      some (name, match measureEps (r.aeval cat A F T) m r.maxRows with
        | some (e, rel) => boundJson e rel p
        | none => Json.mkObj [("abs", Json.null)])
    | .unbounded why => some (name, Json.mkObj [("abs", Json.null), ("why", toJson why)])
    | .other => none
  -- D52: a column that reads a marked value: its band (`exprEps`'s rule), the
  -- largest on any engine, proved where every engine's is (ruling 104's C-out).
  let mk := Rel.markDeps cat root
  let mnames := if plan.names.length == mk.length then plan.names
    else (List.range mk.length).map (s!"#{·}")
  let perEngine := (es.map (·.name)).map fun engine => colEps es engine cat A F T root
  let marked := ((mnames.zip mk).zipIdx).filterMap fun ((name, m), i) =>
    if !m then none
    else
      let bs := perEngine.map fun cs? => cs?.bind (·.getD i none)
      if bs.all Option.isSome && !bs.isEmpty then
        let e := bs.foldl (fun acc b => max acc (b.map (·.1) |>.getD 0)) 0
        some (name, boundJson e none (bs.all fun b => b.any (·.2)))
      else some (name, Json.mkObj [("abs", Json.null)])
  let some (r, gs, ms) := findAggregate root | return Json.mkObj (winCols ++ marked)
  let some (srcs, _) := colSrcs plan.root | return Json.mkObj (winCols ++ marked)
  let env := r.aeval cat A F T
  -- The measure's values, rows and groups are the same on every engine.
  let same (m : Measure) : Bool := !hasFp32 tj && ordersProved es &&
    (es.map (·.name)).all fun engine => match colEps es engine cat A F T r with
      | some cs => (m.arg :: gs ++ m.filter.toList).all fun e => exactP (exprEps es engine env cs e)
      | none => false
  let doubles := (doubleIdx ms).filterMap (ms[·]?)
  let names := if plan.names.length == srcs.length then plan.names
    else (List.range srcs.length).map (s!"#{·}")
  let cols := (names.zip srcs).filterMap fun (name, src) => match src with
    | .bounded j => some (name, match doubles[j]?.bind fun m =>
          (measureEps env m r.maxRows).map (·, same m) with
        | some ((e, rel), p) => boundJson e rel p
        | none =>
          -- No row cap: each group's sum still has a bound from its own values.
          match doubles[j]? with
          | some m =>
            if (m.fn == .fsum || m.fn == .avg) && !m.distinct && m.filter.isNone && same m then
              perGroupJson (m.fn == .avg)
            else Json.mkObj [("abs", Json.null)]
          | none => Json.mkObj [("abs", Json.null)])
    | .unbounded => some (name, Json.mkObj [("abs", Json.null)])
    | _ => none
  -- D30: a statistic's column is within `statEps` of the reference's on an
  -- engine, proved for `VAR_*`, `STDDEV_*` and `COVAR_*` where every engine's algorithm
  -- is one the theorems cover and the measure reads the same values; one
  -- computed from a statistic has no bound.
  let stats : List (String × Option Measure) := match statCols plan.root with
    | some cs => (names.zip cs).filterMap fun (name, (c : Option (Option Measure))) =>
        c.map fun m => (name, m)
    | none => []
  let statJson := stats.map fun (name, (m? : Option Measure)) =>
    (name, match m?.bind (fun m => statEps (statTolOn (statGroup m) es) env m r.maxRows) with
    | some e =>
      -- Proved on the engines of `statsProvedOn`, tested on the others.
      let p := m?.any fun m => statProvedFn m && same m
      let on := match m? with
        | some m => if p then statsProvedOn (statGroup m) es else []
        | none => []
      Json.mkObj [("abs", toJsonUp e), ("proved", Json.mkObj [("abs", toJson (p && on.length ==
        es.length))]), ("proved_on", toJson on)]
    | none => Json.mkObj ([("abs", Json.null), ("proved", Json.mkObj [("abs", toJson false)])] ++
        if m?.any (·.fn == .corr) then [("why", toJson corrWhy)] else []))
  let known := cols ++ statJson.filter fun (n, _) => !cols.any (·.1 == n)
  return Json.mkObj (known.filter (fun (n, _) => !winCols.any (·.1 == n)) ++ winCols ++
    marked.filter fun (n, _) => !known.any (·.1 == n) && !winCols.any (·.1 == n))

/-! ## The dependency report of a contract

`Rel.reads` lists every option a plan's calls, aggregates, sorts and keys
meet, by syntax: it is what `Rel.transfer_of_transferB` covers. A contract
knows more, the columns' types and what the preconditions rule out, and its
`"depends"` leaves out the options the plan cannot meet:

* the keys' NaN and zeros (`rel.keys`), where no grouping or `DISTINCT` key
  is a double and no join compares doubles;
* `empty_group_aggregates`, where every `SUM` and `AVG` is grouped, without a
  filter, over an argument that cannot be NULL (a group then has a value);
* a comparison's NaN and zeros options (`cmp`), where no comparison has a
  double side;
* `min_mod_neg_one`, where every integer `%`'s dividend is bounded above
  `-2⁶³` by the preconditions;
* a value-side or open option of an expression whose result reaches neither
  the output nor the rows kept (`liveReads`): a projected column nothing reads.
  An error-side option counts wherever it is met, since an engine may still
  compute such a column and raise.

`avg_int_result` needs no filter: since reads are per function (D34,
`ctorReads`), only an integer `AVG` reads it. -/

/-- Every aggregate of a plan: its input, keys and measures. A window's
aggregates count as ungrouped: a frame may be empty. -/
def aggNodes : Rel → List (Rel × List Expr × List Measure)
  | .read _ | .values _ _ => []
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _
  | .distinct r | .unnest r _ => aggNodes r
  | .window r _ _ fns =>
    (r, [], fns.filterMap fun | .agg m _ _ => some m | _ => none) :: aggNodes r
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
  | .filter r _ | .project r _ | .emit r _ | .fetch r _ _ | .orderBy r _
  | .unnest r _ => doubleKeys schemas cat r
  | .window r part _ _ => part.any (fun i => (kinds r)[i]? == some .float) || doubleKeys schemas cat r
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
  | .window r part sort fns, _ => windowReads part sort fns ++ liveReads cat r (List.range (r.arity cat))
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

/-- The reads `"depends"` reports for a `--contract` request: those that can
reach the output, or raise; none without a transformation. -/
def dependsReads (input : Json) : Except String (Option (List Read)) := do
  let some tj := (input.getObjVal? "transform").toOption | return none
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
  let T := Rel.keyedWindows cat A F { keys := fun _ => [] }
  let aggs := aggNodes plan.root
  let keys := doubleKeys (Write.planSchemas plan) cat plan.root
  let empty := aggs.any fun (r, gs, ms) => ms.any fun m =>
    (m.fn = .sum || m.fn = .fsum || m.fn = .avg) &&
      (gs.isEmpty || m.filter.isSome || (m.arg.absD (r.aeval cat A F T) []).null)
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
      !(g == "cmp" && !cmp) &&
      !(o == "min_mod_neg_one" && !minMod)
  return some reads

/-- `"depends"` of a `--contract` request. -/
def depends (input : Json) : Except String Json :=
  return ((← dependsReads input).map readsJson).getD .null

end Substrait.Epsilon
