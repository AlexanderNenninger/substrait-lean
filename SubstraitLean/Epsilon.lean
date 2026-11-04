import SubstraitLean.ShardCheck
import SubstraitLean.Transfer

/-!
# The float tolerance of a plan's outputs (#444, #85)

A double `SUM` or `AVG` whose order an engine picks (`sum_order`, a choice
the reference leaves open, with the observation `{"floats": {"bound":
"plan"}}`) is within a per-plan bound of a result the reference allows. This
computes that bound per output column, from what the contract's
preconditions and row caps give (`Measure.abs`, `floatBound`):

* a reference result is within `sumTolScaled n B` (`avgTolScaled` for an
  `AVG`) of the exact one, for at most `n` values in `[-B, B]`
  (`floatSum_mem`, `floatAvg_mem`);
* an engine's order is taken to meet the same bound: a sequential sum and a
  pairwise one are orders the reference allows, and Kahan's compensated sum
  is more accurate than the sequential bound for `n ≥ 3` (Higham, *Accuracy
  and Stability of Numerical Algorithms*, §4.3). This is the part Lean does
  not prove; the engine facts record the algorithms (`polars-sum-float`);
* so the engine's result is within twice the bound of one the reference
  allows: `"abs"`, as a double;
* where the argument's values have one sign nothing cancels, and the bound
  is also relative (`relEps`): `"rel"`.

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
two results are within `2γ/(1 − γ)` of each other relative to either. Like
the engines' orders, this step is not proved in Lean; it is rounded up. -/
def relEps (k : Nat) : Float :=
  let u : Float := Float.scaleB 1.0 (-53)
  let ku := Float.ofNat k * u
  let γ := ku / (1.0 - ku)
  2.0 * γ / (1.0 - γ) * 1.000001

/-- As `upJson`, `0` for zero. -/
def upJsonZ (f : Float) : Json := if f == 0.0 then toJson (0 : Nat) else upJson f

/-- The bound for a double measure over rows described by `env`, at most
`rows` of them: absolute, and relative where the values have one sign. -/
def measureEps (env : List AVal) (m : Measure) (rows : Option Nat) :
    Option (Float × Option Float) := do
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
  let rel := if oneSign && n < 2 ^ 40 then some (relEps (if m.fn = .avg then n + 2 else n)) else none
  return (unscale (2 * t), rel)

/-- `"epsilon"` of a `--contract` request: per output column of the
transformation that is a double `SUM` or `AVG`,
`{"abs": …, "rel"?: …, "proved": {"abs": false, "rel"?: false}}`.

The bounds are a conjunction: each holds on its own, so the engine's result
is within `abs` of a result the reference allows and also within `rel` of
it, and a tolerance that either bound meets is met.

`proved` says which bounds Lean proves. Neither is yet: the reference's
half of `abs` is (`floatSum_mem`, `floatAvg_mem`), but that an engine's
order meets the same bound is a cited algorithm (`polars-sum-float`), and
`rel` is Higham's no-cancellation bound, stated here without a proof. A
route that rests on them is tested, not proved. -/
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
  let some (r, _, ms) := findAggregate root | return Json.mkObj []
  let some (srcs, _) := colSrcs plan.root | return Json.mkObj []
  let T := Rel.keyedWindows cat A F (fun _ => [])
  let env := r.aeval cat A F T
  let doubles := (doubleIdx ms).filterMap (ms[·]?)
  let names := if plan.names.length == srcs.length then plan.names
    else (List.range srcs.length).map (s!"#{·}")
  let cols := (names.zip srcs).filterMap fun (name, src) => match src with
    | .bounded j => some (name, match doubles[j]?.bind (measureEps env · r.maxRows) with
        | some (e, r) => Json.mkObj ([("abs", upJson e)] ++
            (match r with | some r => [("rel", upJson r)] | none => []) ++
            [("proved", Json.mkObj ([("abs", toJson false)] ++
              match r with | some _ => [("rel", toJson false)] | none => []))])
        | none => Json.mkObj [("abs", Json.null)])
    | .unbounded => some (name, Json.mkObj [("abs", Json.null)])
    | _ => none
  return Json.mkObj cols

/-! ## Per engine: the error carried through arithmetic

`epsilon` above is the summation order's share, the same for every engine.
`epsilonByEngine` carries it, and each engine's own per-operation error,
through the double arithmetic between the aggregates and the output, from
the ranges the preconditions give (#568's propagation):

* `+`, `-`: `ε' = (εa + εb)(1 + u) + 2u·(|a| + |b|)` once an input is off;
* `*`: `ε' = |a|εb + |b|εa + εaεb`, plus `2u` of the result's bound;
* `/` by an exact divisor bounded away from 0: `ε' = εa / min|b|`, plus `2u`;
* each engine's operations that differ from the reference's (the
  characterization's round 5): Polars's `/` by a literal multiplies by the
  reciprocal (`fl(x · fl(1/y))`, within `3u` of IEEE's quotient,
  polars-scalar-divisor), its `log10`, `log2` and `log(b)` are `ln / ln`
  (2.1 ulp), DuckDB's `log(b, x)` 1.4 ulp. `+ - * /` and `sqrt` are correctly
  rounded on both, as are integer-to-double conversions;
* other elementary functions are the platform's `libm` (macOS `tan` up to
  2.4 ulp, glibc `cos` and `tan` far more near zeros of `cos`): unbounded
  here where an input is off, and their rows stay `tested`.

None of this is proved in Lean (`proved` false): the per-operation constants
are probed, not modelled, and the propagation is the standard one. -/

/-- The unit roundoff of a double. -/
def unitRound : Float := Float.scaleB 1.0 (-53)

/-- A bound on `|e|` from the preconditions, for a double expression. -/
def magOf (env : List AVal) (e : Expr) : Option Float := do
  let a := e.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  return unscale (max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs)

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
`u` and the result's bound: Polars's `/` by a literal, its logarithms by
`ln / ln`, DuckDB's `log(b, x)`. -/
def opExtra (engine : String) : Expr → Option Float
  | .bin .fdiv _ (.lit _) => if engine == "polars" then some 3.0 else some 0.0
  | .un (.fmath .log10) _ | .un (.fmath .log2) _ =>
    if engine == "polars" then some (2.0 * (2.1 + 1.0)) else some 0.0
  | .bin .flogb _ _ =>
    some (2.0 * ((if engine == "polars" then 2.1 else 1.4) + 1.0))
  | _ => some 0.0

/-- How far an engine's value of `e` may be from the reference's, from the
columns' errors `cols` (`none`: not bounded). -/
def exprEps (engine : String) (env : List AVal) (cols : List (Option Float)) :
    Expr → Option Float
  | .lit _ => some 0.0
  | .field i => cols.getD i none
  | e@(.un .fneg a) => exprEps engine env cols a |>.map fun x => x + 0.0 * (magOf env e).getD 0.0
  | .un .itof a => (exprEps engine env cols a).bind fun x => if x == 0.0 then some 0.0 else none
  | e@(.bin f a b) => do
    let ea ← exprEps engine env cols a
    let eb ← exprEps engine env cols b
    let extra ← opExtra engine e
    let own ← if extra == 0.0 then pure 0.0 else (resultMag env e).map (extra * unitRound * ·)
    if ea == 0.0 && eb == 0.0 then return own
    match f with
    | .fadd | .fsub =>
      let ma ← magOf env a
      let mb ← magOf env b
      return (ea + eb) * (1.0 + unitRound) + 2.0 * unitRound * (ma + mb) + own
    | .fmul =>
      let ma ← magOf env a
      let mb ← magOf env b
      return ma * eb + mb * ea + ea * eb + 2.0 * unitRound * (ma + ea) * (mb + eb) + own
    | .fdiv =>
      guard (eb == 0.0)
      let lb ← minAbsOf env b
      let mq ← resultMag env e
      return ea / lb + 2.0 * unitRound * mq + own
    | _ => none
  | e@(.un _ a) => do
    let ea ← exprEps engine env cols a
    let extra ← opExtra engine e
    if ea == 0.0 && extra == 0.0 then return 0.0
    if ea == 0.0 then return extra * unitRound * (← resultMag env e)
    none
  | .ifThen _ t f => do
    let et ← exprEps engine env cols t
    let ef ← exprEps engine env cols f
    return max et ef
  | .hof _ _ _ => none

/-- Each column's error on `engine`, for plans of projections, filters,
sorts and one aggregate over reads. -/
def colEps (engine : String) (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) : Rel → Option (List (Option Float))
  | .read t => some ((List.range (cat t).arity).map fun _ => some 0.0)
  | .values n _ => some ((List.range n).map fun _ => some 0.0)
  | .filter r _ | .orderBy r _ | .fetch r _ _ | .distinct r => colEps engine cat A F T r
  | .emit r m => (colEps engine cat A F T r).map fun cs => m.map (cs.getD · none)
  | .project r es => (colEps engine cat A F T r).map fun cs =>
      cs ++ es.map (exprEps engine (r.aeval cat A F T) cs)
  | .aggregate r gs ms => (colEps engine cat A F T r).map fun cs =>
      let env := r.aeval cat A F T
      gs.map (fun _ => some 0.0) ++ ms.map fun m => do
        let ea ← exprEps engine env cs m.arg
        match m.fn with
        | .fsum | .avg =>
          let (order, _) ← measureEps env m r.maxRows
          let n ← r.maxRows
          return order + (if m.fn = .avg then ea else Float.ofNat n * ea)
        | .count => return 0.0
        | .min | .max => return ea
        | _ => if ea == 0.0 then some 0.0 else none
  | _ => none

/-- `"epsilon_by_engine"` of a `--contract` request: per engine and double
output column, how far the engine's value may be from one the reference
allows, `{"abs": …, "proved": {"abs": false}}` (`null`: not bounded). -/
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
  return Json.mkObj <| engines.map fun engine =>
    let cols := colEps engine cat A F T root
    (engine, Json.mkObj <| ((names.zip kinds).zipIdx.filter (·.1.2 == .float)).map
      fun ((name, _), i) => (name, Json.mkObj [
        ("abs", match cols.bind (·.getD i none) with | some e => upJsonZ e | none => Json.null),
        ("proved", Json.mkObj [("abs", toJson false)])]))

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
  `-2⁶³` by the preconditions. -/

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
  let reads := plan.root.reads.filter fun (g, o, _) =>
    !(g == "rel.keys" && !keys) && !(o == "empty_group_aggregates" && !empty) &&
      !(o == "avg_int_result" && !iavg) && !(g == "cmp" && !cmp) &&
      !(o == "min_mod_neg_one" && !minMod)
  return readsJson reads

end Substrait.Epsilon
