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
  allows: `"abs"`, as a double.

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

/-- The bound for a double measure over rows described by `env`, at most `rows` of them. -/
def measureEps (env : List AVal) (m : Measure) (rows : Option Nat) : Option Float := do
  let a := m.arg.absD env []
  guard a.intsOnly
  let b ← a.int
  let lo ← b.lo
  let hi ← b.hi
  let n ← rows
  let bs := max (FloatCode.scaled lo).natAbs (FloatCode.scaled hi).natAbs
  guard (n ≤ 2 ^ 32 ∧ bs ≤ 2 ^ 1474)
  let t := if m.fn = .avg then FloatCode.avgTolScaled n bs else FloatCode.sumTolScaled n bs
  return unscale (2 * t)

/-- `"epsilon"` of a `--contract` request: per output column of the
transformation that is a double `SUM` or `AVG`, `{"abs": …}`. -/
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
        | some e => Json.mkObj [("abs", upJson e)]
        | none => Json.mkObj [("abs", Json.null)])
    | .unbounded => some (name, Json.mkObj [("abs", Json.null)])
    | _ => none
  return Json.mkObj cols

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
