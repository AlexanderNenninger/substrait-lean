import SubstraitLean.ShardCheck

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

end Substrait.Epsilon
