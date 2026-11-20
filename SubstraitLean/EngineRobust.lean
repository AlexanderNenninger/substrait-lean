import SubstraitLean.Epsilon

/-!
# Postconditions that hold on every engine's doubles (#1045)

A postcondition is proved of the reference's values (`ContractCheck`). Where
an output double column is an engine's own sum or statistic, the engine's
value differs from the reference's by up to the column's bound `ε`
(`Report.epsilon`). A postcondition that reads such a column holds on the
engine too when it holds of every value the engine may give: the column's
abstract value widened by `ε` on both sides (`Bound.widen`) and, for a sum,
an average or a variance, kept to its sign (`Bound.signHull`). That is
**engine-robust**: `robust` reports it per postcondition, and the routes
refuse only a postcondition that is not (`routes._plan_bound`).

Soundness: an engine value `v` within `ε` of the reference's `r`
(`epsilon_sum_cr`, `epsilon_var_cr`, …) is in the widened bound
(`Bound.widen_mem`), and one that keeps the sign Lean gave `r` is in its sign
part (`Bound.signHull_mem`). A sum of values of one sign keeps that sign in
every order but Kahan's (`FloatBounds.StdModel.TreeSum.sign`); a variance
is clamped at `0` (`Stat.clamp_near`). So `engineVal_mem` gives the
engine's row the environment the postcondition is checked in, and
`Expr.absD_sound` its value there.
-/

namespace Substrait.EngineRobust

open Lean (Json toJson)
open ContractCheck ShardCheck Parse

/-- The sign of `b`: at least `0` where `b` is, at most `0` where it is. -/
def signHull (b : Bound) : Bound :=
  ⟨b.lo.bind fun l => if 0 ≤ l then some 0 else none,
   b.hi.bind fun h => if h ≤ 0 then some 0 else none⟩

/-- A value that keeps the sign `b` gives is in its sign part. -/
theorem signHull_mem {b : Bound} {v : Int} (hlo : ∀ l, b.lo = some l → 0 ≤ l → 0 ≤ v)
    (hhi : ∀ h, b.hi = some h → h ≤ 0 → v ≤ 0) : (signHull b).Mem v := by
  obtain ⟨lo, hi⟩ := b
  constructor
  · intro l hl
    cases lo with
    | none => simp [signHull] at hl
    | some x =>
      simp only [signHull, Option.bind_some] at hl
      split at hl
      · next hx => cases hl; exact hlo x rfl hx
      · cases hl
  · intro h hh
    cases hi with
    | none => simp [signHull] at hh
    | some x =>
      simp only [signHull, Option.bind_some] at hh
      split at hh
      · next hx => cases hh; exact hhi x rfl hx
      · cases hh

/-- `b` widened by `t` units of `2⁻¹⁰⁷⁴` (`FloatCode.scaled`) on both sides. -/
def widen (t : Nat) (b : Bound) : Bound :=
  ⟨b.lo.map fun l => FloatCode.codeLo (FloatCode.scaled l - t),
   b.hi.map fun h => FloatCode.codeHi (FloatCode.scaled h + t)⟩

/-- **A value within `t` of one of `b` is in `b` widened by `t`.** -/
theorem widen_mem {b : Bound} {t : Nat} {r v : Int} (hr : b.Mem r)
    (hv : (FloatCode.scaled v - FloatCode.scaled r).natAbs ≤ t) : (widen t b).Mem v := by
  obtain ⟨lo, hi⟩ := b
  obtain ⟨hlo, hhi⟩ := hr
  constructor
  · intro l hl
    cases lo with
    | none => simp [widen] at hl
    | some x =>
      simp only [widen, Option.map_some, Option.some.injEq] at hl
      subst hl
      have := FloatCode.scaled_mono (hlo x rfl)
      exact FloatCode.codeLo_le (by omega)
  · intro h hh
    cases hi with
    | none => simp [widen] at hh
    | some x =>
      simp only [widen, Option.map_some, Option.some.injEq] at hh
      subst hh
      have := FloatCode.scaled_mono (hhi x rfl)
      exact FloatCode.le_codeHi (by omega)

/-- The values an engine may give for an output column whose reference value
`a` describes: within `t` of it, and, where `sign`, of the same sign. -/
def engineVal (t : Nat) (sign : Bool) (a : AVal) : AVal :=
  { a with int := a.int.map fun b => if sign then (widen t b).meet (signHull b) else widen t b }

/-- **The engine's value is in `AVal.engine`**: NULL where the reference's
is, else within `t` of it and, where `sign`, of the sign Lean gave it, by
canonical codes (D31). -/
theorem engineVal_mem {a : AVal} {t : Nat} {sign : Bool} {r v : Int} (hr : a.Mem (.float r))
    (hv : (FloatCode.scaled (FloatCode.canon v) - FloatCode.scaled (FloatCode.canon r)).natAbs ≤ t)
    (hs : sign = true → ∀ b, a.int = some b →
      (∀ l, b.lo = some l → 0 ≤ l → 0 ≤ FloatCode.canon v) ∧
        (∀ h, b.hi = some h → h ≤ 0 → FloatCode.canon v ≤ 0)) :
    (engineVal t sign a).Mem (.float v) := by
  obtain ⟨b, hb, hm, hk⟩ := hr
  refine ⟨if sign then (widen t b).meet (signHull b) else widen t b, ?_, ?_, hk⟩
  · simp [engineVal, hb]
  · cases sign with
    | false => exact widen_mem hm hv
    | true =>
      obtain ⟨hlo, hhi⟩ := hs rfl b hb
      exact Bound.mem_meet (widen_mem hm hv) (signHull_mem hlo hhi)

/-- `t` units of `2⁻¹⁰⁷⁴` at least the reported `ε ≥ 0`, read exactly from
its JSON number: `⌈ε · 2¹⁰⁷⁴⌉`. -/
def scaledOf (n : Lean.JsonNumber) : Nat :=
  let q := ExactBound.ofJsonNumber n * ((2 ^ 1074 : Nat) : Rat)
  q.ceil.toNat

/-- The `sum_order` behaviours whose sums keep the sign of values of one sign
(`FloatBounds.StdModel.TreeSum.sign`): every order the engines' rows name
but Kahan's (`COMPENSATED`), whose sign is a fact, not yet a theorem. -/
def signKept : List String := ["EXACT", "ANY", "PAIRWISE", "SEQUENTIAL", "SCALED_CONSTANT"]

/-- The engines whose sums keep the sign by the theorem: an engine-robust
postcondition is proved there, and tested on the others. -/
def signKeptOn (es : List EngineProfile) : List String :=
  es.filterMap fun e =>
    if (e.table.allows "agg.fsum" "sum_order" []).all (signKept.contains ·) then some e.name else none

-- Polars's in-memory `sum` is Kahan's (polars-sum-float).
#guard signKeptOn builtinEngines == ["duckdb", "spark"]

variable [Boxes.Ambient]
/-- `"robust"` of a `--contract` request: per postcondition, in the order of
`"ensures"`, `{"robust": …, "proved_on": […]}`: whether it is certainly TRUE
over the values every engine may give (`engineVal`), and the engines where
that is a theorem (`signKeptOn`; tested on the others): each double column `Report.epsilon` bounds widened by
its `"abs"`, and a sum's, average's or variance's kept to its sign (not a
covariance's). Columns without a finite bound keep their abstract value: a
postcondition reads only their sign (`signBound`, which
`TreeSum.sign` keeps on every engine). -/
def robust (es : List EngineProfile) (input : Json) : Except String Json := do
  let R ← ContractCheck.parse input
  let some plan := R.transform | return Json.arr #[]
  let cat := R.cat
  let A := fun t => tableEnv (R.schemas t) (R.preOf t)
  let F := fun t => (R.preOf t).flatMap Expr.factsOf
  let T := Rel.keyedWindows cat A F { keys := fun _ => [] }
  let env := (plan.root.capReads R.caps).aeval cat A F T
  let names := if plan.names.length == env.length then plan.names
    else (List.range env.length).map (s!"#{·}")
  let eps ← Epsilon.epsilon es input
  -- A covariance has no sign of its own.
  let covs : List String := match Epsilon.statCols plan.root with
    | some cs => (names.zip cs).filterMap fun
        | (n, some (some m)) => if m.fn matches .cov _ then some n else none
        | _ => none
    | none => []
  let E := (names.zip env).map fun (n, a) =>
    match ((eps.getObjVal? n).toOption.bind (·.getObjVal? "abs" |>.toOption)).bind
        (fun j => j.getNum?.toOption) with
    | some f => if f.mantissa < 0 then { a with int := a.int.map fun _ => Bound.top }
      else engineVal (scaledOf f) (!covs.contains n) a
    | none => a
  -- Each postcondition's columns as expressions over the transformation's
  -- output (`Post.plan`).
  let out := R.posts.flatMap fun p =>
    let cs := (List.range env.length).map Expr.field ++ p.exprs
    p.mapping.map fun j => ((cs.getD j (.lit .null)).absD E []).certainlyTrue
  return toJson (out.map fun b => Json.mkObj [("robust", toJson b),
    ("proved_on", toJson (if b then signKeptOn es else []))])

end Substrait.EngineRobust
