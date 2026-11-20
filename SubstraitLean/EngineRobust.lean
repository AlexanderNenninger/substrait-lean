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

/-- `t` units of `2⁻¹⁰⁷⁴` at least the double `f ≥ 0`: its own scaled value,
which is exact, as a reported `ε` is a double rounded up. -/
def scaledOf (f : Float) : Option Nat :=
  if f.isNaN || f.isInf || f < 0 then none
  else some ((FloatCode.scaled (FloatCode.ofFloat f)).toNat + 1)

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
  let T := Rel.keyedWindows cat A F ⟨fun _ => []⟩
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
        (fun j => (j.getNum?.toOption).map (·.toFloat)) with
    | some f => match scaledOf f with
      | some t => engineVal t (!covs.contains n) a
      | none => { a with int := a.int.map fun _ => Bound.top }
    | none => a
  -- Each postcondition's columns as expressions over the transformation's
  -- output (`Post.plan`).
  let out := R.posts.flatMap fun p =>
    let cs := (List.range env.length).map Expr.field ++ p.exprs
    p.mapping.map fun j => ((cs.getD j (.lit .null)).absD E []).certainlyTrue
  return toJson (out.map fun b => Json.mkObj [("robust", toJson b),
    ("proved_on", toJson (if b then signKeptOn es else []))])


/-- `"source_threshold"` issues of a `--contract` request (D52, ruling 104):
where the plan carries a source mark, every row decision that reads a marked
value has one outcome over the band (C-rows), every output column that reads
one has a bound (C-out), every postcondition that reads one holds over it
(C-contract), and every reported key holds through a key inside it that reads
none (C-key, ruling 108). Each failure is an error issue: the source may keep other rows,
or give other values, than the plan Sverify verified. Checked for the engine
the request's `"profile"` names, or for every engine. -/
def sourceIssues (es : List EngineProfile) (input : Json) : Except String (List Json) := do
  let some ⟨_, plan, cat, A, F, _, root, T⟩ ← Epsilon.inputs? input | return []
  -- No mark, no tainted value: nothing to check (every request comes here).
  unless Epsilon.Rel.hasMark root do return []
  let deps := Epsilon.Rel.markDeps cat root
  let prof := (input.getObjValAs? String "profile").toOption
  let engines := match prof with
    | some e => if es.any (fun (E : EngineProfile) => E.name == e) then [e]
      else es.map (fun (E : EngineProfile) => E.name)
    | none => es.map (fun (E : EngineProfile) => E.name)
  let issue (what : String) : Json := Json.mkObj [("kind", toJson "source_threshold"),
    ("error", toJson true), ("assumed", toJson false), ("expr", toJson what),
    ("constant", toJson false), ("under_and_or", toJson false), ("bound", .null)]
  -- C-rows: a decision that may differ over the band.
  let rows := (engines.flatMap fun e => (Epsilon.rowSites es e cat A F T root).filterMap
    fun (ok, dep, what) => if !ok && dep then some what else none).eraseDups
  -- C-out: an output column that reads a marked value and has no bound.
  let names := if plan.names.length == deps.length then plan.names
    else (List.range deps.length).map (s!"#{·}")
  -- Each engine's column bounds, computed once: one pass over the plan per engine.
  let bounds := engines.map fun e => Epsilon.colEps es e cat A F T root
  let cols := ((names.zip deps).zipIdx.filterMap fun ((n, d), i) =>
    if d && bounds.any (fun b => (b.bind (·.getD i none)).isNone)
    then some s!"the column {n}" else none)
  -- C-contract: a postcondition that reads a marked column and does not hold over the band.
  let rob ← robust es input
  let R ← ContractCheck.parse input
  let robs := (rob.getArr?.toOption.getD #[]).toList.map fun j =>
    (j.getObjValAs? Bool "robust").toOption.getD false
  let posts := (R.posts.flatMap fun p =>
      let cs := (List.range deps.length).map Expr.field ++ p.exprs
      p.mapping.map fun j => cs.getD j (.lit .null)).zip robs
  let contract := posts.filterMap fun (e, r) =>
    if !r && Epsilon.Expr.markDep deps e then some s!"the postcondition {e.render}" else none
  -- C-key (ruling 108): a reported key holds on the engine's result only through
  -- a derived key inside it that reads no marked column.
  let keys := match R.transform with
    | some p =>
      let K := R.kenv
      let derived := p.root.keys R.cat K.cols K.facts K.keys
      let pdeps := Epsilon.Rel.markDeps R.cat p.root
      (R.keysIn K).filterMap fun (k, ok) =>
        if !ok || derived.any (fun k' => k'.all (k.contains ·) && k'.all fun c => !pdeps.getD c true)
        then none
        else some s!"the key [{", ".intercalate (k.map fun c => names.getD c s!"#{c}")}]"
    | none => []
  return (rows ++ cols ++ contract ++ keys).map issue

end Substrait.EngineRobust
