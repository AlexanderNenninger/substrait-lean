import Sverify.Engines.Engine
import Sverify.Engines.Transfer
import Sverify.Core.AllowedNear
import Sverify.Analysis.AllowedAnalysis

/-!
# What an engine's model is sound for (#900)

`Engine.Sound E side`: for every plan `r` that `E` translates to `r'`, where
`side` holds, the rows `r'` computes with `E`'s functions are a result the reference allows for `r`
(`Rel.Allowed`). `Engine.reference_sound` is the reference's own; each
engine proves its own (`Engine.duckdb_sound`, `Engine.polars_sound`,
`Engine.spark_sound`).

`Engine.GuardFreeSide` is guard elimination's side condition
(`Rel.guardFree_sound`), under which the engines that run the plan as written
(Polars, Spark) are sound. Its plan part (`Engine.GuardFreePlan`) is
decidable; its data part (`Engine.GuardFreeData`) states preconditions on the
catalog, as `hK` does, with the size hypothesis (`Rel.Small`).
`Engine.guardFreeSide_example` shows one catalog and plan that meet it, so
that `Engine.polars_sound` and `Engine.spark_sound` apply to something.
`Engine.example_contract` goes on to inhabit every hypothesis of
`Engine.contract_sound` for that plan and a postcondition, and each engine
(`Engine.duckdb_contract_example`, `Engine.polars_contract_example`,
`Engine.spark_contract_example`) supplies its own two.

What each engine's side condition is. DuckDB's model is its profile's
functions where they do not raise (`okImpl`), so its side condition is that
the translated plan does not raise (`Engine.NoRaiseSide`). Polars's and
Spark's models are the written plan's functions, total: on data that meets
`Engine.GuardFreeSide` they compute `Rel.eval`
(`Impl.Faithful`, guard elimination). That the engine computes what its
model says on such data is D16's trusted claim (`Engine.Runs`), carried by
the engine's facts and tests.

`Engine.contract_sound` composes it with `contract_sound_allowed`: unless the
translated plan raises, the contract's postconditions hold on the rows the
engine's model computes for it (`r'.eval cat E.impl`). `Engine.contract_sound_runs` is the form for the
engine's actual result, which D16's trusted claim (`Engine.Runs`) places in
`Rel.AllowedP E.table`; it needs the transfer check `htr` from `E`'s table
to the reference's, which fails where an engine's choice is not the
reference's (`sum_order`, `stat_algo`, `quantile_interp`, `zero_sign` on every
engine). Those reads need the tolerance route of #929, PR 3 of #900.

The conclusion is `Rel.Allowed`, the reference's set, and needs no table
condition. Membership in `Rel.AllowedP E.table` follows only under
`Engine.RefWithin` (`Engine.Sound.allowedP`): no engine's table admits the
reference's choice at every option (`Profile.reference.table.leB` is false
for all three).
-/

namespace Substrait

variable [Boxes.Ambient]

/-! ## The bridge -/

/-- The side condition of an engine whose model is its profile's functions
where they do not raise (`okImpl`, DuckDB): the translated plan does not
raise. -/
def Engine.NoRaiseSide (E : Engine) (cat : Catalog) (r : Rel) : Prop :=
  ∀ r', E.lower r = some r' → ¬r'.Raises E.profile cat

/-- **`E`'s run is sound under `side`**: where `E` translates `r` to `r'` and
`side cat r` holds, the rows `r'` computes with `E`'s functions are a result the
reference allows for `r`. -/
def Engine.Sound (E : Engine) (side : Catalog → Rel → Prop) : Prop :=
  ∀ {cat : Catalog} {r r' : Rel}, E.lower r = some r' → side cat r →
    r.Allowed cat (r'.eval cat E.impl)

theorem Engine.reference_sound : Engine.reference.Sound fun _ _ => True := by
  intro cat r r' hl _; cases hl; exact r.eval_allowed cat

/-- The data part of guard elimination's side condition: preconditions on the catalog
(`A` its tables' values, `F` their facts, `T` the window keys), and the size
hypothesis. Not decidable: the checker assumes it of the data, as `hK`. -/
def Engine.GuardFreeData (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (r : Rel) : Prop :=
  cat.WF ∧ (∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row) ∧
    (∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) ∧ T.SoundAll cat ∧ r.Small cat

/-- The plan part of guard elimination's side condition, decidable (`Rel.checkWF`):
the plan is well-formed, keeps its loose subtractions (`Rel.looseSub`), and
`Rel.mayIssues` reports only assumed issues. -/
def Engine.GuardFreePlan (cat : Catalog) (A : String → List AVal) (F : String → List Fact)
    (T : WindowKeys) (r : Rel) : Prop :=
  r.WF cat ∧ r.looseSub = true ∧ (r.mayIssues cat A F T false).all (·.1.assumed) = true

/-- **Guard elimination's side condition**: `Rel.guardFree_sound`'s
hypotheses, Polars's and Spark's. -/
def Engine.GuardFreeSide (cat : Catalog) (r : Rel) : Prop :=
  ∃ A F T, Engine.GuardFreeData cat A F T r ∧ Engine.GuardFreePlan cat A F T r

/-! ## Within the engine's table -/

/-- The reference's choices are within `E`'s at every option `r` reads. -/
def Engine.RefWithin (E : Engine) (r : Rel) : Prop :=
  ∀ p ∈ r.reads, Profile.reference.table.LeAt E.table p

theorem Engine.refWithin_of_transferB {E : Engine} {r : Rel}
    (h : transferB r E.table Profile.reference.table = true) : E.RefWithin r :=
  fun p hp => ProfileTable.leAt_of_leAtB (List.all_eq_true.mp h p hp)

/-- Where the reference's choices are within `E`'s, `E`'s table allows the
run too. -/
theorem Engine.Sound.allowedP {E : Engine} {side : Catalog → Rel → Prop} (hE : E.Sound side)
    {cat : Catalog} {r r' : Rel} (hl : E.lower r = some r')
    (hs : side cat r) (hw : E.RefWithin r) : r.AllowedP E.table cat (r'.eval cat E.impl) :=
  Rel.AllowedP_transfer hw (Rel.allowedP_reference.mpr (hE hl hs))

/-! ## Determined plans (#1285)

A plan determined up to an observation (`Rel.DeterminedUpTo`) has one observed
answer, the reference's. Every sound engine gives it. -/

/-- **A sound engine gives the one observed answer of a determined plan**: its
model's rows are `Equiv o ctx` to the reference's value. -/
theorem Engine.Sound.equiv_eval {E : Engine} {side : Catalog → Rel → Prop} (hE : E.Sound side)
    {cat : Catalog} {r r' : Rel} (hl : E.lower r = some r') (hs : side cat r) {o : Obs}
    {ctx : ObsCtx} (hd : r.DeterminedUpTo o ctx cat) :
    Relation.Equiv o ctx (r'.eval cat E.impl) (r.eval cat) :=
  hd _ (hE hl hs)

/-- **Two sound engines agree on a determined plan** up to the observation, in
the context where `ctx` composes with itself (`Comp ctx ctx ctx` for an exact
tolerance; a tolerance `t` agrees within `2t`). -/
theorem Engine.sound_agree {E F : Engine} {sE sF : Catalog → Rel → Prop} (hE : E.Sound sE)
    (hF : F.Sound sF) {cat : Catalog} {r r' r'' : Rel} (hl : E.lower r = some r')
    (hl' : F.lower r = some r'') (hs : sE cat r) (hs' : sF cat r) {o : Obs} {ctx ctx' : ObsCtx}
    (hc : ctx.WF) (hcomp : ObsCtx.Comp ctx ctx ctx') (hd : r.DeterminedUpTo o ctx cat) :
    Relation.Equiv o ctx' (r'.eval cat E.impl) (r''.eval cat F.impl) :=
  hd.pair hc hcomp (hE hl hs) (hF hl' hs')

/-! ## Contracts on an engine -/

/-- The postcondition columns `mp` of `es`, as the contract query computes
them on a result `t` of the transformation. -/
def postRows (es : List Expr) (mp : List Nat) (t : Relation) : Relation :=
  (t.map fun row => row ++ es.map (·.eval row)).map fun row => mp.map (row.getD · .null)

theorem Rel.Allowed.postRows {cat : Catalog} {T : Rel} {es : List Expr} {mp : List Nat}
    {t : Relation} (h : T.Allowed cat t) :
    (Rel.emit (.project T es) mp).Allowed cat (postRows es mp t) :=
  ⟨_, ⟨t, h, rfl⟩, rfl⟩

/-- **A verified contract holds on an engine's model** (#900). On data that
meets the preconditions, with `contract_sound_allowed`'s hypotheses on the
transformation `T` and its postconditions `es` (selected by `mp`), where `E`
translates `T` to `T'` and `E`'s side condition holds, the postconditions hold on the rows `T'` computes with `E`'s
functions. -/
theorem Engine.contract_sound {E : Engine} {side : Catalog → Rel → Prop} (hE : E.Sound side)
    {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafe : T.FloatOpenSafe q ctx cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true)
    {T' : Rel} (hl : E.lower T = some T') (hside : side cat T) :
    ∀ row ∈ postRows es mp (T'.eval cat E.impl), ∀ v ∈ row, v = .bool true :=
  contract_sound_allowed hcat hS hpre hT hq hsafe hsh hrob hQ hW hproved
    (hE hl hside).postRows

/-- **D16's trusted claim**: what `E` returns for `r` on `cat` is `out`, a
result `E`'s table allows. The evidence behind it, each observation row `r`
reads proved or tested (`Engine.Refines`), is listed in `trusted-base.md`
and is no hypothesis here. For an engine that runs the plan as it is
(`lower := some`), `Rel.AllowedE.allowedP` gives it from `Rel.AllowedE`. -/
def Engine.Runs (E : Engine) (cat : Catalog) (r : Rel) (out : Relation) : Prop :=
  r.AllowedP E.table cat out

/-- **An engine's actual result is the one observed answer of a determined
plan**, where `E`'s choices are within the reference's at every option the
plan reads (`htr`) and D16's trusted claim holds of the result
(`Engine.Runs`). Where `htr` fails (`sum_order`, `stat_algo`,
`quantile_interp`, `zero_sign`) the near form is #929's; no theorem is stated
for it. -/
theorem Engine.Runs.equiv_eval {E : Engine} {cat : Catalog} {r : Rel} {out : Relation}
    (hrun : E.Runs cat r out) (htr : transferB r Profile.reference.table E.table = true)
    {o : Obs} {ctx : ObsCtx} (hd : r.DeterminedUpTo o ctx cat) :
    Relation.Equiv o ctx out (r.eval cat) :=
  hd _ (Rel.allowedP_reference.mp (Rel.transfer_of_transferB htr hrun))

/-- **Every result `t` allows for `r` is, up to `q`, one of the reference's
orders.** The side condition of a run on doubles: `Rel.FloatOpenSafe` is the
case of the reference's table (`Rel.floatOpenSafe_iff_reference`), and an
engine whose choices are the reference's at every option `r` reads has it
from there (`Rel.floatOpenSafeP_of_transferB`). `transferB` fails on every
engine at `sum_order`; for an aggregate at the root whose double `SUM`s and
`AVG`s are near the correctly rounded ones (`Rel.SumsNear`),
`Rel.floatOpenSafeP_aggregate` (`SubstraitLean/OpenSums.lean`) discharges it,
and `Engine.polars_sum_example` applies it to a double `SUM` on Polars. Elsewhere
(`stat_algo`, `quantile_interp`, `zero_sign`, a double `SUM` below a filter or a
join) nothing discharges it yet (#929). -/
def Rel.FloatOpenSafeP (q : Obs) (ctx : ObsCtx) (t : ProfileTable) (cat : Catalog) (r : Rel) :
    Prop :=
  ∀ out, r.AllowedP t cat out → ∃ out', r.OrderAllowed cat out' ∧ Relation.Equiv q ctx out' out

theorem Rel.floatOpenSafe_iff_reference {q : Obs} {ctx : ObsCtx} {cat : Catalog} {r : Rel} :
    r.FloatOpenSafeP q ctx Profile.reference.table cat ↔ r.FloatOpenSafe q ctx cat :=
  forall_congr' fun _ => imp_congr_left Rel.allowedP_reference

/-- With the reference's choices at every option `r` reads, the reference's
side condition is the table's. -/
theorem Rel.floatOpenSafeP_of_transferB {q : Obs} {ctx : ObsCtx} {cat : Catalog} {r : Rel}
    {t : ProfileTable} (htr : transferB r Profile.reference.table t = true)
    (h : r.FloatOpenSafe q ctx cat) : r.FloatOpenSafeP q ctx t cat :=
  fun out ho => h out (Rel.allowedP_reference.mp (Rel.transfer_of_transferB htr ho))

/-- **A verified contract holds on the engine's actual result, open float
rows included**, where every result `E`'s table allows for `T` is, up to `q`,
one of the reference's orders (`Rel.FloatOpenSafeP`), and D16's trusted claim
holds of the result (`Engine.Runs`). Where `transferB` fails, a root
aggregate's double `SUM` and `AVG` discharge `hsafeE` by
`Rel.floatOpenSafeP_aggregate`; other shapes are #929's (`Rel.FloatOpenSafeP`). -/
theorem Engine.contract_sound_runs_near {E : Engine}
    {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafeE : T.FloatOpenSafeP q ctx E.table cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true)
    {out : Relation} (hrun : E.Runs cat T out) :
    ∀ row ∈ postRows es mp out, ∀ v ∈ row, v = .bool true := by
  obtain ⟨t', ht', heq⟩ := hsafeE out hrun
  exact contract_sound_near hcat hS hpre hT hq hsh hrob hQ hW hproved ht' heq

/-- **A verified contract holds on the engine's actual result**, where `E`'s
choices are within the reference's at every option `T` reads (`htr`) and D16's
trusted claim holds of the result (`Engine.Runs`). `htr` fails where an
engine's choice is not the reference's (`sum_order`, `stat_algo`,
`quantile_interp`, `zero_sign`); there `Engine.contract_sound_runs_near`
takes `Rel.FloatOpenSafeP` over the engine's table instead. -/
theorem Engine.contract_sound_runs {E : Engine}
    {cat : Catalog} (hcat : cat.WF) {S : String → List AVal}
    {pre : String → List Expr} {T : Rel} {es : List Expr} {mp : List Nat}
    (hS : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (S t) row)
    (hpre : ∀ t, ∀ row ∈ (cat t).rows, ∀ e ∈ pre t, (e.eval row).isTrue = true)
    (hT : T.WF cat) {q : Obs} {ctx : ObsCtx} (hq : q.rows = .multiset)
    (hsafe : T.FloatOpenSafe q ctx cat) {sh : Nat → Option Shift}
    (hsh : ∀ i s, sh i = some s → s.Sound q ctx i)
    (hrob : ∀ j ∈ mp, (postExpr (T.arity cat) es j).robustB q ctx sh = true)
    (hQ : (Rel.emit (.project T (es.map (·.narrow sh))) mp).WF cat) {W : WindowKeys}
    (hW : W.SoundAll cat)
    (hproved : ((Rel.emit (.project T (es.map (·.narrow sh))) mp).aeval cat
      (fun t => tableEnv (S t) (pre t)) (fun t => (pre t).flatMap Expr.factsOf) W).all
        AVal.certainlyTrue = true)
    (htr : transferB T Profile.reference.table E.table = true) {out : Relation}
    (hrun : E.Runs cat T out) :
    ∀ row ∈ postRows es mp out, ∀ v ∈ row, v = .bool true :=
  Engine.contract_sound_runs_near hcat hS hpre hT hq (Rel.floatOpenSafeP_of_transferB htr hsafe)
    hsh hrob hQ hW hproved hrun

end Substrait

namespace Substrait

/-! ## An example that meets the side condition

One catalog and one plan, shown to meet `Engine.GuardFreeSide`, so that
`Engine.polars_sound` and `Engine.spark_sound` apply to something
(`engines/polars/Sverify/Polars/Engine.lean`, `engines/spark/Sverify/Spark/Engine.lean`).
The plan adds 1 to a column of two rows. On unbounded data the sum can leave
64 bits, so the plan has an overflow to eliminate: the environment bounds the
column to `[0, 100]` and gives it integer kind, which rules it out and lets the
analysis find the postcondition `0 < sum` certainly true. The example runs with no
black boxes. -/

/-- No black boxes. -/
abbrev Engine.exampleBoxes : Boxes.Ambient := Boxes.Ambient.none

section Example
attribute [local instance] Engine.exampleBoxes

def Engine.exampleCat : Catalog := fun
  | "t" => ⟨1, [[.int 1], [.int 2]]⟩
  | _ => ⟨0, []⟩

def Engine.examplePlan : Rel :=
  .project (.read "t") [.bin .add (.field 0) (.lit (.int 1))]

def Engine.exampleA : String → List AVal := fun
  | "t" => [{ int := some ⟨some 0, some 100⟩, nk := some .int }]
  | _ => []

theorem Engine.exampleCat_wf : Engine.exampleCat.WF := by
  intro t row h
  unfold Engine.exampleCat at h ⊢
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  · simp at h

theorem Engine.exampleA_mem :
    ∀ t, ∀ row ∈ (Engine.exampleCat t).rows, EnvMem (Engine.exampleA t) row := by
  intro t row h i
  unfold Engine.exampleCat at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    unfold Engine.exampleA
    rcases h with rfl | rfl <;> cases i <;>
      simp [AVal.Mem, AVal.MemR, AVal.MemNum, Bound.Mem, AVal.top]
  · simp at h

theorem Engine.examplePlan_wf : Engine.examplePlan.WF Engine.exampleCat := by
  simp [Engine.examplePlan, Rel.WF, Expr.refsLt, Rel.arity, Engine.exampleCat]

theorem Engine.guardFreeSide_example : Engine.GuardFreeSide Engine.exampleCat Engine.examplePlan := by
  refine ⟨Engine.exampleA, fun _ => [], WindowKeys.none,
    ⟨Engine.exampleCat_wf, Engine.exampleA_mem, ?_, WindowKeys.none_soundAll _, ?_⟩,
    Engine.examplePlan_wf, ?_, ?_⟩
  · intro t row h f hf
    simp at hf
  · trivial
  · decide +kernel
  · decide +kernel

/-- The postcondition of the example: the sum, column 1 of the plan's output,
is positive. -/
def Engine.examplePost : List Expr := [.bin .lt (.lit (.int 0)) (.field 1)]

/-- **`Engine.contract_sound`'s hypotheses are inhabited**: for the example's
catalog, plan and postcondition (`Engine.examplePost`, column 2 of the
selection), every hypothesis but the engine's own (`hl`, `hside`) is
shown here: the data meets the bounds, the plan is well-formed and closed
(so `FloatOpenSafe`), no shift is used, and the analysis finds the
postcondition certainly true. Each engine states its two in its own
module. -/
theorem Engine.example_contract {E : Engine} {side : Catalog → Rel → Prop} (hE : E.Sound side)
    {T' : Rel} (hl : E.lower Engine.examplePlan = some T')
    (hside : side Engine.exampleCat Engine.examplePlan) :
    ∀ row ∈ postRows Engine.examplePost [2] (T'.eval Engine.exampleCat E.impl),
      ∀ v ∈ row, v = .bool true :=
  Engine.contract_sound hE Engine.exampleCat_wf (S := Engine.exampleA) (pre := fun _ => [])
    Engine.exampleA_mem (by intro t row _ e he; simp at he) Engine.examplePlan_wf
    (q := { rows := .multiset }) (ctx := {}) rfl
    (Rel.floatOpenSafe_of_closed ⟨fun n h => by simp at h, fun s h hne => absurd h.symm hne⟩
      (by decide))
    (sh := fun _ => none) (by simp) (by decide +kernel)
    (by simp [Rel.WF, Expr.refsLt, Rel.arity, Engine.exampleCat, Engine.examplePlan,
      Engine.examplePost, Expr.narrow, Expr.narrowCmp, Expr.cmp?])
    (WindowKeys.none_soundAll _) (by rw [Rel.aeval_csimp]; decide +kernel) hl hside

end Example

end Substrait
