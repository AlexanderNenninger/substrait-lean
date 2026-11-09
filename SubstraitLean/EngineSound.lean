import SubstraitLean.Engine
import Sverify.Core.AllowedNear
import Sverify.Analysis.AllowedAnalysis

/-!
# What an engine's model is sound for (#900)

`Engine.Sound E side`: for every plan `r` that `E` translates to `r'`, where
`r'` does not raise under `E`'s profile and `side` holds, the rows `r'`
computes with `E`'s functions are a result the reference allows for `r`
(`Rel.Allowed`). It is proved for the four engines:

* `Engine.reference_sound`: Lean's functions on the plan as it is, so the
  run is `Rel.eval`.
* `Engine.duckdb_sound`: DuckDB at its default settings, through its lowering
  (`Rel.eval_okImpl`, then `Rel.duckdb_shim_allowed`).
* `Engine.polars_sound`, `Engine.spark_sound`: under `Engine.GuardFreeSide`,
  guard elimination's hypotheses (`Rel.guardFree_sound`), with the engine's
  functions faithful where the reference reports no issue
  (`Polars.written_faithful`, `Profile.sparkWritten_okImpl_faithful`). Its plan part
  (`Engine.GuardFreePlan`) is decidable; its data part
  (`Engine.GuardFreeData`) states preconditions on the catalog, as `hK` does,
  with the size hypothesis (`Rel.Small`).

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

/-! ## The bridge -/

variable [Boxes.Ambient]
/-- **`E`'s run is sound under `side`**: where `E` translates `r` to `r'`,
`r'` does not raise under `E`'s profile and `side cat r` holds, the rows `r'`
computes with `E`'s functions are a result the reference allows for `r`. -/
def Engine.Sound (E : Engine) (side : Catalog → Rel → Prop) : Prop :=
  ∀ {cat : Catalog} {r r' : Rel}, E.lower r = some r' → ¬r'.Raises E.profile cat → side cat r →
    r.Allowed cat (r'.eval cat E.impl)

theorem Engine.reference_sound : Engine.reference.Sound fun _ _ => True := by
  intro cat r r' hl _ _; cases hl; exact r.eval_allowed cat

/-- DuckDB at its default settings: where the lowered plan does not raise,
`okImpl` computes DuckDB's run (`Rel.eval_okImpl`), which the reference
allows (`Rel.duckdb_shim_allowed`). -/
theorem Engine.duckdb_sound : (Engine.duckdb {} rfl).Sound fun _ _ => True := by
  intro cat r r' hl hr _
  cases hl
  show r.Allowed cat ((Lowering.duckdb.lowerRel r).eval cat (Profile.duckdb {}).okImpl)
  rw [Rel.eval_okImpl (p := Profile.duckdb {}) hr]; exact Rel.duckdb_shim_allowed hr

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

theorem Engine.polars_sound : Engine.polars.Sound Engine.GuardFreeSide := by
  intro cat r r' hl _ ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  show r.Allowed cat (r.eval cat Polars.written)
  rw [Rel.polars_sound hcat hA hF hT hwf hsmall hs hm]; exact r.eval_allowed cat

/-- Spark: its profile's functions where they do not raise give the
reference's value wherever the reference reports no issue
(`Profile.sparkWritten_okImpl_faithful`), so guard elimination applies. -/
theorem Engine.spark_sound : Engine.spark.Sound Engine.GuardFreeSide := by
  intro cat r r' hl _ ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  exact Rel.guardFree_allowed hcat hA hF hT hwf hsmall hs hm Profile.sparkWritten_okImpl_faithful

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
    {cat : Catalog} {r r' : Rel} (hl : E.lower r = some r') (hr : ¬r'.Raises E.profile cat)
    (hs : side cat r) (hw : E.RefWithin r) : r.AllowedP E.table cat (r'.eval cat E.impl) :=
  Rel.AllowedP_transfer hw (Rel.allowedP_reference.mpr (hE hl hr hs))

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
translates `T` to `T'`, `T'` does not raise under `E`'s profile and `E`'s side
condition holds, the postconditions hold on the rows `T'` computes with `E`'s
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
    {T' : Rel} (hl : E.lower T = some T') (hr : ¬T'.Raises E.profile cat) (hside : side cat T) :
    ∀ row ∈ postRows es mp (T'.eval cat E.impl), ∀ v ∈ row, v = .bool true :=
  contract_sound_allowed hcat hS hpre hT hq hsafe hsh hrob hQ hW hproved
    (hE hl hr hside).postRows

/-- **D16's trusted claim**: what `E` returns for `r` is `out`, a result `E`'s
table allows for `r`, on the strength of the observation rows `r` relies on,
each proved or `tested` (`Engine.Refines`). For an engine that runs the plan
as it is (`lower := some`), `Rel.AllowedE.allowedP` gives the second part from
`Rel.AllowedE`. -/
def Engine.Runs (E : Engine) (tested : ObsRow → Prop) (cat : Catalog) (r : Rel)
    (out : Relation) : Prop :=
  E.Refines r tested ∧ r.AllowedP E.table cat out

/-- **A verified contract holds on the engine's actual result**, where `E`'s
choices are within the reference's at every option `T` reads (`htr`) and D16's
trusted claim holds of the result (`Engine.Runs`). `htr` fails where an
engine's choice is not the reference's (`sum_order`, `stat_algo`,
`quantile_interp`, `zero_sign`); there the result is near one the reference
allows (#929), the tolerance form of PR 3. -/
theorem Engine.contract_sound_runs {E : Engine} {tested : ObsRow → Prop}
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
    (hrun : E.Runs tested cat T out) :
    ∀ row ∈ postRows es mp out, ∀ v ∈ row, v = .bool true :=
  contract_sound_allowed hcat hS hpre hT hq hsafe hsh hrob hQ hW hproved
    (Rel.allowedP_reference.mp (Rel.transfer_of_transferB htr hrun.2)).postRows

end Substrait
