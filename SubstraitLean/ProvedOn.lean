import SubstraitLean.ContractCheck
import SubstraitLean.Engine

/-!
# From the checker's verdict to an engine (#1484, A6)

`check_proved_sound` speaks of every result the reference allows; each
engine's theorem (`Engine.Sound`) says the rows its model computes for the
translated plan are one of them. `check_proved_on` joins the two: when
`substrait-check --contract` reports a postcondition proved and the
transformation closed, the postcondition holds on the rows the engine's model
computes, on any data that meets the request, under the engine's side
condition.

Each engine's corollary discharges its side condition from the report:
DuckDB's (`Engine.NoRaiseSide`) from a report without issues under the
reference and with `guard_free` (`check_proved_on_duckdb`), Polars's and
Spark's (`Engine.GuardFreeSide`) from `guard_free`
(`check_proved_on_polars`, `check_proved_on_spark`). No hypothesis names an
analysis; each is a report field, a request field, or a property of the data.

What stays outside: the model is the engine's scalar functions over the
reference's relational evaluator (`trusted-base.md`), the run is the model
(`Engine.Runs`), and an open float measure (`VAR_*`, `STDDEV_*`, `COVAR_*`,
`CORR`, `QUANTILE_CONT`) needs `Rel.FloatOpenSafeP`, which nothing
discharges for them yet (#929). For a double `SUM` or `AVG`, `Engine.contract_sound_runs_near`
with `Rel.floatOpenSafeP_aggregate` covers an aggregate at the root
(`engines/Sverify/Engines/OpenSums.lean`), and `Rel.floatOpenSafeP_of_noDouble` a closed
plan without doubles (`engines/Sverify/Engines/NoDouble.lean`).
-/

namespace Substrait.ContractCheck

open Lean (Json)
open Parse

variable [Boxes.Ambient]

/-- **A proved postcondition holds on an engine's model** (#1484, finding 1).
When `check` reports every column of the request's `k`-th postcondition
proved and the transformation closed, and the engine `E` translates the
transformation to `T'` under its side condition, the postcondition holds on
every row of the rows `E`'s model computes (`postRows`), for any data that
meets the request. -/
theorem check_proved_on {E : Engine} {side : Catalog → Rel → Prop} (hE : E.Sound side)
    {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) (hclosed : rep.closed = true)
    {T' : Rel} (hl : E.lower T.root = some T') (hside : side data T.root) :
    ∀ row ∈ postRows p.exprs p.mapping (T'.eval data E.impl), ∀ v ∈ row, v = .bool true := by
  rw [check_closed hR hc] at hclosed
  simp only [Request.closedIn, hT, Option.any_some] at hclosed
  have ho := Rel.allowed_orderAllowed hclosed (hE hl hside)
  exact check_proved_sound hR hc hD hT hp hproved ⟨_, ⟨_, ho, rfl⟩, rfl⟩

/-- **DuckDB's side condition from the report**: under the reference, a
report without issues whose transformation is guard-free (its loose inputs
its own, `Rel.looseSub`) leaves DuckDB's lowered plan nothing to raise on
(`Rel.hasIssue_of_raises`, `check_issues_sound`), on data that meets the
request, its bounds per key (`rows_per`) and the size hypothesis. -/
theorem check_noRaise_duckdb {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data) {T : Plan} (hT : R.transform = some T)
    (hP : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows)
    (hsm : T.root.Small data) (href : R.underReference = true) (hi : rep.issues = [])
    (hg : rep.guardFree = true) : (Engine.duckdb {} rfl).NoRaiseSide data T.root := by
  intro r' hl hr
  cases hl
  rw [(Request.check_ok (check_parse hR hc)).guardFree] at hg
  simp only [Request.guardFreeIn, hT, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨-, hloose⟩, -⟩, -⟩ := hg
  obtain ⟨p, hp, -⟩ := Rel.hasIssue_of_raises false hloose
    (Lowering.lowerRel_raises Lowering.duckdb_total Lowering.duckdb_allExact
      Lowering.duckdb_noneOnDbl hr)
  rcases check_issues_sound hR hc hD hT hP hsm p hp with h | ⟨-, h, -⟩
  · rw [hi] at h; cases h
  · rw [href] at h; cases h

/-- **A proved postcondition holds on DuckDB's model**, everything taken from
the report: proved, closed (no open measure), no issues under the reference,
guard-free. It covers the default route: the plan verified under the
reference and lowered by `Lowering.duckdb`, DuckDB at its default settings. A
`semantics="duckdb"` request runs natively and is outside it. `hg` gives
`Rel.looseSub` only, which `Rel.hasIssue_of_raises` needs; it goes when
`Rel.HasIssue` reads the loose rows a left join pads (Fable's log entry 41). -/
theorem check_proved_on_duckdb {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) (hclosed : rep.closed = true)
    (hP : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows)
    (hsm : T.root.Small data) (href : R.underReference = true) (hi : rep.issues = [])
    (hg : rep.guardFree = true) :
    ∀ row ∈ postRows p.exprs p.mapping
        ((Lowering.duckdb.lowerRel T.root).eval data (Engine.duckdb {} rfl).impl),
      ∀ v ∈ row, v = .bool true :=
  check_proved_on Engine.duckdb_sound hR hc hD hT hp hproved hclosed rfl
    (check_noRaise_duckdb hR hc hD hT hP hsm href hi hg)

/-- **Guard elimination's side condition from the request**: a transformation
the request finds guard-free (`Request.guardFreeIn`) meets
`Engine.GuardFreeSide` on data that meets the request and the size
hypothesis, with the request's own description of its inputs. It serves the
plan as written (`check_guardFreeSide`) and the plan to run
(`run_plan_guardFreeSide`). -/
theorem Request.guardFreeSide {R : Request} {data : Catalog} (hD : DataMeets R data) {T : Plan}
    (hT : R.transform = some T) (hsm : T.root.Small data) (hg : R.guardFreeIn R.kenv = true) :
    Engine.GuardFreeSide data T.root := by
  simp only [Request.guardFreeIn, hT, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hw, hloose⟩, hm⟩, -⟩ := hg
  have hK : R.kenv.Sound data := R.kenv_eq ▸ KnowledgeEnv.ofSpec_sound hD.schemas hD.pre hD.keys hD.ranges
  rw [KnowledgeEnv.windows, ← Rel.keyedWindows_congr hD.arity, ← Rel.mayIssues_congr hD.arity] at hm
  exact ⟨R.kenv.cols, R.kenv.facts, R.kenv.windows data,
    ⟨hD.wf, hK.cols, hK.facts, hK.windows hD.wf, hsm⟩,
    ⟨Rel.wf_congr hD.arity (Rel.checkWF_iff.mp hw), hloose,
      by simpa [KnowledgeEnv.windows] using hm⟩⟩

/-- **Guard elimination's side condition from the report**: a guard-free
transformation (`guard_free`) meets `Engine.GuardFreeSide` on data that meets
the request and the size hypothesis. -/
theorem check_guardFreeSide {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data) {T : Plan} (hT : R.transform = some T)
    (hsm : T.root.Small data) (hg : rep.guardFree = true) : Engine.GuardFreeSide data T.root :=
  R.guardFreeSide hD hT hsm (by rwa [(Request.check_ok (check_parse hR hc)).guardFree] at hg)

/-- **A proved postcondition holds on Polars's model**: proved, closed and
guard-free in the report, on the plan Polars's table lowers. -/
theorem check_proved_on_polars {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) (hclosed : rep.closed = true)
    (hsm : T.root.Small data) (hg : rep.guardFree = true) {r' : Rel}
    (hr : Lowering.polars.lowerRel? T.root = .ok r') :
    ∀ row ∈ postRows p.exprs p.mapping (r'.eval data Engine.polars.impl),
      ∀ v ∈ row, v = .bool true :=
  check_proved_on Engine.polars_sound hR hc hD hT hp hproved hclosed
    (by simp [Engine.polars, hr, Except.toOption]) (check_guardFreeSide hR hc hD hT hsm hg)

/-- **A proved postcondition holds on Spark's model**: proved, closed and
guard-free in the report. -/
theorem check_proved_on_spark {input : Json} {R : Request} {rep : Report}
    (hR : parse input = .ok R) (hc : check input = .ok rep)
    {data : Catalog} (hD : DataMeets R data)
    {T : Plan} (hT : R.transform = some T) {k : Nat} {p : Post} (hp : R.posts[k]? = some p)
    (hproved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true) (hclosed : rep.closed = true)
    (hsm : T.root.Small data) (hg : rep.guardFree = true) :
    ∀ row ∈ postRows p.exprs p.mapping (T.root.eval data Engine.spark.impl),
      ∀ v ∈ row, v = .bool true :=
  check_proved_on Engine.spark_sound hR hc hD hT hp hproved hclosed rfl
    (check_guardFreeSide hR hc hD hT hsm hg)

end Substrait.ContractCheck
