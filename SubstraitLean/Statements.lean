import SubstraitLean.ProvedOn
import SubstraitLean.RunPlan
import Sverify.Engines.Rewrite
import SubstraitLean.IssuesAll

/-!
# The top-level statements, named (#1484, A7)

What a verified contract guarantees, stated over a few named predicates so
that each statement can be read without the checker's internals. Each one is
proved by applying an existing theorem; a statement asks for what that
theorem asks for, regrouped under names. Where a grouping asks for more, the
docstring names the sharper theorem.

* `Checked input R rep T`: `substrait-check --contract` parsed the request and
  answered it, and the request has a transformation `T`.
* `Verified input R rep T k p`: checked, and the report marks every column of
  the `k`-th postcondition `p` proved.
* `Verified.DuckDB rep R`, `Verified.GuardFree rep`: the report's engine
  conditions. DuckDB's: the transformation is closed (no open measure), the
  request is under the reference, the report lists no issues, and it is
  guard-free. Polars's and Spark's: closed and guard-free.
* `DataMeets R data`: the data meets the request (schemas, preconditions,
  keys, caps). `DataAssumed R data T` adds its bounds on rows per key
  (`rows_per`) and the size hypothesis on every order (`Rel.SmallAll`,
  which gives `Rel.Small`: `DataAssumed.small`).
* `Post.HoldsOn p out`: every column `p` keeps is TRUE on every row of `out`.

## The evaluators

| Evaluator | What it is | Trusted | Theorem |
|---|---|---|---|
| `Rel.Allowed`, `Rel.OrderAllowed` | The reference's results, every choice it leaves open | the specification | `Rel.eval_allowed`, `Rel.eval_orderAllowed` |
| `Rel.eval` | One result the reference allows | no | `Rel.eval_allowed` |
| `r'.eval cat (Engine.duckdb {} rfl).impl` | DuckDB's model: its profile's functions over the reference's relational evaluator | the model's relational part (`trusted-base.md`) | `Engine.duckdb_sound` |
| `r.eval cat Engine.polars.impl`, `Engine.spark.impl` | Polars's and Spark's models: the written plan's functions | as above | `Engine.polars_sound`, `Engine.spark_sound` |
| the compiled checker | `check`, run natively | the compiler, as every report is | the `#guard`s below |
| the engines themselves | the run | D16's claim (`Engine.Runs`), facts and tests | none |

The steps between an engine's model and its actual run are listed in
`docs/trusted-base.md` ("An engine's run of a proved plan").

The verdict depends on no engine module only at test strength, and no test
checks it on main yet (#1484 S1a). `verdict_proved_sound` states what
`Verdict.PROVED` reads (#2010).
`Report.output` (Ibis's dtypes, `contracts.py`) is tested, not proved: the
checker reports no output types.
-/

namespace Substrait.ContractCheck

open Lean (Json)
open Parse

variable [Boxes.Ambient]

/-- `substrait-check --contract` parsed `input` into `R` and answered it with
`rep`, and the request has a transformation `T`. -/
structure Checked (input : Json) (R : Request) (rep : Report) (T : Plan) : Prop where
  parsed : parse input = .ok R
  checked : check input = .ok rep
  transform : R.transform = some T

/-- Checked, and every column of the `k`-th postcondition `p` proved. -/
structure Verified (input : Json) (R : Request) (rep : Report) (T : Plan) (k : Nat) (p : Post) :
    Prop extends Checked input R rep T where
  post : R.posts[k]? = some p
  proved : ∀ e ∈ rep.ensures.getD k [], e.2.1 = true

/-- DuckDB's report condition: closed (no open measure), under the reference,
no issues, guard-free. -/
def Verified.DuckDB (rep : Report) (R : Request) : Prop :=
  rep.closed = true ∧ R.underReference = true ∧ rep.issues = [] ∧ rep.guardFree = true

/-- Polars's and Spark's report condition: closed and guard-free. -/
def Verified.GuardFree (rep : Report) : Prop := rep.closed = true ∧ rep.guardFree = true

/-- The data a contract's engine statements speak of: it meets the request,
its bounds on rows per key (`rows_per`) and the size hypothesis on every order
the reference allows (`Rel.SmallAll`, #202): the engine's input is one of
them. -/
structure DataAssumed (R : Request) (data : Catalog) (T : Plan) : Prop where
  meets : DataMeets R data
  rowsPer : ∀ t, ∀ kn ∈ R.perKeyOf t, RowsPer kn.1 kn.2 (data t).rows
  smallAll : T.root.SmallAll data

/-- The size hypothesis on `Rel.eval`'s order, one of every order's. -/
theorem DataAssumed.small {R : Request} {data : Catalog} {T : Plan} (hD : DataAssumed R data T) :
    T.root.Small data :=
  hD.smallAll.small

/-- Every column `p` keeps is TRUE on every row of `out`, the rows of the
transformation `p` selects from. -/
def Post.HoldsOn (p : Post) (out : Relation) : Prop :=
  ∀ row ∈ postRows p.exprs p.mapping out, ∀ v ∈ row, v = .bool true

/-- **A verified postcondition holds on every result the reference allows**
(`check_proved_sound`), on any data that meets the request. -/
theorem verified_holds {input : Json} {R : Request} {rep : Report} {T : Plan} {k : Nat}
    {p : Post} (h : Verified input R rep T k p) {data : Catalog} (hD : DataMeets R data) :
    ∀ out, T.root.OrderAllowed data out → p.HoldsOn out :=
  fun _ ho => check_proved_sound h.parsed h.checked hD h.transform h.post h.proved
    ⟨_, ⟨_, ho, rfl⟩, rfl⟩

/-- Every column of every postcondition is proved: the report's half of
`Verdict.PROVED` (`python/src/sverify/report.py`). -/
def Report.AllProved (rep : Report) : Prop := ∀ k, ∀ e ∈ rep.ensures.getD k [], e.2.1 = true

/-- **`Verdict.PROVED`: every postcondition holds on every result the reference
allows** (#2010). Checked, every postcondition proved and the report closed
(no open measure, so every result is one of an order's: `Rel.allowed_orderAllowed`),
on any data that meets the request. On an engine the statement is its
evidence line: `verified_holds_duckdb`, `verified_holds_polars`,
`verified_holds_spark`. -/
theorem verdict_proved_sound {input : Json} {R : Request} {rep : Report} {T : Plan}
    (h : Checked input R rep T) (hp : rep.AllProved) (hclosed : rep.closed = true)
    {data : Catalog} (hD : DataMeets R data) :
    ∀ out, T.root.Allowed data out →
      ∀ (k : Nat) (p : Post), R.posts[k]? = some p → p.HoldsOn out := by
  intro out hout k p hk
  rw [check_closed h.parsed h.checked] at hclosed
  simp only [Request.closedIn, h.transform, Option.any_some] at hclosed
  exact verified_holds { toChecked := h, post := hk, proved := hp k } hD out
    (Rel.allowed_orderAllowed hclosed hout)

/-- **A verified postcondition holds on DuckDB's model** (default route:
verified under the reference, lowered by `Lowering.duckdb`, default
settings), under DuckDB's report condition (`check_proved_on_duckdb`). -/
theorem verified_holds_duckdb {input : Json} {R : Request} {rep : Report} {T : Plan} {k : Nat}
    {p : Post} (h : Verified input R rep T k p) (hE : Verified.DuckDB rep R) {data : Catalog}
    (hD : DataAssumed R data T) :
    p.HoldsOn ((Lowering.duckdb.lowerRel T.root).eval data (Engine.duckdb {} rfl).impl) :=
  check_proved_on_duckdb h.parsed h.checked hD.meets h.transform h.post h.proved hE.1 hD.rowsPer
    hD.small hE.2.1 hE.2.2.1 hE.2.2.2

/-- **A verified postcondition holds on Polars's model**, under its report
condition. `DataAssumed` asks for the bounds on rows per key, which the
sharper `check_proved_on_polars` does not need. -/
theorem verified_holds_polars {input : Json} {R : Request} {rep : Report} {T : Plan} {k : Nat}
    {p : Post} (h : Verified input R rep T k p) (hE : Verified.GuardFree rep) {data : Catalog}
    (hD : DataAssumed R data T) : p.HoldsOn (T.root.eval data Engine.polars.impl) :=
  check_proved_on_polars h.parsed h.checked hD.meets h.transform h.post h.proved hE.1 hD.small hE.2

/-- **A verified postcondition holds on Spark's model**, under its report
condition. The sharper form is `check_proved_on_spark`, without the bounds
on rows per key. -/
theorem verified_holds_spark {input : Json} {R : Request} {rep : Report} {T : Plan} {k : Nat}
    {p : Post} (h : Verified input R rep T k p) (hE : Verified.GuardFree rep) {data : Catalog}
    (hD : DataAssumed R data T) : p.HoldsOn (T.root.eval data Engine.spark.impl) :=
  check_proved_on_spark h.parsed h.checked hD.meets h.transform h.post h.proved hE.1 hD.small hE.2

/-- What a postcondition says of a result holds of it in any order. -/
theorem Post.HoldsOn.perm {p : Post} {out out' : Relation} (h : p.HoldsOn out')
    (hp : out.Perm out') : p.HoldsOn out :=
  fun row hrow => h row (((hp.map _).map _).mem_iff.mp hrow)

/-- **A verified postcondition holds on an engine's run of the plan to run**
(#1787, `check_run_plan_sound`): where the report is closed and the checker
gives a plan to run, an engine that is sound under its side condition and
translates that plan computes rows on which the postcondition holds. The data
meets the request and its declared foreign keys (`references`), which
`check_inputs` checks with the other preconditions. -/
theorem verified_holds_run_plan {input : Json} {R : Request} {rep : Report} {T : Plan} {k : Nat}
    {p : Post} (h : Verified input R rep T k p) (hclosed : rep.closed = true) {data : Catalog}
    (hD : DataMeets R data) (hFK : R.foreignKeysOf.Hold data) {s : Rel}
    (hs : R.runPlanIn R.kenv = .ok s) {E : Engine} {side : Catalog → Rel → Prop}
    (hE : E.Sound side) {s' : Rel} (hl : E.lower s = some s') (hside : side data s) :
    p.HoldsOn (s'.eval data E.impl) := by
  obtain ⟨hbag, -⟩ := check_run_plan_sound h.parsed h.checked hD h.transform hFK hs
  obtain ⟨out, hout, hp⟩ := hE.of_refinesBag hl hside hbag
  rw [check_closed h.parsed h.checked] at hclosed
  simp only [Request.closedIn, h.transform, Option.any_some] at hclosed
  exact (verified_holds h hD out (Rel.allowed_orderAllowed hclosed hout)).perm hp

/-- **A verified postcondition holds on DuckDB's model of the plan to run**
(default route), under DuckDB's report condition, on data that meets the
request, its declared foreign keys (`references`), its bounds per key and the
size hypothesis of the plan as written. The gate gives the plan to run what
DuckDB's side condition needs (`run_plan_noRaise_duckdb`). -/
theorem verified_holds_run_plan_duckdb {input : Json} {R : Request} {rep : Report} {T : Plan}
    {k : Nat} {p : Post} (h : Verified input R rep T k p) (hE : Verified.DuckDB rep R)
    {data : Catalog} (hD : DataAssumed R data T) (hFK : R.foreignKeysOf.Hold data) {s : Rel}
    (hs : R.runPlanIn R.kenv = .ok s) :
    p.HoldsOn ((Lowering.duckdb.lowerRel s).eval data (Engine.duckdb {} rfl).impl) :=
  verified_holds_run_plan h hE.1 hD.meets hFK hs Engine.duckdb_sound rfl
    (run_plan_noRaise_duckdb h.parsed h.checked hD.meets h.transform hFK hs hD.rowsPer hD.small
      hE.2.1 hE.2.2.2)

/-- **A deterministic report means one result up to row order**
(`check_deterministic_sound`). -/
theorem checked_deterministic {input : Json} {R : Request} {rep : Report} {T : Plan}
    (h : Checked input R rep T) (hd : rep.deterministic = true) {data : Catalog}
    (hD : DataMeets R data) : ∀ {out : Relation}, T.root.Allowed data out →
      out.Perm (T.root.eval data) :=
  check_deterministic_sound h.parsed h.checked hD h.transform hd

/-- **A key the report marks proved is a key of every allowed result**
(`check_keys_sound`). -/
theorem checked_keys {input : Json} {R : Request} {rep : Report} {T : Plan}
    (h : Checked input R rep T) {k : List Nat} (hk : (k, true) ∈ rep.keys) {data : Catalog}
    (hD : DataMeets R data) : ∀ {out : Relation}, T.root.OrderAllowed data out → KeyOn k out :=
  check_keys_sound h.parsed h.checked hD h.transform hk

/-- **Every issue that can happen on any order is reported**
(`check_issues_sound_all`), on the views of a join's inputs included (an
engine that pushes a condition into one input, #1484 R3), but an overflow to
`±∞` of a scalar operation under a profile other than the reference. -/
theorem checked_issues_all {input : Json} {R : Request} {rep : Report} {T : Plan}
    (h : Checked input R rep T) {data : Catalog} (hD : DataAssumed R data T) :
    ∀ p, T.root.HasIssueAll data false p →
      p ∈ rep.issues ∨ (p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs) :=
  check_issues_sound_all h.parsed h.checked hD.meets h.transform hD.rowsPer hD.smallAll

/-- **Every issue that can happen on `Rel.eval`'s order is reported**, one
order of `checked_issues_all`'s. -/
theorem checked_issues {input : Json} {R : Request} {rep : Report} {T : Plan}
    (h : Checked input R rep T) {data : Catalog} (hD : DataAssumed R data T) :
    ∀ p, T.root.HasIssue data false p →
      p ∈ rep.issues ∨ (p.1 = .infinite ∧ R.underReference = false ∧ p.2 ∉ T.root.aggArgs) :=
  fun p hp => checked_issues_all h hD p (Rel.hasIssueAll_of_hasIssue hp)

end Substrait.ContractCheck

/-! ## Worked examples

The compiled checker computes each report below, which is the strength every
user's report has; the kernel does not run `check` (it reaches `partial def`s,
and every real report comes from the compiled checker anyway). Each engine
statement's model side has a kernel-checked evaluation example:
`Engine.duckdb_contract_example`, `Engine.polars_contract_example`,
`Engine.spark_contract_example` (and `Engine.example_contract` for the
reference). -/

namespace Substrait.ContractCheck.Worked

open Lean (Json)

/-- `tests/contracts/int_division.json`: an integer division whose
postcondition `q >= 0` the checker proves. -/
def intDivision : String := include_str "../tests/contracts/int_division.json"

/-- The request and the report on `intDivision`, by the compiled checker. -/
def intDivisionChecked : Except String (Request × Report) :=
  letI : Boxes.Ambient := Boxes.Ambient.none
  match Json.parse intDivision with
  | .ok j => do return (← parse j, ← check j)
  | .error e => .error e

-- Checked, a transformation and postcondition 0, proved, closed, under the
-- reference (no `profile`), no issues, guard-free: `Verified` and both report
-- conditions, so `verified_holds_duckdb`, `verified_holds_polars` and
-- `verified_holds_spark` speak of it.
#guard match intDivisionChecked with
  | .ok (R, rep) => R.transform.isSome && R.posts[0]?.isSome && R.underReference &&
      (rep.ensures.getD 0 []).all (·.2.1) && rep.closed && rep.issues.isEmpty && rep.guardFree
  | .error _ => false

end Substrait.ContractCheck.Worked
