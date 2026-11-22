import Lean.Data.Json
import SubstraitLean.EngineTables
import Sverify.Engines.Entry
import Sverify.Polars.Shims
import Sverify.Spark.Engine
import Sverify.Core.Allowed
import Sverify.DuckDB.Lowering
import Sverify.Engines.LoweringRaises

/-!
# The realizability table: `obligations reference E` (#444, step 3b)

For each engine profile `E` and each group and option, how the translation
from the reference to `E` discharges the option (`docs/core-semantics.md`,
"Obligations, option by option"):

* `native`: `E`'s behaviour is one the reference allows, as the call is;
* `upTo q`: the same up to the observation `q` (D18);
* `approx b`: within the float bound `b` of a behaviour the reference allows;
* `shim s`: after the shim `s`, with its cost;
* `precondition`: `E` differs only where the reference raises, so a plan
  verified never to raise never reaches the difference (an error-side
  option, "What strictness buys");
* `refused`;
* `uncharacterized`: outside the prototype slice, so `E`'s profile allows
  the core's every behaviour there and the row says nothing yet.

Each row is computed from three tables: the reference's choices
(`Profile.reference.table`) and tools (`Profile.reference.tools`), and `E`'s
choices and observation rows (`SubstraitLean/EngineTables.lean`). A row's
evidence is the theorem or the facts and tests of its observation row; a
row the choices decide alone is proved by `Choice.le_sound`.

Checks, by `decide` and at elaboration:

* every row is consistent: where `E` does not give the reference's value by
  default at an option where the reference picks one, the row names a shim,
  an observation or a refusal;
* every shim has a cost class (`EngineProfile.shims`), and every shim and every
  observation row has evidence: a theorem, or facts and tests;
* every theorem a row names exists (a `run_cmd` over the table).

`substrait-check --realizability` prints the table, and
`python -m sverify_dev.realizability --write` renders it to
`docs/realizability.md`; `tests/test_realizability.py` fails until that file
is current, so a change to the reference that costs an engine a shim shows
in review.

For DuckDB, the translation is `Lowering.duckdb.lowerRel`, and it refines
the reference as `docs/core-semantics.md` ("Soundness") defines it:
`Rel.duckdb_refines` gives `Allowed_duckdb(T r) ⊆ Allowed_reference(r)`
(`Rel.duckdb_shim_allowed`) and `Raises_duckdb(T r) ⊆ Raises_reference(r)`. -/

namespace Substrait

/-! ## The cases -/

/-- How a translation discharges one option. -/
inductive Case
  | native
  | upTo (q : Obs)
  | approx (bound : String)
  | shim (name : String)
  | precondition (pre : String)
  | refused
  | uncharacterized
  /-- The tables disagree: the engine gives another value where the
  reference picks one, and the row names no shim. `obligations_consistent`
  rules it out. -/
  | inconsistent
  deriving Repr, DecidableEq

/-! ## The rows -/

/-- One row of `obligations reference E`. -/
structure Obligation where
  group : Option String
  option : String
  tool : Tool
  /-- What the reference and the engine allow where the plan states no preference. -/
  reference : List Behaviour
  engine : List Behaviour
  /-- The behaviours other than the default that a plan may state (a
  Substrait option) and the reference delivers, but the engine's choice does
  not: the translation needs a shim for them, or refuses them (`overflow:
  SILENT` on DuckDB, which the lowering wraps). -/
  statedMissing : List Behaviour
  case : Case
  evidence : Evidence
  deriving Repr, DecidableEq

/-- The keys of the table: the reference's rows, then the engine's own
groups and its observation rows, in the catalogue's order. -/
def obligationKeys (t : ProfileTable) (obs : ObsTable) : List (Option String × String) :=
  options.flatMap fun o =>
    let ks : List (Option String × String) :=
      (Profile.reference.table.choices.filterMap fun (g, o', _) => if o' == o.id then some (g, o') else none) ++
      (t.choices.filterMap fun (g, o', _) => if o' == o.id && g.isSome then some (g, o') else none) ++
      (obs.filterMap fun (g, o', _) => if o' == o.id then some (g, o') else none)
    ks.eraseDups

/-- The observation row at a key: its own, else, for a group, the option's. -/
def obsAt (obs : ObsTable) : Option String → String → Option ObsRow
  | some g, o => obs.row? g o
  | none, o => (obs.find? fun (g, o', _) => g.isNone && o' == o).map (·.2.2)

/-- Behaviours of an open option that are one of the reference's, though
named apart: `(option, engine's, reference's, why)`. The reference's `ANY`
sum order allows every order of the additions, a sequential one among them;
`ANY_ROW` allows the first row read; `DECLARED_TYPE` for an integer `AVG`
(declared `i64`) is the exact mean truncated; `GENERIC` allows Welford with
Chan's merge. -/
def behaviourRefines : List (String × Behaviour × Behaviour × String) := [
  ("sum_order", "SEQUENTIAL", "ANY", "FloatSums: a sequential sum is one order of the additions"),
  ("tie_pick", "FIRST_READ", "ANY_ROW", "the first row read is a row of the tie"),
  ("round_zero_sign", "IEEE", "ANY", "-0.0 is one of the zeros the reference leaves open (duckdb-R15-round, polars-round)"),
  ("round_zero_sign", "POSITIVE", "ANY", "+0.0 is one of the zeros the reference leaves open (spark-round)"),
  ("avg_int_result", "EXACT_TRUNCATE", "DECLARED_TYPE", "AggFn.iavg: the exact mean, truncated (duckdb-R6)"),
  ("stat_algo", "WELFORD_CHAN", "GENERIC", "Welford with Chan's merge meets the generic properties (duckdb-var-stddev, polars-var-std)")]

/-- Each behaviour of `a` is one of `b`'s, or refines one of them. -/
private def sub (o : String) (a b : List Behaviour) : Bool :=
  a.all fun x => b.contains x ||
    behaviourRefines.any fun (o', e, r, _) => o' == o && e == x && b.contains r

/-- Both behaviours of each refinement are the option's. -/
example : behaviourRefines.all fun (o, e, r, _) =>
    ((OptionSpec.find? o).map fun s => s.core.contains e && s.core.contains r).getD false := by
  decide +kernel

/-- Is the engine's choice at the key uncharacterized (the core's `loose`)? -/
def ProfileTable.looseAt (t : ProfileTable) (g : Option String) (o : String) : Bool :=
  match t.choice? (g.getD "") o with
  | some (.loose _) => true
  | _ => false

/-- The row of `obligations reference E` at a group and option. -/
def obligation (t : ProfileTable) (obs : ObsTable) (g : Option String) (o : String) : Obligation :=
  let gr := g.getD ""
  let ref := Profile.reference.table.allows gr o []
  let eng := t.allows gr o []
  let accepted := ((Profile.reference.table.choice? gr o).bind Choice.accepted).getD []
  -- Only options a plan can state (Substrait's own), and only behaviours
  -- other than the default.
  let statable := ((OptionSpec.find? o).bind (·.substrait)).isSome
  let missing := if !statable then [] else accepted.filter fun b =>
    !ref.contains b && Profile.reference.table.allows gr o [b] == [b] && t.allows gr o [b] != [b]
  let tr := Profile.reference.tools.find? (·.option == o)
  let tool := (tr.map (·.tool)).getD .choose
  let pre := (tr.map (·.precondition)).getD ""
  let within := sub o eng ref
  -- Where the engine is within the reference by its choices alone: `Choice.le_sound`.
  let byTables : Evidence :=
    match t.choice? gr o, Profile.reference.table.choice? gr o, OptionSpec.find? o with
    | some c, some d, some spec => if c.le spec.core d then .proved "Choice.le_sound" else .none
    | _, _, _ => .none
  let (case, ev) : Case × Evidence := match obsAt obs g o with
    | some r =>
      match r.cls, r.shim with
      | .refused, _ => (.refused, r.evidence)
      | _, some s => (.shim s, r.evidence)
      | .refinesUpTo, none => (.upTo r.q, r.evidence)
      | .approx, none =>
        (.approx (match r.q.floats with | .within b => b | .exact => ""), r.evidence)
      | .refines, none =>
        -- A row without facts of its own rests on the tables alone.
        if within then (.native, if r.evidence == .none then byTables else r.evidence)
        else if tool == .raise then (.precondition pre, r.evidence)
        else (.inconsistent, r.evidence)
    | none =>
      if t.looseAt g o || eng.isEmpty then (.uncharacterized, .none)
      else if within then (.native, byTables)
      else if tool == .raise then (.precondition pre, .none)
      else (.inconsistent, .none)
  { group := g, option := o, tool, reference := ref, engine := eng, statedMissing := missing,
    case, evidence := ev }

/-- **`obligations reference E`**: the realizability table's rows for `E`. -/
def obligations (t : ProfileTable) (obs : ObsTable) : List Obligation :=
  (obligationKeys t obs).map fun (g, o) => obligation t obs g o

/-- The shims a table names, each once, in order. -/
def shimNames (os : List Obligation) : List String :=
  (os.filterMap fun r => match r.case with | .shim s => some s | _ => none).eraseDups

/-! ## Checks -/

/-- Every row of `e` is consistent: no engine differs silently from the reference. -/
def EngineProfile.consistent (e : EngineProfile) : Bool :=
  (obligations e.table e.obs).all (·.case != .inconsistent)

/-- Every shim of `e` has a cost class and evidence: a theorem, or facts and
tests; every row an observation row decides has evidence; and every shim cost
belongs to a shim the rows name. -/
def EngineProfile.evidenced (e : EngineProfile) : Bool :=
  let os := obligations e.table e.obs
  (os.all fun r => match r.case with
    | .shim s => (e.shimCost? s).isSome && r.evidence != .none && r.evidence != .tested [] none
    | .uncharacterized => true
    | _ => r.evidence != .none) &&
  e.shims.all fun (n, _) => (shimNames os).contains n

/-- Both checks of this repository's engines, decided by the kernel at once:
it computes each engine's `obligations` once for the two. -/
theorem obligations_checked : builtinEngines.all (fun e => e.consistent && e.evidenced) := by
  decide +kernel

theorem obligations_consistent : builtinEngines.all (·.consistent) := by
  have h := obligations_checked
  simp only [List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun e he => (h e he).1

theorem obligations_evidenced : builtinEngines.all (·.evidenced) := by
  have h := obligations_checked
  simp only [List.all_eq_true, Bool.and_eq_true] at h ⊢
  exact fun e he => (h e he).2

/-- A row's evidence and its reruns' name the issue tracking their proof,
where they are no proof (#1131). -/
def ObsRow.Tracked (r : ObsRow) : Prop :=
  (∀ ids i, r.evidence = .tested ids i ∨ r.evidence = .probed ids i → i.isSome) ∧
    ∀ ids i, r.rerunEvidence = .tested ids i ∨ r.rerunEvidence = .probed ids i → i.isSome

theorem Evidence.tracked_iff (e : Evidence) :
    e.tracked = true ↔ ∀ ids i, e = .tested ids i ∨ e = .probed ids i → i.isSome := by
  cases e <;> simp [Evidence.tracked]

/-- Every row of `e` that rests on no theorem, and every rerun claim, names
the issue tracking its proof: the checker `#check_engine_profiles` runs. -/
def EngineProfile.tracked (e : EngineProfile) : Bool :=
  e.obs.all fun (_, _, r) => r.evidence.tracked && r.rerunEvidence.tracked

/-- **`tracked` decides `ObsRow.Tracked`** of every row. -/
theorem EngineProfile.tracked_iff (e : EngineProfile) :
    e.tracked = true ↔ ∀ x ∈ e.obs, x.2.2.Tracked := by
  simp only [EngineProfile.tracked, List.all_eq_true, Bool.and_eq_true, ObsRow.Tracked,
    Evidence.tracked_iff]

/-- This repository's tables refine the core (`Profile.duckdb_le_core`, …): each
engine's test, from `Profile.duckdb_leB`, `Profile.polars_leB` and
`Profile.spark_leB`, which the kernel decides once. -/
theorem builtinEngines_leCore : builtinEngines.all (·.leCore) := by
  show ((Profile.duckdb.table {}).leB Profile.core.table &&
    (Profile.polars.table.leB Profile.core.table &&
      (Profile.spark.table.leB Profile.core.table && true))) = true
  rw [Profile.duckdb_leB, Profile.polars_leB, Profile.spark_leB]
  rfl

/-! ## Raise sets under a lowering

`Rel.raises_mapExprs`, `Lowering.lowerRel_raises` and `Lowering.lowerRel?_raises`
are in `engines/Sverify/Engines/LoweringRaises.lean`, and `Rel.hasIssue_of_raises`
in `analysis/Sverify/Analysis/ProfileImpl.lean`. -/

variable [Boxes.Ambient]

section LooseGap
-- No black boxes: the counterexample calls none.
attribute [local instance] Boxes.Ambient.none

/-- The counterexample's tables: `a = {(1)}`, `b = {(1, -1)}`. -/
def Rel.looseGapCat : Catalog := fun t =>
  if t = "a" then ⟨1, [[.int 1]]⟩ else if t = "b" then ⟨2, [[.int 1, .int (-1)]]⟩ else ⟨0, []⟩
/-- `1 / coalesce(b.v, 0) > 0` over `a ++ b`'s columns `(k, k', v)`. -/
def Rel.looseGapCond : Expr :=
  .bin .lt (.lit (.int 0))
    (.bin .idiv (.lit (.int 1)) (.ifThen (.un .not (.un .isNull (.field 2))) (.field 2) (.lit (.int 0))))
/-- `filter (join a (filter b (v > 0)) .left (a.k = b.k)) (1 / coalesce(b.v, 0) > 0)`. -/
def Rel.looseGapPlan : Rel :=
  .filter (.join (.read "a") (.filter (.read "b") (.bin .lt (.lit (.int 0)) (.field 1))) .left
    (.bin .eq (.field 0) (.field 1))) Rel.looseGapCond
/-- The reference raises on the padded row `(1, NULL, NULL)`. -/
example : Rel.looseGapPlan.Raises Profile.reference Rel.looseGapCat := by
  refine .inr ⟨[.int 1, .null, .null], ?_, ?_⟩
  · simp [Rel.looseGapCat, Rel.eval, Rel.arity, leftJoinRow, Expr.eval, Profile.reference,
      BinFn.apply, Value.isTrue, raiseIf, BinFn.issue, Profile.impl, Outcome.val]
  · simp [Expr.RaisesOn, Expr.evalP_reference, Expr.refOutcome_err, Rel.looseGapCond,
      Expr.issues, firstError, Expr.eval, BinFn.issueAll, UnFn.issueAll, BinFn.issue, UnFn.issue,
      UnFn.apply, Issue.isError]
/-- `Rel.HasIssue` reads the condition over the loose join, `{(1, 1, -1)}`, where
nothing happens. -/
example : ∀ p, ¬Rel.looseGapPlan.HasIssue Rel.looseGapCat false p := by
  intro p h
  simp [Rel.looseGapPlan, Rel.HasIssue, Rel.loose, Rel.eval, Rel.arity, Rel.looseGapCat,
    Rel.looseGapCond, leftJoinRow,
    Expr.issues, Expr.eval, BinFn.issueAll, UnFn.issueAll, BinFn.issue, UnFn.issue, BinFn.apply,
    UnFn.apply, Value.isTrue, BinFn.infIssue, UnFn.infIssue, inI64, between] at h
  obtain ⟨_, ⟨h, -⟩, -⟩ := h
  exact absurd (h (by simp [FloatCode.minI64])) (by simp [FloatCode.maxI64])

end LooseGap

/-! ## DuckDB: the translation refines the reference -/

/-- **`(duckdb, T r) ⊑ (reference, r)`**, for `T = Lowering.duckdb.lowerRel`
(`docs/core-semantics.md`, "Soundness"): unless the translated plan raises,
DuckDB's result is one the reference allows (`Rel.duckdb_shim_allowed`), and
it raises only where the reference may (`Rel.lowerRel_raises`). Its trusted
base is `Rel.duckdb_sound`'s, aggregates included: DuckDB's double `SUM` and
`AVG` are taken to be Lean's, which holds only within #85's bound (#633). -/
theorem Rel.duckdb_refines {cat : Catalog} (r : Rel) :
    (¬(Lowering.duckdb.lowerRel r).Raises (Profile.duckdb {}) cat →
      r.AllowedP Profile.reference.table cat
        ((Lowering.duckdb.lowerRel r).eval cat (Profile.duckdb {}).impl)) ∧
    ((Lowering.duckdb.lowerRel r).Raises (Profile.duckdb {}) cat →
      r.Raises Profile.reference cat) :=
  ⟨fun h => Rel.allowedP_reference.mpr (Rel.duckdb_shim_allowed h),
   Lowering.lowerRel_raises Lowering.duckdb_total Lowering.duckdb_allExact
      Lowering.duckdb_noneOnDbl⟩

/-! ## Every theorem a row names exists -/

open Lean Elab Command Meta in
unsafe def evalEnginesUnsafe (e : Lean.Expr) : TermElabM (List EngineEntry) :=
  evalExpr (List EngineEntry) (mkApp (mkConst ``List [.zero]) (mkConst ``EngineEntry)) e

open Lean Elab Command Meta in
@[implemented_by evalEnginesUnsafe]
opaque evalEngines (e : Lean.Expr) : TermElabM (List EngineEntry)

open Lean Elab Command Meta in
/-- `#check_engine_profiles es`: fail the build unless the theorems the rows
of every engine of `es` name exist (in `Substrait` or at the root, or
`float-bounds`'s, `floatBoundsTheorems`), and its rows are well-formed
(`EngineProfile.rowsWf`), within the core (`leCore`), consistent, evidenced
and tracked. That the engine is sound is the entry's type (`EngineEntry.sound`).
For this repository's engines the checks are also theorems, by `decide`; a
profile from outside states its own. -/
elab "#check_engine_profiles " t:term : command => do
  let es ← liftTermElabM do
    let e ← Term.elabTermEnsuringType t
      (mkApp (mkConst ``List [.zero]) (mkConst ``EngineEntry))
    Term.synthesizeSyntheticMVarsNoPostponing
    evalEngines (← instantiateMVars e)
  let env ← getEnv
  let known (thm : String) : Bool :=
    env.contains (`Substrait ++ thm.toName) || env.contains thm.toName ||
      floatBoundsTheorems.contains thm
  for e in es.map (·.rows) do
    for r in obligations e.table e.obs do
      if let .proved thm _ := r.evidence then
        unless known thm do
          throwError "obligations {e.name} at {r.option}: no theorem {thm}"
    for (_, o, r) in e.obs do
      if let .proved thm _ := r.evidence then
        unless known thm do
          throwError "{e.name}'s rows at {o}: no theorem {thm}"
    unless e.rowsWf do throwError "{e.name}: rows not well-formed"
    unless e.leCore do throwError "{e.name}: choices not within the core's"
    unless e.consistent do throwError "{e.name}: a row differs from the reference with no shim"
    unless e.evidenced do throwError "{e.name}: a shim or row without evidence or cost"
    unless e.tracked do throwError "{e.name}: a tested or probed row names no issue tracking its proof"


/-! ## For Python -/

open Lean (Json toJson) in
def Case.json : Case → List (String × Json)
  | .native => [("case", toJson "native")]
  | .upTo q => [("case", toJson "refines_up_to"), ("q", q.sparseJson)]
  | .approx b => [("case", toJson "approx"), ("bound", toJson b)]
  | .shim s => [("case", toJson "shim"), ("shim", toJson s)]
  | .precondition p => [("case", toJson "precondition"), ("precondition", toJson p)]
  | .refused => [("case", toJson "refused")]
  | .uncharacterized => [("case", toJson "uncharacterized")]
  | .inconsistent => [("case", toJson "inconsistent")]

open Lean (Json toJson) in
def Obligation.json (e : EngineProfile) (r : Obligation) : Json :=
  Json.mkObj <| [
    ("group", toJson r.group), ("option", toJson r.option),
    ("tool", toJson (match r.tool with
      | .raise => "raise" | .choose => "choose" | .leaveOpen => "open")),
    ("reference", toJson r.reference), ("engine", toJson r.engine),
    ("stated_missing", toJson r.statedMissing)] ++ r.case.json ++
    (match r.case with
      | .shim s => [("cost", toJson ((e.shimCost? s).map ShimCost.name))]
      | _ => []) ++
    (match r.evidence with
      | .proved thm ids => [("evidence", toJson "proved"), ("theorem", toJson thm), ("facts", toJson ids)]
      | .tested ids i => [("evidence", toJson "tested"), ("facts", toJson ids), ("issue", toJson i),
          ("version", toJson e.table.version)]
      | .probed ids i => [("evidence", toJson "probe"), ("facts", toJson ids), ("issue", toJson i),
          ("version", toJson e.table.version)]
      | .none => [("evidence", Json.null), ("facts", toJson ([] : List String))])

open Lean (Json toJson) in
/-- `substrait-check --realizability`: per engine, its version, the theorem
that its run is sound (`EngineEntry.soundName`) and the side condition it
is sound under (`sideName`), its shims with their costs, the functions it
refuses, and `obligations reference E`'s rows. -/
def realizabilityJson (es : List EngineEntry) : Json :=
  Json.mkObj <| es.map fun entry =>
    let e := entry.rows
    let os := obligations e.table e.obs
    (e.name, Json.mkObj [
      ("version", toJson e.table.version),
      ("theorem", toJson (reportedName entry.soundName)),
      ("side", toJson (reportedName entry.sideName)),
      ("shims", Json.arr <| ((shimNames os).map fun s => Json.mkObj [
        ("name", toJson s), ("cost", toJson ((e.shimCost? s).map ShimCost.name))]).toArray),
      ("refused_functions", Json.arr <| (e.table.missing.map fun (f, ids) =>
        Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray),
      ("rows", Json.arr <| (os.map (·.json e)).toArray)])

end Substrait
