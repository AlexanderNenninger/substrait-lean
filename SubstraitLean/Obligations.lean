import Lean.Data.Json
import SubstraitLean.EngineTables
import SubstraitLean.PolarsShims
import SubstraitLean.SparkShims
import SubstraitLean.Allowed
import SubstraitLean.LoweringDuckDB

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
* every shim has a cost class (`shimCosts`), and every shim and every
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

/-- What a shim costs at run time. -/
inductive ShimCost
  /-- A written argument or keyword (`NULLS LAST`, `nulls_last=True`): free. -/
  | argument
  /-- An extra expression per row or group (a `CASE`, a cast). -/
  | expression
  /-- An extra sort. -/
  | sort
  deriving Repr, DecidableEq

def ShimCost.name : ShimCost → String
  | .argument => "argument" | .expression => "expression" | .sort => "sort"

/-- Each engine's shims, by the name its observation rows give them, with
their cost. Polars's are `python/src/sverify/_polars_shims.py`'s `SHIMS`
(named as their lemmas `Polars.<name>`), which
`tests/test_realizability.py` checks against these. -/
def shimCosts : List (String × String × ShimCost) := [
  ("duckdb", "MIN % -1 written out", .expression),
  ("duckdb", "Dialect.canon", .expression),
  ("duckdb", "ORDER BY the keys", .sort),
  ("polars", "null_order", .argument),
  ("polars", "round_half_away", .argument),
  ("polars", "int_div_trunc", .expression),
  ("polars", "int_mod_trunc", .expression),
  ("polars", "sum_empty_null", .expression),
  ("polars", "avg_int_declared", .expression),
  ("polars", "one_zero", .expression),
  ("polars", "strpos_chars", .expression),
  ("polars", "substring_wrap", .expression),
  ("polars", "column_divisor", .expression),
  ("polars", "decimal_round_half_away", .expression),
  ("polars", "decimal_div_half_away", .expression),
  ("polars", "max_nan_greatest", .expression),
  ("polars", "sort on the keys", .sort),
  ("spark", "int_sum_decimal", .expression),
  ("spark", "int_avg_decimal", .expression),
  ("spark", "Dialect.canon", .expression),
  ("spark", "null_order", .argument),
  ("spark", "sort on the keys", .sort)]

def shimCost? (engine name : String) : Option ShimCost :=
  (shimCosts.find? fun (e, n, _) => e == engine && n == name).map (·.2.2)

/-- The theorem each engine's translation as a whole rests on. -/
def translationTheorem : String → String
  | "duckdb" => "Rel.duckdb_refines"
  | "polars" => "Rel.polars_sound"
  | "spark" => "Rel.spark_sound"
  | _ => ""

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
Chan's merge, and `BETWEEN` a linear interpolation. -/
def behaviourRefines : List (String × Behaviour × Behaviour × String) := [
  ("sum_order", "SEQUENTIAL", "ANY", "FloatSums: a sequential sum is one order of the additions"),
  ("tie_pick", "FIRST_READ", "ANY_ROW", "the first row read is a row of the tie"),
  ("avg_int_result", "EXACT_TRUNCATE", "DECLARED_TYPE", "AggFn.iavg: the exact mean, truncated (duckdb-R6)"),
  ("stat_algo", "WELFORD_CHAN", "GENERIC", "Welford with Chan's merge meets the generic properties (duckdb-var-stddev, polars-var-std)"),
  ("quantile_interp", "LINEAR", "BETWEEN", "a linear interpolation lies between the neighbouring values (duckdb-quantile-cont-interpolation, polars-quantile)")]

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

/-- The shim count (D9's measure of few shims). -/
def shimTotal (os : List Obligation) : Nat := (shimNames os).length

/-! ## Checks -/

/-- Every row is consistent: no engine differs silently from the reference. -/
theorem obligations_consistent :
    engineTables.all fun (t, obs) => (obligations t obs).all (·.case != .inconsistent) := by
  decide +kernel

/-- Every shim has a cost class and evidence: a theorem, or facts and tests. -/
theorem obligations_shims_evidenced :
    engineTables.all fun (t, obs) => (obligations t obs).all fun r =>
      match r.case with
      | .shim s => (shimCost? t.name s).isSome && r.evidence != .none &&
          r.evidence != .tested []
      | _ => true := by
  decide +kernel

/-- Every row an observation row decides (`native`, up to `q`, `approx`, a
precondition) has evidence too. -/
theorem obligations_evidenced :
    engineTables.all fun (t, obs) => (obligations t obs).all fun r =>
      match r.case with
      | .uncharacterized => true
      | _ => r.evidence != .none := by
  decide +kernel

/-- Every shim cost belongs to a shim some table names. -/
theorem shimCosts_used :
    shimCosts.all fun (e, n, _) =>
      engineTables.any fun (t, obs) => t.name == e && (shimNames (obligations t obs)).contains n := by
  decide +kernel

/-! ## Raise sets under a lowering -/

theorem Measure.mapExpr_id (m : Measure) : m.mapExpr id = m := by
  cases m; simp [Measure.mapExpr]

theorem Rel.mapExprs_id : ∀ r : Rel, r.mapExprs id = r
  | .read _ | .values _ _ => rfl
  | .filter r _ | .emit r _ | .fetch r _ _ | .window r _ _ _ | .orderBy r _ | .distinct r
  | .unnest r _ => by simp [mapExprs, Rel.mapExprs_id r]
  | .project r _ => by simp [mapExprs, Rel.mapExprs_id r]
  | .cross a b | .unionAll a b | .join a b _ _ | .semi a b _ _ => by
    simp [mapExprs, Rel.mapExprs_id a, Rel.mapExprs_id b]
  | .aggregate r _ ms => by
    simp only [mapExprs, Rel.mapExprs_id r, List.map_id_fun, id_eq]
    congr 1
    exact (List.map_congr_left fun m _ => Measure.mapExpr_id m).trans (List.map_id ms)

/-- Where the reference does not raise, its functions give `Rel.eval`'s rows. -/
theorem Rel.evalI_reference {cat : Catalog} {r : Rel} (h : ¬r.Raises Profile.reference cat) :
    r.evalI Profile.reference.impl cat = r.eval cat := by
  have := Rel.evalI_mapExprs (f := id) Expr.reference_exact (fun _ => rfl) (cat := cat) (r := r)
  rw [Rel.mapExprs_id] at this
  exact this h

theorem Measure.mem_mapExpr_exprs {f : Expr → Expr} (hf : ∀ i, f (.field i) = .field i)
    {m : Measure} {e' : Expr} (h : e' ∈ (m.mapExpr f).exprs) : ∃ e ∈ m.exprs, f e = e' := by
  rw [Measure.mapExpr_exprs] at h
  simp only [List.mem_cons, List.mem_append, List.mem_map] at h
  rcases h with (rfl | ⟨e, he, rfl⟩) | ⟨k, hk, rfl⟩
  · exact ⟨m.arg, List.mem_cons_self .., rfl⟩
  · exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), rfl⟩
  · exact ⟨.field k.col, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hk)), hf _⟩

/-- **A plan whose expressions raise only where the originals do raises only
where the original does.** With `q`'s functions giving `Rel.eval`'s rows
where `q` does not raise, the rows each translated expression is evaluated on
are rows the original one is evaluated on. -/
theorem Rel.raises_mapExprs {p q : Profile} {f : Expr → Expr} (hx : ∀ e, Expr.Exact p (f e) e)
    (hf : ∀ i, f (.field i) = .field i)
    (hr : ∀ e row, (f e).RaisesOn p row → e.RaisesOn q row) {cat : Catalog}
    (hq : ∀ r : Rel, ¬r.Raises q cat → r.evalI q.impl cat = r.eval cat) :
    ∀ {r : Rel}, (r.mapExprs f).Raises p cat → r.Raises q cat
  | .read _, h | .values _ _, h => h.elim
  | .filter r c, h => by
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs hx hf hr hq (r := r)
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs hx hf (fun h' => h0 (ih h'))] at hrow
        exact ⟨row, by rw [hq r h0]; exact hrow, hr c row hc⟩
  | .project r es, h => by
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs hx hf hr hq (r := r)
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs hx hf (fun h' => h0 (ih h'))] at hrow
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
        exact ⟨row, by rw [hq r h0]; exact hrow, e, he, hr e row hc⟩
  | .emit r _, h | .orderBy r _, h | .distinct r, h | .unnest r _, h | .window r _ _ _, h
  | .fetch r _ _, h => by
    simp only [mapExprs, Raises] at h ⊢
    exact raises_mapExprs hx hf hr hq h
  | .cross a b, h | .unionAll a b, h => by
    simp only [mapExprs, Raises] at h ⊢
    exact h.imp (raises_mapExprs hx hf hr hq) (raises_mapExprs hx hf hr hq)
  | .join a b _ on, h | .semi a b _ on, h => by
    simp only [mapExprs, Raises] at h ⊢
    have iha := raises_mapExprs hx hf hr hq (r := a)
    have ihb := raises_mapExprs hx hf hr hq (r := b)
    by_cases ha : a.Raises q cat
    · exact .inl ha
    · by_cases hb : b.Raises q cat
      · exact .inr (.inl hb)
      · refine .inr (.inr ?_)
        rcases h with h | h | ⟨x, hx', y, hy, hc⟩
        · exact absurd (iha h) ha
        · exact absurd (ihb h) hb
        · rw [evalI_mapExprs hx hf (fun h' => ha (iha h'))] at hx'
          rw [evalI_mapExprs hx hf (fun h' => hb (ihb h'))] at hy
          exact ⟨x, by rw [hq a ha]; exact hx', y, by rw [hq b hb]; exact hy, hr on _ hc⟩
  | .aggregate r gs ms, h => by
    simp only [mapExprs, Raises] at h ⊢
    have ih := raises_mapExprs hx hf hr hq (r := r)
    by_cases h0 : r.Raises q cat
    · exact .inl h0
    · refine .inr ?_
      rcases h with h | ⟨row, hrow, e', he', hc⟩
      · exact absurd (ih h) h0
      · rw [evalI_mapExprs hx hf (fun h' => h0 (ih h'))] at hrow
        refine ⟨row, by rw [hq r h0]; exact hrow, ?_⟩
        simp only [List.mem_append, List.mem_flatMap, List.mem_map] at he'
        rcases he' with ⟨e, he, rfl⟩ | ⟨m', hm', he'⟩
        · exact ⟨e, List.mem_append_left _ he, hr e row hc⟩
        · obtain ⟨m, hm, rfl⟩ := hm'
          obtain ⟨e, he, rfl⟩ := Measure.mem_mapExpr_exprs hf he'
          exact ⟨e, List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hm, he⟩), hr e row hc⟩

/-- A lowered expression raises only where the reference does (`agree`). -/
theorem Lowering.lowerE_raises {p : Profile} {L : Lowering p} (hL : L.Total) (e : Expr) (row : Row)
    (h : (L.lowerE e).RaisesOn p row) : e.RaisesOn Profile.reference row := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (lower_isSome hL e)
  have hc := L.lower_correct e t ht row
  simp only [lowerE, ht, Option.getD_some, Expr.RaisesOn] at h ⊢
  revert h hc
  cases t.evalP p row <;> cases e.evalP Profile.reference row <;>
    simp [Outcome.Agree, Outcome.err?]

/-- **A lowered plan raises only where the reference may.** -/
theorem Lowering.lowerRel_raises {p : Profile} {L : Lowering p} (hL : L.Total) {cat : Catalog}
    {r : Rel} (h : (L.lowerRel r).Raises p cat) : r.Raises Profile.reference cat :=
  Rel.raises_mapExprs (lowerE_exact hL) (fun _ => rfl) (lowerE_raises hL)
    (fun _ h => Rel.evalI_reference h) h

/-! ## DuckDB: the translation refines the reference -/

/-- The DuckDB shim: unless the shimmed plan raises, DuckDB returns an allowed
result. -/
theorem Rel.duckdb_shim_allowed {cat : Catalog} {r : Rel}
    (h : ¬(Lowering.duckdb.lowerRel r).Raises (Profile.duckdb {}) cat) :
    r.Allowed cat ((Lowering.duckdb.lowerRel r).evalI (Profile.duckdb {}).impl cat) := by
  rw [Rel.duckdb_shim_sound h]; exact r.eval_allowed cat

/-- **`(duckdb, T r) ⊑ (reference, r)`**, for `T = Lowering.duckdb.lowerRel`
(`docs/core-semantics.md`, "Soundness"): unless the translated plan raises,
DuckDB's result is one the reference allows (`Rel.duckdb_shim_allowed`), and
it raises only where the reference may (`Rel.lowerRel_raises`). Its trusted
base is `Rel.duckdb_sound`'s, aggregates included: DuckDB's double `SUM` and
`AVG` are taken to be Lean's, which holds only within #85's bound (#633). -/
theorem Rel.duckdb_refines {cat : Catalog} (r : Rel) :
    (¬(Lowering.duckdb.lowerRel r).Raises (Profile.duckdb {}) cat →
      r.AllowedP Profile.reference.table cat
        ((Lowering.duckdb.lowerRel r).evalI (Profile.duckdb {}).impl cat)) ∧
    ((Lowering.duckdb.lowerRel r).Raises (Profile.duckdb {}) cat →
      r.Raises Profile.reference cat) :=
  ⟨fun h => Rel.allowedP_reference.mpr (Rel.duckdb_shim_allowed h),
   Lowering.lowerRel_raises Lowering.duckdb_total⟩

/-! ## Every theorem a row names exists -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let known (thm : String) : Bool :=
    env.contains (`Substrait ++ thm.toName) || env.contains thm.toName ||
      floatBoundsTheorems.contains thm
  for (t, obs) in engineTables do
    unless known (translationTheorem t.name) do
      throwError "{t.name}: no translation theorem {translationTheorem t.name}"
    for r in obligations t obs do
      if let .proved thm _ := r.evidence then
        unless known thm do
          throwError "obligations {t.name} at {r.option}: no theorem {thm}"

/-! Every theorem the Polars rows name (`Profile.polars.obs`) is one. -/
open Lean Elab Command in
run_cmd do
  for (_, o, r) in Substrait.Profile.polars.obs do
    if let .proved thm _ := (r : Substrait.ObsRow).evidence then
      let n := thm.toName
      unless (← getEnv).contains (`Substrait ++ n) || (← getEnv).contains n ||
          Substrait.floatBoundsTheorems.contains thm do
        throwError "Profile.polars.obs at {o}: no theorem {thm}"

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
def Obligation.json (engine : String) (r : Obligation) : Json :=
  Json.mkObj <| [
    ("group", toJson r.group), ("option", toJson r.option),
    ("tool", toJson (match r.tool with
      | .raise => "raise" | .choose => "choose" | .leaveOpen => "open")),
    ("reference", toJson r.reference), ("engine", toJson r.engine),
    ("stated_missing", toJson r.statedMissing)] ++ r.case.json ++
    (match r.case with
      | .shim s => [("cost", toJson ((shimCost? engine s).map ShimCost.name))]
      | _ => []) ++
    (match r.evidence with
      | .proved thm ids => [("evidence", toJson "proved"), ("theorem", toJson thm), ("facts", toJson ids)]
      | .tested ids => [("evidence", toJson "tested"), ("facts", toJson ids)]
      | .probed ids => [("evidence", toJson "probe"), ("facts", toJson ids)]
      | .none => [("evidence", Json.null), ("facts", toJson ([] : List String))])

open Lean (Json toJson) in
/-- `substrait-check --realizability`: per engine, its version, the theorem
its translation rests on, its shims with their costs, the functions it
refuses, and `obligations reference E`'s rows. -/
def realizabilityJson : Json :=
  Json.mkObj <| engineTables.map fun (t, obs) =>
    let os := obligations t obs
    (t.name, Json.mkObj [
      ("version", toJson t.version),
      ("theorem", toJson (translationTheorem t.name)),
      ("shims", Json.arr <| ((shimNames os).map fun s => Json.mkObj [
        ("name", toJson s), ("cost", toJson ((shimCost? t.name s).map ShimCost.name))]).toArray),
      ("refused_functions", Json.arr <| (t.missing.map fun (f, ids) =>
        Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray),
      ("rows", Json.arr <| (os.map (·.json t.name)).toArray)])

end Substrait
