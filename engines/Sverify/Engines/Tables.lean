import Lean.Data.Json
import Sverify.Core.Observations
import Sverify.Core.AllowedP
import Sverify.Core.Profile

/-!
# The table machinery every engine shares (#444, #1189)

An engine's choices are a `ProfileTable` and its observation rows an
`ObsTable` (both in the core). This module holds what every engine's tables
are written and reported with: the rows' constructors (`ObsRow.native`,
`ObsRow.shimmed`, `ObsRow.upTo`, …) and their evidence, what reruns give
(`withReruns`), `EngineProfile`, the entry the checker takes per engine, its
well-formedness checks (`EngineProfile.rowsWf`, `EngineProfile.leCore`), and
the JSON the checker reports a table in (`profileRowsJson`). Each engine's
own tables are in its profile's module (`SubstraitLean/EngineTables.lean`
for DuckDB, Polars and Spark until #1189's step 5 moves them).
-/

namespace Substrait

/-! ## Rows and their evidence -/

/-- The core's rows at every option outside `slice`: not characterized. -/
def uncharacterized (slice : List String) : List (Option String × String × Choice) :=
  (options.filter fun o => !slice.contains o.id).map fun o => (none, o.id, .loose o.core)

/-- The options the prototype slice characterizes. -/
def prototypeSlice : List String :=
  ["overflow", "on_division_by_zero", "on_domain_error", "division_type", "min_mod_neg_one",
   "rounding", "nan_creation", "zero_sign", "round_zero_sign", "nan_kind", "nan_order",
   "nan_equality", "sum_order", "avg_int_result", "empty_group_aggregates", "null_order", "clustered",
   "tie_order", "tie_pick", "negative_start", "case_sensitivity", "string_positions",
   "null_join_keys", "float_overflow", "stat_algo", "quantile_interp", "decimal_rescale",
   "window_sum_algo"]

/-- The theorems of the package `float-bounds` (Mathlib, kept out of the core)
that rows name as evidence. The core cannot see them: the `run_cmd` at the
ends of `float-bounds/FloatBounds/Epsilon.lean` and `ChanCorr.lean` check
these names there, and `tests/test_float_bounds.py` that the two lists agree. -/
def floatBoundsTheorems : List String :=
  ["FloatBounds.StdModel.epsilon_sum", "FloatBounds.StdModel.epsilon_avg",
   "FloatBounds.StdModel.epsilon_sum_rel", "FloatBounds.StdModel.epsilon_avg_rel",
   "FloatBounds.StdModel.core_var_chan", "FloatBounds.StdModel.core_cov_chan",
   "FloatBounds.StdModel.core_corr_chan", "FloatBounds.StdModel.epsilon_sum_cr",
   "FloatBounds.StdModel.epsilon_avg_cr", "FloatBounds.StdModel.epsilon_var_cr",
   "FloatBounds.StdModel.epsilon_cov_cr", "FloatBounds.StdModel.TreeSum.sign",
   "FloatBounds.StdModel.TreeSum.avg_sign"]

/-- Evidence from the facts or tests `ids`, none where empty. -/
def Evidence.ofIds (ids : List String) : Evidence := if ids.isEmpty then .none else .tested ids

/-- The engine refines the reference as it is: natively, or, at an error-side
option, on the reference's non-raising domain. -/
def ObsRow.native (ids : List String) : ObsRow := { cls := .refines, evidence := .ofIds ids }

/-- The engine refines the reference after the shim. -/
def ObsRow.shimmed (shim : String) (ids : List String) : ObsRow :=
  { cls := .refines, shim := some shim, evidence := .ofIds ids }

/-- The engine refines the reference up to `q`. -/
def ObsRow.upTo (q : Obs) (ids : List String) : ObsRow :=
  { cls := .refinesUpTo, q, evidence := .ofIds ids }

/-- Within the bound named `b` of a result the reference allows. -/
def ObsRow.approxWithin (b : String) (ids : List String) : ObsRow :=
  { cls := .approx, q := { floats := .within b }, evidence := .ofIds ids }

/-- The row, proved by the theorem `thm` (`SubstraitLean/PolarsShims.lean`),
whose trusted model rests on the row's facts. -/
def ObsRow.proved (r : ObsRow) (thm : String) : ObsRow :=
  { r with evidence := .proved thm (match r.evidence with | .tested ids _ | .probed ids _ => ids | _ => []) }

/-- The row, its evidence and its reruns' not proved, with the issue `n` that
tracks their proof (#1131): `EngineProfile.tracked` requires one. -/
def ObsRow.tracking (r : ObsRow) (n : Nat) : ObsRow :=
  { r with evidence := r.evidence.tracking n, rerunEvidence := r.rerunEvidence.tracking n }

/-- A double `SUM` or `AVG`'s `sum_order` row: within the plan's bound of the
reference's correctly rounded sum, in each run (`StdModel.epsilon_sum_cr`, D25);
`ids` are the facts behind it, `rerunIds` those behind its run-to-run variation. -/
def ObsRow.fsumOrder (ids rerunIds : List String) (note : String := "") : ObsRow :=
  ({ ObsRow.approxWithin "plan" ids with
    note, rerun := some { floats := .within "plan" },
    rerunEvidence := .proved "FloatBounds.StdModel.epsilon_sum_cr" rerunIds }).proved
    "FloatBounds.StdModel.epsilon_sum_cr"

/-- A double `SUM` or `AVG`'s `rounding` row: the standard model
(`FloatBounds.StdModel`) holds of every rounding to nearest, whatever its tie
rule, so `StdModel.epsilon_sum_cr` (and `epsilon_avg_cr` for `AVG`) bounds the
engine's additions, each rounded, against the reference's sum, rounded once,
within the plan's bound. `ids` are the facts that the engine's additions round
to nearest and that its order is one `StdModel.Summed` covers; `note` says how. -/
def ObsRow.fsumRounding (ids : List String) (note : String) : ObsRow :=
  ({ ObsRow.approxWithin "plan" ids with note }).proved "FloatBounds.StdModel.epsilon_sum_cr"

/-! ## Reruns and engine profiles -/

/-- The options whose functions an engine computes row by row, or exactly
whatever the order (integer sums, a placement a key fixes, a sorted
quantile): every run gives the same result, as each row's facts were probed
to give, where `rerun` is not set already. The others stay unknown. -/
def rerunExact : List String :=
  ["overflow", "on_division_by_zero", "on_domain_error", "division_type", "min_mod_neg_one",
   "rounding", "nan_creation", "float_overflow", "negative_start", "case_sensitivity",
   "string_positions", "avg_int_result", "empty_group_aggregates", "null_order",
   "null_join_keys", "quantile_interp", "decimal_rescale"]

/-- The issue that tracks the proof that reruns give what a row says (D20):
the Engine object's (#900). -/
def rerunIssue : Nat := 900

/-- Each row with what reruns give: exact where `rerunExact` says so, with the
row's facts as evidence; a variation keeps its own. -/
def withReruns (obs : ObsTable) : ObsTable :=
  obs.map fun (g, o, r) =>
    -- A row's correctness theorem is no evidence for its reruns: keep its
    -- facts, tested, and the issue that tracks the proof of reruns (#900).
    let ev := match r.evidence with
      | .proved _ ids => Evidence.tested ids (some rerunIssue) | e => e
    match r.rerun with
    | some _ => (g, o, if r.rerunEvidence == .none then { r with rerunEvidence := ev } else r)
    | none =>
      -- A sum's sign of zero is the row's own; a group key's or `min`'s zero is
      -- the one seen first, or the platform's: not settled here.
      -- Exact only with evidence: a row without facts stays unknown.
      if ev != .none && (rerunExact.contains o || (o == "zero_sign" && g == some "fp.arith")) then (g, o, { r with rerun := some Obs.exact, rerunEvidence := ev })
      else (g, o, r)

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

/-- An engine profile as the checker reports it: its choices, its
observation rows, the theorem its translation from the reference rests on,
and its shims' costs. The checker takes a list of them (`checkerMain`), so a
package outside this repository can add a profile: it requires this one,
checks its entry with `#check_engine_profiles`, and builds a checker of its
own over `builtinEngines ++ [its entry]`. -/
structure EngineProfile where
  table : ProfileTable
  obs : ObsTable
  /-- The theorem the translation from the reference rests on, by name
  (`Rel.polars_sound`); `#check_engine_profiles` resolves it. -/
  translationTheorem : String
  /-- Each shim of `obs`, by name, with its cost. -/
  shims : List (String × ShimCost) := []
  /-- Where the engine executes, as `--options` reports it (`"streaming"`,
  `"batch"`), or empty. -/
  executes : String := ""
  /-- A `--contract` request under this profile gets the reference's report,
  marked with the profile's name: a plan states the profile's choices as the
  reference's templates (`Polars.elaborate_eq`). -/
  asReference : Bool := false

def EngineProfile.name (e : EngineProfile) : String := e.table.name

/-- The cost of the shim `name` of `e`, if `e` has it. -/
def EngineProfile.shimCost? (e : EngineProfile) (name : String) : Option ShimCost :=
  e.shims.lookup name

/-- The engine named `name` among `es`. -/
def engineNamed? (es : List EngineProfile) (name : String) : Option EngineProfile :=
  es.find? (·.name == name)

/-- An engine's observation rows: well-formed, at options of the catalogue,
one per group and option. -/
def ObsTable.wf (t : ObsTable) : Bool :=
  t.all (fun (_, o, r) => r.wf && (OptionSpec.find? o).isSome) &&
    nodupB (t.map fun (g, o, _) => (g, o))

/-- An engine's rows: well-formed, at options the slice characterizes, and
its table within the core's (`EngineProfile.leCore`). `#check_engine_profiles`
evaluates it for a profile from outside; this repository's are proved. -/
def EngineProfile.rowsWf (e : EngineProfile) : Bool :=
  e.obs.wf && e.obs.all fun (_, o, _) => prototypeSlice.contains o

/-- `e`'s choices refine the core's (`ProfileTable.le_of_leB`). -/
def EngineProfile.leCore (e : EngineProfile) : Bool := e.table.leB Profile.core.table

/-- How many of an engine's rows at `option` need a shim. -/
def shimCount (obs : ObsTable) (option : String) : Nat :=
  (obs.filter fun (_, o, r) => o == option && r.shim.isSome).length

/-! ## For Python -/

open Lean (Json toJson) in
def choicesJson (t : ProfileTable) : Json :=
  Json.arr <| (t.choices.map fun (g, o, c) => Json.mkObj [
    ("group", toJson g), ("option", toJson o), ("choice", c.json)]).toArray

open Lean (Json toJson) in
/-- The tool table, with each engine's shim count per option. -/
def toolsJson (es : List EngineProfile) : Json :=
  Json.arr <| (Profile.reference.tools.map fun r => Json.mkObj [
    ("option", toJson r.option),
    ("tool", toJson (match r.tool with
      | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open")),
    ("precondition", toJson r.precondition),
    ("shims", Json.mkObj (es.map fun e => (e.name, toJson (shimCount e.obs r.option))))
  ]).toArray

open Lean (Json toJson) in
/-- A profile's rows as the Python side reads them: per group (or `null`) and
option, the choice, and where the observation table has a row for it its
class, observation (only the components that are not exact), shim and
evidence; for the reference also D9's tool, the precondition of a raise and
the observation a contract must keep at an option left open. -/
def profileRowsJson (t : ProfileTable) (obs : ObsTable) (reference : Bool) : Json :=
  let keys := (t.choices.map fun (g, o, _) => (g, o)) ++
    ((obs.map fun (g, o, _) => (g, o)).filter fun k => !(t.choices.any fun (g, o, _) => (g, o) == k))
  Json.arr <| (keys.map fun (g, o) =>
    let choice := match g with
      | some g => t.choice? g o
      | none => t.dflt? o
    let row := match g with
      | some g => obs.row? g o
      | none => (obs.find? fun (x : Option String × String × ObsRow) =>
          x.1.isNone && x.2.1 == o).map fun (x : Option String × String × ObsRow) => x.2.2
    let base : List (String × Json) := [("group", toJson g), ("option", toJson o),
      ("choice", match choice with | some c => c.json | none => Json.null)]
    let obsFields : List (String × Json) := match row with
      | none => []
      | some r =>
        -- A refinement only after a shim is the class `shim` (#568's fourth).
        [("class", toJson (match r.cls, r.shim with
          | .refines, some _ => "shim"
          | .refines, none => "refines" | .refinesUpTo, _ => "refines_up_to"
          | .approx, _ => "approx" | .refused, _ => "refused")),
         ("shim", toJson r.shim)] ++
        [("q", r.q.sparseJson)] ++
        (match r.rerun with
          | none => []
          | some q =>
            [("rerun", q.sparseJson), ("deterministic", toJson (q == Obs.exact))] ++
            match r.rerunEvidence with
            | .proved thm _ => [("rerun_evidence", toJson "proved"), ("rerun_theorem", toJson thm)]
            | .tested ids i => [("rerun_evidence", toJson "tested"), ("rerun_facts", toJson ids),
                ("rerun_issue", toJson i)]
            | .probed ids i => [("rerun_evidence", toJson "probe"), ("rerun_facts", toJson ids),
                ("rerun_issue", toJson i)]
            | .none => []) ++
        (match r.engine with | some e => [("engine", toJson e)] | none => []) ++
        (if r.precondition == "" then [] else [("precondition", toJson r.precondition)]) ++
        (if r.note == "" then [] else [("note", toJson r.note)]) ++
        (match r.evidence with
          | .proved thm ids => [("evidence", toJson "proved"), ("theorem", toJson thm), ("facts", toJson ids),
              ("version", toJson t.version)]
          | .tested ids i => [("evidence", toJson "tested"), ("facts", toJson ids),
              ("issue", toJson i), ("version", toJson t.version)]
          | .probed ids i => [("evidence", toJson "probe"), ("facts", toJson ids),
              ("issue", toJson i), ("version", toJson t.version)]
          | .none => [("facts", toJson ([] : List String))])
    let toolFields : List (String × Json) := if !reference then [] else
      match Profile.reference.tools.find? (·.option == o) with
      | none => []
      | some tr =>
        [("tool", toJson (match tr.tool with
          | .raise => "raise" | .choose => "choose" | .leaveOpen => "open"))] ++
        (if tr.precondition == "" then [] else [("precondition", toJson tr.precondition)]) ++
        (match tr.q with | some q => [("q", q.sparseJson)] | none => [])
    -- At an option the reference leaves open, `q` is what a contract keeps.
    let obsFields := if toolFields.any (·.1 == "q") then obsFields.filter (·.1 != "q") else obsFields
    Json.mkObj (base ++ obsFields ++ toolFields)).toArray

end Substrait
