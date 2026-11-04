import Lean.Data.Json
import SubstraitLean.Observations
import SubstraitLean.AllowedP
import SubstraitLean.Profile

/-!
# Engine profiles as choice tables (#444, step 3a, prototype slice)

DuckDB's and Polars's choices and observation rows, from their facts
(`characterization/duckdb/facts/`, `characterization/polars/facts/`), pinned to
the versions those were probed at (D14). The rows cover the prototype slice:
integer `+ - × /` and `%`, `SUM` and `AVG` of integers and doubles, double
arithmetic, and an `ORDER BY`'s NULL order, clustering and ties, with what
these need (zeros, NaNs, rounding). Every other option is left as the core
has it (`loose` over its behaviours): not characterized, so anything.

Each table refines the core, by `decide` (`Profile.duckdb_le_core` for every
setting, `Profile.polars_le_core`), hence `Rel.AllowedP_mono` gives
`Allowed_E ⊆ Allowed_core`. `Profile.duckdb s`, the semantic profile the
lowering proves its shims against, stays as it is; its table names what it
models.

Each observation row says how the engine's behaviour relates to the
reference's: an error-side option refines on the reference's non-raising
domain, so a verified plan needs no shim there (`docs/core-semantics.md`,
"What strictness buys"); a value-side one names its shim. -/

namespace Substrait

/-- The core's rows at every option outside `slice`: not characterized. -/
def uncharacterized (slice : List String) : List (Option String × String × Choice) :=
  (options.filter fun o => !slice.contains o.id).map fun o => (none, o.id, .loose o.core)

/-- The options the prototype slice characterizes. -/
def prototypeSlice : List String :=
  ["overflow", "on_division_by_zero", "on_domain_error", "division_type", "min_mod_neg_one",
   "rounding", "nan_creation", "zero_sign", "nan_kind", "nan_order", "nan_equality",
   "sum_order", "avg_int_result", "empty_group_aggregates", "null_order", "clustered",
   "tie_order", "tie_pick", "negative_start", "case_sensitivity", "string_positions",
   "null_join_keys", "float_overflow"]

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
  { r with evidence := .proved thm (match r.evidence with | .tested ids => ids | _ => []) }

/-! ## DuckDB -/

/-- DuckDB 2.0.0 under the settings `s`. -/
def Profile.duckdb.table (s : DuckDBSettings) : ProfileTable where
  name := "duckdb"
  version := "2.0.0"
  choices := [
    (none, "overflow", .asked ["ERROR"] ["ERROR"]),
    (none, "on_division_by_zero", .oneOf [if s.errorOnDivZero then "ERROR" else "NULL"]),
    (some "fp.div", "on_division_by_zero", .oneOf [if s.ieeeOps then "IEEE" else "ERROR"]),
    (none, "on_domain_error", .oneOf [if s.ieeeOps then "NAN" else "ERROR"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.div", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.mod", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (none, "min_mod_neg_one", .oneOf ["ERROR"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (some "fp.round", "rounding", .asked ["TIE_AWAY_FROM_ZERO"] ["TIE_AWAY_FROM_ZERO"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "float_overflow", .oneOf ["INFINITY"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    (none, "sum_order", .oneOf ["SEQUENTIAL"]),
    (none, "avg_int_result", .oneOf ["EXACT_TRUNCATE"]),
    (none, "empty_group_aggregates", .oneOf ["NULL"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_LAST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"]),
    (none, "tie_pick", .oneOf ["FIRST_READ"]),
    (none, "negative_start", .asked ["WRAP_FROM_END"] ["WRAP_FROM_END"]),
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (none, "string_positions", .oneOf ["ONE_BASED_CHARS"]),
    (none, "null_join_keys", .oneOf ["NO_MATCH"])] ++ uncharacterized prototypeSlice

def Profile.duckdb.obs : ObsTable := [
  (none, "overflow", .native ["duckdb-R1", "duckdb-R15-int-arith"]),
  -- `SUM(BIGINT)` is a `HUGEINT`; the written plan casts it back, which raises
  -- where the reference does: a type, not a value, so no shim.
  (some "agg.isum", "overflow", .native ["duckdb-R6"]),
  (none, "on_division_by_zero", .native ["duckdb-R2"]),
  (some "fp.div", "on_division_by_zero", .native ["duckdb-R5"]),
  (none, "on_domain_error", .native ["duckdb-R15-double-arith"]),
  (none, "division_type", .native ["duckdb-R3"]),
  (none, "min_mod_neg_one", .shimmed "MIN % -1 written out" ["duckdb-R15-int-modulus"]),
  (none, "rounding", .native []),
  (none, "nan_creation", .native ["duckdb-R15-double-arith"]),
  -- Two zeros, as IEEE has them: the reference's up to one zero, or exactly
  -- after `Dialect.canon`.
  (none, "zero_sign", { ObsRow.upTo { zeros := .canon } ["duckdb-R14"] with
    shim := some "Dialect.canon" }),
  (none, "nan_kind", .upTo { zeros := .canon } ["duckdb-signbit"]),
  (none, "nan_order", .native ["duckdb-arg-min-nulls"]),
  (none, "nan_equality", .native []),
  -- One value at a time: one of the orders the reference allows (`FloatSums`).
  (none, "sum_order", .native ["duckdb-sum-double", "duckdb-avg-double"]),
  (none, "avg_int_result", .native ["duckdb-R6"]),
  (none, "empty_group_aggregates", .native []),
  (none, "null_order", .native ["duckdb-F2"]),
  -- The written `ORDER BY` is the model's sort, which `SortAllowed` allows for
  -- a clustered key (`Rel.duckdb_refines`; `test_realizability.py` runs it).
  (none, "clustered", (ObsRow.shimmed "ORDER BY the keys" []).proved "Rel.duckdb_refines"),
  (none, "tie_order", .native ["duckdb-mode-ties"]),
  (none, "tie_pick", .native ["duckdb-mode-ties", "duckdb-arg-min-nulls"]),
  (some "fp.round", "rounding", .native ["duckdb-R15-round"]),
  (none, "float_overflow", .native ["duckdb-R15-double-arith"]),
  (none, "negative_start", .native ["duckdb-R13"]),
  (none, "case_sensitivity", .native []),
  (none, "string_positions", .native []),
  (none, "null_join_keys", .native [])]

/-! ## Polars -/

/-- Polars 2.1.0 (its Python API). -/
def Profile.polars.table : ProfileTable where
  name := "polars"
  version := "2.1.0"
  choices := [
    (none, "overflow", .oneOf ["SILENT"]),
    (none, "on_division_by_zero", .oneOf ["NULL"]),
    (some "fp.div", "on_division_by_zero", .oneOf ["IEEE"]),
    (none, "on_domain_error", .oneOf ["NAN"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "division_type", .oneOf ["FLOOR"]),
    (some "int.div", "division_type", .oneOf ["FLOOR"]),
    (some "int.mod", "division_type", .oneOf ["FLOOR"]),
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (some "fp.round", "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "float_overflow", .oneOf ["INFINITY"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    (none, "sum_order", .oneOf ["PAIRWISE", "KAHAN"]),
    (none, "avg_int_result", .oneOf ["FP64"]),
    (none, "empty_group_aggregates", .oneOf ["ZERO"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_FIRST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"]),
    (none, "tie_pick", .oneOf ["FIRST_READ"]),
    (none, "negative_start", .asked ["WRAP_FROM_END"] ["WRAP_FROM_END"]),
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (some "str.sub", "string_positions", .oneOf ["ZERO_BASED_CHARS"]),
    (some "str.match", "string_positions", .oneOf ["ZERO_BASED_BYTES"]),
    (none, "null_join_keys", .oneOf ["NO_MATCH"])] ++ uncharacterized prototypeSlice
  missing := (["md5", "sha256", "levenshtein", "repeat", "ascii", "like", "ilike"].map
    (·, ["polars-string-functions-missing"]))

def Profile.polars.obs : ObsTable := [
  (none, "overflow", (ObsRow.native ["polars-int-arith", "polars-int-divide"]).proved "Rel.polars_sound"),
  (some "agg.isum", "overflow", (ObsRow.native ["polars-sum-int"]).proved "Polars.sum_leaves_i64"),
  (none, "on_division_by_zero", (ObsRow.native ["polars-int-divide", "polars-int-modulus"]).proved "Rel.polars_sound"),
  (some "fp.div", "on_division_by_zero", (ObsRow.native ["polars-double-divide"]).proved "Rel.polars_sound"),
  (none, "on_domain_error", (ObsRow.native ["polars-double-divide"]).proved "Rel.polars_sound"),
  (none, "division_type", (ObsRow.shimmed "int_mod_trunc" ["polars-int-modulus"]).proved "Polars.int_mod_trunc"),
  (some "int.div", "division_type", (ObsRow.shimmed "int_div_trunc" ["polars-int-divide"]).proved "Polars.int_div_trunc"),
  (some "int.mod", "division_type", (ObsRow.shimmed "int_mod_trunc" ["polars-int-modulus"]).proved "Polars.int_mod_trunc"),
  (none, "min_mod_neg_one", (ObsRow.native ["polars-int-modulus"]).proved "Rel.polars_sound"),
  (none, "rounding", .native []),
  (none, "nan_creation", (ObsRow.native ["polars-double-arith"]).proved "Rel.polars_sound"),
  -- Up to one zero; the shim `one_zero` makes it exact.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["polars-zero-sign", "polars-zero-order"]
    with shim := some "one_zero" }).proved "Polars.one_zero"),
  (none, "nan_kind", .upTo { zeros := .canon } ["polars-nan-sign"]),
  (none, "nan_order", .native ["polars-nan-order"]),
  (none, "nan_equality", .native ["polars-nan-equality"]),
  -- Pairwise is a tree sum, one of the reference's; Kahan's compensated sum
  -- (groups) is not, so within #85's bound.
  (none, "sum_order", .approxWithin "plan" ["polars-sum-float", "polars-mean-float"]),
  (none, "avg_int_result", (ObsRow.shimmed "avg_int_declared" ["polars-avg-int"]).proved "Polars.avg_int_declared"),
  (none, "empty_group_aggregates", (ObsRow.shimmed "sum_empty_null" ["polars-sum-int"]).proved "Polars.sum_empty_null"),
  -- Every stated placement is native, by `nulls_last`; where a key leaves it
  -- open, Polars's default (first) is not the reference's (last), which the
  -- choices say (`transferB`), so the translation writes `nulls_last` on every
  -- key, a written argument. `Polars.null_order`: with it, Polars orders as
  -- `sortLe`.
  (none, "null_order", (ObsRow.shimmed "null_order" ["polars-null-order"]).proved "Polars.null_order"),
  (none, "clustered", .shimmed "sort on the keys" ["polars-clustered"]),
  (none, "tie_order", (ObsRow.native ["polars-sort-stability", "polars-first-last"]).proved "Polars.tie_order"),
  (none, "tie_pick", .native ["polars-first-last"]),
  (some "fp.round", "rounding", (ObsRow.shimmed "round_half_away" ["polars-round"]).proved "Polars.round_half_away"),
  (none, "float_overflow", (ObsRow.native ["polars-double-arith"]).proved "Polars.makes_infinite"),
  (none, "negative_start", .native ["polars-substring"]),
  (none, "case_sensitivity", .native ["polars-match-functions"]),
  (some "str.sub", "string_positions", (ObsRow.shimmed "substring_wrap" ["polars-substring"]).proved "Polars.substring_wrap"),
  (some "str.match", "string_positions", (ObsRow.shimmed "strpos_chars" ["polars-strpos"]).proved "Polars.strpos_chars"),
  (none, "null_join_keys", .native ["polars-null-keys"])]

/-! ## The engines -/

/-- The engine profiles, under DuckDB's default settings. -/
def engineTables : List (ProfileTable × ObsTable) :=
  [(Profile.duckdb.table {}, Profile.duckdb.obs), (Profile.polars.table, Profile.polars.obs)]

/-- **Every DuckDB setting refines the core.** -/
theorem Profile.duckdb_le_core (s : DuckDBSettings) : (Profile.duckdb.table s).Le Profile.core.table := by
  obtain ⟨e, i⟩ := s
  apply ProfileTable.le_of_leB
  cases e <;> cases i <;> decide +kernel

theorem Profile.polars_le_core : Profile.polars.table.Le Profile.core.table :=
  ProfileTable.le_of_leB (by decide +kernel)

/-- `Allowed_duckdb ⊆ Allowed_core`, for every setting. -/
theorem Rel.allowed_duckdb_core (s : DuckDBSettings) {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP (Profile.duckdb.table s) cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono (Profile.duckdb_le_core s) h

/-- `Allowed_polars ⊆ Allowed_core`. -/
theorem Rel.allowed_polars_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.polars.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.polars_le_core h

/-- An engine's observation rows: well-formed, at options of the catalogue,
one per group and option. -/
def ObsTable.wf (t : ObsTable) : Bool :=
  t.all (fun (_, o, r) => r.wf && (OptionSpec.find? o).isSome) &&
    (t.map fun (g, o, _) => (g, o)).Nodup

example : engineTables.all (·.2.wf) := by decide +kernel
/-- Each observation row is at an option the slice characterizes. -/
example : engineTables.all fun (_, obs) => obs.all fun (_, o, _) => prototypeSlice.contains o := by
  decide +kernel

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
def toolsJson : Json :=
  Json.arr <| (Profile.reference.tools.map fun r => Json.mkObj [
    ("option", toJson r.option),
    ("tool", toJson (match r.tool with
      | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open")),
    ("precondition", toJson r.precondition),
    ("shims", Json.mkObj (engineTables.map fun (t, obs) => (t.name, toJson (shimCount obs r.option))))
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
        (match r.evidence with
          | .proved thm ids => [("evidence", toJson "proved"), ("theorem", toJson thm), ("facts", toJson ids)]
          | .tested ids => [("evidence", toJson "tested"), ("facts", toJson ids)]
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

open Lean (Json toJson) in
/-- `substrait-check --options`: the options, the groups' options, each
profile's choices and observation rows, the profiles' versions, and the tool
table. -/
def tablesJson : Json :=
  optionsJson
    |>.setObjVal! "choices" (Json.mkObj ([
        ("reference", profileRowsJson Profile.reference.table Profile.reference.obs true),
        ("core", choicesJson Profile.core.table)] ++
      engineTables.map fun (t, obs) => (t.name, profileRowsJson t obs false)))
    |>.setObjVal! "profiles" (Json.mkObj ([
        ("reference", Json.mkObj [("engine", Json.null)]),
        ("core", Json.mkObj [("engine", Json.null)])] ++
      engineTables.map fun (t, _) => (t.name, Json.mkObj [
        ("engine", toJson t.name), ("versions", toJson [t.version]),
        ("missing", Json.arr <| (t.missing.map fun (f, ids) =>
          Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray)])))
    |>.setObjVal! "observations" (Json.mkObj ([("reference", obsTableJson Profile.reference.obs)] ++
      engineTables.map fun (t, obs) => (t.name, obsTableJson obs)))
    |>.setObjVal! "versions" (Json.mkObj (engineTables.map fun (t, _) => (t.name, toJson t.version)))
    |>.setObjVal! "tools" toolsJson

end Substrait
