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
   "tie_order"]

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
    (none, "min_mod_neg_one", .oneOf ["ERROR"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    (none, "sum_order", .oneOf ["SEQUENTIAL"]),
    (none, "avg_int_result", .oneOf ["EXACT_TRUNCATE"]),
    (none, "empty_group_aggregates", .oneOf ["NULL"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_LAST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"])] ++ uncharacterized prototypeSlice

def Profile.duckdb.obs : ObsTable := [
  (none, "overflow", .native ["duckdb-R1", "duckdb-R15-int-arith"]),
  (some "agg.isum", "overflow", .shimmed "CAST(SUM(x) AS BIGINT)" ["duckdb-R6"]),
  (none, "on_division_by_zero", .native ["duckdb-R2"]),
  (some "fp.div", "on_division_by_zero", .native ["duckdb-R5"]),
  (none, "on_domain_error", .native ["duckdb-R15-double-arith"]),
  (none, "division_type", .native ["duckdb-R3"]),
  (none, "min_mod_neg_one", .shimmed "MIN % -1 written out" ["duckdb-R15-int-modulus"]),
  (none, "rounding", .native []),
  (none, "nan_creation", .native ["duckdb-R15-double-arith"]),
  (none, "zero_sign", .shimmed "Dialect.canon" ["duckdb-R14"]),
  (none, "nan_kind", .upTo { zeros := .canon } ["duckdb-signbit"]),
  (none, "nan_order", .native ["duckdb-arg-min-nulls"]),
  (none, "nan_equality", .native []),
  (none, "sum_order", .approxWithin "#85" ["duckdb-sum-double", "duckdb-avg-double"]),
  (none, "avg_int_result", .shimmed "the HUGEINT sum // the count" ["duckdb-R6"]),
  (none, "empty_group_aggregates", .native []),
  (none, "null_order", .native ["duckdb-F2"]),
  (none, "clustered", .shimmed "ORDER BY the keys" []),
  (none, "tie_order", .native ["duckdb-mode-ties"])]

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
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    (none, "sum_order", .oneOf ["PAIRWISE", "KAHAN"]),
    (none, "avg_int_result", .oneOf ["FP64"]),
    (none, "empty_group_aggregates", .oneOf ["ZERO"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_FIRST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"])] ++ uncharacterized prototypeSlice

def Profile.polars.obs : ObsTable := [
  (none, "overflow", .native ["polars-int-arith", "polars-int-divide"]),
  (some "agg.isum", "overflow", .native ["polars-sum-int"]),
  (none, "on_division_by_zero", .native ["polars-int-divide", "polars-int-modulus"]),
  (some "fp.div", "on_division_by_zero", .native ["polars-double-divide"]),
  (none, "on_domain_error", .native ["polars-double-divide"]),
  (none, "division_type",
    .shimmed "truncating division and remainder" ["polars-int-divide", "polars-int-modulus"]),
  (none, "min_mod_neg_one", .native ["polars-int-modulus"]),
  (none, "rounding", .native []),
  (none, "nan_creation", .native ["polars-double-arith"]),
  (none, "zero_sign", .upTo { zeros := .canon } ["polars-zero-sign", "polars-zero-order"]),
  (none, "nan_kind", .upTo { zeros := .canon } ["polars-nan-sign"]),
  (none, "nan_order", .native ["polars-nan-order"]),
  (none, "nan_equality", .native ["polars-nan-equality"]),
  (none, "sum_order", .approxWithin "#85" ["polars-sum-float", "polars-mean-float"]),
  (none, "avg_int_result", .shimmed "the exact sum divided by the count" ["polars-avg-int"]),
  (none, "empty_group_aggregates", .shimmed "NULL for no values" ["polars-sum-int"]),
  (none, "null_order", .shimmed "nulls_last" ["polars-null-order"]),
  (none, "clustered", .shimmed "sort on the keys" []),
  (none, "tie_order", .native ["polars-sort-stability"])]

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
/-- `substrait-check --options`: the options, the groups' options, each
profile's choices and observation rows, the profiles' versions, and the tool
table. -/
def tablesJson : Json :=
  optionsJson
    |>.setObjVal! "choices" (Json.mkObj ([("reference", choicesJson Profile.reference.table),
        ("core", choicesJson Profile.core.table)] ++
      engineTables.map fun (t, _) => (t.name, choicesJson t)))
    |>.setObjVal! "observations" (Json.mkObj ([("reference", obsTableJson Profile.reference.obs)] ++
      engineTables.map fun (t, obs) => (t.name, obsTableJson obs)))
    |>.setObjVal! "versions" (Json.mkObj (engineTables.map fun (t, _) => (t.name, toJson t.version)))
    |>.setObjVal! "tools" toolsJson

end Substrait
