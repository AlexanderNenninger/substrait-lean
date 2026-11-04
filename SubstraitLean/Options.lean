import Lean.Data.Json
import SubstraitLean.Functions

/-!
# The options and the profiles' choices

Step 1a of #444 (`docs/core-semantics.md`, "How a profile states its
constraints"). A choice point is an option: Substrait's own (`overflow`,
`rounding`, …) with the values of its YAML, or sverify's (`zero_sign`,
`sum_order`, …) where Substrait leaves the point unnamed. `options` is the
option catalogue, one row per option; `Functions.groups` gives each function
group its options; a `ProfileTable` gives, per option or per group and option,
the behaviours a profile allows.

`Profile.reference.table` is the reference's table. The parser reads the
options a plan sets from it (`Parse.optionAccepts`). Step 1c reads it in
`Rel.AllowedP`; until then it describes what `Rel.Allowed` does. -/

namespace Substrait

/-- A behaviour, by its Substrait name (`ERROR`, `TIE_TO_EVEN`) or sverify's
(`ONE_ZERO`). -/
abbrev Behaviour := String

/-- One option of the catalogue. -/
structure OptionSpec where
  /-- `overflow`, `zero_sign`, … -/
  id : String
  /-- Its name in the YAML, where plans can set it; `none` for sverify's own. -/
  substrait : Option String
  /-- What the core allows. -/
  core : List Behaviour
  /-- What the YAML lists (`[]` for sverify's own), at `v0.106.0`. -/
  yaml : List Behaviour := []
  /-- Behaviours outside the YAML, each with the engine fact that records it (D3). -/
  extra : List (Behaviour × String) := []
  deriving Repr, DecidableEq

private def roundings : List Behaviour :=
  ["TIE_TO_EVEN", "TIE_AWAY_FROM_ZERO", "TRUNCATE", "CEILING", "FLOOR"]

/-- The option catalogue (`docs/core-semantics.md`, "The option catalogue"),
in its order. -/
def options : List OptionSpec := [
  -- Integers and decimals
  { id := "overflow", substrait := some "overflow", core := ["ERROR", "SILENT", "SATURATE"],
    yaml := ["ERROR", "SILENT", "SATURATE"] },
  { id := "on_division_by_zero", substrait := some "on_division_by_zero",
    core := ["IEEE", "LIMIT", "NULL", "ERROR"], yaml := ["IEEE", "LIMIT", "NULL", "ERROR"] },
  { id := "division_type", substrait := some "division_type", core := ["TRUNCATE", "FLOOR"],
    yaml := ["TRUNCATE", "FLOOR"] },
  { id := "min_mod_neg_one", substrait := none, core := ["ZERO", "ERROR"],
    extra := [("ERROR", "duckdb-R15-int-modulus")] },
  { id := "shift_range", substrait := none, core := ["ERROR", "ZERO", "DROP_BITS"],
    extra := [("ERROR", "duckdb-R15-shift-left"), ("ZERO", "duckdb-R15-shift-right")] },
  { id := "decimal_rescale", substrait := none,
    core := ["TIE_AWAY_FROM_ZERO", "TIE_TO_EVEN", "TRUNCATE"] },
  -- Doubles
  { id := "rounding", substrait := some "rounding",
    core := roundings ++ ["AWAY_FROM_ZERO", "TIE_DOWN", "TIE_UP", "TIE_TOWARDS_ZERO", "TIE_TO_ODD"],
    yaml := roundings ++ ["AWAY_FROM_ZERO", "TIE_DOWN", "TIE_UP", "TIE_TOWARDS_ZERO", "TIE_TO_ODD"] },
  { id := "on_domain_error", substrait := some "on_domain_error", core := ["NAN", "NULL", "ERROR"],
    yaml := ["NAN", "NULL", "ERROR"], extra := [("NAN", "duckdb-R15-math-domain")] },
  { id := "on_log_zero", substrait := some "on_log_zero", core := ["NAN", "ERROR", "MINUS_INFINITY"],
    yaml := ["NAN", "ERROR", "MINUS_INFINITY"] },
  { id := "nan_creation", substrait := none, core := ["NAN", "ERROR"],
    extra := [("NAN", "duckdb-R15-double-arith")] },
  { id := "zero_sign", substrait := none, core := ["IEEE", "ONE_ZERO"],
    extra := [("IEEE", "duckdb-R14")] },
  -- Substrait's for `index_in`, which the model does not have; sverify's for
  -- `=`, grouping, `DISTINCT` and joins.
  { id := "nan_equality", substrait := none, core := ["NAN_IS_NAN", "NAN_IS_NOT_NAN"] },
  { id := "nan_order", substrait := none, core := ["GREATEST", "UNORDERED"],
    extra := [("GREATEST", "duckdb-arg-min-nulls")] },
  { id := "nan_kind", substrait := none, core := ["IEEE", "ONE_NAN"],
    extra := [("IEEE", "duckdb-signbit")] },
  -- Strings, dates and lists
  { id := "negative_start", substrait := some "negative_start",
    core := ["WRAP_FROM_END", "LEFT_OF_BEGINNING", "ERROR"],
    yaml := ["WRAP_FROM_END", "LEFT_OF_BEGINNING", "ERROR"] },
  { id := "substring_range", substrait := none, core := ["ERROR", "COMPUTE"],
    extra := [("ERROR", "duckdb-substring-range")] },
  { id := "case_sensitivity", substrait := some "case_sensitivity",
    core := ["CASE_SENSITIVE", "CASE_INSENSITIVE", "CASE_INSENSITIVE_ASCII"],
    yaml := ["CASE_SENSITIVE", "CASE_INSENSITIVE", "CASE_INSENSITIVE_ASCII"] },
  { id := "char_set", substrait := some "char_set", core := ["UTF8", "ASCII_ONLY"],
    yaml := ["UTF8", "ASCII_ONLY"] },
  { id := "null_handling", substrait := some "null_handling",
    core := ["IGNORE_NULLS", "ACCEPT_NULLS"], yaml := ["IGNORE_NULLS", "ACCEPT_NULLS"] },
  { id := "date_range", substrait := none, core := ["ERROR", "COMPUTE"] },
  { id := "time_interval_months", substrait := none, core := ["DROP_MONTHS", "ERROR"],
    extra := [("DROP_MONTHS", "duckdb-time-plus-interval")] },
  { id := "list_null_order", substrait := none, core := ["NULL", "GREATEST", "LEAST"],
    extra := [("GREATEST", "duckdb-R11")] },
  -- Aggregates, windows and relations
  { id := "sum_order", substrait := none, core := ["ANY", "SEQUENTIAL"],
    extra := [("SEQUENTIAL", "duckdb-sum-double")] },
  { id := "stat_algo", substrait := none, core := ["GENERIC", "WELFORD_CHAN"],
    extra := [("WELFORD_CHAN", "duckdb-var-stddev")] },
  { id := "stat_degenerate", substrait := none, core := ["NULL", "NAN", "ERROR"],
    extra := [("NAN", "duckdb-corr")] },
  { id := "avg_int_result", substrait := none, core := ["DECLARED_TYPE"] },
  { id := "quantile_interp", substrait := none, core := ["BETWEEN", "LINEAR"],
    extra := [("LINEAR", "duckdb-quantile-cont-interpolation")] },
  { id := "tie_pick", substrait := none, core := ["ANY_ROW", "FIRST_READ"],
    extra := [("FIRST_READ", "duckdb-mode-ties")] },
  { id := "tie_order", substrait := none, core := ["ANY"] },
  -- A sort key's direction, not a function's option.
  { id := "null_order", substrait := none, core := ["NULLS_FIRST", "NULLS_LAST"],
    extra := [("NULLS_LAST", "duckdb-F2")] },
  { id := "clustered", substrait := none, core := ["ADJACENT"] },
  { id := "ntile_spread", substrait := none, core := ["STANDARD"] },
  { id := "float_to_int", substrait := none,
    core := ["TRUNCATE", "TIE_AWAY_FROM_ZERO", "TIE_TO_EVEN"],
    extra := [("TIE_AWAY_FROM_ZERO", "duckdb-R9")] },
  -- A cast's `failureBehavior`, not a function's option.
  { id := "cast_failure", substrait := none, core := ["THROW_EXCEPTION", "RETURN_NULL"] },
  -- Which variance `variance` and `std_dev` compute (#54): a function's
  -- parameter more than a behaviour, and every profile reads it.
  { id := "distribution", substrait := some "distribution", core := ["SAMPLE", "POPULATION"],
    yaml := ["SAMPLE", "POPULATION"] }]

def OptionSpec.find? (id : String) : Option OptionSpec := options.find? (·.id == id)

/-- A profile's choice at one option. -/
inductive Choice where
  /-- Any of these behaviours, whatever the plan prefers; `oneOf []` refuses. -/
  | oneOf (bs : List Behaviour)
  /-- The plan's first preference among `bs`; any of `dflt` where it states none. -/
  | asked (bs : List Behaviour) (dflt : List Behaviour)
  /-- The option never applies to the group's inputs (`on_domain_error` of
  integers): every preference is accepted, and any of the core's behaviours. -/
  | any
  deriving Repr, DecidableEq

/-- The behaviours a plan may prefer for the choice to accept it; `none`:
every preference. A plan whose preferences miss them is refused. -/
def Choice.accepted : Choice → Option (List Behaviour)
  | .oneOf bs | .asked bs _ => some bs
  | .any => none

/-- Does the choice allow only behaviours of `core`? The premise of the
refinement `Allowed_P ⊆ Allowed_core` (step 1c), per choice. -/
def Choice.within (core : List Behaviour) : Choice → Bool
  | .oneOf bs => bs.all core.contains
  | .asked bs d => bs.all core.contains && d.all core.contains && d.all bs.contains
  | .any => true

/-- Where an engine's behaviour comes from (engine profiles only, step 3b). -/
inductive Realization where
  | native
  /-- A shim the translation writes, by what it costs (an extra `CASE`, …). -/
  | shim (cost : String)
  | refused
  deriving Repr, DecidableEq

structure ProfileTable where
  name : String
  /-- Per option (`none`), or per group and option; the more specific row wins. -/
  choices : List (Option String × String × Choice)
  /-- Where each behaviour comes from: option, behaviour, realization. -/
  realize : List (String × Behaviour × Realization) := []
  /-- The facts each option's choice rests on. -/
  facts : List (String × List String) := []

/-- The choice at `option` for a function of `group`. -/
def ProfileTable.choice? (t : ProfileTable) (group option : String) : Option Choice :=
  match t.choices.find? (fun (g, o, _) => g == some group && o == option) with
  | some (_, _, c) => some c
  | none => (t.choices.find? (fun (g, o, _) => g.isNone && o == option)).map (·.2.2)

/-- The preferences a plan may give the Substrait option named `name` on a
function of `group`: `none` when the group does not take it, `some none` when
any preference is accepted. -/
def ProfileTable.accepts (t : ProfileTable) (group name : String) :
    Option (Option (List Behaviour)) := do
  let o ← options.find? (·.substrait == some name)
  let opts ← Functions.groups.lookup group
  if opts.contains o.id then (t.choice? group o.id).map Choice.accepted else none

/-- The reference's choices (`docs/core-semantics.md`, the catalogue's
"Reference" column). -/
def Profile.reference.table : ProfileTable where
  name := "reference"
  choices := [
    -- Integer overflow raises at the declared width (#202). `+`, `-`, `×` and
    -- negation also wrap around (`SILENT`) or clamp (`SATURATE`) when the plan
    -- asks (`UnFn.fit`, #241); `mkScalar` refuses them on decimals.
    (none, "overflow", .asked ["ERROR"] ["ERROR"]),
    (some "int.arith", "overflow", .asked ["ERROR", "SILENT", "SATURATE"] ["ERROR"]),
    -- Every value is modelled (`divByZero`). `IEEE` and `LIMIT` are only for
    -- dividing doubles: integers have neither, and the remainder of doubles is
    -- C's `fmod` (#203), whose IEEE value by zero is not `±∞`.
    (none, "on_division_by_zero", .asked ["ERROR", "NULL"] ["ERROR"]),
    (some "fp.div", "on_division_by_zero", .asked ["ERROR", "IEEE", "NULL", "LIMIT"] ["ERROR"]),
    -- The remainder takes the dividend's sign (`Int.tmod`, `FloatCode.fmod`):
    -- `TRUNCATE`. `FLOOR` is not modelled yet (#209 R3).
    (none, "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    (none, "shift_range", .oneOf ["DROP_BITS"]),
    (none, "decimal_rescale", .oneOf ["TIE_AWAY_FROM_ZERO"]),
    -- Native doubles round to nearest, ties to even (D5); `ROUND` rounds
    -- halves away from zero (`SubstraitLean/Rounding.lean`, #335).
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (some "fp.round", "rounding", .asked ["TIE_AWAY_FROM_ZERO"] ["TIE_AWAY_FROM_ZERO"]),
    -- Outside their domains the elementary functions raise (`Numeric.lean`,
    -- #215); no operation creates a NaN (#257). Integers have no domain error.
    (none, "on_domain_error", .asked ["ERROR"] ["ERROR"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "on_log_zero", .asked ["ERROR"] ["ERROR"]),
    (none, "nan_creation", .oneOf ["ERROR"]),
    -- One zero and one NaN, equal to itself and above `+∞` (#89).
    (none, "zero_sign", .oneOf ["ONE_ZERO"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_kind", .oneOf ["ONE_NAN"]),
    -- `Text.substrWrap` and `Text.substr`; `ERROR` is not modelled (#209).
    (none, "negative_start", .asked ["WRAP_FROM_END", "LEFT_OF_BEGINNING"] ["WRAP_FROM_END"]),
    (none, "substring_range", .oneOf ["ERROR"]),
    -- The model's string matching is case-sensitive, and `UPPER` and `LOWER`
    -- map Unicode case (`SubstraitLean/Text.lean`).
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (none, "char_set", .asked ["UTF8"] ["UTF8"]),
    (none, "null_handling", .asked ["ACCEPT_NULLS"] ["ACCEPT_NULLS"]),
    (none, "date_range", .oneOf ["ERROR"]),
    -- Refused (`TIME ± INTERVAL` with months).
    (none, "time_interval_months", .oneOf []),
    -- `NULL` in `<` of lists, last in `ORDER BY`, `MIN` and `MAX` (#207).
    (none, "list_null_order", .oneOf ["NULL"]),
    (some "agg.order", "list_null_order", .oneOf ["GREATEST"]),
    (none, "sum_order", .oneOf ["ANY"]),
    (none, "stat_algo", .oneOf ["GENERIC"]),
    (none, "stat_degenerate", .oneOf ["NULL"]),
    (none, "avg_int_result", .oneOf ["DECLARED_TYPE"]),
    (none, "quantile_interp", .oneOf ["BETWEEN"]),
    (none, "tie_pick", .oneOf ["ANY_ROW"]),
    (none, "tie_order", .oneOf ["ANY"]),
    -- As the key states; last for `UNSPECIFIED` (D8).
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_LAST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "ntile_spread", .oneOf ["STANDARD"]),
    (none, "float_to_int", .oneOf ["TRUNCATE"]),
    (none, "cast_failure", .asked ["THROW_EXCEPTION", "RETURN_NULL"] ["THROW_EXCEPTION"]),
    -- The sample's unless the plan asks for the population's (#54).
    (none, "distribution", .asked ["SAMPLE", "POPULATION"] ["SAMPLE"])]

/-! ## Checks -/

/-- Option ids and Substrait names are unique; each option's behaviours are
distinct, and its YAML values and extra behaviours are in its core. -/
example : (options.map (·.id)).Nodup := by decide +kernel
example : (options.filterMap (·.substrait)).Nodup := by decide +kernel
example : options.all fun o =>
    o.core.Nodup && o.yaml.all o.core.contains && o.extra.all (o.core.contains ·.1) := by
  decide +kernel
/-- Every group's options are options. -/
example : Functions.groups.all fun (_, os) => os.all fun o => (OptionSpec.find? o).isSome := by
  decide +kernel
/-- The reference chooses at every option, and only behaviours the core allows. -/
example : options.all fun o => (Profile.reference.table.choices.any (·.2.1 == o.id)) := by
  decide +kernel
example : Profile.reference.table.choices.all fun (g, o, c) =>
    g.all (Functions.groups.lookup · |>.any (·.contains o)) &&
    ((OptionSpec.find? o).map (c.within ·.core)).getD false := by
  decide +kernel

/-! ## For the Python mirror -/

open Lean (Json toJson) in
def Choice.json : Choice → Json
  | .oneOf bs => Json.mkObj [("kind", "oneOf"), ("behaviours", toJson bs)]
  | .asked bs d => Json.mkObj [("kind", "asked"), ("behaviours", toJson bs), ("default", toJson d)]
  | .any => Json.mkObj [("kind", "any")]

open Lean (Json toJson) in
/-- The options, the groups' options and the reference's choices as JSON:
`substrait-check --options`. -/
def optionsJson : Json :=
  Json.mkObj [
    ("options", Json.arr <| (options.map fun o => Json.mkObj [
      ("id", toJson o.id), ("substrait", toJson o.substrait), ("core", toJson o.core),
      ("yaml", toJson o.yaml),
      ("extra", toJson (o.extra.map fun (b, f) => [b, f]))]).toArray),
    ("groups", Json.mkObj (Functions.groups.map fun (g, os) => (g, toJson os))),
    ("choices", Json.mkObj [("reference", Json.arr <|
      (Profile.reference.table.choices.map fun (g, o, c) => Json.mkObj [
        ("group", toJson g), ("option", toJson o), ("choice", c.json)]).toArray)])]

end Substrait
