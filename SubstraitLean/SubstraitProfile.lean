import Lean.Data.Json
import Sverify.Core.Observations
import Sverify.Core.AllowedP

/-!
# The Substrait profile (#444, step 2)

`Profile.substrait.table` is Substrait's own semantics, as its extension
YAMLs (`substrait-extensions` 0.106.0) and its docs state it
(`docs/core-semantics.md`, "The option catalogue", the Substrait column):

* an option the YAML lists follows the plan's first preference among the
  YAML's values for that function, and where the plan states none, any of
  them: the YAMLs give no defaults, and Substrait's docs say an omitted
  option leaves the consumer "free to choose any supported behavior";
* sverify's own options take what Substrait's docs fix (IEEE 754's two
  zeros and signed NaNs, `sum`'s NULL for no values, `avg` truncating
  integers, 1-based character positions), and are left open where they fix
  nothing; each such gap is an `ST` entry of `upstream/bugs/`;
* a sort key's `UNSPECIFIED` direction leaves the NULL placement open, and
  `CLUSTERED` is the adjacency relation (D6).

Substrait is a sibling of the reference: neither refines the other. Both
refine the core (`Profile.substrait_le_core`, `Profile.reference_le_core`),
and `substraitDiff` lists where their choices differ. No engine runs plans
"on Substrait": the profile is something to check under, with
`verify(semantics="substrait")`. -/

namespace Substrait

private def fpRoundings : List Behaviour :=
  ["TIE_TO_EVEN", "TIE_AWAY_FROM_ZERO", "TRUNCATE", "CEILING", "FLOOR"]

/-- The core's choice at `option`: Substrait states nothing there. -/
private def openAt (option : String) : Choice :=
  .loose ((OptionSpec.find? option).map (·.core) |>.getD [])

/-- The YAML's values, the plan's first preference among them, any where it
states none. -/
private def yaml (bs : List Behaviour) : Choice := .asked bs bs

/-- Substrait's choices. Each row's comment names its source: the YAML
(`functions_*.yaml` at 0.106.0), a Substrait doc, or the `ST` entry that
records the gap. -/
def Profile.substrait.table : ProfileTable where
  name := "substrait"
  version := "0.106.0"
  choices := [
    -- Every integer and decimal function with an overflow takes the three
    -- values (`functions_arithmetic.yaml`, `functions_arithmetic_decimal.yaml`).
    (none, "overflow", yaml ["ERROR", "SILENT", "SATURATE"]),
    -- Integer `divide`: `NULL` or `ERROR`; integer `modulus` has no
    -- `on_division_by_zero` and governs `y = 0` by `on_domain_error`, with the
    -- same two values. Double `divide` has four.
    (none, "on_division_by_zero", yaml ["ERROR", "NULL"]),
    (some "fp.div", "on_division_by_zero", yaml ["IEEE", "LIMIT", "NULL", "ERROR"]),
    -- Double `modulus` and `sverify_fmod` are not Substrait functions.
    (some "fp.mod", "on_division_by_zero", openAt "on_division_by_zero"),
    -- `modulus` of integers takes either; `divide` of integers truncates
    -- ("partial values are truncated").
    (none, "division_type", yaml ["TRUNCATE", "FLOOR"]),
    (some "int.div", "division_type", yaml ["TRUNCATE"]),
    (some "fp.mod", "division_type", openAt "division_type"),
    -- The remainder of `MIN % -1` is 0, which fits.
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    -- A shift by a count outside the width, and bits shifted out (ST-1).
    (none, "shift_range", openAt "shift_range"),
    -- How a decimal result with too many digits rounds (ST-8).
    (none, "decimal_rescale", openAt "decimal_rescale"),
    -- The five modes of the double functions, the ten of `round` (D5).
    (none, "rounding", yaml fpRoundings),
    (some "fp.round", "rounding",
      yaml (fpRoundings ++ ["AWAY_FROM_ZERO", "TIE_DOWN", "TIE_UP", "TIE_TOWARDS_ZERO", "TIE_TO_ODD"])),
    -- `sqrt`, the trigonometric functions and `atan2` (ST-2): `NAN` or
    -- `ERROR`; `divide` of doubles and the logarithms add `NULL`; `divide`
    -- of integers has `NULL` and `ERROR`, and no input reaches it. Integer
    -- `power` has no such option.
    (none, "on_domain_error", yaml ["NAN", "ERROR"]),
    (some "fp.div", "on_domain_error", yaml ["NAN", "NULL", "ERROR"]),
    (some "fp.log", "on_domain_error", yaml ["NAN", "NULL", "ERROR"]),
    (some "int.div", "on_domain_error", yaml ["NULL", "ERROR"]),
    (some "int.pow", "on_domain_error", .any),
    (none, "on_log_zero", yaml ["NAN", "ERROR", "MINUS_INFINITY"]),
    -- `inf - inf`, `0 * inf` (ST-5); `inf / inf` is `divide`'s
    -- `on_domain_error`.
    (none, "nan_creation", openAt "nan_creation"),
    -- `fp32` and `fp64` are IEEE 754's (`type_classes.md`): two zeros, NaNs
    -- with a sign; `equal` is IEEE's `==`, and NaN compares with nothing.
    -- Grouping, joins and sorts say nothing of NaN or `-0.0` (ST-4).
    (none, "zero_sign", .oneOf ["IEEE"]),
    -- `round` and `ceil` say nothing of a zero's sign.
    (none, "round_zero_sign", openAt "round_zero_sign"),
    -- The YAML's `power` says nothing of `1 ^ ∞` (D40).
    (none, "pow_one_inf", openAt "pow_one_inf"),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_equality", openAt "nan_equality"),
    (some "cmp", "nan_equality", .oneOf ["NAN_IS_NOT_NAN"]),
    (none, "nan_order", openAt "nan_order"),
    (some "cmp", "nan_order", .oneOf ["UNORDERED"]),
    -- `substring`'s three (two without a length); its offsets are `i32`, so
    -- no offset leaves the range.
    (none, "negative_start", yaml ["WRAP_FROM_END", "LEFT_OF_BEGINNING", "ERROR"]),
    (none, "substring_range", .oneOf ["COMPUTE"]),
    (none, "case_sensitivity", yaml ["CASE_SENSITIVE", "CASE_INSENSITIVE", "CASE_INSENSITIVE_ASCII"]),
    (none, "char_set", yaml ["UTF8", "ASCII_ONLY"]),
    (none, "null_handling", yaml ["IGNORE_NULLS", "ACCEPT_NULLS"]),
    -- The YAML gives no rule for a result past the types' ranges.
    (none, "date_range", openAt "date_range"),
    (none, "time_interval_months", openAt "time_interval_months"),
    -- `lt` of lists is not defined.
    (none, "list_null_order", openAt "list_null_order"),
    -- `sum`, `avg`, `variance`, `corr` and `quantile` name no algorithm, and
    -- `any_value` "selects an arbitrary value"; the degenerate cases are ST-3.
    (none, "sum_order", openAt "sum_order"),
    (none, "stat_algo", openAt "stat_algo"),
    (none, "window_sum_algo", openAt "window_sum_algo"),
    (none, "stat_degenerate", openAt "stat_degenerate"),
    -- `avg` of an integer type returns it, and "truncates partial values".
    (none, "avg_int_result", .oneOf ["DECLARED_TYPE"]),
    (none, "quantile_interp", openAt "quantile_interp"),
    (none, "tie_pick", openAt "tie_pick"),
    (none, "tie_order", openAt "tie_order"),
    -- A key's direction states its NULL placement; `UNSPECIFIED` leaves it
    -- open (D6, ST-7). `CLUSTERED` is `relations/basics.md`'s.
    (none, "null_order", yaml ["NULLS_FIRST", "NULLS_LAST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "ntile_spread", openAt "ntile_spread"),
    -- A cast to an integer names no rounding; `FAILURE_BEHAVIOR_UNSPECIFIED`
    -- is not described (ST-6).
    (none, "float_to_int", openAt "float_to_int"),
    (none, "cast_failure", yaml ["THROW_EXCEPTION", "RETURN_NULL"]),
    -- `variance` and `std_dev` give no default distribution.
    (none, "distribution", yaml ["SAMPLE", "POPULATION"]),
    -- "The sum of zero elements yields null."
    (none, "empty_group_aggregates", .oneOf ["NULL"]),
    -- A finite double operation past the largest double (ST-9).
    (none, "float_overflow", openAt "float_overflow"),
    -- A join keeps the rows its condition is true for; `equal` of a NULL is NULL.
    (none, "null_join_keys", .oneOf ["NO_MATCH"]),
    -- Positions count characters from 1.
    (none, "string_positions", .oneOf ["ONE_BASED_CHARS"])]

/-- How Substrait's semantics relates to the reference's, where it does as an
engine would: two zeros and signed NaNs are the reference's up to `canon`. -/
def Profile.substrait.obs : ObsTable := [
  (none, "zero_sign", { cls := .refinesUpTo, q := { zeros := .canon } }),
  (none, "nan_kind", { cls := .refinesUpTo, q := { zeros := .canon } }),
  -- A consumer adds a double `SUM` in an order of its own: within the plan's
  -- bound of the reference's correctly rounded sum (D25, `epsilon_sum_cr`).
  (none, "sum_order", { cls := .approx, q := { floats := .within "plan" } }),
  -- A consumer's own algorithm for a statistical aggregate: within the plan's
  -- bound of the exact moments rounded once (D30).
  (none, "stat_algo", { cls := .approx, q := { floats := .within "plan" } })]

/-! ## Checks -/

/-- Substrait chooses at every option, once per group and option, and only
behaviours the core allows. -/
example : options.all fun o => Profile.substrait.table.choices.any (·.2.1 == o.id) := by
  decide +kernel
example : (Profile.substrait.table.choices.map fun (g, o, _) => (g, o)).Nodup :=
  nodup_of_nodupB (by decide +kernel)
example : Profile.substrait.table.choices.all fun (g, o, c) =>
    g.all (Functions.groups.lookup · |>.any (·.contains o)) &&
    ((OptionSpec.find? o).map (c.within ·.core)).getD false := by
  decide +kernel
/-- An option of Substrait's YAMLs is never left open: its row lists YAML
values, or the group takes the option from no Substrait function. Only the
YAMLs' options and two fields of the plan's messages (a sort key's direction,
a cast's failure behaviour) follow the plan's preference. -/
example : Profile.substrait.table.choices.all fun (g, o, c) =>
    match OptionSpec.find? o, c with
    | some spec, .asked s d =>
      (spec.substrait.isSome && s.all spec.yaml.contains || ["null_order", "cast_failure"].contains o) &&
        d == s
    | some spec, .loose _ => spec.substrait.isNone || g == some "fp.mod"
    | _, _ => true := by
  decide +kernel
example : Profile.substrait.obs.all (·.2.2.wf) := by decide +kernel

/-- **Substrait refines the core**, choice by choice. -/
theorem Profile.substrait_le_core : Profile.substrait.table.Le Profile.core.table :=
  ProfileTable.le_of_leB (by decide +kernel)

/-- `Allowed_substrait ⊆ Allowed_core`. -/
theorem Rel.allowed_substrait_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.substrait.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.substrait_le_core h

/-- Neither refines the other: Substrait leaves `overflow` open where the
reference raises, and the reference has one zero where Substrait has two. -/
example : Profile.substrait.table.leB Profile.reference.table = false := by decide +kernel
example : Profile.reference.table.leB Profile.substrait.table = false := by decide +kernel

/-! ## Where Substrait and the reference differ -/

/-- One row of the diff: a group (`none`: every group without a row of its
own) and option, with what each profile accepts from a plan
(`Choice.accepted`, `none`: anything) and allows where the plan states no
preference. -/
structure DiffRow where
  group : Option String
  option : String
  accepts : Option (List Behaviour) × Option (List Behaviour)
  dflt : List Behaviour × List Behaviour
  deriving Repr, DecidableEq

/-- What `t` accepts and allows by default at `group` and `option`. -/
private def ProfileTable.rowAt (t : ProfileTable) (group : Option String) (option : String) :
    Option (Option (List Behaviour) × List Behaviour) := do
  let c ← match group with
    | some g => t.choice? g option
    | none => t.dflt? option
  let o ← OptionSpec.find? option
  pure (c.accepted, c.allows o.core [])

private def sameSet (a b : List Behaviour) : Bool := a.all b.contains && b.all a.contains

/-- The options where `t` and `u` differ, per row either names: in what they
accept from a plan, or in what they allow where it states nothing. -/
def profileDiff (t u : ProfileTable) : List DiffRow :=
  options.flatMap fun o =>
    let keys := (none :: ((t.groupsAt o.id ++ u.groupsAt o.id).eraseDups.map some))
    keys.filterMap fun g => do
      let (ta, td) ← t.rowAt g o.id
      let (ua, ud) ← u.rowAt g o.id
      let sameAccepts := match ta, ua with
        | some a, some b => sameSet a b
        | none, none => true
        | _, _ => false
      if sameAccepts && sameSet td ud then none
      else some { group := g, option := o.id, accepts := (ta, ua), dflt := (td, ud) }

/-- Where Substrait and the reference differ: generated, and published in
`docs/core-semantics.md` (`substrait-check --profile-diff`). -/
def substraitDiff : List DiffRow := profileDiff Profile.substrait.table Profile.reference.table

/-- The diff names the differences the design expects: one zero, one NaN,
`nan_creation`, and the open defaults. -/
example : ["zero_sign", "nan_kind", "nan_creation", "overflow", "null_order", "distribution",
    "rounding"].all fun o => substraitDiff.any (·.option == o) := by
  decide +kernel

open Lean (Json toJson) in
def DiffRow.json (r : DiffRow) : Json :=
  let acc : Option (List Behaviour) → Json
    | some bs => toJson bs
    | none => Json.null
  Json.mkObj [("group", toJson r.group), ("option", toJson r.option),
    ("substrait", Json.mkObj [("accepts", acc r.accepts.1), ("default", toJson r.dflt.1)]),
    ("reference", Json.mkObj [("accepts", acc r.accepts.2), ("default", toJson r.dflt.2)]),
    ("tool", toJson ((Profile.reference.tools.find? (·.option == r.option)).map fun t =>
      match t.tool with | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open"))]

open Lean (Json toJson) in
/-- `substrait-check --profile-diff`. -/
def substraitDiffJson : Json := Json.arr (substraitDiff.map DiffRow.json).toArray

end Substrait
