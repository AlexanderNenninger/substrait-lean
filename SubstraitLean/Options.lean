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
  /-- One of these behaviours: the plan's first preference among them, any of
  them where it states none; `oneOf []` refuses. The same as `asked bs bs`. -/
  | oneOf (bs : List Behaviour)
  /-- The plan's first preference among `bs`; any of `dflt` where it states none. -/
  | asked (bs : List Behaviour) (dflt : List Behaviour)
  /-- The option never applies to the group's inputs (`on_domain_error` of
  integers): every preference is accepted, and any of the core's behaviours
  the plan prefers. -/
  | any
  /-- Any of the plan's preferences among `bs`, or any of `bs` where it states
  none: the core's choice, which allows every behaviour a consumer may
  deliver, where a profile delivers the first it supports. -/
  | loose (bs : List Behaviour)
  deriving Repr, DecidableEq

/-- The behaviours a plan may prefer for the choice to accept it; `none`:
every preference. A plan whose preferences miss them is refused. -/
def Choice.accepted : Choice → Option (List Behaviour)
  | .oneOf bs | .asked bs _ | .loose bs => some bs
  | .any => none

/-- Does the choice allow only behaviours of `core`? -/
def Choice.within (core : List Behaviour) : Choice → Bool
  | .oneOf bs | .loose bs => bs.all core.contains
  | .asked bs d => bs.all core.contains && d.all core.contains && d.all bs.contains
  | .any => true

/-- Substrait's rule: the first of the preferences `ps` that `s` supports, or
`d` where `ps` is empty; nothing (the plan is refused) where `s` supports none. -/
def Choice.pick (s d ps : List Behaviour) : List Behaviour :=
  match ps.find? (s.contains ·) with
  | some p => [p]
  | none => if ps.isEmpty then d else []

/-- The behaviours the choice allows for a call whose plan prefers `ps`
(`[]`: the plan states none). `core` is the option's. -/
def Choice.allows (core : List Behaviour) : Choice → List Behaviour → List Behaviour
  | .oneOf bs, ps => pick bs bs ps
  | .asked s d, ps => pick s d ps
  | .loose bs, ps => if ps.isEmpty then bs else ps.filter (bs.contains ·)
  | .any, ps => if ps.isEmpty then core else ps.filter (core.contains ·)

private def subset (a b : List Behaviour) : Bool := a.all (b.contains ·)

private def Choice.asAsked : Choice → Option (List Behaviour × List Behaviour)
  | .oneOf bs => some (bs, bs)
  | .asked s d => some (s, d)
  | _ => none

/-- A decidable test that `c` allows no more than `d`, for every list of
preferences (`Choice.le_sound`). Against an `asked` choice, `c` must support
the same behaviours, since the first preference it supports is the one it
delivers. -/
def Choice.le (core : List Behaviour) (c d : Choice) : Bool :=
  match d with
  | .loose S => match c with
    | .oneOf bs | .loose bs => subset bs S
    | .asked s dflt => subset s S && subset dflt S
    | .any => subset core S
  | .any => match c with
    | .oneOf bs | .loose bs => subset bs core
    | .asked s dflt => subset s core && subset dflt core
    | .any => true
  | _ => match c.asAsked, d.asAsked with
    | some (s, dflt), some (s', dflt') => subset s s' && subset s' s && subset dflt dflt'
    | _, _ => false

private theorem mem_of_subset {a b : List Behaviour} (h : subset a b = true) {x : Behaviour}
    (hx : x ∈ a) : x ∈ b := by
  simp only [subset, List.all_eq_true, List.contains_iff_mem] at h
  exact h x hx

private theorem mem_pick {s d ps : List Behaviour} {b : Behaviour} (h : b ∈ Choice.pick s d ps) :
    (b ∈ ps ∧ b ∈ s) ∨ (ps = [] ∧ b ∈ d) := by
  unfold Choice.pick at h
  split at h
  · next p hp =>
    simp only [List.mem_singleton] at h; subst h
    exact .inl ⟨List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
  · split at h
    · next he => exact .inr ⟨List.isEmpty_iff.mp he, h⟩
    · simp at h

private theorem pick_congr {s s' d d' ps : List Behaviour} (h₁ : subset s s' = true)
    (h₂ : subset s' s = true) (hd : subset d d' = true) {b : Behaviour}
    (h : b ∈ Choice.pick s d ps) : b ∈ Choice.pick s' d' ps := by
  have hc : (fun x => s.contains x) = fun x => s'.contains x := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact ⟨mem_of_subset h₁, mem_of_subset h₂⟩
  unfold Choice.pick at h ⊢
  rw [hc] at h
  cases hf : ps.find? (s'.contains ·) with
  | some p => rw [hf] at h; exact h
  | none =>
    rw [hf] at h
    by_cases he : ps.isEmpty
    · simp only [he, ite_true] at h ⊢; exact mem_of_subset hd h
    · simp [he] at h

/-- **`Choice.le` is sound**: whatever the plan prefers, `c` allows no
behaviour `d` does not. -/
theorem Choice.le_sound {core : List Behaviour} {c d : Choice} (h : c.le core d = true)
    {ps : List Behaviour} {b : Behaviour} (hb : b ∈ c.allows core ps) : b ∈ d.allows core ps := by
  cases d with
  | loose S =>
    simp only [allows]
    cases c with
    | oneOf bs | asked bs _ =>
      simp only [le, Bool.and_eq_true] at h
      simp only [allows] at hb
      rcases mem_pick hb with ⟨hp, hs⟩ | ⟨rfl, hd⟩
      · have : ps.isEmpty = false := by cases ps <;> simp_all
        simp only [this, Bool.false_eq_true, ite_false, List.mem_filter, List.contains_iff_mem]
        first
          | exact ⟨hp, decide_eq_true (mem_of_subset h hs)⟩
          | exact ⟨hp, decide_eq_true (mem_of_subset h.1 hs)⟩
          | exact ⟨hp, by simpa using mem_of_subset h.1 hs⟩
          | exact ⟨hp, by simpa using mem_of_subset h hs⟩
      · simp only [List.isEmpty_nil, ite_true]
        first | exact mem_of_subset h hd | exact mem_of_subset h.2 hd
    | loose bs =>
      simp only [le] at h
      simp only [allows] at hb
      split at hb
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact mem_of_subset h hb
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        simp only [List.mem_filter, List.contains_iff_mem] at hb ⊢
        exact ⟨hb.1, mem_of_subset h hb.2⟩
    | any =>
      simp only [le] at h
      simp only [allows] at hb
      split at hb
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact mem_of_subset h hb
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        simp only [List.mem_filter, List.contains_iff_mem] at hb ⊢
        exact ⟨hb.1, by simpa using mem_of_subset h (by simpa using hb.2)⟩
  | any =>
    simp only [allows]
    cases c with
    | oneOf bs | asked bs _ =>
      simp only [le, Bool.and_eq_true] at h
      simp only [allows] at hb
      rcases mem_pick hb with ⟨hp, hs⟩ | ⟨rfl, hd⟩
      · have : ps.isEmpty = false := by cases ps <;> simp_all
        simp only [this, Bool.false_eq_true, ite_false, List.mem_filter, List.contains_iff_mem]
        first
          | exact ⟨hp, by simpa using mem_of_subset h hs⟩
          | exact ⟨hp, by simpa using mem_of_subset h.1 hs⟩
      · simp only [List.isEmpty_nil, ite_true]
        first | exact mem_of_subset h hd | exact mem_of_subset h.2 hd
    | loose bs =>
      simp only [le] at h
      simp only [allows] at hb
      split at hb
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]; exact mem_of_subset h hb
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        simp only [List.mem_filter, List.contains_iff_mem] at hb ⊢
        exact ⟨hb.1, by simpa using mem_of_subset h (by simpa using hb.2)⟩
    | any => exact hb
  | oneOf bs' | asked bs' _ =>
    cases c with
    | oneOf bs | asked bs _ =>
      simp only [le, asAsked, Bool.and_eq_true] at h
      simp only [allows] at hb ⊢
      exact pick_congr h.1.1 h.1.2 h.2 hb
    | loose _ | any => simp [le, asAsked] at h

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

/-- The behaviours the profile allows at `option` for a function of `group`,
where the plan prefers `ps`; `[]` where it has no choice there. -/
def ProfileTable.allows (t : ProfileTable) (group option : String) (ps : List Behaviour) :
    List Behaviour :=
  match t.choice? group option, OptionSpec.find? option with
  | some c, some o => c.allows o.core ps
  | _, _ => []

/-- `t` allows no more than `u`, at every group, option and list of
preferences: the premise of `Rel.AllowedP_mono`. -/
def ProfileTable.Le (t u : ProfileTable) : Prop :=
  ∀ group option ps b, b ∈ t.allows group option ps → b ∈ u.allows group option ps

/-- The choice of the row without a group. -/
def ProfileTable.dflt? (t : ProfileTable) (option : String) : Option Choice :=
  (t.choices.find? fun (g, o, _) => g.isNone && o == option).map (·.2.2)

/-- The groups the table has rows of its own for, at `option`. -/
def ProfileTable.groupsAt (t : ProfileTable) (option : String) : List String :=
  t.choices.filterMap fun (g, o, _) => if o == option then g else none

theorem ProfileTable.choice?_of_not_mem {t : ProfileTable} {g o : String}
    (h : g ∉ t.groupsAt o) : t.choice? g o = t.dflt? o := by
  unfold choice? dflt?
  rw [List.find?_eq_none.mpr]
  rintro ⟨g', o', c⟩ hm
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  rintro rfl rfl
  exact h (List.mem_filterMap.mpr ⟨_, hm, by simp⟩)

private def leOpt (core : List Behaviour) : Option Choice → Option Choice → Bool
  | none, _ => true
  | some c, some d => c.le core d
  | some _, none => false

private theorem leOpt_sound {core : List Behaviour} {c d : Option Choice}
    (h : leOpt core c d = true) {ps : List Behaviour} {b : Behaviour}
    (hb : b ∈ (match c with | some c => c.allows core ps | none => [])) :
    b ∈ (match d with | some d => d.allows core ps | none => []) := by
  cases c with
  | none => simp at hb
  | some c => cases d with
    | none => simp [leOpt] at h
    | some d => exact Choice.le_sound h hb

/-- A decidable test of `Le` (`ProfileTable.le_of_leB`): per option, the rows
without a group and the groups either table names. -/
def ProfileTable.leB (t u : ProfileTable) : Bool :=
  options.all fun o => leOpt o.core (t.dflt? o.id) (u.dflt? o.id) &&
    (t.groupsAt o.id ++ u.groupsAt o.id).all fun g => leOpt o.core (t.choice? g o.id) (u.choice? g o.id)

theorem ProfileTable.le_of_leB {t u : ProfileTable} (h : t.leB u = true) : t.Le u := by
  intro g o ps b hb
  unfold allows at hb ⊢
  cases hf : OptionSpec.find? o with
  | none => simp [hf] at hb
  | some spec =>
    have hmem := List.mem_of_find?_eq_some hf
    have hid : spec.id = o := by simpa using List.find?_some hf
    subst hid
    simp only [leB, List.all_eq_true, Bool.and_eq_true] at h
    obtain ⟨hd, hg⟩ := h spec hmem
    have key : leOpt spec.core (t.choice? g spec.id) (u.choice? g spec.id) = true := by
      by_cases hin : g ∈ t.groupsAt spec.id ++ u.groupsAt spec.id
      · exact hg g hin
      · rw [List.mem_append, not_or] at hin
        rw [choice?_of_not_mem hin.1, choice?_of_not_mem hin.2]; exact hd
    have hb' : b ∈ (match t.choice? g spec.id with | some c => c.allows spec.core ps | none => []) := by
      rw [hf] at hb
      cases hc : t.choice? g spec.id <;> rw [hc] at hb <;> simp_all
    have := leOpt_sound key hb'
    cases hc : u.choice? g spec.id <;> rw [hc] at this <;> simp_all

/-- The core: every option `loose` over all its behaviours. -/
def Profile.core.table : ProfileTable where
  name := "core"
  choices := options.map fun o => (none, o.id, .loose o.core)

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

/-- **The reference refines the core**, choice by choice. -/
theorem Profile.reference_le_core : Profile.reference.table.Le Profile.core.table :=
  ProfileTable.le_of_leB (by decide +kernel)

/-! ## For the Python mirror -/

open Lean (Json toJson) in
def Choice.json : Choice → Json
  | .oneOf bs => Json.mkObj [("kind", "oneOf"), ("behaviours", toJson bs)]
  | .asked bs d => Json.mkObj [("kind", "asked"), ("behaviours", toJson bs), ("default", toJson d)]
  | .any => Json.mkObj [("kind", "any")]
  | .loose bs => Json.mkObj [("kind", "loose"), ("behaviours", toJson bs)]

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
