# The loose core: design

Sverify's semantics share one loose core in Lean, and every semantics
sverify knows is a refinement of it: Substrait's, the reference's and each
engine's
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
Plans are proved under the strict reference profile
([Terminology](#terminology)).
This page began as the design pass of step 3 of epic
[#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544), and
both epics have closed. It lists, per function, the points where profiles
differ, gives the tables that hold each profile's choices, says which values
the core needs, and states when a translation between two profiles is sound.
The approach is CASL's loose semantics and WebAssembly's profiles, applied to
Substrait, with refinement as CompCert and Alive2 state it
([Prior work](#prior-work)). Wave 3 of #544 built the function tables in this
shape. Each engine's profile and shims are in
[engine-profiles.md](engine-profiles.md).

The choices this page left open were decided in its review
([Decisions](decisions.md#decisions)). Everything else follows decisions already made on
#185, #202, #209, #257, #336, #427 and #444; [reference-semantics.md](reference-semantics.md)
records them.

## Core, profiles and engines

Sverify has one core that does a superset of operations, and profiles refine
it (the maintainer, 2026-11-08). This section is the one statement of that
layering; the other pages link here.

```text
core       every value, every behaviour of every option
   │       a profile picks a refinement: one choice per option
   ▼
profiles   reference · Substrait · DuckDB · Polars · Spark · Snowflake
   │       an engine runs its profile; Engine.Refines, Engine.Sound per plan
   ▼
engines    DuckDB · Polars · Spark · Snowflake · DataFusion (optional)
```

- The core computes on the full value space. A double is an IEEE 754
  binary64 code, `-0.0` and the negative NaN included
  ([The value domain](#the-value-domain)); `+ − × ÷` are the exact result
  rounded once ([D31](decisions.md#d31-double-arithmetic-is-exact-rounded-once)), and so
  are double sums and statistical moments
  ([D25](decisions.md#d25-float-aggregates-are-correctly-rounded-exact-sums),
  [D30](decisions.md#d30-statistical-aggregates-are-correctly-rounded-exact-moments)).
  Every option holds all of its behaviours
  ([The option catalogue](#the-option-catalogue)). One evaluator serves every
  weight type, bags and Z-sets among them (`Rel.evalK`,
  [#905](https://github.com/AlexanderNenninger/substrait-lean/issues/905)).
- A profile is a refinement of the core: for each option it picks the
  behaviours it allows, such as `zero_sign`, `nan_kind`, `nan_equality`,
  `nan_order`, `stat_algo` and `sum_order` ([The options table](#the-options-table)).
  `Rel.AllowedP_mono` proves that every result a profile allows the core
  allows. The reference profile (`Profile.reference`) makes the usual SQL
  choices: `ONE_ZERO`, `ONE_NAN`, `NAN_IS_NAN` and NaN `GREATEST`, and
  raises on the edge cases where engines disagree. For each option it picks
  a behaviour every 1.0 engine has natively or reaches with a cheap shim in
  the writers, such as `Dialect.canon` for `ONE_ZERO` or a stated
  `NULLS LAST` ([principle 3](reference-semantics.md#principles)). Substrait's profile
  (`Profile.substrait`) is strict IEEE: two zeros, signed NaNs, and NaN
  unequal to itself in comparisons. Each engine has a profile of its own, from its facts. The
  profiles are siblings ([Terminology](#terminology)).
- An engine runs its profile. A plan proved under the reference reaches
  the engine through the engine's translation; per plan, `Engine.Refines`
  names the observation rows the run relies on, and `Engine.Sound` proves
  that the rows the engine's model computes are a result the reference
  allows ([#1132](https://github.com/AlexanderNenninger/substrait-lean/pull/1132),
  [#1134](https://github.com/AlexanderNenninger/substrait-lean/pull/1134),
  [Which plans run on an engine](#which-plans-run-on-an-engine)). Where an
  engine's choice of an open option differs from the reference's
  (`sum_order`, `stat_algo`), its result is within the plan's tolerance of
  one the reference allows (`Relation.Near`,
  [#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929)).
  DataFusion is an optional engine, and no test takes it as a reference or
  an oracle ([#1139](https://github.com/AlexanderNenninger/substrait-lean/pull/1139)).
  DuckDB is the default oracle.

## Principles the code follows

Four rules shape how the core states its guarantees
([#1017](https://github.com/AlexanderNenninger/substrait-lean/issues/1017)).
The decisions below apply them; they add no semantics of their own.

- A side condition on a top-level theorem is a decidable predicate of the
  plan, which the checker proves on each plan; the Python side trusts no
  hypothesis. `Rel.closedB` is the side condition of
  `contract_sound_allowed_closed`
  ([#899](https://github.com/AlexanderNenninger/substrait-lean/issues/899),
  [#1010](https://github.com/AlexanderNenninger/substrait-lean/pull/1010)),
  `Expr.robustB` that of `contract_sound_allowed`, and `Rel.FloatOpenSafe`
  comes with two sufficient conditions (`Rel.floatOpenSafe_of_closed`,
  `Rel.floatOpenSafe_aggregate`), as the kind checker's `Rel.kinds_sound`
  carries the kinds (D28).
- Work across epics goes interface first. A change that several epics build
  on lands as its interface before the epics change the definitions behind
  it: the helpers of `Value` by kind
  ([#1005](https://github.com/AlexanderNenninger/substrait-lean/pull/1005))
  came before `Value`'s constructor per kind
  ([D29](decisions.md#d29-a-value-has-its-kind), #923).
- The reference states a value; a profile states a distance from it. Where
  engines compute a result in different ways, the reference fixes one value
  and each engine's profile bounds how far the engine may be from it: the
  correctly rounded sums and moments of
  [D25](decisions.md#d25-float-aggregates-are-correctly-rounded-exact-sums) and
  [D30](decisions.md#d30-statistical-aggregates-are-correctly-rounded-exact-moments),
  with each engine within the plan's bound (`Relation.Near`).
- Engines meet the reference through the `AllowedP` profile tables. A new
  engine is a profile and a facts table, with no change to `Rel.eval` or
  `Rel.Allowed` ([Translations between profiles](#translations-between-profiles)),
  and a package can add one without changing sverify
  ([engine profiles from outside](engine-profiles.md#engine-profiles-from-outside)).

## Terminology

Three kinds of semantics, each with one job.

- The core is the loosest semantics, a specification layer. It admits every
  engine's behaviour ([D3](decisions.md#d3-behaviours-outside-the-yaml)), every profile
  refines it, and it is where profiles are stated and related: a profile is
  the core with its choices narrowed, and a translation from the reference
  to an engine is a refinement between two profiles
  ([Translations](#translations-between-profiles)).
  Every point where engines or Substrait differ is an open option, and its
  values are at least as fine as Substrait's (`-0.0`, signed NaNs, `fp32`
  later; [The value domain](#the-value-domain)). Sverify runs no plan under
  the core. A proof under it would hold under every profile, but few plans
  verify there: the core allows every engine's raises and NaNs at once.
- The reference profile (`Profile.reference`, "the reference") is what plans
  are proved under. It is strict, stricter than every engine in most
  options. Where engines disagree on an edge case (integer overflow, NaN
  creation, double overflow to `±∞` (#575), domain errors, division by zero,
  out-of-range casts and dates), it raises. Where it picks a value, it picks
  one every engine can produce
  ([principle 3](reference-semantics.md#principles)).
  The reference may still choose a behaviour some engine needs a shim for,
  where that keeps the profile practical for users (the NULL order, rounding
  ties). Each such choice costs a shim on every engine that differs, so these
  choices are few and deliberate: the reference prefers raising, proved
  absent for a proved plan, or a choice every engine gives natively.
- Engine profiles say what each engine does, from
  `characterization/<engine>/facts/`, and refine the core. They are
  siblings: no engine profile refines another, or the reference. A plan
  proved under the reference reaches an engine through a translation,
  shimmed only on the reference's value choices
  ([Which plans run on an engine](#which-plans-run-on-an-engine)).
  `Profile.substrait` (step 2) is a sibling of the same kind: the YAMLs'
  own looseness, with IEEE's two zeros and signed NaNs. The reference
  overrides Substrait in places ([Overrides](reference-semantics.md#overrides)),
  so neither of the two refines the other.

Black boxes are rows of a black-box catalogue (`Boxes`,
`core/Sverify/Core/BlackBox.lean`) that engine packages supply: DuckDB's is
`Boxes.duckdb` (`SubstraitLean/DuckDBBoxes.lean`). The core holds the
mechanism and no rows, and the reference is parametric in the catalogue
(`Rel.Allowed B cat`). A proof uses only a row's laws, and they hold by
construction: the model's value is the row's function where that keeps the
laws and the row's sample elsewhere, and the catalogue's well-formedness
(`Boxes.WF`, each sample keeps its laws) is proved by the engine package. A
black box's value under the reference is any value keeping its row's laws;
the catalogue's evaluator is one such value, and that an engine's function
keeps the laws is a fact of that engine, with evidence in its package.

### What strictness buys

A plan proved under the reference never raises: its preconditions,
stated or inferred, are proved to exclude the reference's raise set, or
checked on the data. The inputs where engines disagree on errors are in that
raise set, so a proved plan never reaches them, and it creates no new NaN
(`nan_creation` raises in the reference). In the classes of
[#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568),
each call of such a plan is `exact` on every engine on the domain `D`, the
reference's non-raising domain at that call, and the proof keeps the plan's
inputs inside `D`.

So the options split in three, and a proved plan needs a shim only for the
second:

| Kind | Reference | Options | A proved plan on an engine |
|---|---|---|---|
| Error side | raises | `overflow` (`ERROR`), `on_division_by_zero`, `on_domain_error`, `on_log_zero`, `nan_creation`, double overflow to `±∞` (#575), `shift_range`, `substring_range`, `date_range`, `cast_failure` (`UNSPECIFIED`), `stat_degenerate` for `±∞` | no shim: the engine's behaviour there (a wrap, NULL, NaN, `±∞`, a panic) is never reached |
| Value side | picks one value | `null_order`, `rounding` of `round`, `division_type`, floor or truncating division of negatives, `float_to_int`, `decimal_rescale`, `avg_int_result`, an empty `SUM`, string and list positions, `zero_sign`, `nan_kind`, `nan_order`, `list_null_order`, `stat_degenerate` for `CORR`, result types | native where the engine picks the same value; a shim otherwise |
| Open | allows several | `sum_order`, `stat_algo`, `quantile_interp`, `tie_pick`, `tie_order` | native where the engine's pick is one the reference allows; `observed` within the plan's tolerance `ε` (#568, D22) otherwise |

An option the plan states itself (`overflow: SILENT`) is a value choice too.
A precondition only checked on the data, such as a `SUM`'s overflow bound
(#316), needs its run-time check, the guard, on every engine; guard
elimination (#83) drops the guards the inferred bounds rule out.
[The Polars example](engine-profiles.md#the-polars-example) counts the shims for one engine.

## The shape

The reference is already a relation: `Rel.Allowed` (`core/Sverify/Core/Allowed.lean`,
[#427](https://github.com/AlexanderNenninger/substrait-lean/pull/427)) allows a
set of results per input, and `Rel.eval` computes one of them
(`Rel.eval_allowed`). The core generalises it in one direction: every place
where `Rel.Allowed` makes a choice for the reference becomes a choice
point, and a profile is the set of choices it allows at each point.

- A choice point is an option: a name and a finite set of behaviours.
  Substrait's own options (`overflow`, `on_division_by_zero`, `rounding`, …)
  are options with the values of their YAML. The points Substrait leaves
  unnamed (the sign of zero, NaN's order, the order of a double `SUM`, the row
  `FIRST` takes) are options of sverify's own, with the behaviours the
  profiles have.
- A profile gives, for each option, the subset of its behaviours it
  allows: `Choice := List Behaviour`, read as "any of these". The core
  allows every behaviour of every option. The reference, Substrait and each
  engine allow fewer.
- `Rel.AllowedP P` is `Rel.Allowed` with every choice taken from `P`.
  It is monotone: if each of `P`'s choices is a subset of `Q`'s, every result
  `P` allows `Q` allows. So `Allowed_P ⊆ Allowed_core` is one theorem,
  proved once, and each profile discharges its premise by `decide` on its
  table.

A plan's own option narrows the point before the profile does. Substrait
says that a consumer "must deliver" the first preference it can, and that an
omitted option leaves the consumer "free to choose any supported behavior"
([scalar functions, Options](https://substrait.io/expressions/scalar_functions/#options)).
So the core allows any preference the plan lists, or any behaviour of the
option where the plan lists none; a profile takes its first supported
preference, and refuses the plan where it supports none (as
`Parse.checkOptions` does today).

### Errors

The core, as a specification, allows raising anywhere: a profile states
where it may raise, its raise set, a constraint like any other, and `verify`'s error issues
(`Rel.mayIssues`, `analysis/Sverify/Analysis/Safety.lean`) are the reference's raise
set. A theorem that a plan cannot raise is then a theorem about one profile's
raise set, and holds on every profile whose raise set is smaller. This keeps
principle 4 (an error means "may raise", so rewrites stay refinements) and
lets DuckDB's extra raises (`MIN % -1`, `<<` of a negative number) stay
inside the core without new options. Decided ([D2](decisions.md#d2-raises-in-the-core)).

An engine runs a plan correctly when it returns an allowed result, or
raises only where the reference may raise; resource errors, such as running
out of memory, are outside this ([D16](decisions.md#d16-engine-correctness)). This is
the raise-set half of [Soundness](#soundness). Today Lean proves partial
correctness for every lowered plan, an allowed result or an error
(`Rel.duckdb_shim_sound`). For a plan proved to never raise the two agree,
and the engine raises nowhere (`Rel.duckdb_sound`,
[engine-profiles.md](engine-profiles.md#profiles-and-shims-in-lean-185-first-slice)).

### Values of an option the YAML does not list

An engine sometimes does something none of the YAML's values describe:
DuckDB gives `0` for `x >> 64`
([`duckdb-R15-shift-right`](../characterization/duckdb/facts/duckdb-R15-shift-right.json)),
where Substrait's `shift_right` has no option. Its `-∞` for `ln(0)` is the
YAML's `on_log_zero: MINUS_INFINITY`, and needs nothing new. The core needs every profile's native
behaviour, so an option's behaviours are the YAML's values and the
behaviours an engine fact records, each extra one tagged with its fact.
Decided ([D3](decisions.md#d3-behaviours-outside-the-yaml)).

## Options per function

### The option catalogue

The catalogue of options, with each one's behaviours in the core, in
Substrait, in the reference and in DuckDB, is the user-facing
[Options](reference-semantics.md#options) table of reference-semantics.md.
The ids there are the names the tables below use.

### Function groups

Functions with the same options share a row. Every function of an area is in
exactly one group; wave 3's tables give each function its group
(`core/Sverify/Core/Functions.lean`, one row per constructor, so `add` has a row
in `int.arith`, `fp.arith`, `dec.arith` and `time.arith`).

| Area | Group | Functions | Options |
|---|---|---|---|
| core | `int.arith` | `add`, `subtract`, `multiply`, `negate` on integers | `overflow` |
| core | `int.pow` | `power` on integers | `overflow` (`ERROR` only), `on_domain_error` (none occurs) |
| core | `int.abs` | `abs` on integers | `overflow` |
| core | `int.div` | `divide` on integers | `overflow` (`MIN / -1`), `on_division_by_zero`, `on_domain_error` (none occurs) |
| core | `int.mod` | `modulus` on integers | `overflow`, `on_division_by_zero`, `division_type`, `min_mod_neg_one` |
| core | `int.bit` | `bitwise_and`, `bitwise_or`, `bitwise_xor` | none |
| core | `int.shift` | `bitwise_shift_left`, `bitwise_shift_right` | `shift_range` |
| core | `dec.arith` | `add`, `subtract`, `multiply`, `negate`, `abs` on decimals | `overflow` (`ERROR` only), `decimal_rescale` |
| core | `dec.div` | `divide`, `modulus` on decimals, `sverify_decimal_div` | `divide` and `modulus` refused in every profile until [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27); `sverify_decimal_div`, a decimal by an integer (how a windowed `AVG` is written), is read ([reference-semantics.md](reference-semantics.md#decimals)) |
| core | `fp.arith` | `add`, `subtract`, `multiply` on doubles | `rounding`, `nan_creation`, `zero_sign` |
| core | `fp.neg` | `negate` on doubles (exact) | `zero_sign` |
| core | `fp.div` | `divide` on doubles | `rounding`, `on_division_by_zero`, `on_domain_error`, `nan_creation`, `zero_sign` |
| core | `fp.mod` | `modulus` on doubles, `sverify_fmod` (C's `fmod`, exact) | `division_type`, `on_division_by_zero` (`ERROR`, `NULL`), `nan_creation`, `zero_sign` |
| core | `fp.elem` | `sqrt`, `exp`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `power` | `rounding`, `on_domain_error`, `pow_one_inf` (`power`) |
| core | `fp.log` | `ln`, `log10`, `log2`, `logb` | `rounding`, `on_domain_error`, `on_log_zero` |
| core | `fp.round` | `round` | `rounding`, `round_zero_sign`, `float_to_int` (where `round` returns a `BIGINT`) |
| core | `fp.floor` | `floor`, `ceil` | `round_zero_sign` (`ceil` of a negative value above `-1`), `float_to_int` (where they return a `BIGINT`) |
| core | `cmp` | `equal`, `lt`, `greatest`, `least`, `nanvl`, `is_null`, `not`, `and`, `or` | `nan_equality`, `nan_order`, `zero_sign` (doubles only) |
| core | `sverify` | `sverify_raise`, `sverify_is_number` (a shim's guards, #185), `sverify_pair` (a two-argument aggregate's argument) | none |
| strings | `str.sub` | `substring` | `negative_start`, `substring_range` |
| strings | `str.match` | `like`, `strpos`, `starts_with`, `ends_with`, `replace` | `case_sensitivity` |
| strings | `str.case` | `upper`, `lower` | `char_set` |
| strings | `str.concat` | `str_concat` | `null_handling` |
| strings | `str.plain` | `character_length`, `reverse`, `ascii`, `repeat`, `btrim`, `ltrim`, `rtrim`, `levenshtein` | none (the size hypothesis bounds their results) |
| strings | `str.opaque` | `regexp_match`, `regexp_extract`, `regexp_replace`, `ilike`, `md5`, `sha256` | none; `case_sensitivity` fixed by the function |
| temporal | `time.arith` | date and timestamp `±` intervals, `date_diff`, `date_bin` | `date_range`, `time_interval_months` |
| temporal | `time.part` | `date_part`, `date_trunc`, `strftime` | none (their range is the reference's timestamps, D32) |
| nested | `list.order` | `list_lt`, `ORDER BY`/`MIN`/`MAX` of lists | `list_null_order`, and the element's options |
| nested | `list.plain` | `array_length`, `cardinality`, `any_match`, `all_match`, `transform`, `filter` | none |
| aggregates | `agg.isum` | `sum`, `avg` of integers and decimals | `overflow`, `avg_int_result` |
| aggregates | `agg.fsum` | `sum`, `avg` of doubles | `sum_order`, `rounding`, `nan_creation` |
| aggregates | `agg.var` | `variance`, `std_dev` | `distribution` (Substrait's: the sample's or the population's), `rounding`, `stat_algo`, `stat_degenerate` |
| aggregates | `agg.stat` | `covar_samp`, `covar_pop`, `corr` | `stat_algo`, `stat_degenerate` |
| aggregates | `agg.order` | `min`, `max`, `quantile_disc`, `median` of non-numbers | `nan_order`, `zero_sign`, `list_null_order` |
| aggregates | `agg.quant` | `quantile_cont`, `median` | `quantile_interp`, `nan_order` |
| aggregates | `agg.pick` | `first`, `last`, `arg_min`, `arg_max`, `mode` | `tie_pick` |
| aggregates | `agg.seq` | `string_agg`, `array_agg` | `tie_order` |
| aggregates | `agg.plain` | `count`, `bit_and`, `bit_or`, `bit_xor` | none (`count`'s `overflow` is out of reach by the size hypothesis) |
| windows | `win.rank` | `row_number`, `rank`, `dense_rank`, `percent_rank`, `cume_dist` | `tie_order` |
| windows | `win.ntile` | `ntile` | `ntile_spread`, `tie_order` |
| windows | `win.value` | `lag`, `lead`, `first_value`, `last_value`, `nth_value` | `tie_order` |
| windows | `win.agg` | aggregates over a frame | the aggregate's group, with `sum_order` over the frame |
| casts | `cast.num` | double or decimal to integer, integer to a narrower one | `float_to_int`, `cast_failure` |
| casts | `cast.dec` | to and from decimals, integer to double | `decimal_rescale`, `cast_failure` |
| relations | `rel.sort` | `orderBy`, a window's order | `null_order`, `clustered`, `tie_order` |
| relations | `rel.fetch` | `fetch` | `tie_order` (the rows taken of a tie) |
| relations | `rel.keys` | `aggregate`'s keys, `distinct`, joins, `UNION DISTINCT`, `INTERSECT`, `EXCEPT` | `nan_equality`, `zero_sign` |

`fp32` adds no group: once
[#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417) lands,
each `fp.*` group covers both formats, and the options apply per format.

## How a profile states its constraints

Three tables, the first two shared by every profile:

1. Options (`core/Sverify/Core/Options.lean`, new): one row per option of the
   catalogue above.
2. Functions (wave 3: the per-area tables of
   [#269](https://github.com/AlexanderNenninger/substrait-lean/issues/269) in
   Lean, the scalar table in Python): one row per function, with its group.
3. Choices (one per profile): one row per option, or per group and option
   where a profile chooses differently by group.

### The options table

```lean
/-- A behaviour, by its Substrait name (`ERROR`, `TIE_TO_EVEN`) or sverify's
(`ONE_ZERO`). -/
abbrev Behaviour := String

structure OptionSpec where
  id : String                     -- `overflow`, `zero_sign`, …
  substrait : Option String       -- its name in the YAML; `none` for sverify's own
  core : List Behaviour           -- what the core allows
  yaml : List Behaviour           -- what the YAML lists (`[]` for sverify's own)
  extra : List (Behaviour × String)  -- behaviours outside the YAML, with their fact id

def options : List OptionSpec := [
  { id := "overflow", substrait := some "overflow",
    core := ["ERROR", "SILENT", "SATURATE"], yaml := ["ERROR", "SILENT", "SATURATE"],
    extra := [] },
  { id := "zero_sign", substrait := none, core := ["IEEE", "ONE_ZERO"], yaml := [],
    extra := [("IEEE", "duckdb-R14")] },
  … ]
```

Checks by `decide` (`core/Sverify/Core/Options.lean`) reject a repeated id or
behaviour, and a `yaml` value or `extra` behaviour outside `core`; the rest of
`core` is sverify's own (`ONE_ZERO`, `DROP_BITS`). `tests/test_functions.py`
checks that every fact id names a file of `characterization/*/facts/`.

### The functions table

Wave 3's rows gain one column, the group:

```lean
structure FnRow where
  name : String          -- Substrait's name
  anchor : Nat           -- `Write.lean`'s anchor, in the area's range
  group : String         -- `fp.div`, …
  -- wave 3's own columns: the constructor for Parse, Write and Pretty, …

def groups : List (String × List String) := [
  ("int.arith", ["overflow"]),
  ("fp.div", ["rounding", "on_division_by_zero", "nan_creation", "zero_sign"]),
  … ]
```

A function's options are its group's. `optionAccepts` (`Parse.lean`) is a
lookup: `optionGroup` gives a call's group (by its name, and whether it is of
doubles), an option is known for the call when its group lists it, and
accepted when the reference's choice meets the plan's preferences
(`ProfileTable.accepts`). A `#guard` checks the lookup against the
hand-written function it replaced, on every name and option.

### The choices table

```lean
inductive Choice where
  /-- Any of these behaviours. -/
  | oneOf (bs : List Behaviour)
  /-- The plan's first preference among these; any of them where it states none. -/
  | asked (bs : List Behaviour) (dflt : List Behaviour)
  /-- The option never applies to the group's inputs (`on_domain_error` of
  integers): every preference is accepted. -/
  | any

structure ProfileTable where
  name : String
  /-- Per option, or per group and option (the more specific row wins). -/
  choices : List (Option String × String × Choice)
  /-- Where each behaviour comes from: the engine natively, a shim (with its
  cost), or nowhere (refused). Engines only. -/
  realize : List (String × Behaviour × Realization)
  facts : List (String × List String)   -- option ↦ fact ids

def Profile.reference.table : ProfileTable := {
  name := "reference",
  choices := [
    (none, "overflow", .asked ["ERROR", "SILENT", "SATURATE"] ["ERROR"]),
    (some "int.abs", "overflow", .asked ["ERROR"] ["ERROR"]),
    (none, "zero_sign", .oneOf ["ONE_ZERO"]),
    (none, "sum_order", .oneOf ["ANY"]),
    … ] }
```

`.asked supported dflt` reads Substrait's rule: the first of the plan's
preferences in `supported`, or `dflt` where the plan states none; a plan
whose preferences miss `supported` is refused. The core's table is
`.asked (core) (core)` for every option, so the core follows every
preference and leaves an omitted option open.

`Profile` reads the table through one function, `Profile.allows : String →
String → List Behaviour → List Behaviour` (group, option, the plan's
preferences ↦ allowed behaviours), and the semantics of each option, a
function from a behaviour to the outcomes (`Overflow.apply`, `ZeroSign.canon`,
…), interprets it. The existing fields stay: `un`, `bin`, `statAlgo` and
`sumAlgo` become derived from the table (`statAlgo := some .welfordChan` is
the choice `stat_algo: WELFORD_CHAN`), so `Profile.duckdb`'s
`duckBin`/`duckUn` keep their proofs and gain a row each that names them.
Settings enter as a parameter: `Profile.duckdb.table (s : DuckDBSettings)`
picks `on_division_by_zero` from `s.errorOnDivZero` and `nan_creation`,
`on_domain_error` from `s.ieeeOps`.

The refinement premise is one decidable check: for every group, option and
preference list, `P.allows ⊆ core.allows`. Since preference lists are
unbounded, the check runs per `Choice` (`oneOf bs ⊆ core`,
`asked s d`: `s ⊆ core ∧ d ⊆ core`), which implies it.

### In Python

The Python side has the same three tables, as frozen dataclasses next to
wave 3's function table (`python/src/sverify/_functions.py`):

```python
@dataclass(frozen=True)
class Option:
    id: str
    substrait: str | None
    core: tuple[str, ...]
    extra: tuple[tuple[str, str], ...] = ()   # (behaviour, fact id)

@dataclass(frozen=True)
class Fn:
    name: str
    anchor: int
    area: str
    group: str
    # wave 3's columns: the writer's kinds, SQL, the lift's node type, …

CHOICES: dict[str, dict[tuple[str | None, str], Choice]]  # profile ↦ (group, option) ↦ choice
REALIZE: dict[str, dict[tuple[str, str], Realization]]    # engine ↦ (option, behaviour) ↦ native | shim | refused
```

Python reads them for four things:

- the SQL lift writes each option the source dialect fixes, from the
  dialect's profile (today the lift writes them by hand per rule);
- `_support.py` refuses a plan whose behaviour an engine `REALIZE`s as
  `refused`, with the fact as the reason (it now refuses by function name);
- the writers pick the shim `REALIZE` names;
- `sverify_dev` generates the realizability table of #444's second comment
  from `CHOICES["reference"]` and `REALIZE`.

The Lean tables are the source. A test dumps them as JSON (an `#eval` in
`Examples.lean`, or `substrait-check --tables`) and compares them with the
Python tables row by row, as `tests/test_black_box.py` does for the black
boxes. `substrait-check --options` prints the options, the groups' options
and the reference's choices. Decided ([D1](decisions.md#d1-where-the-tables-live)).

### The realizability table

For every option, the behaviour the reference chooses, and every engine:
native, a shim with its cost (an extra `CASE`, a cast to `HUGEINT`, a second
pass), or refused. An error-side option needs no shim for a plan proved
to never raise ([What strictness buys](#what-strictness-buys)), so its cell
names the guard, used only where a precondition is checked on the data.
Generated from `REALIZE` and the facts, published in
`docs/`, and checked in CI: a change to the reference that makes an engine
refuse, or need a shim of a higher cost class, fails a test until the
table's expected output is updated. This is principle 3 ("every engine can
follow it with reasonable effort") as a check. The cells are the shims;
their count per engine is how [few shims](#what-a-proof-under-the-reference-guarantees)
is measured.

The table is [realizability.md](realizability.md): `obligations reference E`
for DuckDB and Polars (`SubstraitLean/Obligations.lean`), printed by
`substrait-check --realizability` and rendered by
`python -m sverify_dev.realizability --write`. The `Generated files`
workflow rewrites it on `main` after every merge, so feature branches leave
it alone. Lean checks that no row differs from the reference without a
shim, an observation or a precondition (`obligations_consistent`), that
every shim has a cost class and evidence (`obligations_shims_evidenced`),
and that every theorem a row names exists. Each row is computed from the
reference's choices and tools and the engine's choices and observation
rows; behaviours of an open option that are one of the reference's though
named apart (`SEQUENTIAL` is one order of `ANY`) are listed in
`behaviourRefines`.

### Classes of an engine's functions

Each row of the realizability table, for an engine, a function and its
argument types, falls in one class against the reference
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)),
best first. #568 named them `refines[D]`, `refines[D]` up to an observation
and `approx[D, ε]`; [D22](decisions.md#d22-four-route-classes-and-tolerances-are-observations)
renamed them `exact`, `observed` and `observed`:

1. `exact` on `D`: on every input in the domain `D`, every outcome the engine
   gives is one the reference allows. For a proved plan, `D` is the
   reference's non-raising domain, so error-side differences cost nothing
   ([What strictness buys](#what-strictness-buys)).
2. `observed` up to an observation `o`: `o ∘ f_engine = o ∘ f_reference` on
   `D`, with `o` a map that forgets the difference: the multiset of rows,
   permutations within ties, `canon` (one zero, one NaN), the error's kind,
   a decimal's value without its scale, the UTC instant, parsing back a
   string, NFC. Equality up to `o` is transitive and composes. The contract
   must not tell `o`-equal results apart, and each operation downstream
   must keep `o`; where one does not, a shim makes the value canonical first
   ([#568's comment](https://github.com/AlexanderNenninger/substrait-lean/issues/568#issuecomment-6632368108)).
3. `observed` within a tolerance `ε`: on `D`, within `ε` of an outcome the reference allows.
   Floating point only; `ε` propagates through arithmetic, and a comparison
   whose threshold lies within `ε` of its argument's range drops the call
   site to a shim
   ([#568's comment](https://github.com/AlexanderNenninger/substrait-lean/issues/568#issuecomment-6632287946)).
   Lean proves `ε` for a double `SUM` and `AVG` under every summation order
   the engines use, and its propagation through `+`, `−`, `×` and `/`;
   elementary functions stay tested
   ([float-bounds.md](float-bounds.md#the-engines-orders-and-epsilon-444)).
4. Each of the three after a shim: a written flag, a rewrite or a guard,
   mostly for the reference's value choices.
5. Refused.

A plan takes the worst class over its call sites.

Each row also carries the engine's run-to-run variation next to its class:
the observation up to which two runs of the engine on the same input
agree. The class answers correctness against the postcondition's
observation, the variation answers reproducibility against a consumer's
([D20](decisions.md#d20-two-observations-per-output)). Polars's streaming float `SUM`,
for example, is `observed` within `ε` and also varies in its last bits between
runs.

### Where the evidence lives

- The characterization checklist, [characterization/areas.json](../characterization/areas.json):
  the areas and items a characterization covers, each item an option of
  the catalogue or a point the options do not reach.
- The facts, `characterization/<engine>/facts/`, each naming the items it
  settles in its `options` field; `python -m sverify_dev.facts --coverage
  <engine>` lists, per item, the facts that settle it or `missing`.
- The upstream ledger, [upstream/README.md](../upstream/README.md): spec gaps
  as `ST-<n>` entries with `kind: "spec-gap"` (D3), engine bugs under their
  project's prefix.

## The value domain

The core needs every value any profile gives, so each must be at least as
fine as Substrait's. `Value` has a constructor per kind ([D29](decisions.md#d29-a-value-has-its-kind)):
`null | bool | int | float | date | ts | tod | dec | str | list | struct`.
A double is a `float` code, `-0.0` and the negative NaN among them
(`core/Sverify/Core/FloatFormat.lean`), which the reference profile reads with
one zero and one NaN through `canon`; a decimal is its scale and unscaled
integer.

| Value | What the core needs | Blocks #444? |
|---|---|---|
| `-0.0` | a code apart from `+0.0`, ordered by `zero_sign` | Yes, before step 2: `Profile.substrait` gives `1.0 / -0.0 = -∞`. Step 1 can land with it. |
| NaN's sign | NaN codes with a sign, ordered by `nan_order` | Yes, before step 2 (Substrait), and for DuckDB's `signbit` ([duckdb-signbit](../characterization/duckdb/facts/duckdb-signbit.json)). |
| NaN payloads | not observed by any function sverify models | No: a NaN is one of two codes, by its sign ([D4](decisions.md#d4-nan-payloads)). |
| `fp32` | the `FloatFormat` layer ([PR #558](https://github.com/AlexanderNenninger/substrait-lean/pull/558), #417 stage 1) carries the codes per format; the second instance is #417 stage 3 | No: the core is generic over `FloatFormat` from the start, and every profile refuses `fp32` arithmetic until stage 3 (fact [duckdb-R12](../characterization/duckdb/facts/duckdb-R12.json)). |
| Timestamp precisions | `precisionTimestamp` at 0, 3, 6 and 9, a count of units ([#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323)) | No: the value is an `int` already; the precision is the type's. Refused in every profile until #323. |
| Decimal division | `DECIMAL(p, s)` is its unscaled `int`; division needs the YAML's result type and a rounding ([#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27)) | No: refused in every profile until #27. |
| Strings | code points, as now; the size hypothesis (fewer than 2³² characters) is a premise of every theorem, `Profile.substrait`'s included | No. Decided (#336). |
| Unsigned integers | Substrait's `unsigned_integers.yaml` | No: outside the core until a profile needs them. |

The extra codes go into the `FloatFormat` layer: one more code for `-0.0`
and one for the negative NaN, outside the range of the existing ones, so
that the reference's codes keep their values and their order lemmas.
`FloatFormat.canon` maps `-0.0` to `+0.0` and the negative NaN to the NaN,
and `ONE_ZERO`/`ONE_NAN` are "apply `canon` to every input and output",
which is what DuckDB's written plan does (`Dialect.canon`). The reference
never meets the new codes, so its proofs do not change. The SQL order of the
full set (`-0.0` right below `+0.0`, the negative NaN by `nan_order`) is the
`IEEE` behaviour of `zero_sign` and `nan_order`.

Step 1b put them there (`core/Sverify/Core/FloatFormat.lean`): `negNan` is the
code negation of NaN and `negZero` the even code below it, `key` orders the
full set, `canon_idem` and `canon_mono` prove `canon` idempotent and
order-preserving, and `core/Sverify/Core/Float.lean` proves that each operation
on doubles commutes with `canon` on the reference's codes (`lift₂_canon`,
`roundTo_canon`, `fmod_canon`, `finite_canon`; `canon_ofFloat` for results
built from a native double). Code negation is the one exception: it sends
NaN to `negNan`, and `canon_neg` shows that `canon` of it is the parser's
negation, which keeps NaN.

## The Substrait profile

`Profile.substrait.table` (`SubstraitLean/SubstraitProfile.lean`) states
Substrait's semantics as the extension YAMLs at `substrait-extensions`
0.106.0 and Substrait's docs give it, in the format of the reference's and
the engines' tables:

- an option of the YAMLs is `.asked yaml yaml`: the plan's first preference
  among the values the YAML lists for that function, any of them where the
  plan states none, since the YAMLs give no defaults and an omitted option
  leaves the consumer free to choose. Per-function lists narrow it by group:
  integer `divide` truncates, double `divide` has four `on_division_by_zero`
  values, `round` ten roundings;
- sverify's own options take what Substrait fixes: IEEE 754's two zeros and
  signed NaNs (`zero_sign`, `nan_kind`), IEEE's `==` and unordered NaN in
  `cmp`, `sum`'s NULL for no values, `avg` of integers truncating to the
  declared type, positions counting characters from 1, `MIN % -1` as `0`;
- every other option is the core's (`loose` over its behaviours), each such
  gap an `ST` entry ([D3](decisions.md#d3-behaviours-outside-the-yaml)): `nan_creation`
  ([ST-5](../upstream/bugs/ST-5.json)), `float_overflow`
  ([ST-9](../upstream/bugs/ST-9.json)), the statistical aggregates
  ([ST-3](../upstream/bugs/ST-3.json)), NaN in grouping and sorts
  ([ST-4](../upstream/bugs/ST-4.json)), casts
  ([ST-6](../upstream/bugs/ST-6.json));
- a sort key's `UNSPECIFIED` direction leaves the NULL placement open, and
  `CLUSTERED` is the adjacency relation
  ([D6](decisions.md#d6-sort-keys-without-a-null-order)).

Lean proves `Profile.substrait_le_core` by `decide` on the table, so
`Rel.allowed_substrait_core` gives `Allowed_substrait ⊆ Allowed_core` by
`Rel.AllowedP_mono`. Two `decide` checks show the two siblings apart: neither
table is within the other.

`verify(semantics="substrait")` checks an Ibis transformation under it.
`substrait-check --contract` with `"profile": "substrait"` proves the
contract under the reference, then runs the transfer check on the
transformation (`transferB`, sound by `Rel.transfer_of_transferB`): the proof
holds under Substrait when Substrait allows only behaviours the reference
allows at every option the plan meets. Otherwise no postcondition is proved
there, and the report's `transfer` names each option with both profiles'
behaviours. An integer `+` already fails it, since Substrait leaves
`overflow` open where the reference raises. No route runs a plan on
Substrait: the profile is one to check under.

Where the two differ, generated from the tables by `substrait-check
--profile-diff` (`python -m sverify_dev.profile_diff --write`;
`tests/test_substrait_profile.py` fails while it is stale). "Any preference"
is a choice that accepts every value the plan states.

<!-- substrait-diff:start -->
| Option | Group | Substrait | Reference | Reference's tool |
|---|---|---|---|---|
| `overflow` | all others | `ERROR`, `SILENT`, `SATURATE` | `ERROR` | raise |
| `overflow` | `int.arith` | `ERROR`, `SILENT`, `SATURATE` | `ERROR`, `SILENT`, `SATURATE`; `ERROR` by default | raise |
| `on_division_by_zero` | all others | `ERROR`, `NULL` | `ERROR`, `NULL`; `ERROR` by default | raise |
| `on_division_by_zero` | `fp.div` | `IEEE`, `LIMIT`, `NULL`, `ERROR` | `ERROR`, `IEEE`, `NULL`, `LIMIT`; `ERROR` by default | raise |
| `on_division_by_zero` | `fp.mod` | `IEEE`, `LIMIT`, `NULL`, `ERROR` | `ERROR`, `NULL`; `ERROR` by default | raise |
| `division_type` | all others | `TRUNCATE`, `FLOOR` | `TRUNCATE` | choose |
| `division_type` | `int.div` | `TRUNCATE` | `TRUNCATE`, `FLOOR`; `TRUNCATE` by default | choose |
| `division_type` | `fp.mod` | `TRUNCATE`, `FLOOR` | `TRUNCATE` | choose |
| `division_type` | `int.mod` | `TRUNCATE`, `FLOOR` | `TRUNCATE`, `FLOOR`; `TRUNCATE` by default | choose |
| `shift_range` | all others | `ERROR`, `ZERO`, `DROP_BITS` | `DROP_BITS` | raise |
| `decimal_rescale` | all others | `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN`, `TRUNCATE` | `TIE_AWAY_FROM_ZERO` | choose |
| `rounding` | all others | `TIE_TO_EVEN`, `TIE_AWAY_FROM_ZERO`, `TRUNCATE`, `CEILING`, `FLOOR` | `TIE_TO_EVEN` | choose |
| `rounding` | `fp.round` | `TIE_TO_EVEN`, `TIE_AWAY_FROM_ZERO`, `TRUNCATE`, `CEILING`, `FLOOR`, `AWAY_FROM_ZERO`, `TIE_DOWN`, `TIE_UP`, `TIE_TOWARDS_ZERO`, `TIE_TO_ODD` | `TIE_AWAY_FROM_ZERO` | choose |
| `on_domain_error` | all others | `NAN`, `ERROR` | `ERROR` | raise |
| `on_domain_error` | `fp.div` | `NAN`, `NULL`, `ERROR` | `ERROR` | raise |
| `on_domain_error` | `fp.log` | `NAN`, `NULL`, `ERROR` | `ERROR` | raise |
| `on_domain_error` | `int.div` | `NULL`, `ERROR` | any preference; `NAN`, `NULL`, `ERROR` by default | raise |
| `on_log_zero` | all others | `NAN`, `ERROR`, `MINUS_INFINITY` | `ERROR` | raise |
| `nan_creation` | all others | `NAN`, `ERROR` | `ERROR` | raise |
| `zero_sign` | all others | `IEEE` | `ONE_ZERO` | choose |
| `round_zero_sign` | all others | `ANY`, `IEEE`, `POSITIVE` | `ANY` | leave open |
| `pow_one_inf` | all others | `ONE`, `NAN` | `ONE` | choose |
| `nan_equality` | all others | `NAN_IS_NAN`, `NAN_IS_NOT_NAN` | `NAN_IS_NAN` | choose |
| `nan_equality` | `cmp` | `NAN_IS_NOT_NAN` | `NAN_IS_NAN` | choose |
| `nan_order` | all others | `GREATEST`, `UNORDERED`, `IGNORED` | `GREATEST` | choose |
| `nan_order` | `cmp` | `UNORDERED` | `GREATEST` | choose |
| `nan_kind` | all others | `IEEE` | `ONE_NAN` | choose |
| `negative_start` | all others | `WRAP_FROM_END`, `LEFT_OF_BEGINNING`, `ERROR` | `WRAP_FROM_END`, `LEFT_OF_BEGINNING`; `WRAP_FROM_END` by default | choose |
| `substring_range` | all others | `COMPUTE` | `ERROR` | raise |
| `case_sensitivity` | all others | `CASE_SENSITIVE`, `CASE_INSENSITIVE`, `CASE_INSENSITIVE_ASCII` | `CASE_SENSITIVE` | choose |
| `char_set` | all others | `UTF8`, `ASCII_ONLY` | `UTF8` | choose |
| `null_handling` | all others | `IGNORE_NULLS`, `ACCEPT_NULLS` | `ACCEPT_NULLS` | choose |
| `date_range` | all others | `ERROR`, `COMPUTE` | `ERROR` | raise |
| `time_interval_months` | all others | `DROP_MONTHS`, `ERROR` | refused | raise |
| `list_null_order` | all others | `NULL`, `GREATEST`, `LEAST` | `NULL` | choose |
| `list_null_order` | `agg.order` | `NULL`, `GREATEST`, `LEAST` | `GREATEST` | choose |
| `sum_order` | all others | `ANY`, `SEQUENTIAL`, `PAIRWISE`, `COMPENSATED`, `SCALED_CONSTANT`, `EXACT` | `EXACT` | choose |
| `stat_algo` | all others | `GENERIC`, `WELFORD_CHAN`, `EXACT` | `EXACT` | choose |
| `window_sum_algo` | all others | `RECOMPUTE`, `TREE`, `RUNNING_ADD`, `SLIDING` | `RECOMPUTE` | choose |
| `stat_degenerate` | all others | `NULL`, `NAN`, `ERROR` | `NULL` | choose |
| `quantile_interp` | all others | `BETWEEN`, `LINEAR` | `BETWEEN` | leave open |
| `tie_pick` | all others | `ANY_ROW`, `FIRST_READ` | `ANY_ROW` | leave open |
| `null_order` | all others | `NULLS_FIRST`, `NULLS_LAST` | `NULLS_FIRST`, `NULLS_LAST`; `NULLS_LAST` by default | choose |
| `float_to_int` | all others | `TRUNCATE`, `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN` | `TRUNCATE` | choose |
| `cast_failure` | all others | `THROW_EXCEPTION`, `RETURN_NULL` | `THROW_EXCEPTION`, `RETURN_NULL`; `THROW_EXCEPTION` by default | raise |
| `distribution` | all others | `SAMPLE`, `POPULATION` | `SAMPLE`, `POPULATION`; `SAMPLE` by default | choose |
| `float_overflow` | all others | `ERROR`, `INFINITY` | `ERROR` | raise |
<!-- substrait-diff:end -->

### Substrait's test cases

Substrait keeps test cases for its extension functions in
`tests/cases/<area>/*.test` of `substrait-io/substrait`: a call, the options
it states and the expected result, an error, or anything but an error.
`python -m sverify_dev.substrait_cases` runs every case at v0.106.0, the
extensions `Profile.substrait` reads, through `substrait-check`: scalar
calls with `--outcomes` (`Expr.evalP`), aggregates and windows over a
`VALUES` with `Rel.eval`. A case that leaves an option of its YAML open runs
once per value the YAML lists, and each run states every option. The parser
accepts a preference only where the reference's behaviour is that value,
so an accepted run gives Substrait's outcome; the two profiles differ beyond
that only at sverify's own options (the table above).

A case agrees when every accepted run gives its result, is refused when
sverify accepts none (a function, an option value or a type it does not
model), and disagrees otherwise. A case that states an option or a value its
YAML does not list disagrees before it runs. The ledger
[`upstream/substrait-cases.json`](../upstream/substrait-cases.json) keeps the
totals per area, the refusals' reasons with their counts, and each
disagreement with its triage: `profile` (the two profiles differ at an
option; counted as refused), `model` (a bug of sverify's, with its issue),
`case` (a wrong test case) or `gap` (a spec gap), the last two with their
`ST` entry. `tests/test_substrait_cases.py` fails on a disagreement the
ledger does not triage and on a stale ledger.

Of the 1,317 cases, 631 agree, 625 are refused and 61 disagree. Every
disagreement is a test case at fault, and all are still on Substrait's
`main`: wrong expected values for `variance`, `std_dev`, `multiply` and
`shift_left` ([ST-13](../upstream/bugs/ST-13.json)), `logb`'s arguments in
the order opposite to its YAML ([ST-14](../upstream/bugs/ST-14.json)), and
options no YAML defines (`lookaround`, `spaces_only`, `full_unicode`) or
values their option does not list ([ST-15](../upstream/bugs/ST-15.json)).
The replay found four bugs of sverify's parser, fixed with it: `negate` of
the least integer of its width folded past the width, a list literal
argument stopped constant folding with an error, `variance` and `std_dev`
did not read the `distribution` enum argument of their current signatures,
and a date minus an interval typed as a coarse timestamp returned a date.

## Translations between profiles

A plan means something only under a profile, so the unit sverify reasons
about is the pair: a plan `r` under a profile `P`, which allows the results
`Allowed_P(r)` and may raise on the rows of its raise set `Raises_P(r)`.
Everything that moves a plan, from a source language to a profile, from the
reference to an engine, or within one profile, is one relation on these
pairs.

### Soundness

`(Q, t)` refines `(P, r)`, written `(Q, t) ⊑ (P, r)`, when on every input

- every result `Q` allows for `t` is one `P` allows for `r`:
  `Allowed_Q(t) ⊆ Allowed_P(r)`, and
- `t` under `Q` raises only where `r` under `P` may:
  `Raises_Q(t) ⊆ Raises_P(r)`.

Refinement up to an observation `o` asks the first only up to `o`: every
result `Q` allows for `t` is, up to `o`, one `P` allows for `r`
(`Rel.RefinesUpTo`, `Rel.RefinesPUpTo`, with `Relation.Equiv o` from
[ObsEquiv.lean](../core/Sverify/Core/ObsEquiv.lean)). `o = Obs.exact` is the
relation above (`Rel.Refines`); `o = {rows := .multiset}` forgets the order
of rows (`Rel.RefinesBag`, `Rel.RefinesP`), which is all an unsorted plan
gives against an `ORDER BY`.

A translation `T : P → Q` maps plans to plans or refuses them, and it is
sound when `(Q, T r) ⊑ (P, r)` for every plan `r` it does not refuse. A
theorem about `Allowed_P(r)`, the kind `verify` proves, then holds of every
result `Q` returns for `T r`, and a proof that `r` cannot raise under `P`
carries over. A refusal is always sound.

The relation covers every move sverify makes:

| Move | As refinement | Today |
|---|---|---|
| A rewrite within a profile | `(P, t) ⊑ (P, r)` up to `o` | `Rel.RefinesUpTo` ([Allowed.lean](../core/Sverify/Core/Allowed.lean)); `optimize` up to the order of rows, for plans without choices (`Rel.optimize_refines`, `Rel.refines_of_same`, `Rel.refines_of_perm`) |
| A narrower profile, the same plan | `(P, r) ⊑ (core, r)` when `P`'s choices are within the core's | step 1c's `Rel.AllowedP_mono` |
| Lowering to an engine | `(E, T_E r) ⊑ (reference, r)`: exactly for DuckDB's lowering, up to an engine row's `q` where the row is `refinesUpTo q` | `Rel.duckdb_refines` (from `Rel.duckdb_shim_allowed` and `Lowering.lowerRel_raises`), `Lowering.lower_correct`, `Rel.guardFree_allowed` |
| Lifting from a source language | `(X, s) ⊑ (P, L s)`: whatever `X` does with `s` is allowed for the lifted plan under `P` | the SQLGlot lift, trusted and tested; `LiftDuckDB`'s entries proved per rule (#242) |
| A round trip | `(Substrait, s) ⊑ (core, read s)` and back | step 2 |

A lift points the other way from a lowering: it over-approximates its source,
so that a theorem about the lifted plan covers what the source language
does. A query written in DuckDB's SQL, lifted, checked under the reference
and lowered to Polars is the chain
`(Polars, T_Polars (L s)) ⊑ (reference, L s) ⊒ (DuckDB, s)`: the proof is
about the middle, and both ends are covered by it.

### Composition

`⊑` is reflexive and transitive, because both of its parts are inclusions.
So the identity is a sound translation, and sound translations compose, as
CompCert's passes do ([Prior work](#refinement-of-programs)): if
`T : P → Q` and `U : Q → R` are sound, so is `U ∘ T : P → R`. Sverify uses
composition along one path, from the reference to an engine: a lift, the
checked plan, then the engine's translation, each step sound on its own. The
translation switch of #444 (step 5) then needs nothing new per query: the
query's proof is about `(reference, r)`, and each engine's translation is
proved once.

### Which plans run on an engine

Profiles are siblings under the core, and sverify has no translations
between them, so no shims for them either. A plan runs on the engine `E`
in one of three ways:

1. Proved under `Profile.E`: it runs natively.
2. Proved under the reference: it runs through the translation from the
   reference to `E`, whose realizability row is proved once per engine, so
   it costs a plan nothing.
3. Proved under another profile `P`, with a proof that transfers to
   `Profile.E` by the option-wise check: for every option the proof depends
   on (the option dependency report, step 3c), `E`'s choices are within
   `P`'s. By monotonicity (`Rel.AllowedP_mono`, applied per option) the
   proof then holds under `Profile.E` as it is. The check is a table lookup
   and needs no new proof.

Otherwise the checker runs again, under `Profile.E` or the reference. That is
automatic and costs checker time, and where it fails the plan is refused on
`E`. A proof under the core holds under every profile by monotonicity, but
few plans verify there ([Terminology](#terminology)). Translations are linear
in the number of engines: one per engine, from the reference.

For the second way, `Engine.contract_sound` (`SubstraitLean/EngineSound.lean`)
is the theorem: unless the translated plan raises, the rows the engine's
model computes for it (DuckDB's, Polars's, Spark's or the reference's) are a
result the reference allows (`Engine.Sound`), and the contract holds on them.
The engine's actual output rests on D16's claim (`Engine.Runs`) and the
transfer check from the engine's table to the reference's
(`Engine.contract_sound_runs`); it fails today at `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on every engine, `null_order` without a preference on Polars and Spark, and integer overflow on Polars ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900), PR 3).

### Obligations, option by option

The core is compositional: replacing a call or an operator by one that
refines it refines the plan (`Rel.AllowedP_congr`, step 1c, the profile
form of today's `Rel.evalI_mapExprs` and `Expr.Exact`). A translation that
keeps the plan's shape and changes calls and operators one at a time is then
sound when each change is, and each change is about the options of one
group. For two profiles `P` and `Q`, a group and one of its options, with
`p = P.allows` and `q = Q.allows` for the plan's preferences:

| Case | Realization | Example |
|---|---|---|
| `q ⊆ p` | native: the call as it is | `overflow`, reference to DuckDB: both `ERROR` |
| `q ⊄ p`, and a shim in `Q` gives a subset of `p` | a shim, with its cost | `zero_sign`, reference (`ONE_ZERO`) to DuckDB (`IEEE`): `Dialect.canon`; `overflow: SILENT` to DuckDB: wrap in `HUGEINT` |
| `q ⊄ p` only on inputs a precondition excludes | a precondition: proved, or listed in `Report.assumed` and checked on the data | the reference's error-side options to any engine: `nan_creation` (raise) to DuckDB (`NAN`) is sound on the inputs a plan proved to never raise reaches; `zero_sign` and `nan_kind`, Substrait (`IEEE`) to the reference: sound on inputs without `-0.0` or a negative NaN |
| none of these | refused | `ntile_spread` on DataFusion ([DF-11](../upstream/bugs/DF-11.json)); `FLOOR` modulus anywhere today |

From the reference to an engine, the third case covers every error-side
option ([What strictness buys](#what-strictness-buys)): the reference raises
there, so its raise set is the precondition, and a plan proved to never
raise discharges it. The guard that raises (`UnFn.raise`) is needed only
where the precondition is checked on the data. The second case is left for
the value choices.

`obligations P Q` lists, for every group and option, which case holds and
which shim or precondition discharges it. Sverify translates from the
reference only ([Which plans run on an engine](#which-plans-run-on-an-engine)),
so `P` is the reference wherever a shim is written; for other pairs only the
first case, `q ⊆ p`, is used, as the option-wise transfer check. It is generated from `P`'s and
`Q`'s choices rows and the shim table, so it stays current with the facts.
Two of its rows are tables this page already has:
`obligations reference E` is the [realizability table](#the-realizability-table)
for the engine `E`, and `obligations substrait reference` is step 2's diff
between Substrait and the reference.

Two limits of the per-option view:

- A shim's own calls must be native in `Q`, or be discharged in turn. The
  generator checks this; a shim that needs a refused behaviour makes its row
  refused.
- Relational options act on operators, not calls: `null_order` is
  discharged by writing the sort key's NULL placement, `tie_order` and
  `tie_pick` natively (any engine's pick is one the reference allows), or,
  under the deterministic profile, by a total order or a refusal
  ([D24](decisions.md#d24-tie-order-belongs-to-the-deterministic-profile)), and `sum_order`
  (any order in `P`, a fixed one in `Q`) is native, while the converse needs
  an ordered aggregation (`Dialect.float_sum`), at the cost of a sort.

### A worked example: NULL order

A sort key's NULL placement shows each case of the table. Take a plan with
`ORDER BY x` whose key's direction is `UNSPECIFIED`.

- Under `Profile.substrait`, `null_order` is open: `p` is both placements.
  Every engine fixes one, so `q ⊆ p`, and the plan translates to any engine
  natively, with no shim and whatever its default.
- Under the reference, `p` is `NULLS_LAST` (D8). DuckDB's default is the
  same (F2), so the key is native there. An engine whose default differs
  needs the shim: the SQL states `NULLS LAST`, which costs nothing at run
  time.
- A key that states `NULLS_FIRST` has `p = {NULLS_FIRST}` under every
  profile. On DuckDB, `q` is `NULLS_LAST` by default, so it needs the shim:
  the written SQL says `NULLS FIRST`. The writers do this for every key
  today, so DuckDB realizes every placement.
- A `CLUSTERED` key allows any order with equal keys adjacent, under the
  reference as under Substrait. An engine without clustering realizes it by
  sorting on the keys: a sorted order is clustered, at the cost of a sort.

`obligations reference duckdb` holds the last three of these, generated from
the `null_order` and `clustered` rows of the two profiles. The first is the
option-wise transfer check from `Profile.substrait` to DuckDB's profile:
`q ⊆ p`, so the proof holds there with no shim.

### Proved once, or checked per plan

Two ways to know a translation is sound:

- Prove the translator once. sverify does this per table entry: the lowering
  search (`LoweringSearch.lean`, #241) finds a template for each function and
  proves it, `Lowering.lower_correct` proves that a lowering with proved
  entries is sound, and the generated modules are checked in CI. The lift
  (`LiftDuckDB`) follows the same pattern. Composition is then a theorem
  proved once, and no plan pays for a proof at run time.
- Check each translated plan: given `r` and `T r`, prove `(Q, T r) ⊑ (P, r)`
  for that plan alone. This covers translators sverify did not write, such
  as another producer's Substrait plan of the same query, or an engine's own
  optimized plan.

Both are established ([Prior work](#translation-validation)): CompCert proves
most passes and validates register allocation per run, and Alive2 validates
LLVM per function. sverify proves translators once, entry by entry, as today,
and checks single plans only for translations it does not own
([D7](decisions.md#d7-per-plan-checks)): such a plan is checked through the lift, by
proving that `lift(write(T r))` refines `r` with the same refinement checker.
`obligations P Q` is what both need: the entries to prove, or the conditions
to check.

### What a proof under the reference guarantees

A plan proved under the reference, `requires R ⇒ ensures E`, keeps `E` on
every engine with a sound translation, along every chain of them, and for
every choice the reference leaves open (ties, order-free `FIRST`, clustered
groups). It does not carry to the core or to `Profile.substrait`, which
allow results the reference does not; a Substrait consumer gets `E` only through a
translation that shims the choices `E` needs. And refinement keeps
properties of every outcome: that a plan returns some row is not one of them.
[#444's comment on translations](https://github.com/AlexanderNenninger/substrait-lean/issues/444#issuecomment-6630983452) sets this out.

Beyond `E`, the proof has five goals:

1. No error, given the checked preconditions. Where the inferred bounds prove
   a precondition, the plan cannot raise. Where a precondition is checked on
   the data, the error moves to the input boundary: a bad batch is refused
   before anything runs, with the violated precondition as the message, and
   no refresh fails halfway.
2. No new non-finite values. A NaN or `±∞` from the inputs stays allowed, as
   `semantics="duckdb"` models them; the plan creates none the inputs did
   not hold. With #85's bounds, every floating result has a usable error
   bound. The reference raises where an operation would create a NaN, on a
   zero divisor ([No operation creates a NaN](reference-semantics.md#floating-point)),
   and where an operation on finite doubles overflows to `±∞` (`exp(1000)`,
   `1e308 * 10`, a `SUM` of large values;
   [No operation creates `±∞`](reference-semantics.md#floating-point),
   [#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)).
   Verification rules the overflow out by an inferred precondition, as a
   `SUM`'s overflow is: proved from the bounds where they do it (a `SUM` or
   `AVG` of values within `2⁴⁰⁰` over at most `2³²` rows), otherwise listed
   in `Report.assumed` and checked on the data (`Issue.infinite`,
   `Rel.noIssue_of_assumedHold`). `Rel.eval` keeps the IEEE `±∞` on the rows
   the precondition excludes, so the lift states DuckDB's result exactly.
3. A result determined up to row order. Leaving an option open is the third
   tool beside raising and choosing a value: it costs no shim, and the
   contract must not tell the open choices apart (#568's invariance under an
   observation `q`). A proof that the output is fixed up to row order makes
   reruns, incremental refreshes and idempotent sink epochs reproducible,
   and where it fails the proof names the place (a `LIMIT` without
   `ORDER BY`).
4. Explicit intent overrides strictness. Options the plan states
   (`TRY_CAST`, `NULLS FIRST`, a rounding mode, flooring division) are
   honoured at their shim cost; strictness applies to the defaults and to
   what Substrait leaves unspecified.
5. Minimal shimming is a measure the proof does not carry: the
   [realizability table](#the-realizability-table)'s shim count per engine,
   so the cost of each new choice of the reference shows.

The stricter the reference, the more preconditions a plan must prove or
check on the data. For each strict choice, the test is whether its
precondition is usually provable from the bounds or cheap to check; where
it is neither, the reference picks a value or leaves the option open.

What a plan needs from the reference is often less than all of it. The
weakest set of constraints under which the plan still verifies names the
choices its proof uses (say `nan_order = GREATEST` and
`null_order = NULLS_LAST`), and the shims an engine's translation needs for
that plan are the obligations of those options alone. A plan then pays for
the choices it uses: the option dependency report (step 3c) computes the
set, and guard elimination (#83) drops the shims the inferred bounds rule
out.

### The engines' profiles

[The Polars example](engine-profiles.md#the-polars-example), which counts the
shims for one engine, and Polars and Spark as profiles
([Polars](engine-profiles.md#polars-as-a-profile),
[Spark](engine-profiles.md#spark-as-a-profile)) are in
[engine-profiles.md](engine-profiles.md).

## The steps of #444

The steps of [#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)
have landed, and the issue keeps their record: the tables (step 0, 1a), the
signed zero and NaN codes (1b), `Rel.AllowedP` and the core table (1c), the
Substrait profile (2, [The Substrait profile](#the-substrait-profile)), the
DuckDB profile (3a), the obligations and the realizability table (3b,
[realizability.md](realizability.md)), the option dependency report and the
transfer check (3c), Substrait's test cases in CI (4,
[Substrait's test cases](#substraits-test-cases)), and one query checked
under the reference and run on DuckDB and Polars (5,
`tests/test_profiles_e2e.py`).

## Prior work

The design follows five lines of work, and departs from each where SQL
engines need it. Full references are at the end of this section.

### Loose specifications and profiles

In CASL, a specification denotes the class of all its models, kept as large
as possible to leave room for implementations [CASL, §3.1], and a refinement
is correct when every model of the refined specification is a model of the
original [MST04, §3]. The core is such a loose specification, a profile adds
constraints, and `Allowed_P ⊆ Allowed_core` is model-class inclusion. The
models here are the results of one evaluator per input, so the inclusion is
a check over finite choice tables (`decide`), with no general theorem
proving.

WebAssembly's spec is the closest precedent for profiles of one language
[Wasm, Profiles]. Its full profile holds every behaviour, a NaN result is any
element of a set the spec defines (`nans_N`), and the deterministic profile
removes the rules that allow more than one, so that every NaN an operation
creates is the positive canonical one; every profile is a subset of the full
one. The core is the full profile. The reference fixes the values Wasm's
deterministic profile fixes, NaNs among them, and leaves the order of ties
open; sverify's deterministic profile is the reference with that order
fixed as well ([D24](decisions.md#d24-tie-order-belongs-to-the-deterministic-profile)). The
reference goes further on zeros: Wasm keeps `-0` and `+0` apart, and its
`fmin(-0, +0)` is `-0`, while the reference has one zero (#89). D4's NaN
codes by sign follow Wasm's treatment of the sign as a choice; IEEE 754 does
not interpret a NaN's sign and only recommends that payloads propagate
[IEEE754, 6.3, 6.2.3].

### Refinement of programs

CompCert proves that every behaviour of the compiled program is one of the
source's (backward simulation), for sources that cannot go wrong, and that
correct passes compose [Leroy09, Defs. 2–3, Thm. 2]. `⊑` is the same
inclusion, input by input, and composes for the same reason. LLVM's
refinement allows a transformation to remove non-determinism and never to
add it [Alive2, §1], which is how a profile narrows the core.

sverify departs in what an error allows. In CompCert a source that goes wrong
constrains the target not at all, and in LLVM undefined behaviour allows any
result [Leroy09, §2.1; Alive2, §5.1]. In sverify an error means "may raise":
where `P` may raise, a translated plan may raise or return a result `P`
allows, and nothing else, and it may raise only where `P` may. This is
Alive2's check that the target has undefined behaviour only where the source
does [Alive2, §5.3], read for raises. Poison and
`undef` [Lee17, §2–4] have no counterpart: the core's open choices are sets
of defined values.

### Translation validation

Pnueli, Siegel and Singerman validate each run of a translator, so that the
translator itself can change without a new proof [PSS98], and Necula validates every pass of GCC this
way [Necula00]; Alive2 does it per function, with bounded unrolling. CompCert
mixes both: an unverified translator followed by a verified validator is a
verified translator [Leroy09, Thm. 1], and register allocation is checked
this way [Leroy09, §8.2.4]. sverify's lowering and lift searches are of this
kind at the granularity of table entries: an unproved search proposes an
entry, Lean proves it at build time, and `Lowering.lower_correct` composes the
entries. Single plans are checked only for translations sverify does not own (D7).

### Institutions

An institution comorphism translates sentences forward and models back, so
that a sentence holds of a translated model exactly when its translation
holds [GR02], and comorphisms compose; within one logic, a refinement is a
theory morphism [GB92]. A translation `T : P → Q` has this shape: plans go
forward, `Q`'s results are read back as results of `P`, and a theorem about
`Allowed_P(r)` holds of what `Q` returns for `T r`. sverify uses only the
preorder: every profile shares the core's values, so the map back is the
identity, or `canon` where `Q` keeps two zeros. A translation into a profile
with other values (DuckDB's `HUGEINT` sums) reads them back by a cast in the
written plan.

### Formal semantics of SQL

Guagliardo and Libkin give SQL's queries one semantics, with bags and
three-valued logic but without aggregation, `ORDER BY` or `LIMIT`, and test
it on 100,000 random queries against PostgreSQL and Oracle, with a variant
for each where they differ [GL17, §4]. Benzaken and Contejean mechanise SQL
with grouping and aggregates in Coq, with functions and aggregates as fixed
interpretations passed as parameters [BC19, §3.2]. HoTTSQL and its successor
U-semiring model relations as K-relations and prove rewrites, leaving
functions uninterpreted, without NULLs [HoTTSQL, §7; UDP, §6.4], and
Ricciotti and Cheney mechanise SQL with NULLs over two- and three-valued
logic [RC22].

sverify follows them in bags, three-valued logic and NULLs equal in grouping,
and in taking each function's meaning as a parameter (here, the profile).
None of them gives an engine's choice a set of outcomes, and none models
`ORDER BY` with ties, `LIMIT`, floating point, NaN or `-0.0`. Guagliardo and
Libkin's engine variants are separate semantics; here they are profiles of
one core, so translations between them can be stated. Their random
differential testing against two engines is the closest precedent for
sverify's engine facts.

Substrait's own function tests record one result per call, `<!ERROR>`, or
`<!UNDEFINED>` for any result, and run an omitted option under each of its
values ([`tests/README.md`](https://github.com/substrait-io/substrait/blob/main/tests/README.md)).
Step 4 reads `<!UNDEFINED>` as the core's whole set and an omitted option as
the option left open.

### References

- [Alive2] N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr. Alive2: Bounded Translation Validation for LLVM. PLDI 2021. [doi:10.1145/3453483.3454030](https://doi.org/10.1145/3453483.3454030)
- [BC19] V. Benzaken, É. Contejean. A Coq Mechanised Formal Semantics for Realistic SQL Queries. CPP 2019. [doi:10.1145/3293880.3294107](https://doi.org/10.1145/3293880.3294107)
- [CASL] E. Astesiano, M. Bidoit, H. Kirchner, B. Krieg-Brückner, P. D. Mosses, D. Sannella, A. Tarlecki. CASL: The Common Algebraic Specification Language. TCS 286(2), 2002. [doi:10.1016/S0304-3975(01)00368-1](https://doi.org/10.1016/S0304-3975(01)00368-1)
- [GB92] J. A. Goguen, R. M. Burstall. Institutions: Abstract Model Theory for Specification and Programming. JACM 39(1), 1992. [doi:10.1145/147508.147524](https://doi.org/10.1145/147508.147524)
- [GL17] P. Guagliardo, L. Libkin. A Formal Semantics of SQL Queries, Its Validation, and Applications. PVLDB 11(1), 2017. [doi:10.14778/3136610.3136613](https://doi.org/10.14778/3136610.3136613)
- [GR02] J. Goguen, G. Roșu. Institution Morphisms. Formal Aspects of Computing 13, 2002. [doi:10.1007/s001650200013](https://doi.org/10.1007/s001650200013)
- [HoTTSQL] S. Chu, K. Weitz, A. Cheung, D. Suciu. HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics. PLDI 2017. [doi:10.1145/3062341.3062348](https://doi.org/10.1145/3062341.3062348)
- [IEEE754] IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019. [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229). Clauses 6.3 and 6.2.3 as quoted in [C++ LWG issue 4101](https://cplusplus.github.io/LWG/issue4101) and on LLVM's forum; the standard itself was not read.
- [Lee17] J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes. Taming Undefined Behavior in LLVM. PLDI 2017. [doi:10.1145/3062341.3062343](https://doi.org/10.1145/3062341.3062343)
- [Leroy09] X. Leroy. A Formally Verified Compiler Back-end. JAR 43(4), 2009. [doi:10.1007/s10817-009-9155-4](https://doi.org/10.1007/s10817-009-9155-4)
- [MST04] T. Mossakowski, D. Sannella, A. Tarlecki. A Simple Refinement Language for CASL. WADT 2004, LNCS 3423.
- [Necula00] G. C. Necula. Translation Validation for an Optimizing Compiler. PLDI 2000. [doi:10.1145/349299.349314](https://doi.org/10.1145/349299.349314)
- [PSS98] A. Pnueli, M. Siegel, E. Singerman. Translation Validation. TACAS 1998, LNCS 1384. [doi:10.1007/BFb0054170](https://doi.org/10.1007/BFb0054170)
- [RC22] W. Ricciotti, J. Cheney. A Formalization of SQL with Nulls. JAR 66, 2022. [doi:10.1007/s10817-022-09632-4](https://doi.org/10.1007/s10817-022-09632-4)
- [UDP] S. Chu, B. Murphy, J. Roesch, A. Cheung, D. Suciu. Axiomatic Foundations and Algorithms for Deciding Semantic Equivalences of SQL Queries. PVLDB 11(11), 2018. [vldb.org](https://www.vldb.org/pvldb/vol11/p1482-chu.pdf)
- [Wasm] WebAssembly Core Specification, 3.0: [NaN propagation](https://webassembly.github.io/spec/core/exec/numerics.html#nan-propagation) and [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).

## Decisions

The decision log moved to [decisions.md](decisions.md). Each entry below links
to it, so links to an entry here still land.

- <a id="d1-where-the-tables-live"></a>[D1. Where the tables live](decisions.md#d1-where-the-tables-live)
- <a id="d2-raises-in-the-core"></a>[D2. Raises in the core](decisions.md#d2-raises-in-the-core)
- <a id="d3-behaviours-outside-the-yaml"></a>[D3. Behaviours outside the YAML](decisions.md#d3-behaviours-outside-the-yaml)
- <a id="d4-nan-payloads"></a>[D4. NaN payloads](decisions.md#d4-nan-payloads)
- <a id="d5-rounding-of-doubles-where-the-plan-omits-it"></a>[D5. Rounding of doubles where the plan omits it](decisions.md#d5-rounding-of-doubles-where-the-plan-omits-it)
- <a id="d6-sort-keys-without-a-null-order"></a>[D6. Sort keys without a NULL order](decisions.md#d6-sort-keys-without-a-null-order)
- <a id="d7-per-plan-checks"></a>[D7. Per-plan checks](decisions.md#d7-per-plan-checks)
- <a id="d8-the-references-null-order"></a>[D8. The reference's NULL order](decisions.md#d8-the-references-null-order)
- <a id="d9-one-tool-per-option"></a>[D9. One tool per option](decisions.md#d9-one-tool-per-option)
- <a id="d10-determinism"></a>[D10. Determinism](decisions.md#d10-determinism)
- <a id="d11-postconditions-name-the-equivalence"></a>[D11. Postconditions name the equivalence](decisions.md#d11-postconditions-name-the-equivalence)
- <a id="d12-contracts-and-the-observation"></a>[D12. Contracts and the observation](decisions.md#d12-contracts-and-the-observation)
- <a id="d13-choosing-the-route"></a>[D13. Choosing the route](decisions.md#d13-choosing-the-route)
- <a id="d14-engine-versions"></a>[D14. Engine versions](decisions.md#d14-engine-versions)
- <a id="d15-where-the-observations-live"></a>[D15. Where the observations live](decisions.md#d15-where-the-observations-live)
- <a id="d16-engine-correctness"></a>[D16. Engine correctness](decisions.md#d16-engine-correctness)
- <a id="d17-changing-the-reference"></a>[D17. Changing the reference](decisions.md#d17-changing-the-reference)
- <a id="d18-observations-ordered-by-refinement"></a>[D18. Observations ordered by refinement](decisions.md#d18-observations-ordered-by-refinement)
- <a id="d19-and-and-or-raise-eagerly"></a>[D19. `AND` and `OR` raise eagerly](decisions.md#d19-and-and-or-raise-eagerly)
- <a id="d20-two-observations-per-output"></a>[D20. Two observations per output](decisions.md#d20-two-observations-per-output)
- <a id="d21-tighten-the-reference-where-it-stays-practical"></a>[D21. Tighten the reference where it stays practical](decisions.md#d21-tighten-the-reference-where-it-stays-practical)
- <a id="d22-four-route-classes-and-tolerances-are-observations"></a>[D22. Four route classes, and tolerances are observations](decisions.md#d22-four-route-classes-and-tolerances-are-observations)
- <a id="d23-inferred-preconditions-are-errors-by-default"></a>[D23. Inferred preconditions are errors by default](decisions.md#d23-inferred-preconditions-are-errors-by-default)
- <a id="d24-tie-order-belongs-to-the-deterministic-profile"></a>[D24. Tie order belongs to the deterministic profile](decisions.md#d24-tie-order-belongs-to-the-deterministic-profile)
- <a id="d25-float-aggregates-are-correctly-rounded-exact-sums"></a>[D25. Float aggregates are correctly rounded exact sums](decisions.md#d25-float-aggregates-are-correctly-rounded-exact-sums)
- <a id="d26-two-equalities-for-null"></a>[D26. Two equalities for NULL](decisions.md#d26-two-equalities-for-null)
- <a id="d27-the-size-hypothesis-is-the-only-size-assumption"></a>[D27. The size hypothesis is the only size assumption](decisions.md#d27-the-size-hypothesis-is-the-only-size-assumption)
- <a id="d28-lambdas-have-lexical-scope"></a>[D28. Lambdas have lexical scope](decisions.md#d28-lambdas-have-lexical-scope)
- <a id="d29-a-value-has-its-kind"></a>[D29. A value has its kind](decisions.md#d29-a-value-has-its-kind)
- <a id="d30-statistical-aggregates-are-correctly-rounded-exact-moments"></a>[D30. Statistical aggregates are correctly rounded exact moments](decisions.md#d30-statistical-aggregates-are-correctly-rounded-exact-moments)
- <a id="d31-double-arithmetic-is-exact-rounded-once"></a>[D31. Double arithmetic is exact, rounded once](decisions.md#d31-double-arithmetic-is-exact-rounded-once)
- <a id="d32-calendar-functions-work-on-the-references-timestamps-0001-to-9999"></a>[D32. Calendar functions work on the reference's timestamps, 0001 to 9999](decisions.md#d32-calendar-functions-work-on-the-references-timestamps-0001-to-9999)
- <a id="d34-an-option-differs-from-the-reference-only-on-its-scope"></a>[D34. An option differs from the reference only on its scope](decisions.md#d34-an-option-differs-from-the-reference-only-on-its-scope)
- <a id="d35-engine-summation-orders-are-bounded-sets"></a>[D35. Engine summation orders are bounded sets](decisions.md#d35-engine-summation-orders-are-bounded-sets)
- <a id="d36-doubles-have-one-zero-and-one-nan"></a>[D36. Doubles have one zero and one NaN](decisions.md#d36-doubles-have-one-zero-and-one-nan)
- <a id="d37-no-operation-creates-a-nan"></a>[D37. No operation creates a NaN](decisions.md#d37-no-operation-creates-a-nan)
- <a id="d38-no-operation-on-finite-doubles-overflows-to-infinity"></a>[D38. No operation on finite doubles overflows to infinity](decisions.md#d38-no-operation-on-finite-doubles-overflows-to-infinity)
- <a id="d39-division-by-zero-has-an-ieee-value"></a>[D39. Division by zero has an IEEE value](decisions.md#d39-division-by-zero-has-an-ieee-value)
- <a id="d40-power1--is-cs-pow"></a>[D40. `power(±1, ±∞)` is C's `pow`](decisions.md#d40-power1--is-cs-pow)
