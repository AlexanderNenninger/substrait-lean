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
([Decisions](#decisions)). Everything else follows decisions already made on
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
  rounded once ([D31](#d31-double-arithmetic-is-exact-rounded-once)), and so
  are double sums and statistical moments
  ([D25](#d25-float-aggregates-are-correctly-rounded-exact-sums),
  [D30](#d30-statistical-aggregates-are-correctly-rounded-exact-moments)).
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
  ([D29](#d29-a-value-has-its-kind), #923).
- The reference states a value; a profile states a distance from it. Where
  engines compute a result in different ways, the reference fixes one value
  and each engine's profile bounds how far the engine may be from it: the
  correctly rounded sums and moments of
  [D25](#d25-float-aggregates-are-correctly-rounded-exact-sums) and
  [D30](#d30-statistical-aggregates-are-correctly-rounded-exact-moments),
  with each engine within the plan's bound (`Relation.Near`).
- Engines meet the reference through the `AllowedP` profile tables. A new
  engine is a profile and a facts table, with no change to `Rel.eval` or
  `Rel.Allowed` ([Translations between profiles](#translations-between-profiles)),
  and a package can add one without changing sverify
  ([engine profiles from outside](engine-profiles.md#engine-profiles-from-outside)).

## Terminology

Three kinds of semantics, each with one job.

- The core is the loosest semantics, a specification layer. It admits every
  engine's behaviour ([D3](#d3-behaviours-outside-the-yaml)), every profile
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
(`Rel.mayIssues`, `SubstraitLean/Safety.lean`) are the reference's raise
set. A theorem that a plan cannot raise is then a theorem about one profile's
raise set, and holds on every profile whose raise set is smaller. This keeps
principle 4 (an error means "may raise", so rewrites stay refinements) and
lets DuckDB's extra raises (`MIN % -1`, `<<` of a negative number) stay
inside the core without new options. Decided ([D2](#d2-raises-in-the-core)).

An engine runs a plan correctly when it returns an allowed result, or
raises only where the reference may raise; resource errors, such as running
out of memory, are outside this ([D16](#d16-engine-correctness)). This is
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
Decided ([D3](#d3-behaviours-outside-the-yaml)).

## Options per function

### The option catalogue

Each row is one option. "Core" is the set of behaviours the core allows;
"Substrait" is what the extension YAMLs at `v0.106.0` (the
`substrait-extensions` package `python/uv.lock` pins) list, none with a
default; "Reference" is `Profile.reference`'s choice; "DuckDB" is DuckDB
2.0 under its default settings, with the fact that records it. The ids in
the first column are the names the tables below use.

#### Integers and decimals

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `overflow` (`+ - ×`, negate) | `ERROR`, `SILENT`, `SATURATE` | the three | `ERROR` at the declared width; `SILENT`/`SATURATE` when the plan asks (#202, #241) | `ERROR` native; `SILENT`/`SATURATE` shimmed in `HUGEINT` ([R1](../characterization/duckdb/facts/duckdb-R1.json), [R15-int-arith](../characterization/duckdb/facts/duckdb-R15-int-arith.json)) |
| `overflow` (`abs`, `divide` at `MIN / -1`) | `ERROR`, `SILENT`, `SATURATE` | the three | `ERROR` | `ERROR` native ([R1-min](../characterization/duckdb/facts/duckdb-R1-min.json)) |
| `overflow` (`sum`, integer and decimal) | `ERROR`, `SILENT`, `SATURATE` | the three | `ERROR`, an inferred precondition checked on the data (#316, #437) | a `HUGEINT` sum, never past 64 bits; the written plan casts back and raises ([R6](../characterization/duckdb/facts/duckdb-R6.json)) |
| `on_division_by_zero` (integers) | `ERROR`, `NULL` | the two | `ERROR`; `NULL` when asked | `ERROR` native; `NULL` with `error_on_division_by_zero` off ([R2](../characterization/duckdb/facts/duckdb-R2.json), [R15-int-divide](../characterization/duckdb/facts/duckdb-R15-int-divide.json)) |
| `division_type` (`modulus`) | `TRUNCATE`, `FLOOR` | the two | `TRUNCATE`; `FLOOR` refused | `TRUNCATE` native ([R3](../characterization/duckdb/facts/duckdb-R3.json)) |
| `min_mod_neg_one` (sverify's: `MIN % -1`) | `0`, raise | not an option: the remainder, `0`, fits | `0` | raises, written out ([R15-int-modulus](../characterization/duckdb/facts/duckdb-R15-int-modulus.json)) |
| `shift_range` (sverify's: `<<`, `>>` by `< 0` or `≥ 64`, bits shifted out) | raise, `0`, drop the bits | `shift_left` drops the bits shifted out | drop the bits; raise outside `[0, 63]` | `<<` raises on a negative operand and on lost bits, `>>` gives `0` outside `[0, 63]`; both shimmed ([R15-shift-left](../characterization/duckdb/facts/duckdb-R15-shift-left.json), [R15-shift-right](../characterization/duckdb/facts/duckdb-R15-shift-right.json)) |
| `decimal_rescale` (sverify's: a result scale smaller than the exact one) | `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN`, `TRUNCATE` | `functions_arithmetic_decimal.yaml` gives result types, no rounding | `TIE_AWAY_FROM_ZERO` | `TIE_AWAY_FROM_ZERO`; its own result types, which the translation compensates ([engine-profiles.md](engine-profiles.md#decimals-27), [decimal-arith](../characterization/duckdb/facts/duckdb-decimal-arith.json)) |

#### Doubles

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `rounding` (`+ - × /`, the elementary functions, `sum`, `avg`, `variance`, `std_dev`) | the five of the YAML | `TIE_TO_EVEN`, `TIE_AWAY_FROM_ZERO`, `TRUNCATE`, `CEILING`, `FLOOR` | `TIE_TO_EVEN`: the exact result rounded once for `+ - × /` (D31) and the aggregates (D25, D30), native `Float` for the elementary functions | `TIE_TO_EVEN` (native IEEE; no fact records it) |
| `rounding` (`round`) | the ten of the YAML | ten modes | `TIE_AWAY_FROM_ZERO` (#335) | `TIE_AWAY_FROM_ZERO` ([R15-round](../characterization/duckdb/facts/duckdb-R15-round.json), [R15-round-digits](../characterization/duckdb/facts/duckdb-R15-round-digits.json)) |
| `on_division_by_zero` (doubles) | `IEEE`, `LIMIT`, `NULL`, `ERROR` | the four | `ERROR`; the others when asked (#204) | `IEEE` under `ieee_floating_point_ops`, `ERROR` with it off ([R5](../characterization/duckdb/facts/duckdb-R5.json)) |
| `on_domain_error` (`sqrt`, `asin`, `acos`, `atanh`, `acosh`, logs, `atan2`, `divide`) | `NAN`, `NULL`, `ERROR` | `NAN`, `ERROR` (logs and integer `divide` add `NULL`) | `ERROR` (#215) | `NAN` ([R15-math-domain](../characterization/duckdb/facts/duckdb-R15-math-domain.json)); `atan2(0, 0)` is `0` ([R15-atan2](../characterization/duckdb/facts/duckdb-R15-atan2.json)) |
| `on_log_zero` | `NAN`, `ERROR`, `MINUS_INFINITY` | the three | `ERROR` | `MINUS_INFINITY` (R15-math-domain) |
| `nan_creation` (sverify's: `∞ − ∞`, `0 · ∞`, `∞ / ∞`, `fmod(±∞, y)`, a `SUM` of `+∞` and `−∞`) | `NAN`, raise | IEEE: NaN | raise (#257) | `NAN` ([R15-double-arith](../characterization/duckdb/facts/duckdb-R15-double-arith.json), [R15-double-modulus](../characterization/duckdb/facts/duckdb-R15-double-modulus.json), [nonfinite-aggregates](../characterization/duckdb/facts/duckdb-nonfinite-aggregates.json)) |
| `zero_sign` (sverify's) | `IEEE` (two zeros), `ONE_ZERO` | IEEE; grouping and order of `-0.0` unspecified | `ONE_ZERO` (#89, an override) | `IEEE` in arithmetic (`1.0 / -0.0 = -∞`) and kept through a sort, where `-0.0` and `0.0` are peers; the written plan canonicalises (`Dialect.canon`, [R14](../characterization/duckdb/facts/duckdb-R14.json)) |
| `nan_equality` (sverify's for `=`, grouping, `DISTINCT`, joins; Substrait's for `index_in`) | `NAN_IS_NAN`, `NAN_IS_NOT_NAN` | IEEE `=` (NaN unequal); `index_in` takes the option | `NAN_IS_NAN` (#89, an override) | `NAN_IS_NAN`, either sign ([nan-equality](../characterization/duckdb/facts/duckdb-nan-equality.json)) |
| `nan_order` (sverify's: sort, `MIN`, `MAX`, `<`) | `GREATEST`, `UNORDERED` | IEEE comparisons (`NaN < x` false) | `GREATEST`, above `+∞` | `GREATEST` ([arg-min-nulls](../characterization/duckdb/facts/duckdb-arg-min-nulls.json), [quantile-disc](../characterization/duckdb/facts/duckdb-quantile-disc.json)) |
| `nan_kind` (sverify's: a NaN's sign and payload) | `IEEE`, `ONE_NAN` | IEEE | `ONE_NAN` | the sign survives (`signbit(-'nan')` is TRUE, [signbit](../characterization/duckdb/facts/duckdb-signbit.json)) |

#### Strings, dates and lists

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `negative_start` (`substring`) | `WRAP_FROM_END`, `LEFT_OF_BEGINNING`, `ERROR` | the three | `WRAP_FROM_END` (#209) | `WRAP_FROM_END` native ([R13](../characterization/duckdb/facts/duckdb-R13.json)) |
| `substring_range` (sverify's: an offset outside `[-2³², 2³²)`) | raise, compute | no limit | raise (#336) | raises ([substring-range](../characterization/duckdb/facts/duckdb-substring-range.json)) |
| `case_sensitivity` (`like`, `contains`, `starts_with`, `ends_with`, `strpos`, regexes) | the three of the YAML | `CASE_SENSITIVE`, `CASE_INSENSITIVE`, `CASE_INSENSITIVE_ASCII` | `CASE_SENSITIVE` | `CASE_SENSITIVE` (no fact) |
| `char_set` (`upper`, `lower`) | `UTF8`, `ASCII_ONLY` | the two | `UTF8`, a black box (Rust's `str::to_uppercase`) | `UTF8` with simple one-to-one mappings (`ß` → `ẞ`); the written plan raises on non-ASCII text ([case-mapping](../characterization/duckdb/facts/duckdb-case-mapping.json), [ST-10](../upstream/bugs/ST-10.json)) |
| `null_handling` (`concat`) | `IGNORE_NULLS`, `ACCEPT_NULLS` | the two | `ACCEPT_NULLS`; the other refused | `ACCEPT_NULLS` for `\|\|`; `concat` skips NULLs ([null-concat](../characterization/duckdb/facts/duckdb-null-concat.json)) |
| `date_range` (sverify's: date arithmetic past 0001-01-01 … 9999-12-31) | raise, compute | no limit | raise (#251) | wider dates, to 5881580 AD; the written plan guards ([date-range](../characterization/duckdb/facts/duckdb-date-range.json)) |
| `time_interval_months` (sverify's: `TIME ± INTERVAL` with months) | drop the months, raise | not specified | refused | drops them ([time-plus-interval](../characterization/duckdb/facts/duckdb-time-plus-interval.json)) |
| `list_null_order` (sverify's: a NULL element deciding `<` of lists) | `NULL`, `GREATEST`, `LEAST` | `lt` of lists not defined | `NULL` in `<`, `GREATEST` in `ORDER BY` (#207) | `GREATEST` in both; shimmed ([R11](../characterization/duckdb/facts/duckdb-R11.json)) |

#### Aggregates, windows and relations

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `sum_order` (sverify's: `SUM`, `AVG` of doubles) | any order and grouping (`FloatSums`) | not specified | any order and grouping, within #85's bound | sequential, partial states merged by addition ([sum-double](../characterization/duckdb/facts/duckdb-sum-double.json), [avg-double](../characterization/duckdb/facts/duckdb-avg-double.json)) |
| `stat_algo` (sverify's: `VAR_*`, `STDDEV_*`, `COVAR_*`, `CORR`) | `EXACT`: the exact moments rounded once (D30) | not specified | the generic properties before D30 (#85); `EXACT` since D30 | Welford with Chan's merge ([var-stddev](../characterization/duckdb/facts/duckdb-var-stddev.json), [covar](../characterization/duckdb/facts/duckdb-covar.json), [corr](../characterization/duckdb/facts/duckdb-corr.json)); `VAR_POP` of one NaN is `0` ([one-value](../characterization/duckdb/facts/duckdb-var-pop-one-value.json), [DD-3](../upstream/bugs/DD-3.json)), shimmed by the writer's NaN guard (`Stat.nanGuard_varStat`) |
| `stat_degenerate` (sverify's: `CORR` of one pair or a constant side; a statistical aggregate of `±∞`) | `NULL`, `NAN`, raise | not specified | `NULL` for `CORR`; raise for `±∞` | `NAN` for both (duckdb-corr, nonfinite-aggregates) |
| `avg_int_result` (sverify's: `avg` of integers) | the declared output type: `fp64` or `i64` truncated | `avg` of `i64` returns `i64` | follows the declared type (#209) | `DOUBLE` natively, the exact sum divided in `double` or `long double` ([avg-int](../characterization/duckdb/facts/duckdb-avg-int.json)); sverify's SQL writes the `HUGEINT` sum `//` the count for `i64` ([R6](../characterization/duckdb/facts/duckdb-R6.json)) |
| `quantile_interp` (sverify's: `QUANTILE_CONT` between neighbours) | any double between them | `quantile` has `rounding` | any double between them (`contAllowed`) | `lo·(1−d) + hi·d`, may round past; clamped ([quantile-cont-interpolation](../characterization/duckdb/facts/duckdb-quantile-cont-interpolation.json)) |
| `tie_pick` (sverify's: `FIRST`, `LAST`, `ARG_MIN`, `ARG_MAX`, `any_value`, `MODE`, ranks over ties) | any row of the tie | `any_value` "selects an arbitrary value" | any row; each measure may take its own | the row it read first, which depends on parallelism ([mode-ties](../characterization/duckdb/facts/duckdb-mode-ties.json), arg-min-nulls) |
| `tie_order` (sverify's: `STRING_AGG`, `collect`, a sort, a window's order) | any order of the ties | not specified | any order | not stable (mode-ties) |
| `null_order` (a sort key) | `NULLS_FIRST`, `NULLS_LAST` | stated by the key's direction; `UNSPECIFIED` leaves it open | as the key states; `NULLS_LAST` for `UNSPECIFIED` ([D8](#d8-the-references-null-order)) | `NULLS_LAST` by default ([F2](../characterization/duckdb/facts/duckdb-F2.json)); either when the SQL states it |
| `clustered` (a sort key's `CLUSTERED` direction) | equal keys adjacent, the groups in any order | `SORT_DIRECTION_CLUSTERED` | the same relation | an `ORDER BY` on the keys, which clusters them ([clustered](../characterization/duckdb/facts/duckdb-clustered.json)) |
| `ntile_spread` (sverify's) | the SQL standard's, spread out | not specified | the SQL standard's | the SQL standard's ([ntile](../characterization/duckdb/facts/duckdb-ntile.json); DataFusion spreads, [DF-11](../upstream/bugs/DF-11.json)) |
| `float_to_int` (casts) | `TRUNCATE`, `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN` | not specified | `TRUNCATE` (#209) | `TIE_TO_EVEN` from `FLOAT`/`DOUBLE`, `TIE_AWAY_FROM_ZERO` from `DECIMAL`; shimmed with `trunc` ([R9](../characterization/duckdb/facts/duckdb-R9.json)) |
| `cast_failure` | `THROW_EXCEPTION`, `RETURN_NULL` | the cast's `failureBehavior`; `UNSPECIFIED` exists | `THROW_EXCEPTION` for `UNSPECIFIED` | both native ([R8](../characterization/duckdb/facts/duckdb-R8.json)) |

Opaque functions need no option: the black boxes (#325), the regexes and the
digests have one meaning each, the function itself, and every profile shares
it. The conversions between integers, decimals and doubles stay opaque
constants with proved properties (`core/Sverify/Core/Conversions.lean`), the same
in every profile.

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
| core | `fp.elem` | `sqrt`, `exp`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `power` | `rounding`, `on_domain_error` |
| core | `fp.log` | `ln`, `log10`, `log2`, `logb` | `rounding`, `on_domain_error`, `on_log_zero` |
| core | `fp.round` | `round` | `rounding` |
| core | `fp.floor` | `floor`, `ceil` | none |
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
and the reference's choices. Decided ([D1](#d1-where-the-tables-live)).

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
and `approx[D, ε]`; [D22](#d22-four-route-classes-and-tolerances-are-observations)
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
([D20](#d20-two-observations-per-output)). Polars's streaming float `SUM`,
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
fine as Substrait's. `Value` has a constructor per kind ([D29](#d29-a-value-has-its-kind)):
`null | bool | int | float | date | ts | tod | dec | str | list | struct`.
A double is a `float` code, `-0.0` and the negative NaN among them
(`core/Sverify/Core/FloatFormat.lean`), which the reference profile reads with
one zero and one NaN through `canon`; a decimal is its scale and unscaled
integer.

| Value | What the core needs | Blocks #444? |
|---|---|---|
| `-0.0` | a code apart from `+0.0`, ordered by `zero_sign` | Yes, before step 2: `Profile.substrait` gives `1.0 / -0.0 = -∞`. Step 1 can land with it. |
| NaN's sign | NaN codes with a sign, ordered by `nan_order` | Yes, before step 2 (Substrait), and for DuckDB's `signbit` ([duckdb-signbit](../characterization/duckdb/facts/duckdb-signbit.json)). |
| NaN payloads | not observed by any function sverify models | No: a NaN is one of two codes, by its sign ([D4](#d4-nan-payloads)). |
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
  gap an `ST` entry ([D3](#d3-behaviours-outside-the-yaml)): `nan_creation`
  ([ST-5](../upstream/bugs/ST-5.json)), `float_overflow`
  ([ST-9](../upstream/bugs/ST-9.json)), the statistical aggregates
  ([ST-3](../upstream/bugs/ST-3.json)), NaN in grouping and sorts
  ([ST-4](../upstream/bugs/ST-4.json)), casts
  ([ST-6](../upstream/bugs/ST-6.json));
- a sort key's `UNSPECIFIED` direction leaves the NULL placement open, and
  `CLUSTERED` is the adjacency relation
  ([D6](#d6-sort-keys-without-a-null-order)).

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
  ([D24](#d24-tie-order-belongs-to-the-deterministic-profile)), and `sum_order`
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
([D7](#d7-per-plan-checks)): such a plan is checked through the lift, by
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
fixed as well ([D24](#d24-tie-order-belongs-to-the-deterministic-profile)). The
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

Decided on [#562](https://github.com/AlexanderNenninger/substrait-lean/pull/562):
D6 as the first draft's alternative, the others as it recommended.
D9 and the decisions after it were made after #568's classes and #577's translation policy.

### D1. Where the tables live

Lean is the source; Python mirrors it, and a test compares the two, as
`tests/test_black_box.py` does for the black boxes. Lean proves the
refinement by `decide` on its own table, so the proof depends on no parser
and no generated module.

### D2. Raises in the core

The core allows raising everywhere, as the reference's correctness does
today, and each profile states its raise set. It keeps principle 4 and
admits each engine's extra raises (`MIN % -1`, `<<` of a negative number)
without new options.

### D3. Behaviours outside the YAML

An option's core set is the YAML's values and the behaviours the engine
facts record, each extra one tagged with its fact. Every engine profile then
refines the core by construction, and the facts say why each extra is there.

Each such gap, where Substrait could state the behaviour (an option, an
option's value, a default) and does not, is also an entry of the upstream
ledger with `kind: "spec-gap"` ([upstream/README.md](../upstream/README.md)).
This design pass found seven, each checked against Substrait's `main` at
`a4d8e00`:

| Entry | The gap | Options here |
|---|---|---|
| [ST-1](../upstream/bugs/ST-1.json) | a shift by a count outside the width, bits shifted out | `shift_range` |
| [ST-2](../upstream/bugs/ST-2.json) | whether `atan2(0, 0)` is a domain error | `on_domain_error` |
| [ST-3](../upstream/bugs/ST-3.json) | `corr`, `variance`, `std_dev` of one pair, a constant side, or non-finite values | `stat_degenerate` |
| [ST-4](../upstream/bugs/ST-4.json) | NaN and `-0.0` in equality, grouping and sorting | `nan_equality`, `nan_order`, `zero_sign`, `nan_kind` |
| [ST-5](../upstream/bugs/ST-5.json) | `inf - inf` and `0 * inf` in `add`, `subtract`, `multiply` | `nan_creation` |
| [ST-6](../upstream/bugs/ST-6.json) | how a cast to an integer rounds; `FAILURE_BEHAVIOR_UNSPECIFIED` | `float_to_int`, `cast_failure` |
| [ST-7](../upstream/bugs/ST-7.json) | what `SORT_DIRECTION_UNSPECIFIED` means | `null_order` (D6) |
| [ST-9](../upstream/bugs/ST-9.json) | a result of finite doubles beyond the largest double: `±inf` or an error | double overflow to `±∞` (#575) |
| [ST-10](../upstream/bugs/ST-10.json) | `upper`, `lower` with `char_set: UTF8`: Unicode's simple or full case mapping | `char_set` |
| [ST-11](../upstream/bugs/ST-11.json) | integer `power` with a negative exponent | none: the reference raises (`Issue.negExponent`), D2 |
| [ST-16](../upstream/bugs/ST-16.json) | a logarithm of zero that is NULL (Spark's), which `on_log_zero` cannot state | `on_log_zero` |

`CLUSTERED` needs no entry: Substrait's `relations/basics.md` defines it.

### D4. NaN payloads

A NaN is one of two codes, by its sign. No function sverify models reads a
payload, and `signbit` reads the sign
([duckdb-signbit](../characterization/duckdb/facts/duckdb-signbit.json)).
WebAssembly treats a NaN's sign as a choice too, and IEEE 754 only
recommends that payloads propagate ([Prior work](#loose-specifications-and-profiles)).

### D5. Rounding of doubles where the plan omits it

The core leaves the YAML's five modes open, and the reference and every
engine profile fix `TIE_TO_EVEN`. This is what Substrait says, and #85's
error bounds become theorems of the profiles that fix the mode.

### D6. Sort keys without a NULL order

The core reads a key's `UNSPECIFIED` direction as `null_order` open, and
`CLUSTERED` as an order relation of its own: rows with equal keys adjacent,
the groups in any order. `Profile.substrait` accepts both, and the reference
and each engine profile fix the NULL order (DuckDB: `NULLS_LAST`,
[F2](../characterization/duckdb/facts/duckdb-F2.json)). Substrait's sort
directions include both, so a faithful profile has to read them. The parser
keeps refusing them until step 1c lands the choice point and the relation.

Amended (2026-11-07): step 1c landed, and the parser reads both in a sort
relation's keys: an `UNSPECIFIED` or missing direction leaves the NULL order
open, which the reference fixes as NULLs last (D8), and `CLUSTERED` is its
own order relation. A window's or a measure's key must state its direction
(`parseSortKey`).

### D7. Per-plan checks

Translators are proved once, entry by entry, as the lowering and the lift are
today, and single plans are checked only for translations sverify does not
own (another producer's plan, an engine's own SQL). No plan pays for a proof
at run time, and the generated tables already carry the proofs.

### D8. The reference's NULL order

Where a key's direction is `UNSPECIFIED`, the reference puts NULLs last in
both directions: DuckDB's default ([F2](../characterization/duckdb/facts/duckdb-F2.json))
and the default of the model's `SortKey` for hand-built values.

### D9. One tool per option

Each option gets one of three tools in the reference ([D21](#d21-tighten-the-reference-where-it-stays-practical)): raise, choose a value,
or leave it open. One table, a row per option, records the tool, the
precondition it creates, and the shim count per engine. The reference raises
only where that precondition is usually provable from the bounds or cheap to
check on the data; otherwise it chooses a value or leaves the option open.
Each strict choice creates a precondition for every plan that meets it, so
the table makes that cost visible next to the shims it saves
([What a proof under the reference guarantees](#what-a-proof-under-the-reference-guarantees)).

### D10. Determinism

Whether a plan's result is determined up to row order is reported by
default, and required where the output's consumer states it needs it:
incremental refreshes and idempotent sink epochs. Those consumers state
their own observation, `q_det`, separate from the postcondition's
([D20](#d20-two-observations-per-output)); elsewhere the report names the
open choice.

### D11. Postconditions name the equivalence

Each output can carry a postcondition that names the equivalence its
consumer expects: rows as a multiset (the default) or as a sequence; floats
within the plan's proved bound `ε` (`floats="plan"`, the default, #689),
exact, or within a stated tolerance, absolute, relative or in ulps, which
`verify` checks against `ε` on each engine; timestamps up to a precision;
strings up to NFC. Verification then
means that every engine result the route allows is equivalent, under the
stated relation, to a result the reference allows. A tolerance means "proved
within the stated tolerance", with #568's propagation of `ε` checking that
the tolerance holds; it is no verdict of its own. The user states what they
need, so the classes of [Classes of an engine's functions](#classes-of-an-engines-functions)
become one question: does the route meet the stated relation.

### D12. Contracts and the observation

The same postconditions settle whether a contract can tell `q`-equal
results apart. The user states the observation `q`, and each other
`ensures` is either checked on the canonical representative (`q`'s
canonical map: sort the rows, `canon` the floats, truncate, normalise) or
falls in a syntactic class invariant under `q` (uniqueness, references,
bounds, aggregates for the multiset). Otherwise the checker reports which
`ensures` depends on what `q` ignores.

### D13. Choosing the route

`verify` and `run` choose the route by default: native under the engine's
profile, then translated from the reference (`translated`), then by the option-wise transfer check
([Which plans run on an engine](#which-plans-run-on-an-engine)). The result
names the route taken. `semantics=` and an explicit route override the
choice. The default keeps a plan that verifies somewhere running without the
user knowing the profiles; the override keeps the choice inspectable.

Amended (2026-11-07): a fourth route, `recheck`, added in
[#586](https://github.com/AlexanderNenninger/substrait-lean/pull/586), comes
after the transfer check: the checker proves the contract again under the
engine's profile (`python/src/sverify/routes.py`).

Each route ends in `Engine.contract_sound` (#900): the contract holds on the
rows the engine's model computes for the translated plan, unless it raises.
The engine's actual output rests on `Engine.Runs` and the transfer check
(`Engine.contract_sound_runs`); it fails today at `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on every engine, `null_order` without a preference on Polars and Spark, and integer overflow on Polars ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900), PR 3).

### D14. Engine versions

An engine profile is tied to the engine's versions: it records the version,
or range, its facts were probed at. A run on another version warns, and a
run on another major version is refused until the probes are re-run. A new
version that changes a fact gets a new fact with `supersedes` (the `engine-fact`
skill) and a new row in the profile. Facts hold for the version they
were probed at, and the profile is only as good as its facts.

### D15. Where the observations live

The choices table holds, next to each choice, its class, its observation
`q` and its shim: each (profile, group, option) row reads choice, class,
`q`, shim, so an engine's realizability row comes from one table. This
extends step 1a's `ProfileTable` (#578, `core/Sverify/Core/Options.lean`): a
column for the class and `q`, one for the run-to-run variation
([D20](#d20-two-observations-per-output)) and one for the shim, filled for
engines in step 3a, and read by step 1c.

### D16. Engine correctness

An engine runs a plan correctly when it returns a result the reference
allows, or raises only where the reference may raise. Resource errors, such
as running out of memory, are excluded. The guarantee of no error
([What a proof under the reference guarantees](#what-a-proof-under-the-reference-guarantees))
needs this stricter definition: under partial correctness, an engine could
raise anywhere and still be correct. Partial correctness is what
`Rel.duckdb_shim_sound` proves today for every lowered plan; for a plan
proved to never raise the two agree (`Rel.duckdb_sound`).

Amended (2026-11-08): `Engine.contract_sound` (`SubstraitLean/EngineSound.lean`,
[#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)) proves
a proved contract on the rows each engine's model computes for the
translated plan, unless it raises, through each engine's `Engine.Sound`. That the engine's actual
result is one its table allows stays trusted, as `Engine.Runs`, resting on the
tested rows `Engine.Refines` lists ([What is trusted](proofs.md#what-is-trusted)).

### D17. Changing the reference

While sverify is on 0.x, the reference changes where the design needs it. A
change to the reference ships in a minor version bump, with a
`changelog.d/` fragment that says what changed. Bumping the minor version
costs little, and the fragment tells users which proofs may change.

### D18. Observations ordered by refinement

An observation `q'` refines `q` when `q'` observes everything `q` observes:
`q` factors through `q'` (`q = f ∘ q'` for some `f`), or equivalently
`ker q' ⊆ ker q`. Equality up to `q'` then implies equality up to `q`, so
the finer guarantee refines the coarser one, as `Allowed_P' ⊆ Allowed_P`
does for profiles. The identity is the finest observation, a constant the
coarsest. In Lean, equality up to `q` is `Relation.Equiv q`
(`core/Sverify/Core/ObsEquiv.lean`), and `Relation.Equiv_mono` proves that
`Obs.le q' q` gives it: equality up to `q'` implies equality up to `q`. Five
consequences:

1. The check. An engine function equal to the reference's up to `q_E`
   meets a postcondition that asks for `q_post` ([D11](#d11-postconditions-name-the-equivalence))
   exactly when `q_E` refines `q_post`. Otherwise a canonicalising shim
   makes the function's `q` finer, or the call is refused.
2. Components. `q` is a product of components (rows, floats, zeros and
   NaNs, timestamps, strings, errors), each a short chain from exact to
   coarse. Refinement is componentwise, so it is a partial order: rows as a
   multiset and strings up to case folding are incomparable.
3. Through a plan. Each operation keeps a component or coarsens it (a
   `LIMIT` without `ORDER BY` coarsens the multiset of rows), and the plan's
   output `q` must refine the postcondition's.
4. Tolerances join the floats chain: a tolerance `ε' ≤ ε` refines `ε`, with
   exact equality at the top.
5. The finest `q` is computable. The valid observations of a function, those
   with `q ∘ f_E = q ∘ f_reference`, are closed under meet (if two
   observations each agree on both functions, the pair of them does), so
   within the library of components there is one finest valid `q`. Sverify
   finds it per component by trying candidates from fine to coarse: probes
   give counterexamples that rule candidates out cheaply, and the finest
   candidate left is confirmed by a Lean proof against the engine's
   modelled behaviour (the search-and-prove machinery of the lowering
   search, `SubstraitLean/LoweringSearch.lean`), or by fuzzing where the
   engine is not modelled.

This makes D11 and D12 one comparison: the route's `q`, carried through the
plan, against the `q` the postcondition names. The finest valid `q` is the
`q` column of the choices table ([D15](#d15-where-the-observations-live)).

### D19. `AND` and `OR` raise eagerly

An error in either operand of `AND` or `OR` may raise, whatever the other
operand's value (#604). `p AND q` is not a guard for `q`: in
`x <> 0 AND 10 // x > 1`, the division may run on the rows where `x = 0`.
The reference has always evaluated both operands (`Expr.issues` of `.bin`,
`SubstraitLean/Safety.lean`); D19 states it as a decision.

- It is what the engines do. DuckDB evaluates `AND` and `OR` as values,
  both operands first
  (fact `duckdb-exec-short-circuit`, #602),
  and Polars evaluates every operand and every `when`/`then` branch
  (fact `polars-exec-when-eager`, #603).
  An eager reference needs no shim on either.
- It is strict. A plan that relies on the short-circuit is not proved; the
  report says the operation sits inside an `AND` or `OR` and suggests the
  fix: guard the operation itself with a `CASE` whose value is not
  boolean, `(CASE WHEN x <> 0 THEN 10 // x END) > 1`, or state the guard
  as a precondition. A boolean `CASE` is evaluated whole, as `AND` and `OR`
  are, since an optimizer may rewrite it into them (`Parse.eagerly`).
- A non-boolean `CASE` stays lazy: DuckDB's is, and the Polars translation
  guards each branch's inputs where Polars computes every branch.

A filter above a join is analysed on the cross product of the join's loose
inputs (`Rel.loose`), so DuckDB pushing a raising `WHERE` into one side of an
inner or left join
(fact `duckdb-exec-filter-pushdown`, #602)
evaluates it on rows the analysis covers. The one exception is a join whose
other side is empty: `Rel.HasIssue` then has no pairs, while DuckDB still
evaluates the pushed filter on the side's rows. `Rel.mayIssues` reports
the error anyway, since it describes each side's columns by that side's own
bounds; `Rel.HasIssue` does not model the case yet.

DuckDB 2.0.0 also evaluates a `CASE`'s constant `WHEN` conditions when it
plans the query, with the evaluator that raises:
`SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END FROM t` raises on
an empty `t`, and on a `t` whose rows all take the first branch (probed;
a constant `THEN` or `ELSE` that raises, `ELSE 1 // 0`, and a constant
`WHERE 1 // 0 = 1` on an empty table do not). A constant subexpression of a
condition that raises therefore raises whatever the data. The reference's
`CASE` evaluates a condition only on the rows that reach it, so a plan with
such a constant was proved and raised on DuckDB
([#609](https://github.com/AlexanderNenninger/substrait-lean/issues/609)).
Under D21 the reference now counts every constant subexpression that raises
as raising for the whole plan, whatever the data and whichever branch a row
takes (`Rel.constIssues` in `SubstraitLean/Safety.lean`): stricter than
DuckDB, which leaves a constant `ELSE` or `WHERE` alone, and constants that
raise are rare in real queries. No precondition rules one out; the report
names the constant.


### D20. Two observations per output

Each output has two observations, checked independently.

- `q_post`, for correctness, is stated by the postcondition
  (`sv.equivalent`, [D11](#d11-postconditions-name-the-equivalence)), by
  default the multiset of rows with doubles within the plan's `ε` and other
  values exact. Every engine result must
  equal, up to `q_post`, some result the reference allows. The check is
  D18's: the class `q` of each engine row must refine `q_post`.
- `q_det`, for reproducibility, is stated by whoever consumes the output.
  An idempotent sink or an incremental refresh declares its own: a sink
  that overwrites partitions may tolerate `ε`, one that compares checksums
  needs exact bits. A plain run declares none, so determinism is only
  reported ([D10](#d10-determinism)). The check: the engine's run-to-run
  variation, carried through the plan as D18 carries `q`, must refine
  `q_det`.

The two are independent, and `q_det` is often the finer one. Polars's
streaming float `SUM` varies in the last bits between runs, and grouped
float sums vary between runs on both of Polars's engines (the
characterization pipeline's probes), so such a plan passes a sink whose
`q_det` allows `ε` and fails one that needs exact bits, with the same
`q_post`. A `LIMIT` without `ORDER BY` can be correct under a multiset
`q_post` and still fail every `q_det`, since which rows it keeps can change
between runs.


### D21. Tighten the reference where it stays practical

Sverify tightens the reference when that costs little in practicality. Where
an engine differs from the reference on an edge case, the reference raises
there, and the engine needs no shim, as long as the precondition that
excludes the edge case rarely bites real queries: it is proved from the
bounds or checked on the data by a guard. A guard costs a check where the
precondition is not proved; a shim costs a rewrite on every run. D9's table
records the tool for each option. This is how D9 chooses between raising and
choosing a value.

Example: `power(-∞, y)` for a non-integer `y` raises in the reference.
IEEE 754 gives `+∞`, and Polars's `** 0.5` gives NaN through `sqrt`, so
Polars needs a guard for such plans and no shim.

A second example: a constant subexpression that raises (`1 // 0 = 1`)
counts as raising for the whole plan (#609, under D19), since DuckDB may
evaluate it when it plans the query.

### D22. Four route classes, and tolerances are observations

A route's class is one of four: `exact` (every result the engine gives is one
the reference allows), `observed` (equal to such a result under an
observation the postcondition states), `shim` (either of those after the
translation's shim) and `refused`. The classes `refines`, `refines` up to an
observation and `approx` of [Classes of an engine's functions](#classes-of-an-engines-functions)
map to `exact`, `observed` and `observed`. User-facing docs say
"observation", or "observation model" in prose, and never `q`.

Why: a tolerance is an observation of doubles. `sv.within` is already a
component of `sv.equivalent` (`floats=sv.within(...)`), ordered by
refinement with the other components (D18, item 4). Tolerances differ from
the other observations only in how they compose, by adding their `ε`, and
the checker's propagation of `ε` through a plan handles that. A separate
`approx` class told the user nothing the observation did not.

### D23. Inferred preconditions are errors by default

A precondition sverify infers to rule out a runtime error (`total // qty`
needs `qty != 0`, `amount * 2` needs `amount < 2**62`) is a checking error by
default: `verify` reports the plan as not proved and names the precondition,
where it came from, and the fixes, which are to declare it in `requires` or
to rewrite the plan so no row needs it (filter those rows first, or a `CASE`).
`on_inferred=` chooses: `"error"` (the default), `"warn"` (assumed, checked
on the data before each run, with a warning), `"ignore"` (assumed and
checked, as before #655) or `"off"` (nothing inferred or assumed: a `SUM`
that may overflow is an error too; `infer=False` before 0.6, #690).

Why: an assumed precondition is checked on each batch, and a batch that
breaks one is refused before the run (#604). An inferred precondition is
therefore a run-time error the user never asked for: a job that refuses
data because of a bound nobody wrote down. Declaring it puts the decision
with the user, and the declared form documents it.

`SUM`s assumed to fit 64 bits and operations on doubles assumed to stay
finite (`Report.assumed`) are not inferred preconditions: they keep their
checks on the data.

### D24. Tie order belongs to the deterministic profile

The reference leaves `tie_order` and `tie_pick` open. Rows that tie in an
`ORDER BY` or in a window's order come in any order, a `FETCH` takes the
first rows of any order the plan allows, and `FIRST`, `LAST`,
`ARG_MIN`/`ARG_MAX`, `STRING_AGG`, `collect` and `MODE` take the rows that
tie in their own order in any order. `Rel.OrderAllowed`
(`core/Sverify/Core/OrderAllowed.lean`) holds the results of every such order, and a
contract holds on all of them: `contract_sound_all` for postconditions,
`Rel.keys_sound_all` for keys. An engine's own pick is one of these orders,
so it runs natively.

The deterministic profile is the reference with one order fixed: a stable
sort (`List.mergeSort`) and rows in list order, as `Rel.eval` computes them
(`Rel.eval_orderAllowed`). A consumer that needs a rerun to give the same
rows asks for it, through `run(reproducible=sv.equivalent())` or a sink's
`reproducible=` ([D10](#d10-determinism),
[D20](#d20-two-observations-per-output)). Engines read tables in an order of
their own, so no shim reproduces list order on them. The deterministic
profile needs a plan whose order is total, by a tie-break key or a
uniqueness precondition (`Rel.windowsTotal`, `Rel.fetchesTotal`), and
refuses a plan without one. The refusal names each place where ties stay
open (`str(report)`, with the keys that would close them in `Report.ties`).

An order-sensitive operator reads one sorted enumeration of its input, and
its meaning is the set over all of them (`Lin` and `Sem`,
`SubstraitLean/Seam.lean`, #928). Below an unordered operator, as with a
`FETCH` without a total `ORDER BY` under a join, the order is forgotten and
the result is a set of multisets (`Rel.Bags`): this is where the tie order's
nondeterminism lives. `verify` and `run` allow such a plan, and the proofs
hold for every member; `refresh` commits one member and refuses it unless
the plan has one (`Rel.bags_iff_perm_eval`, `Rel.bags_fetch_two`).

Why: `Rel.eval`'s one order leaked into four places
([#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
Theorems about `FETCH`, ties and windows held for that order only. The
catalogue and the oracles compared each engine with it, and reported
legitimate picks as `tie_order` differences. Shims imitated
`List.mergeSort` on engines, and Polars refused or shimmed picks it could
run natively.

### D25. Float aggregates are correctly rounded exact sums

In the reference, a `SUM`, `AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`
of doubles is the correctly rounded value of the exact sum or moments. Every
finite double is an integer multiple of 2⁻¹⁰⁷⁴, so the sum of the values is
an exact dyadic rational; the result is the double nearest to it, ties to
even (`floatSumCR`, `core/Sverify/Core/FloatExact.lean`), and `AVG` is the exact
sum divided by the count, rounded once (`floatAvgCR`). NaN and infinities
follow IEEE 754: a NaN, or `+∞` with `-∞`, gives NaN, and one kind of
infinity gives it. The value is a function of the multiset of values, so it
is one value and order-free (`floatSumCR_perm`).

Engines add in an order of their own: DuckDB in the order values reach each
thread's state (`duckdb-sum-double`), Polars pairwise in blocks of 128
(`polars-sum-float`), Spark per partition (`spark-sum-double`). Each refines the reference up to the
plan's bound, the distance of any order of additions from the exact sum
(`StdModel.epsilon_sum` in [`float-bounds/`](float-bounds.md)) plus half an
ulp of the final rounding (`epsilon_sum_cr`). Their `sum_order` rows stay
`approxWithin "plan"`, so a double `SUM` or `AVG` on an engine is
`observed (tolerance)`, as it was. Their `agg.fsum` `rounding` rows are
`approxWithin "plan"` too, proved by the same theorem (#929): its standard
model holds of every rounding to nearest, whatever the tie rule, so the
engine's rounded additions stay within the plan's bound.

Three consequences:

- `sum_order` and `stat_algo` are no longer choices of the reference. They
  stay choices of the engines, and the reference's row is `EXACT`.
- `Rel.detPlan` is true of float aggregates, so `contract_sound_all` covers
  every result the reference allows for them.

  Amended (2026-11-07, #1017): this holds of closed plans (`Rel.closedB`); a
  plan with open measures (`Measure.openB`) goes through
  `contract_sound_allowed` and `Rel.FloatOpenSafe`.
- A tolerance is a metric: bounds add along a pipeline
  (`Near ε₁ a b → Near ε₂ b c → Near (ε₁ + ε₂) a c`), and no tolerance passes
  through a filter, group key or sort on a double column.

Why: the reference added doubles one by one in list order (`floatSum`) and
allowed every order and grouping (`FloatSums`). The engines' results were
then the reference's only in DuckDB, which emulated Lean's order with
`list_reduce`; Spark and Snowflake refused double sums for want of a row
order; five facts about `floatSum` were axioms. The correctly rounded sum
turns them into theorems, lets every engine run `SUM` and `AVG` natively,
and gives incremental maintenance an exact state with no drift. A
postcondition at a rounding boundary can move by an ulp, which `sv.approx`
absorbs. The epic is
[#919](https://github.com/AlexanderNenninger/substrait-lean/issues/919).
Precedents: Müller et al. ("Reproducible Floating-Point Aggregation in
RDBMSs", ICDE 2018, [arXiv:1802.09883](https://arxiv.org/abs/1802.09883)) make `SUM` order-free in a database; Neal's
superaccumulator ([arXiv:1505.05571](https://arxiv.org/abs/1505.05571))
computes the correctly rounded sum at less than twice the cost of a naive
one.

Note ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)):
window aggregates of doubles take the same per-measure profile choice as
grouped aggregates; the reference is unchanged. An engine's window sum is
within the plan's bound where its window algorithm sums the frame's own
values (`window_sum_algo`: each frame anew, a tree, or a running sum).

### D26. Two equalities for NULL

In a predicate (`WHERE`, a join's `ON`, `IN`, a `CASE` condition)
`NULL = NULL` is unknown, so a NULL never matches, never equals and never
compares: three-valued logic, `and3`/`or3`, `UnFn.apply .not` and `BinFn.apply .eq` in
`core/Sverify/Core/Expr.lean`. In `GROUP BY`, `DISTINCT`, `UNION` (distinct),
`EXCEPT`, `INTERSECT`, a window's `PARTITION BY` and `IS NOT DISTINCT FROM`,
all NULLs are one value: syntactic equality, `Value.decEq` in
`core/Sverify/Core/Value.lean`, as `dedup` and `groupKey` use it. A key
(`sv.unique`, `KeyOn`) uses the second, so two rows with NULL in a key column
collide, which is stricter than SQL's `UNIQUE` (`Keys.lean`'s header). The
anti part of a left join and a semi or anti join use the first.

Nothing in the core changes. The decision names what it does, so that an
encoding of difference or provenance
([#905](https://github.com/AlexanderNenninger/substrait-lean/issues/905))
keeps the two apart.

### D27. The size hypothesis is the only size assumption

`Rel.Small` (`SubstraitLean/Safety.lean`): every string has fewer than 2³²
characters, every relation a window reads fewer than 2⁶² rows, and every
relation an aggregate reads fewer than 2⁶³. It is a hypothesis of every
soundness theorem over windows and aggregates, never an axiom, and no other
size bound is assumed anywhere. [reference-semantics.md](reference-semantics.md)'s
"Overrides" table states it. A new theorem that needs another bound adds it
to `Rel.Small`, beside the others.

### D28. Lambdas have lexical scope

A lambda in a higher-order call (`Expr.hof`: `any_match`, `all_match`,
`transform`, `filter`) sees the enclosing row, as DuckDB's lambdas can read
outer columns (`list_transform(l, x -> x + col)`). Its body is evaluated on
`x :: row`: field 0 is the parameter and the row's column `i` is field
`i + 1`; a nested lambda's body reads its own parameter as 0, the outer
parameter as 1 and the row from 2 (de Bruijn order). #922's draft
numbered the row first; with the parameter first a body keeps its meaning
when columns are appended to the row, so `Expr.eval_append`, the lemma
behind every pushdown, holds of bodies unchanged, and a closed body (field 0
only) means what it meant before.

The parser reads Substrait's references this way (`Parse.openBody`:
`lambdaParameterReference` with `steps_out` `k` inside `k` nested lambdas,
`rootReference` one further per lambda) and the writer writes them back
(`Write.closeRefs`). Every function that renumbers a row's columns renumbers
a body under one binder (`liftIdx`, `liftPred`, `Expr.shift` with a cutoff,
`Expr.subst` with a shifted substitution), and the kind checker types a body
under its element's kind in front of the row's (`Expr.kindT`). Accepted plans
keep their meaning: before D28 the parser refused a body that read the row.

Why: a closed lambda cannot express `contains` of a column or a filter by an
outer value, and the review of the core (#893) found the restriction in
`Expr.eval`, `Expr.refsLt` and the parser, none of it needed by a proof.

### D29. A value has its kind

Decided 2026-11-07 (#923).

`Value` has a constructor per kind (#923): `int`, `float` (a double's code),
`date` (days), `ts` (microseconds, with or without a time zone), `tod`
(microseconds since midnight), `dec s m` (scale and unscaled integer) and
`struct`, beside `null`, `bool`, `str` and `list`. Intervals stay `int`. A
function of one kind gives NULL on another, so a double can no longer pass
for an integer or a timestamp for a date. Comparisons (`Value.numPair`) take
two numbers of one constructor, decimals of one scale: `=` is TRUE only of
equal values, which equi-joins rest on (`isTrue_eq`). The parser brings both
sides of a decimal comparison to their common scale (`UnFn.dkind`).

`SUM` (`sumOf`) gives a decimal of scale `s` when all its values are
decimals of scale `s`, and otherwise the integer sum of the integers and the
decimals' unscaled values, a mix of decimals with other values or with
other scales included. This case is unreachable for a plan the kind checker accepts; it binds no engine, and no contract theorem is stated for unchecked plans.
The checker is D28's (`Rel.kinds_sound`). The mixed value is a don't-care,
chosen to keep `SUM` independent of the order of its values (`sumOf_perm`)
and of how a partition splits them (`sum_partials`) without a side condition.
A NULL for a mix would break the second: a part that mixes kinds gives NULL,
the combining `SUM` skips NULL parts, and the parts left would add up to a
number where the whole gives NULL.

The abstract domain records the kind of a column's numbers (`AVal.nk`, with
`none` as top). A value of kind `k` is in an abstract value only if its `nk`
is `none` or `some k`, and the join of two different kinds is `none`. Static
kinds from the kind checker may refine `nk` on checked plans later.

Why: the kinds were in the parser and the kind checker (#924) only; with them
in the values, a well-kinded plan's values have their kinds by evaluation, and
the float facts state their premises about doubles. Those were the trusted
axioms `floatSum_mem`, `floatAvg_mem`, `floatSum_sign`, `floatSum_twoPhase`
and `floatAvg_twoPhase`; D25 retired them for theorems about the correctly
rounded sum (`floatSumCR_mem`, `floatAvgCR_mem`, `floatSumCR_sign`,
`twoPhaseSum_near`, `twoPhaseAvg_near`).

### D30. Statistical aggregates are correctly rounded exact moments

Decided 2026-11-07 (#918).

In the reference, `VAR_SAMP`, `VAR_POP`, `STDDEV_SAMP`, `STDDEV_POP`,
`COVAR_SAMP`, `COVAR_POP` and `CORR` of doubles are rounded once from the
exact moments of the values: the count `n`, and `Σx`, `Σx²` and `Σxy` as
exact dyadic rationals, since every finite double is a multiple of
2⁻¹⁰⁷⁴ (`FloatMoments.lean`). The co-moments `S = Σx² − (Σx)²/n` and
`C = Σxy − Σx·Σy/n` are exact. The variance is `S/d` rounded to the nearest
double, ties to even, with `d = n − 1` for a sample and `n` for the
population; the covariance is `C/d` rounded once. `STDDEV` and `CORR` are
rounded by comparing squares against the midpoint, with no square root
computed: `√(S/d)` and `|C|/√(Sxx·Syy)` against each candidate's midpoint
`m` by `m² · d < S` and `m² · Sxx · Syy < C²`, with `C`'s sign
(`sqrtMag`). Each is one value, a function of the multiset of values
(`varOf_perm`, `covOf_perm`, `corrOf_perm`), whatever the engine's
algorithm.

NULL as before D30: no values, a sample of one, and for `CORR` fewer than two
pairs or a side whose values are all equal, which is `Sxx = 0` or `Syy = 0`
(`stat_degenerate` `NULL`; `corrOf` gave NULL there before D30 too). NaN and
infinities as `varOf` had them: a NaN among the values gives NaN, and an
infinity gives NaN in `Rel.eval` and raises in a plan the checker accepts,
since its deviation `∞ − ∞` would create a NaN (#257). A finite result past
the largest double raises (#575).

Engines keep their own algorithms: Welford's update with Chan's merge in
DuckDB, Spark and grouped Polars, a blockwise two-pass in ungrouped Polars.
Each is within the plan's bound of the reference's value: the algorithm's
distance from the exact moments (`StatProps`, proved for Welford and Chan as
`StdModel.core_var_chan`, `core_cov_chan`, `core_corr_chan` in
`float-bounds/`), plus half an ulp of the reference's rounding. Their
`stat_algo` rows are `approxWithin "plan"`, as `sum_order`'s are, and
`StatAlgo` keeps `StatProps` as what `GENERIC` and `WELFORD_CHAN` allow. The
writers clamp an engine's variance and deviation at `0` and its correlation
to `[-1, 1]`, NaN kept (`Dialect.clamp_stat`, Polars likewise): the exact
value lies in the interval, so clamping never moves the engine's value
further from it (`Stat.clamp_near`), and `var ≥ 0` and `|corr| ≤ 1`
hold of every engine's result. The bounds differ in kind: `VAR_*` and
`STDDEV_*` are relative to the spread, the deviation's half the variance's;
`CORR`'s is absolute, about `c · n · u`; `COVAR`'s is absolute, scaled by
`√(Sxx · Syy)`, or relative only under a sign-definite precondition.
`Report.epsilon` reports `VAR_*`, `STDDEV_*` and `COVAR_*` columns
(`Epsilon.statEps`). `CORR` has no data-free bound (decided 2026-11-08,
#918): its distance to the reference is bounded only under a lower bound on
both sides' variances (`core_corr_chan`'s `L`), stated by the user and
checked by the run as a precondition, never inferred. Without one, a `CORR`
postcondition beyond `[-1, 1]` and the clamp is tested only, and the report
names that precondition as the way to a bound (`Epsilon.corrWhy`). The
contract language has no preconditions on aggregates yet, so the stated
bound waits for them. Snowflake keeps
refusing these aggregates (Snowflake behaviour recorded privately).

Consequences:

- `stat_algo` is no longer a choice of the reference; it stays a choice of
  the engines, and the reference's row is `EXACT`.
- The statistical aggregates are order-free (`AggFn.orderFree`), so
  `Measure.closedB`, `Rel.closedB` and `Rel.detPlan` hold of plans with them,
  and `contract_sound_all` and `contract_sound_allowed_closed` cover them.
  `QUANTILE_CONT` stays the only open measure.
- `varOf_props`, `covOf_props` and `corrOf_props` are retired, and
  `Rel.eval_allowed` rests on Lean's standard axioms alone.
- A postcondition at a rounding boundary can move by an ulp, which
  `sv.approx` absorbs.

Why: before D30 the reference stated generic properties for these
aggregates and let engine profiles refine them, so a plan reading one left
the engine a choice of value. `Rel.FloatOpenSafe`, `contract_sound_allowed`'s
side condition, failed for any such plan: `SELECT VAR_POP(x)` allowed many
values while an order fixed one. Exact moments give one value with no
algorithm imposed on engines, as D25 did for sums, retire three axioms, and
are the state an exact incremental `VAR` needs (#918 Part B). The cost:
engines go from refining exactly to within a plan's bound.

### D31. Double arithmetic is exact, rounded once

Decided 2026-11-07 (#929).

The reference defines +, −, × and ÷ of doubles as the exact result rounded
once to binary64, to nearest, ties to even, with IEEE 754's rules for
infinities, NaN and the sign of zero: an exact zero from non-zero operands
is +0, products and quotients take the XOR of the signs, a non-zero result
that rounds to zero keeps its sign. The sign of a NaN an operation produces
is open; an engine fact may pin it per platform. `pow`, the libm functions
and casts to double are separate decisions. On an IEEE engine no finite
value changes; the eight float axioms become theorems. Each engine carries
one fact per platform, binary64 with round to nearest even, no contraction,
no flush to zero, checked by a differential probe; an engine without it gets
a shim or a refusal.

The reference observes these results through its own zero and NaN rules
(ONE_ZERO, #89; `on_division_by_zero`), so its values are unchanged; a
profile with IEEE `zero_sign` sees the signed result.

In the model (`core/Sverify/Core/FloatArith.lean`): every finite double is an
integer multiple of 2⁻¹⁰⁷⁴, so the exact sum, difference and product are
integers in that unit, the product in 2⁻²¹⁴⁸, and the quotient a fraction of
two. `ofExactDiv` rounds each, as it rounds D25's sums, to the nearest
multiple of `ulp = 2^max(e−52, −1074)` with ties by that multiple's parity,
and to `±∞` at `|q| ≥ 2¹⁰²⁴ · (1 − 2⁻⁵⁴)`. `addI`, `subI`, `mulI` and `divI` are
IEEE 754's operations on every code, `-0.0` and the negative NaN included.
The reference has one zero and one NaN (`zero_sign` `ONE_ZERO`, #89), so its
`fadd`, `fsub`, `fmul` and `fdiv` are these followed by `canon`, and on
finite operands they are the rounded exact result (`fadd_fin` …).

Consequences:

- `FloatCode.add_scaled`, `sub_scaled`, `mul_scaled`, `div_scaled`,
  `div_scaled_err`, `add_nonneg`, `mul_nonneg` and `div_nonneg` are theorems
  (#582's axioms). `FloatCode.exp_fin` (libm's `exp`) stays an axiom.
- `Expr.eval`'s `+ − × ÷`, the double sums and ratios of `Aggregate`,
  `Window`, `Profile`, `DuckDBSQL`, `AllowedP` and `AllowedNear`, and the
  interpolation of `QUANTILE_CONT`'s value use them; `contAllowed`'s interval
  stays, so the quantile's formula stays open. `pow` and `log` keep native
  doubles (`lift₂`).
- `FloatArithCheck.lean` checks the operations against native doubles bit
  for bit, signed zeros included, on edge values, ties and pseudo-random
  operands at every exponent; and the reference's against `lift₂`, which they
  replace.
- The checker computes with integers where it called the FPU, and no
  `@[implemented_by]` hides the IEEE assumption in its runtime.

Why: native `Float` is opaque to the kernel, so no rounding bound on `x + y`
or `x · y` was provable, and the checker trusted eight axioms for them. The
exact definitions make `Rel.eval` on doubles unfold in proofs, which the
tolerance fold of #929 needs for its arithmetic rows (`c · x`, `x ± y`,
`x · y`, `x / y`). The trust moves to each engine's fact.

### D32. Calendar functions work on the reference's timestamps, 0001 to 9999

Decided 2026-11-08 (signed off by the maintainer, reviewed by the theory
advisor).

The reference's timestamps are those of its dates (#251): 0001-01-01
00:00:00 to 9999-12-31 23:59:59.999999, `Time.tsMin` to `Time.tsMax` in
microseconds since 1970. Every calendar function is defined on all of them,
with the proleptic Gregorian calendar of `core/Sverify/Core/Time.lean`.
`date_part`, `strftime`, `time_of_day`, adding months to a timestamp,
truncation to a week, month, quarter or year, truncation of a date, and
`date_bin` raise (`Issue.overflow`) where the operand or the result leaves
the range. They no longer depend on DataFusion's ±2⁶³ nanoseconds (1677 to
2262) or on chrono's ±262,142 years. 0001-01-01 is a Monday, so no
truncation of a timestamp in range leaves it. A `date_bin` origin outside
the range is refused when the plan is checked, never at run time.

A DATE or TIMESTAMP value of the reference lies in 0001–9999 by its type. A
source value outside it fails the read, named; a computed date outside it
raises (#251). Calendar functions are total on the reference's values
(`Value.InCalendar`, `UnFn.datePart_issue_of_inCalendar`): a column read
needs no guard and no inferred precondition, and only a computed argument
can leave the range. The read checks each DATE and TIMESTAMP column once,
from the Parquet files' min/max statistics where they cover it (Delta and
Iceberg write them), else with one range predicate over the read, and fails
with "<column> holds dates outside 0001–9999 (<count>, e.g. <value>); the
reference's calendar covers 0001–9999. Filter them, or read the column as
text." (`sverify.engine.Connection.put`).

Outside the range the engines disagree: DuckDB and Polars give
`date_part('year')` 0 and 10000, but `strftime` of year 10000 is
`+10000-01-01` on Polars and Spark, and the reference has no year 0. So the
reference raises there, as it does for date arithmetic (#251), and picks no
value.

Each 1.0 engine reaches the reference natively inside the range and with
one guard outside it:

| engine | inside 0001 to 9999 | outside | type the writer pins |
|---|---|---|---|
| DuckDB | native ([duckdb-calendar-range](../characterization/duckdb/facts/duckdb-calendar-range.json)) | computes; the SQL guards | `TIMESTAMP` (µs) |
| Polars | native ([polars-calendar-range](../characterization/polars/facts/polars-calendar-range.json)) | computes; the translation guards | `Datetime("us")`; `"ns"` covers only 1677 to 2262 |
| Spark | native ([spark-calendar-range](../characterization/spark/facts/spark-calendar-range.json)) | computes; the SQL guards | `TIMESTAMP_NTZ`, session time zone UTC |
| Snowflake | reachable by a shim, probe pending: parts in year 1 are right and sverify truncates weeks itself (private facts); month, quarter and year truncation at the ends is not recorded | computes (years 0 to 302024); the SQL guards | `TIMESTAMP_NTZ` |
| DataFusion | refused: it truncates and bins in nanoseconds ([DF-17](../upstream/bugs/DF-17.json)) | — | — |

The facts record the probe points: 0001-01-01, the leap days 0004-02-29,
1600-02-29 and 2000-02-29, 1900-02-28 and 1900-03-01, both sides of the
Gregorian switch (1582-10-04 and 1582-10-15) and 9999-12-31, each at
23:59:59.999999. `Time.lean`'s `#guard`s and `test_time.py::test_d32_probe_points`
check the same points.

In the model: `Time.tsMin` and `Time.tsMax` replace `nsMin`, `nsMax`,
`nsDayMin`, `nsDayMax`, `partMin`, `partMax`, `chronoDayMin` and
`chronoDayMax`. `Time.datePart` is `NULL` outside the range, where
`UnFn.issue` now raises (`datePart`, `dayPart`); `UnFn.mayIssue` reports it
unless the operand's bounds are inside the range. A column's type gives
those bounds (`ContractCheck.typeEnv`: a DATE in `dayMin` … `dayMax`, a
TIMESTAMP in `tsMin` … `tsMax`), so a column read discharges it. `UnFn.mayIssue_sound` covers
the new rows with the existing `rangeIssue_sound`. `Infer.atIssue` infers the
range as a precondition.

Consequences:

- A `date_part` raises only on a computed argument: on the catalogue's 136
  queries the checker reports one such `date_part` issue, and TPC-H Q09's
  `EXTRACT(YEAR FROM o_orderdate)` stays proved. The SQL writers still emit
  the guard on every `date_part` (35 on the catalogue's DuckDB SQL, 480
  guards in all, from 445) until the checker's discharged issues reach the
  Polars writer (#1174) and DuckDB's (#1169), which drop those on column
  reads.
- Truncation and parts of timestamps from 1677 back to 0001 and from 2262 to
  9999 run on every 1.0 engine, where they raised before.
- `strftime`'s `%Y` is always four digits.

Why: the old ranges were DataFusion's, and DataFusion is a tier-3 engine
(2026-11-08). The SQL standard's timestamps are the reference's dates', which
every 1.0 engine represents.

### D34. An option differs from the reference only on its scope

Decided 2026-11-08, by the maintainer after the theory review.

Each option differs from the reference only on its scope, a predicate on the
call's arguments and reference result stated beside the option. Engine rows
are statements about the scope; agreement outside it is the function's base
row. A plan depends on an option only where a call may be in its scope.

In the model, `optionScope` (`core/Sverify/Core/Scopes.lean`) states each
option's scope, one row per option of the catalogue in its order, and
`Rel.AllowedP` reads it: a call (`CallExtra`) or an aggregate (`AggExtra`)
takes another value than the reference's only where its table allows one of
its group's options a behaviour the reference does not and the call is in
that option's scope. A scope may be wider than where the behaviours differ,
never narrower; one not pinned down yet is every call.

| Option | Scope |
|---|---|
| `overflow` | the exact result is outside the type's range (an integer `SUM` outside 64 bits) |
| `on_division_by_zero` | the divisor is zero |
| `division_type` | the operands have opposite signs and the remainder is not zero |
| `min_mod_neg_one` | `MIN % -1` |
| `nan_creation` | the arguments are not NaN and the IEEE result is: `∞ − ∞`, `0 · ∞`, `∞ / ∞`, `0 / 0`, `fmod(±∞, y)`, `fmod(x, 0)`, a `SUM` of `+∞` and `−∞` |
| `float_overflow` | the arguments are finite and the correctly rounded result is infinite |
| `zero_sign` | an argument or the reference result is a zero (underflow, `x − x`, a sum rounding to zero) |
| `nan_equality`, `nan_order` | an argument is NaN, or holds one |
| `nan_kind` | an argument or the reference result is NaN |
| `on_domain_error`, `on_log_zero`, `substring_range`, `cast_failure`, `date_range` | the reference reports the issue at the call (a domain error, a failed cast, a date out of range) |
| `negative_start` | a negative start |
| `null_handling` | an argument is NULL |
| `empty_group_aggregates` | an aggregate of no values |
| `avg_int_result` | an `AVG` with an integer result (`AggFn.iavg`); a `SUM` never meets it |
| the others (`rounding`, `sum_order`, `stat_algo`, `tie_*`, `shift_range`, …) | every call |

`sum_order`'s true scope is a sum that is not exact; it is every call until
the analyses can tell. An engine's own order of additions, overflow to `±∞`
on the way included, is `sum_order`'s (`FloatSums`), so `agg.fsum`'s
`nan_creation` and `float_overflow` are about the correctly rounded sum.

Consequences:

- `Rel.AllowedP` only narrows. `Rel.allowedP_reference`, `Rel.AllowedP_mono`
  and `Rel.AllowedP_transfer` keep their statements.
- The engines' functions show each of their deviations in an option's scope
  (`Profile.duckdb_withinOk`, `Polars.written_within`). DuckDB's
  `fmod(x, 0)` is NaN under `nan_creation`, since its table gives `fp.mod`
  no other `on_division_by_zero`; Polars's NaN for `power` is a domain
  error's (`on_domain_error`), since `power` has no `nan_creation`.
- A call reads only its group's options that apply to it (`optionApplies`,
  `optionApplies_of_scope`), so a `SUM` does not read `avg_int_result`
  (`ctorReads`, `Rel.reads`, `Rel.AllowedP_transfer`).
- A plan's option dependency report keeps an option only where a call may be
  in its scope, from the arguments' abstract values (`Expr.eval_dead`,
  `Rel.AllowedP_transfer_live`, a follow-up), and reports the function's
  base row's evidence where every option is dead.

### D35. Engine summation orders are bounded sets

Decided 2026-11-08 (#929): approved by the theory advisor, to whom the
maintainer delegated the sign-off.

`SumOrder b vs c`, the doubles a double `SUM` gives under a `sum_order`
behaviour, bounds every behaviour but `EXACT`. On `n ≤ 2³²` finite doubles
whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double, the sum is finite
and within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact sum, `u = 2⁻⁵³`,
`γₙ = nu / (1 − nu)` (`SumBound`). Stated in units of `2⁻¹⁰⁷⁴` and multiplied
out, it is an exact inequality on integers, so it needs no rounding of its
own.

- `ANY` and `PAIRWISE` keep their trees (`FloatSums`) and `SEQUENTIAL` its
  permuted sequential sum, each with the bound.
- `COMPENSATED` (Kahan's sum, Polars) and `SCALED_CONSTANT` (a constant run's
  `fl(k · x)`, DuckDB) were any double. They are now the bound alone: no
  theorem of the core reads their shape (`TreeSum.const` is float-bounds').
- `AvgOrder` follows: a sum within the bound, divided by the count.
- `EXACT`, the reference's order (D25), is unchanged.
- Window sums take their frame's `SumOrder` (`WinFn.AllowedP`): `TREE` and
  `RECOMPUTE` sum each frame's own values. `RUNNING_ADD` is a running state
  over the partition's prefix that never removes a row (duckdb-window-sum-order,
  spark-window-agg), so its value at a row is a sum of exactly the rows
  before it, the frame of the growing windows it runs: the prefix bound is
  the frame's, by those facts. A sliding sum (`SLIDING`) stays any value.

What stays trusted: the engines' algorithms meet the bound. `StdModel`'s
theorems in `float-bounds` justify it on the engines' facts
(`StdModel.Summed.near`, `epsilon_sum_cr`, `Rnd.kahan_near`), as the
`sum_order` rows' evidence. #1196, the bridge from float-bounds to the core,
retires it.

Why: `Rel.AllowedP` is the set the soundness theorems quantify over. A
behaviour that allows any double made every contract on a double `SUM`
unprovable at the plan level on DuckDB and Polars, although both algorithms
are bounded. `SumOrder.bound` reads the bound as a range the abstract domain
computes (finite, in `[sumLo, sumHi]`), which cuts `nan_creation`,
`float_overflow` and the NaN cases of a comparison downstream (D34), and the
margin check's theorem over its plan reads the same set.

### D36. Doubles have one zero and one NaN

Decided on [#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), merged 2026-10-31, and on #209.

The reference profile reads doubles with one zero and one NaN:
`zero_sign` `ONE_ZERO`, `nan_kind` `ONE_NAN`, `nan_equality` `NAN_IS_NAN`
and `nan_order` `GREATEST`, above `+∞`. `-0.0` is `0.0` everywhere, so
`1.0 / -0.0 = inf` where the plan asks for IEEE division, and `GROUP BY`,
`DISTINCT`, joins, partitions and sorts see one zero and one NaN. The core
keeps both zeros and the signed NaNs ([The value domain](#the-value-domain));
the reference applies `FloatFormat.canon` to every input and output, as the
writers do (`Dialect.canon`). Substrait's YAMLs leave the grouping and
order of `-0.0` unspecified and compare NaN by IEEE's rules, so this is an
override ([Overrides](reference-semantics.md#overrides)).

Why: SQL users expect `-0.0 >= 0` and a NaN equal to itself, and DuckDB,
Polars and Spark compare NaN so (`nan_equality` `NAN_IS_NAN` in their
tables); IEEE's NaN, unequal to itself,
would split `GROUP BY` and `DISTINCT` and drop rows from joins.

### D37. No operation creates a NaN

Decided on #185 ("no newly created NaNs") and [#257](https://github.com/AlexanderNenninger/substrait-lean/issues/257), closed
2026-11-02.

No operation creates a NaN. An operation on non-NaN inputs whose IEEE
result is NaN is an issue (`Issue.domain`, `nan_creation = ERROR`), which
`verify` rules out or checks on the data; on the rows a precondition
excludes, `Rel.eval` keeps IEEE's value (NaN), as it keeps ±∞ under #575.
Under a verification profile that sets `nan_creation = NAN`, no issue fires
and the value is NaN.

Why: with no NaN in the inputs (`~_.v.isnan()` in `requires`), there is
none in the outputs. Engines give NaN, NULL or an error there, and a plan
proved to never raise reaches none of them, so no engine needs a shim
([D21](#d21-tighten-the-reference-where-it-stays-practical)).

### D38. No operation on finite doubles overflows to infinity

Decided on [#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575), closed 2026-11-04.

A `±∞` from the data passes through. An operation on finite doubles whose
IEEE result is `±∞` raises: `+`, `-`, `*`, `/` and `power` that overflow
(`1e308 * 10`, `power(10, 400)`, `power(0, -1)`), `exp` past `709.78`, and a
`SUM`, `AVG`, variance, covariance or correlation of finite values that
overflows (`Issue.infinite` in `Safety.lean`). `verify` rules the error out
by an inferred precondition: proved from the bounds where they do it,
otherwise listed in `Report.assumed` and checked on the data. `Rel.eval`
keeps the IEEE value on the rows the precondition excludes, so the lift of
DuckDB's SQL with `semantics="duckdb"` states DuckDB's result exactly.

Why: with no NaN and no `±∞` in the inputs, there is none in the outputs,
and every floating result has a usable bound. Substrait's YAMLs leave the
overflow unspecified ([ST-9](../upstream/bugs/ST-9.json)), and the
precondition rarely bites real queries (D21).
