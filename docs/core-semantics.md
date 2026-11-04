# The loose core: design

Sverify's semantics will share one loose core in Lean, and every semantics
sverify knows becomes a refinement of it: Substrait's, the reference's and
each engine's
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
Plans are verified under the strict reference profile
([Terminology](#terminology)).
This page is the design pass of step 3 of epic
[#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544). It
lists, per function, the points where profiles differ, gives the tables that
hold each profile's choices, says which values the core needs, states when a
translation between two profiles is sound, and orders #444's steps. The
approach is CASL's loose semantics and WebAssembly's profiles, applied to
Substrait, with refinement as CompCert and Alive2 state it
([Prior work](#prior-work)). Wave 3 of #544 builds its function tables in this shape.

The choices this page left open were decided in its review
([Decisions](#decisions)). Everything else follows decisions already made on
#185, #202, #209, #257, #336, #427 and #444; [reference-semantics.md](reference-semantics.md)
records them.

## Terminology

Three kinds of semantics, each with one job.

- The core is the loosest semantics, a specification layer. It admits every
  engine's behaviour ([D3](#d3-behaviours-outside-the-yaml)), every profile
  refines it, and it is where profiles are stated and related: a profile is
  the core with its choices narrowed, and a translation between two profiles
  is a refinement between them ([Translations](#translations-between-profiles)).
  Sverify runs no plan under the core, and verifying a plan under the core
  is no goal: the core allows every engine's raises and NaNs at once.
- The reference profile (`Profile.reference`, "the reference") is what plans
  are verified under. It is strict, stricter than every engine in most
  options. Where engines disagree on an edge case (integer overflow, NaN
  creation, double overflow to `±∞` (#575), domain errors, division by zero,
  out-of-range casts and dates), it raises. Where it picks a value, it picks one every engine can produce
  ([principle 3](reference-semantics.md#principles)).
  The reference may still choose a behaviour some engine needs a shim for,
  where that keeps the profile practical for users (the NULL order, rounding
  ties). Each such choice costs a shim on every engine that differs, so these
  choices are few and deliberate: the reference prefers raising, proved
  absent for a verified plan, or a choice every engine gives natively.
- Engine profiles say what each engine does, from
  `characterization/<engine>/facts/`, and refine the core. A plan verified
  under the reference reaches an engine through a translation, shimmed only
  on the reference's value choices.
  `Profile.substrait` (step 2) is a profile of the same kind: the YAMLs'
  own looseness, between the core and the reference.

### What strictness buys

A plan verified under the reference never raises: its preconditions,
stated or inferred, are proved to exclude the reference's raise set, or
checked on the data. The inputs where engines disagree on errors are in that
raise set, so a verified plan never reaches them, and it creates no new NaN
(`nan_creation` raises in the reference). In
[#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)'s
terms, each call of such a plan is `refines[D]` on every engine, with `D` the
reference's non-raising domain at that call, and the proof keeps the plan's
inputs inside `D`.

So the options split in three, and a verified plan needs a shim only for the
second:

| Kind | Reference | Options | A verified plan on an engine |
|---|---|---|---|
| Error side | raises | `overflow` (`ERROR`), `on_division_by_zero`, `on_domain_error`, `on_log_zero`, `nan_creation`, double overflow to `±∞` (#575), `shift_range`, `substring_range`, `date_range`, `cast_failure` (`UNSPECIFIED`), `stat_degenerate` for `±∞` | no shim: the engine's behaviour there (a wrap, NULL, NaN, `±∞`, a panic) is never reached |
| Value side | picks one value | `null_order`, `rounding` of `round`, `division_type`, floor or truncating division of negatives, `float_to_int`, `decimal_rescale`, `avg_int_result`, an empty `SUM`, string and list positions, `zero_sign`, `nan_kind`, `nan_order`, `list_null_order`, `stat_degenerate` for `CORR`, result types | native where the engine picks the same value; a shim otherwise |
| Open | allows several | `sum_order`, `stat_algo`, `quantile_interp`, `tie_pick`, `tie_order` | native where the engine's pick is one the reference allows; `approx[D, ε]` (#568) otherwise |

An option the plan states itself (`overflow: SILENT`) is a value choice too.
A precondition only checked on the data, such as a `SUM`'s overflow bound
(#316), needs its run-time check, the guard, on every engine; guard
elimination (#83) drops the guards the inferred bounds rule out.
[The Polars example](#the-polars-example) counts the shims for one engine.

## The shape

The reference is already a relation: `Rel.Allowed` (`SubstraitLean/Allowed.lean`,
[#427](https://github.com/AlexanderNenninger/substrait-lean/pull/427)) allows a
set of results per input, and `Rel.eval` computes one of them
(`Rel.eval_allowed`). The core generalises it in one direction: every place
where `Rel.Allowed` makes a choice for the reference becomes a choice
point, and a profile is the set of choices it allows at each point.

- A choice point is an option: a name and a finite set of behaviours.
  Substrait's own options (`overflow`, `on_division_by_zero`, `rounding`, …)
  are options with the values of their YAML. The points Substrait leaves
  unnamed (one zero, NaN's order, the order of a double `SUM`, the row
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

The reference's correctness allows an engine to raise anywhere: it "returns
an allowed result or raises an error" ([What it is](reference-semantics.md#what-it-is)).
The core keeps that. What a profile adds is where it may raise: its
raise set, a constraint like any other, and `verify`'s error issues
(`Rel.mayIssues`, `SubstraitLean/Safety.lean`) are the reference's raise
set. A theorem that a plan cannot raise is then a theorem about one profile's
raise set, and holds on every profile whose raise set is smaller. This keeps
principle 4 (an error means "may raise", so rewrites stay refinements) and
lets DuckDB's extra raises (`MIN % -1`, `<<` of a negative number) stay
inside the core without new options. Decided ([D2](#d2-raises-in-the-core)).

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
| `decimal_rescale` (sverify's: a result scale smaller than the exact one) | `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN`, `TRUNCATE` | `functions_arithmetic_decimal.yaml` gives result types, no rounding | `TIE_AWAY_FROM_ZERO` | its own result types; the translation compensates ([engine-profiles.md](engine-profiles.md#decimals-27)) |

#### Doubles

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `rounding` (`+ - × /`, the elementary functions, `sum`, `avg`, `variance`, `std_dev`) | the five of the YAML | `TIE_TO_EVEN`, `TIE_AWAY_FROM_ZERO`, `TRUNCATE`, `CEILING`, `FLOOR` | `TIE_TO_EVEN` (native `Float`) | `TIE_TO_EVEN` (native IEEE; no fact records it) |
| `rounding` (`round`) | the ten of the YAML | ten modes | `TIE_AWAY_FROM_ZERO` (#335) | `TIE_AWAY_FROM_ZERO` ([R15-round](../characterization/duckdb/facts/duckdb-R15-round.json), [R15-round-digits](../characterization/duckdb/facts/duckdb-R15-round-digits.json)) |
| `on_division_by_zero` (doubles) | `IEEE`, `LIMIT`, `NULL`, `ERROR` | the four | `ERROR`; the others when asked (#204) | `IEEE` under `ieee_floating_point_ops`, `ERROR` with it off ([R5](../characterization/duckdb/facts/duckdb-R5.json)) |
| `on_domain_error` (`sqrt`, `asin`, `acos`, `atanh`, `acosh`, logs, `atan2`, `divide`) | `NAN`, `NULL`, `ERROR` | `NAN`, `ERROR` (logs and integer `divide` add `NULL`) | `ERROR` (#215) | `NAN` ([R15-math-domain](../characterization/duckdb/facts/duckdb-R15-math-domain.json)); `atan2(0, 0)` is `0` ([R15-atan2](../characterization/duckdb/facts/duckdb-R15-atan2.json)) |
| `on_log_zero` | `NAN`, `ERROR`, `MINUS_INFINITY` | the three | `ERROR` | `MINUS_INFINITY` (R15-math-domain) |
| `nan_creation` (sverify's: `∞ − ∞`, `0 · ∞`, `∞ / ∞`, `fmod(±∞, y)`, a `SUM` of `+∞` and `−∞`) | `NAN`, raise | IEEE: NaN | raise (#257) | `NAN` ([R15-double-arith](../characterization/duckdb/facts/duckdb-R15-double-arith.json), [R15-double-modulus](../characterization/duckdb/facts/duckdb-R15-double-modulus.json), [nonfinite-aggregates](../characterization/duckdb/facts/duckdb-nonfinite-aggregates.json)) |
| `zero_sign` (sverify's) | `IEEE` (two zeros), `ONE_ZERO` | IEEE; grouping and order of `-0.0` unspecified | `ONE_ZERO` (#89, an override) | `IEEE` in arithmetic (`1.0 / -0.0 = -∞`) and in order (`-0.0` before `0.0`); the written plan canonicalises (`Dialect.canon`, [R14](../characterization/duckdb/facts/duckdb-R14.json)) |
| `nan_equality` (sverify's for `=`, grouping, `DISTINCT`, joins; Substrait's for `index_in`) | `NAN_IS_NAN`, `NAN_IS_NOT_NAN` | IEEE `=` (NaN unequal); `index_in` takes the option | `NAN_IS_NAN` (#89, an override) | `NAN_IS_NAN` (#89) |
| `nan_order` (sverify's: sort, `MIN`, `MAX`, `<`) | `GREATEST`, `UNORDERED` | IEEE comparisons (`NaN < x` false) | `GREATEST`, above `+∞` | `GREATEST` ([arg-min-nulls](../characterization/duckdb/facts/duckdb-arg-min-nulls.json), [quantile-disc](../characterization/duckdb/facts/duckdb-quantile-disc.json)) |
| `nan_kind` (sverify's: a NaN's sign and payload) | `IEEE`, `ONE_NAN` | IEEE | `ONE_NAN` | the sign survives (`signbit(-'nan')` is TRUE, [signbit](../characterization/duckdb/facts/duckdb-signbit.json)) |

#### Strings, dates and lists

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `negative_start` (`substring`) | `WRAP_FROM_END`, `LEFT_OF_BEGINNING`, `ERROR` | the three | `WRAP_FROM_END` (#209) | `WRAP_FROM_END` native ([R13](../characterization/duckdb/facts/duckdb-R13.json)) |
| `substring_range` (sverify's: an offset outside `[-2³², 2³²)`) | raise, compute | no limit | raise (#336) | raises ([substring-range](../characterization/duckdb/facts/duckdb-substring-range.json)) |
| `case_sensitivity` (`like`, `contains`, `starts_with`, `ends_with`, `strpos`, regexes) | the three of the YAML | `CASE_SENSITIVE`, `CASE_INSENSITIVE`, `CASE_INSENSITIVE_ASCII` | `CASE_SENSITIVE` | `CASE_SENSITIVE` (no fact) |
| `char_set` (`upper`, `lower`) | `UTF8`, `ASCII_ONLY` | the two | `UTF8`, a black box (Rust's `str::to_uppercase`) | Unicode (no fact) |
| `null_handling` (`concat`) | `IGNORE_NULLS`, `ACCEPT_NULLS` | the two | `ACCEPT_NULLS`; the other refused | NULL in, NULL out for `\|\|` (no fact) |
| `date_range` (sverify's: date arithmetic past 0001-01-01 … 9999-12-31) | raise, compute | no limit | raise (#251) | wider dates; the written plan guards |
| `time_interval_months` (sverify's: `TIME ± INTERVAL` with months) | drop the months, raise | not specified | refused | drops them ([time-plus-interval](../characterization/duckdb/facts/duckdb-time-plus-interval.json)) |
| `list_null_order` (sverify's: a NULL element deciding `<` of lists) | `NULL`, `GREATEST`, `LEAST` | `lt` of lists not defined | `NULL` in `<`, `GREATEST` in `ORDER BY` (#207) | `GREATEST` in both; shimmed ([R11](../characterization/duckdb/facts/duckdb-R11.json)) |

#### Aggregates, windows and relations

| Option | Core | Substrait | Reference | DuckDB |
|---|---|---|---|---|
| `sum_order` (sverify's: `SUM`, `AVG` of doubles) | any order and grouping (`FloatSums`) | not specified | any order and grouping, within #85's bound | sequential, partial states merged by addition ([sum-double](../characterization/duckdb/facts/duckdb-sum-double.json), [avg-double](../characterization/duckdb/facts/duckdb-avg-double.json)) |
| `stat_algo` (sverify's: `VAR_*`, `STDDEV_*`, `COVAR_*`, `CORR`) | the generic properties (`StatProps`) | not specified | the generic properties (decided, #85) | Welford with Chan's merge ([var-stddev](../characterization/duckdb/facts/duckdb-var-stddev.json), [covar](../characterization/duckdb/facts/duckdb-covar.json), [corr](../characterization/duckdb/facts/duckdb-corr.json)) |
| `stat_degenerate` (sverify's: `CORR` of one pair or a constant side; a statistical aggregate of `±∞`) | `NULL`, `NAN`, raise | not specified | `NULL` for `CORR`; raise for `±∞` | `NAN` for both (duckdb-corr, nonfinite-aggregates) |
| `avg_int_result` (sverify's: `avg` of integers) | the declared output type: `fp64` or `i64` truncated | `avg` of `i64` returns `i64` | follows the declared type (#209) | a `HUGEINT` sum divided by the count (R6) |
| `quantile_interp` (sverify's: `QUANTILE_CONT` between neighbours) | any double between them | `quantile` has `rounding` | any double between them (`contAllowed`) | `lo·(1−d) + hi·d`, may round past; clamped ([quantile-cont-interpolation](../characterization/duckdb/facts/duckdb-quantile-cont-interpolation.json)) |
| `tie_pick` (sverify's: `FIRST`, `LAST`, `ARG_MIN`, `ARG_MAX`, `any_value`, `MODE`, ranks over ties) | any row of the tie | `any_value` "selects an arbitrary value" | any row; each measure may take its own | the row it read first, which depends on parallelism ([mode-ties](../characterization/duckdb/facts/duckdb-mode-ties.json), arg-min-nulls) |
| `tie_order` (sverify's: `STRING_AGG`, `collect`, a sort, a window's order) | any order of the ties | not specified | any order | not stable (mode-ties) |
| `null_order` (a sort key) | `NULLS_FIRST`, `NULLS_LAST` | stated by the key's direction; `UNSPECIFIED` leaves it open | as the key states; `NULLS_LAST` for `UNSPECIFIED` ([D8](#d8-the-references-null-order)) | `NULLS_LAST` by default ([F2](../characterization/duckdb/facts/duckdb-F2.json)); either when the SQL states it |
| `clustered` (a sort key's `CLUSTERED` direction) | equal keys adjacent, the groups in any order | `SORT_DIRECTION_CLUSTERED` | the same relation | an `ORDER BY` on the keys, which clusters them |
| `ntile_spread` (sverify's) | the SQL standard's, spread out | not specified | the SQL standard's | the SQL standard's (DataFusion spreads, [DF-11](../upstream/bugs/DF-11.json)) |
| `float_to_int` (casts) | `TRUNCATE`, `TIE_AWAY_FROM_ZERO`, `TIE_TO_EVEN` | not specified | `TRUNCATE` (#209) | `TIE_AWAY_FROM_ZERO`; shimmed with `trunc` ([R9](../characterization/duckdb/facts/duckdb-R9.json)) |
| `cast_failure` | `THROW_EXCEPTION`, `RETURN_NULL` | the cast's `failureBehavior`; `UNSPECIFIED` exists | `THROW_EXCEPTION` for `UNSPECIFIED` | both native ([R8](../characterization/duckdb/facts/duckdb-R8.json)) |

Opaque functions need no option: the black boxes (#325), the regexes and the
digests have one meaning each, the function itself, and every profile shares
it. The conversions between integers, decimals and doubles stay opaque
constants with proved properties (`SubstraitLean/Conversions.lean`), the same
in every profile.

### Function groups

Functions with the same options share a row. Every function of an area is in
exactly one group; wave 3's tables give each function its group
(`SubstraitLean/Functions.lean`, one row per constructor, so `add` has a row
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
| core | `dec.div` | `divide`, `modulus` on decimals, `sverify_decimal_div` | refused in every profile until [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27) |
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
| temporal | `time.part` | `date_part`, `date_trunc`, `strftime` | none (their range is open in the reference, [Temporal](reference-semantics.md#temporal)) |
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

1. Options (`SubstraitLean/Options.lean`, new): one row per option of the
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

Checks by `decide` (`SubstraitLean/Options.lean`) reject a repeated id or
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
pass), or refused. An error-side option needs no shim for a plan verified
to never raise ([What strictness buys](#what-strictness-buys)), so its cell
names the guard, used only where a precondition is checked on the data.
Generated from `REALIZE` and the facts, published in
`docs/`, and checked in CI: a change to the reference that makes an engine
refuse, or need a shim of a higher cost class, fails a test until the
table's expected output is updated. This is principle 3 ("every engine can
follow it with reasonable effort") as a check.

## The value domain

The core needs every value any profile gives, so each must be at least as
fine as Substrait's. Today `Value` is `null | bool | int | str | list`, and
a double is an `int` code in SQL order with one zero and one NaN
(`SubstraitLean/Float.lean`).

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

Step 1b put them there (`SubstraitLean/FloatFormat.lean`): `negNan` is the
code negation of NaN and `negZero` the even code below it, `key` orders the
full set, `canon_idem` and `canon_mono` prove `canon` idempotent and
order-preserving, and `SubstraitLean/Float.lean` proves that each operation
on doubles commutes with `canon` on the reference's codes (`lift₂_canon`,
`roundTo_canon`, `fmod_canon`, `finite_canon`; `canon_ofFloat` for results
built from a native double). Code negation is the one exception: it sends
NaN to `negNan`, and `canon_neg` shows that `canon` of it is the parser's
negation, which keeps NaN.

## Translations between profiles

A plan means something only under a profile, so the unit sverify reasons
about is the pair: a plan `r` under a profile `P`, which allows the results
`Allowed_P(r)` and may raise on the rows of its raise set `Raises_P(r)`.
Everything that moves a plan, between profiles or within one, is one
relation on these pairs.

### Soundness

`(Q, t)` refines `(P, r)`, written `(Q, t) ⊑ (P, r)`, when on every input

- every result `Q` allows for `t` is one `P` allows for `r`:
  `Allowed_Q(t) ⊆ Allowed_P(r)`, and
- `t` under `Q` raises only where `r` under `P` may:
  `Raises_Q(t) ⊆ Raises_P(r)`.

A translation `T : P → Q` maps plans to plans or refuses them, and it is
sound when `(Q, T r) ⊑ (P, r)` for every plan `r` it does not refuse. A
theorem about `Allowed_P(r)`, the kind `verify` proves, then holds of every
result `Q` returns for `T r`, and a proof that `r` cannot raise under `P`
carries over. A refusal is always sound.

The relation covers every move sverify makes:

| Move | As refinement | Today |
|---|---|---|
| A rewrite within a profile | `(P, t) ⊑ (P, r)` | `Rel.Refines` ([Allowed.lean](../SubstraitLean/Allowed.lean)), `Rel.refines_of_perm` |
| A narrower profile, the same plan | `(P, r) ⊑ (core, r)` when `P`'s choices are within the core's | step 1c's `Rel.AllowedP_mono` |
| Lowering to an engine | `(E, T_E r) ⊑ (reference, r)` | `Rel.duckdb_shim_allowed`, `Lowering.lower_correct`, `Rel.guardFree_allowed` |
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

1. Verified under `Profile.E`: it runs natively.
2. Verified under the reference: it runs through the translation from the
   reference to `E`, whose realizability row is proved once per engine, so
   it costs a plan nothing.
3. Verified under another profile `P`, with a proof that transfers to
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
| `q ⊄ p` only on inputs a precondition excludes | a precondition: proved, or listed in `Report.assumed` and checked on the data | the reference's error-side options to any engine: `nan_creation` (raise) to DuckDB (`NAN`) is sound on the inputs a plan verified to never raise reaches; `zero_sign` and `nan_kind`, Substrait (`IEEE`) to the reference: sound on inputs without `-0.0` or a negative NaN |
| none of these | refused | `ntile_spread` on DataFusion ([DF-11](../upstream/bugs/DF-11.json)); `FLOOR` modulus anywhere today |

From the reference to an engine, the third case covers every error-side
option ([What strictness buys](#what-strictness-buys)): the reference raises
there, so its raise set is the precondition, and a plan verified to never
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
  `tie_pick` by a total order (`tie_free`) or a refusal, and `sum_order`
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

A plan verified under the reference, `requires R ⇒ ensures E`, keeps `E` on
every engine with a sound translation, along every chain of them, and for
every choice the reference leaves open (ties, order-free `FIRST`, clustered
groups). It does not carry upward, to the core or to `Profile.substrait`,
whose allowed sets are larger; a Substrait consumer gets `E` only through a
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
   bound. Today the reference raises where an operation would create a NaN
   and on a zero divisor ([No operation creates a NaN](reference-semantics.md#core-numbers-and-nulls));
   a finite operation whose result overflows to `±∞` (`exp(1000)`) will
   raise too
   ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)),
   with its precondition inferred as for integer overflow.
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

### The Polars example

Polars 2.1.0's characterization ([characterization/polars/README.md](../characterization/polars/README.md),
with strings, dates and casts in
[#570](https://github.com/AlexanderNenninger/substrait-lean/pull/570) and the
remaining items in
[#573](https://github.com/AlexanderNenninger/substrait-lean/pull/573)) lists
where Polars differs from the reference. Sorted by the three kinds:

Error side, no shim for a verified plan (15). The reference raises on each,
so a verified plan never reaches Polars's behaviour:

- integer `overflow` of `+ - ×`, negate and `**` (wraps,
  [int-arith](../characterization/polars/facts/polars-int-arith.json)),
  `abs(MIN)` ([int-abs](../characterization/polars/facts/polars-int-abs.json)),
  `MIN / -1` and `sum` of `i32`, `i64`
  ([int-divide](../characterization/polars/facts/polars-int-divide.json),
  [sum-int](../characterization/polars/facts/polars-sum-int.json));
- integer division and modulus by zero (`NULL`, int-divide,
  [int-modulus](../characterization/polars/facts/polars-int-modulus.json));
- doubles: `nan_creation`
  ([double-arith](../characterization/polars/facts/polars-double-arith.json)),
  division by zero
  ([double-divide](../characterization/polars/facts/polars-double-divide.json)),
  `x % 0`
  ([double-modulus](../characterization/polars/facts/polars-double-modulus.json)),
  `on_domain_error`, `on_log_zero`
  ([math-domain](../characterization/polars/facts/polars-math-domain.json)),
  `atan2(0, 0)` ([atan2](../characterization/polars/facts/polars-atan2.json)),
  `±∞` in `sum`, `avg`, `variance`, `std_dev`
  ([nonfinite-aggregates](../characterization/polars/facts/polars-nonfinite-aggregates.json));
- `date_range`, past 9999 and PL-2's panic (#570's date-range), and
  `substring_range` (#573's substring-range).

Value side, shimmed (30). Seven of these are a written argument with no run-time
cost: `round(mode='half_away_from_zero')`, `nulls_last`, `nan_max`,
`strip_chars(' ')`, `explode`'s and the set operations' NULL arguments, and
the quantile's `method`. The others are shims with a cost:

- truncating division and modulus of negative integers (`//` floors,
  int-divide, int-modulus), and the sign of a double modulus (double-modulus);
- an empty `SUM` (0, [sum-float](../characterization/polars/facts/polars-sum-float.json)),
  `avg` of integers ([avg-int](../characterization/polars/facts/polars-avg-int.json)),
  `CORR` of one pair ([corr](../characterization/polars/facts/polars-corr.json)),
  `mode`'s list ([mode](../characterization/polars/facts/polars-mode.json)),
  the rank of NULL ([rank](../characterization/polars/facts/polars-rank.json));
- `zero_sign` and `nan_kind` (`canon`, or `refines up to canon` in #568's
  terms), and `round` to negative digits
  ([round-digits](../characterization/polars/facts/polars-round-digits.json));
- decimal result types and `decimal_rescale`
  ([decimal-arith](../characterization/polars/facts/polars-decimal-arith.json)),
  the `i64` against `fp64` comparison, `sum`'s widening of `i8`, `i16`, and
  the implicit casts and literal types of #573;
- 0-based positions of `substring`, `strpos` and `list_extract`,
  `strpos`'s NULL, a regex's NULL without a match, `reverse` by graphemes
  (#570), and `list_null_order` (#573).

Open, native or `approx`: `tie_pick` and `tie_order` (Polars picks
deterministically, which the reference allows), `sum_order` and `stat_algo`
(`approx[D, ε]` within #85's bounds), and `log10`, `log2` an ulp off
([log-base](../characterization/polars/facts/polars-log-base.json)).

Refused: the shifts, `ntile`, `percent_rank`, `cume_dist` and seven string
functions have no Polars expression, and `<`, `min`, `max` of lists raise in
Polars where the reference does not, a raise the reference's raise set does
not cover.

So 15 of Polars's differences cost a verified plan nothing, 7 cost a
written argument, and the 23 run-time shims left each implement a value the
reference chose.

## The steps of #444

Each step is a PR or a short stack, and each ends in a theorem.

| Step | What lands | What it proves |
|---|---|---|
| 0 | This page. Wave 3's tables (#544 step 4) with a `group` column and the Python `Option`/`Fn` rows; `optionAccepts` read from the tables. | Nothing new; tests check the Lean and Python tables agree and that every function has a group. |
| 1a | The options table, `Choice`, `ProfileTable`, and `Profile.reference.table`. | `optionAccepts` equals the reference table's lookup (`#guard` over every group and option); no behaviour change. |
| 1b | `-0.0` and the signed NaN in `FloatFormat`, with `canon`. | `canon` is idempotent and order-preserving; every existing operation commutes with it on the reference's codes. |
| 1c | `Expr.AllowedP` and `Rel.AllowedP P` over the choice points, the core table, and `Rel.Allowed := Rel.AllowedP Profile.reference`. The `null_order` choice point for a key's `UNSPECIFIED` direction and the clustered order relation; the parser accepts both from here on (it refuses them until then). | `Rel.AllowedP_mono` (a profile with smaller choices allows fewer results), hence `Allowed_reference ⊆ Allowed_core`; `Rel.AllowedP_congr` (a call or operator that refines makes the plan refine); `⊑` and its transitivity. `Rel.eval_allowed`, `Rel.allowed_perm_eval` and `Rel.Refines` carry over unchanged. |
| 2 | `Profile.substrait`: every option `.asked yaml yaml`, `IEEE` zeros and NaNs, and `verify(semantics="substrait")`. | `Allowed_substrait ⊆ Allowed_core`; the diff with the reference as a generated list of the options where their choices differ (one zero, one NaN, `nan_creation`, the defaults). |
| 3a | `Profile.duckdb.table s`, from the facts, replacing the hand-written diff's documentation (its functions stay). | `Allowed_duckdb ⊆ Allowed_core` for every `s`; the lift's soundness as refinement: what DuckDB's SQL does is allowed under `Profile.duckdb` (`Rel.duckdb_sound` and #242's lemmas restated). |
| 3b | `obligations reference E` for each engine `E`, the shim table it reads, and the realizability table as its `reference` rows, with the CI check. | For DuckDB, `(duckdb, T_duckdb r) ⊑ (reference, r)`: `Rel.duckdb_shim_allowed` read as refinement, raise sets included. |
| 3c | The option dependency report: for a plan verified under the reference, the weakest set of the reference's constraints it still verifies under, and from it the shims each engine's translation needs. The option-wise transfer check: a proof under a profile `P` holds under `Profile.E` when, for every option in that set, `E`'s choices are within `P`'s. | For each plan, `verify` under the profile that keeps only that set of the reference's choices; the translation shims only those options, and an option in the set that the YAML does not define is an ST entry. The transfer check follows from `Rel.AllowedP_mono` per option, by lookup in the choices tables. |
| 4 | Substrait's function test cases in CI against `Profile.substrait`; disagreements recorded in `upstream/`. | Tested: `Rel.eval` under `Profile.substrait` gives each case's result or the plan is refused. |
| 5 | One query checked under the reference, translated to DuckDB and, once #271 has one, a second engine; and a plan checked under DuckDB's profile run on the second engine by the transfer check, or checked again there. | Soundness of the second engine's translation from `obligations reference E`; the query's proof reused by composition; the transfer check's verdict for the DuckDB-checked plan. |

Step 1b can run alongside 1a. Steps 2 and 3a both need 1c and touch
different tables. The Lean side of step 0 and 1a can merge into one PR if
wave 3 lands first.

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
one. The core is the full profile and the reference a deterministic one. The
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
kind at the granularity of table entries: an unverified search proposes an
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

### D7. Per-plan checks

Translators are proved once, entry by entry, as the lowering and the lift are
today, and single plans are checked only for translations sverify does not
own (another producer's plan, an engine's own SQL). No plan pays for a proof
at run time, and the generated tables already carry the proofs.

### D8. The reference's NULL order

Where a key's direction is `UNSPECIFIED`, the reference puts NULLs last in
both directions: DuckDB's default ([F2](../characterization/duckdb/facts/duckdb-F2.json))
and the default of the model's `SortKey` for hand-built values.
