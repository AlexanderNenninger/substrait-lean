# The loose core: design

Sverify's plans will mean one thing in Lean, a loose core semantics,
and every semantics sverify knows becomes a refinement of it: Substrait's,
the reference's and each engine's
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
This page is the design pass of step 3 of epic
[#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544). It
lists, per function, the points where profiles differ, gives the tables that
hold each profile's choices, says which values the core needs, and orders
#444's steps. Wave 3 of #544 builds its function tables in this shape.

Where a choice is still open, the page names the options with a
recommendation and lists it under [Open questions](#open-questions) for the
project owner. Everything else follows decisions already made on #185, #202,
#209, #257, #336, #427 and #444; [reference-semantics.md](reference-semantics.md)
records them.

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
inside the core without new options. Recommendation in [Q2](#q2-raises-in-the-core).

### Values of an option the YAML does not list

An engine sometimes does something none of the YAML's values describe:
DuckDB gives `0` for `x >> 64`
([`duckdb-R15-shift-right`](../characterization/duckdb/facts/duckdb-R15-shift-right.json)),
where Substrait's `shift_right` has no option. Its `-∞` for `ln(0)` is the
YAML's `on_log_zero: MINUS_INFINITY`, and needs nothing new. The core needs every profile's native
behaviour, so an option's behaviours are the YAML's values and the
behaviours an engine fact records, each extra one tagged with its fact.
Recommendation in [Q3](#q3-behaviours-outside-the-yaml).

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
| `null_order` (a sort key) | `NULLS_FIRST`, `NULLS_LAST` | the sort direction states it; `UNSPECIFIED` and `CLUSTERED` exist | stated by every key; others refused | `NULLS_LAST` by default ([F2](../characterization/duckdb/facts/duckdb-F2.json)) |
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
exactly one group; wave 3's tables give each function its group.

| Area | Group | Functions | Options |
|---|---|---|---|
| core | `int.arith` | `add`, `subtract`, `multiply`, `negate` on integers | `overflow` |
| core | `int.abs` | `abs` on integers | `overflow` |
| core | `int.div` | `divide` on integers | `overflow` (`MIN / -1`), `on_division_by_zero` |
| core | `int.mod` | `modulus` on integers | `on_division_by_zero`, `division_type`, `min_mod_neg_one` |
| core | `int.bit` | `bitwise_and`, `bitwise_or`, `bitwise_xor` | none |
| core | `int.shift` | `bitwise_shift_left`, `bitwise_shift_right` | `shift_range` |
| core | `dec.arith` | `add`, `subtract`, `multiply`, `negate`, `abs` on decimals | `overflow` (`ERROR` only), `decimal_rescale` |
| core | `dec.div` | `divide`, `modulus` on decimals | refused in every profile until [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27) |
| core | `fp.arith` | `add`, `subtract`, `multiply` on doubles | `rounding`, `nan_creation`, `zero_sign` |
| core | `fp.div` | `divide` on doubles, `sverify_fmod` | `rounding`, `on_division_by_zero`, `nan_creation`, `zero_sign` |
| core | `fp.elem` | `sqrt`, `exp`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `power` | `rounding`, `on_domain_error` |
| core | `fp.log` | `ln`, `log10`, `log2`, `logb` | `rounding`, `on_domain_error`, `on_log_zero` |
| core | `fp.round` | `round`, `floor`, `ceil` | `rounding` (`round` only) |
| core | `cmp` | `equal`, `lt`, `greatest`, `least`, `nanvl`, `is_null`, `not`, `and`, `or` | `nan_equality`, `nan_order`, `zero_sign` (doubles only) |
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
| aggregates | `agg.stat` | `variance`, `std_dev`, `covar_samp`, `covar_pop`, `corr` | `stat_algo`, `stat_degenerate` |
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
| relations | `rel.sort` | `orderBy`, a window's order | `null_order`, `tie_order` |
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

`#guard`s check that every `core` is the union of `yaml` and `extra`'s
behaviours, that ids are unique, and that every fact id names a file of
`characterization/*/facts/`.

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

A function's options are its group's. `optionAccepts` (`Parse.lean`) becomes
a lookup: an option is known for a function when its group lists it, and
accepted when the profile's choice meets the plan's preferences.

### The choices table

```lean
inductive Choice where
  /-- Any of these behaviours. -/
  | oneOf (bs : List Behaviour)
  /-- The plan's first preference among these; any of them where it states none. -/
  | asked (bs : List Behaviour) (dflt : List Behaviour)

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
boxes. Alternatives in [Q1](#q1-where-the-tables-live).

### The realizability table

For every option, the behaviour the reference chooses, and every engine:
native, a shim with its cost (an extra `CASE`, a cast to `HUGEINT`, a second
pass), or refused. Generated from `REALIZE` and the facts, published in
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
| NaN payloads | not observed by any function sverify models | No. Recommendation in [Q4](#q4-nan-payloads). |
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

## The steps of #444

Each step is a PR or a short stack, and each ends in a theorem.

| Step | What lands | What it proves |
|---|---|---|
| 0 | This page. Wave 3's tables (#544 step 4) with a `group` column and the Python `Option`/`Fn` rows; `optionAccepts` read from the tables. | Nothing new; tests check the Lean and Python tables agree and that every function has a group. |
| 1a | The options table, `Choice`, `ProfileTable`, and `Profile.reference.table`. | `optionAccepts` equals the reference table's lookup (`#guard` over every group and option); no behaviour change. |
| 1b | `-0.0` and the signed NaN in `FloatFormat`, with `canon`. | `canon` is idempotent and order-preserving; every existing operation commutes with it on the reference's codes. |
| 1c | `Expr.AllowedP` and `Rel.AllowedP P` over the choice points, the core table, and `Rel.Allowed := Rel.AllowedP Profile.reference`. | `Rel.AllowedP_mono` (a profile with smaller choices allows fewer results), hence `Allowed_reference ⊆ Allowed_core`. `Rel.eval_allowed`, `Rel.allowed_perm_eval` and `Rel.Refines` carry over unchanged. |
| 2 | `Profile.substrait`: every option `.asked yaml yaml`, `IEEE` zeros and NaNs, and `verify(semantics="substrait")`. | `Allowed_substrait ⊆ Allowed_core`; the diff with the reference as a generated list of the options where their choices differ (one zero, one NaN, `nan_creation`, the defaults). |
| 3a | `Profile.duckdb.table s`, from the facts, replacing the hand-written diff's documentation (its functions stay). | `Allowed_duckdb ⊆ Allowed_core` for every `s`; the lift's soundness as refinement: what DuckDB's SQL does is allowed under `Profile.duckdb` (`Rel.duckdb_sound` and #242's lemmas restated). |
| 3b | The realizability table, generated, and its CI check. | For DuckDB, realizability: `Allowed_duckdb(T_duckdb(plan)) ⊆ Allowed_reference(plan)`, which is `Rel.duckdb_shim_allowed` read as refinement. |
| 4 | Substrait's function test cases in CI against `Profile.substrait`; disagreements recorded in `upstream/`. | Tested: `Rel.eval` under `Profile.substrait` gives each case's result or the plan is refused. |
| 5 | One query checked under the reference, translated to DuckDB and, once #271 has one, a second engine. | Realizability for the second engine, from its table and #271's shims. |

Step 1b can run alongside 1a. Steps 2 and 3a both need 1c and touch
different tables. The Lean side of step 0 and 1a can merge into one PR if
wave 3 lands first.

## Open questions

### Q1. Where the tables live

- A. Lean is the source; Python mirrors it, and a test compares them (as the
  black boxes do). Recommended: Lean proves the refinement by `decide` on its
  own table, and the mirror costs one test.
- B. One data file (TOML or JSON) both read: Lean through `include_str` and a
  parser at elaboration. One source, but the kernel's proofs then depend on
  a parser.
- C. Python is the source and generates Lean (as `poe regen-lowering` does).
  One source, at the cost of a generated module to commit and check.

### Q2. Raises in the core

- A. The core allows raising everywhere, as the reference's correctness does
  today, and each profile states its raise set. Recommended: it keeps
  principle 4 and admits DuckDB's extra raises without options.
- B. The core raises only at named raise points (overflow, division by zero,
  domain, casts, the size hypothesis). Tighter, but every engine raise
  outside them (`<<` of a negative number) needs a new option.

### Q3. Behaviours outside the YAML

- A. An option's core set is the YAML's values and the engines' recorded
  extras, each with its fact. Recommended: every engine profile refines the
  core by construction.
- B. The core is the YAML's values only, and an engine behaviour outside them
  is a deviation the engine's translation shims. Closer to Substrait, but
  DuckDB's native `>>` then fails `Allowed_duckdb ⊆ Allowed_core`.

### Q4. NaN payloads

- A. A NaN is one of two codes, by its sign. Recommended: no function sverify
  models reads a payload, and `signbit` reads the sign.
- B. A NaN carries its payload. Faithful to IEEE, at the cost of 2⁵² codes per
  sign and no order among them.

### Q5. Rounding of doubles where the plan omits it

- A. The core leaves the YAML's five modes open, and the reference and every
  engine fix `TIE_TO_EVEN`. Recommended: it is what Substrait says, and #85's
  error bounds become theorems of the profiles that fix it.
- B. The core fixes `TIE_TO_EVEN`. Bounds proved in the core then hold on
  every profile, but `Profile.substrait` is narrower than the spec.

### Q6. Sort keys without a NULL order

- A. The parser keeps refusing `UNSPECIFIED` and `CLUSTERED`. Recommended
  until a frontend writes them: the Ibis producer and the SQL writer state
  all four parts of every key.
- B. The core reads `UNSPECIFIED` as `null_order` open, and `CLUSTERED` as
  "equal keys adjacent", so `Profile.substrait` accepts them.
