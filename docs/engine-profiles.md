# Engine profiles: the reference semantics and the engines

How a proof relates to the engines that run a plan. The evidence for each
engine is in [`characterization/`](../characterization/). This note sums up
the design and what Lean proves today.
The layers (the core, its profiles, the engines that run them) are in
[core, profiles and engines](core-and-profiles.md);
the classes of an engine's functions and which plans run on an engine are in
[core-semantics.md](core-semantics.md#which-plans-run-on-an-engine).

## The reference profile

`verify` proves things about `Rel.eval`, the reference semantics, the
core under the reference profile. It is
not a model of any engine, DuckDB included. Its principles, the decided
defaults (overflow and division by zero are errors, errors mean "may raise",
rewrites are refinements) and every row of its behaviour, with its status on
`main`, are in [reference-semantics.md](reference-semantics.md).

An engine runs a plan correctly when, on every input, it gives a result
the reference allows, or raises only where the reference may raise; resource
errors, such as running out of memory, are excluded
([engine correctness](reference-semantics.md#what-it-is)). Today Lean proves partial
correctness, `Rel.eval`'s rows or an error (`Rel.duckdb_shim_sound` below),
and for a plan proved to never raise the two agree (`Rel.duckdb_sound`).

The size hypothesis. Integers have their declared widths, and so do
lengths, positions and ranks. The reference assumes, as every engine's memory
guarantees, that every string has fewer than `2³²` characters, every
relation a window reads fewer than `2⁶²` rows, and every relation an aggregate
reads fewer than `2⁶³`. It is trusted and stated where
it is used: `Text.sizeCap` caps `CHARACTER_LENGTH`, `strpos`, `levenshtein`
and `ascii` at `2³²` (a cap no real string reaches), and `Rel.Small` is a
hypothesis of `Rel.mayIssues_sound`, `Rel.guardFree_sound` and
`Rel.duckdb_sound`. With it, and with input columns bounded by their types,
the range analysis proves that `ROW_NUMBER() - 1`, Ibis's `find`
(`strpos - 1`) and sverify's floor division do not overflow. It infers no
bound from the hypothesis for arithmetic the plan does on its own values
(`amount * 2`); that needs a precondition, which sverify infers.

## An engine profile and its diff

An engine's profile refines the loose core, and its row of the realizability
table is its diff against the reference
([core-semantics.md](core-semantics.md#the-realizability-table)). The
characterization records only where the engine differs from the
reference: which options it implements natively and which need a shim, its
settings (such as DuckDB's `error_on_division_by_zero`), the widths of its
accumulators, and its frontend quirks. Translating a plan for the engine
means applying that diff: writing each function in a form the engine
evaluates to the reference result, or refusing it where no shim exists.
Where the reference raises (overflow, NaN creation, a domain error), a plan
proved to never raise needs no shim, only the guard of a precondition
checked on the data ([What strictness buys](core-semantics.md#what-strictness-buys)).
`Rel.duckdb_sound` below proves this for DuckDB.

DuckDB is the first engine characterized this way:
[`characterization/duckdb/facts/`](../characterization/duckdb/facts/)
judges DuckDB's own sqllogictests and the fuzzer's findings against
Substrait's definitions and options, not against ISO SQL or DuckDB
([how facts are judged](../characterization/README.md)). Polars and Spark
followed, each with its profile and shims in Lean
([Polars as a profile](#polars-as-a-profile),
[Spark as a profile](#spark-as-a-profile)). That a profile
matches its engine is tested against the engine and trusted.

## Engines

[Engines](stability.md#engines) says which engines sverify supports and
which are in the 1.x promise; the [realizability table](realizability.md)
gives each engine's class on every option, its shims and its translation
theorem. DuckDB, Polars and Spark each have a profile, with the
translation from the reference proved (`Rel.duckdb_refines`,
`Rel.polars_sound`, `Rel.spark_sound`).

SQL strings go through SQLGlot and sverify's own lift: DuckDB's SQL
with `sv.sql(query, semantics="duckdb" | "reference")` (`sverify.sql_lift`),
whose two profiles are generated Lean modules
(`SubstraitLean/LiftDuckDB/Duckdb` and `Reference`). DataFusion's SQL planner
is not a frontend, and sverify does not run DataFusion. The reference is
Lean's reference profile, and DuckDB is the default oracle.

<a id="profiles-and-shims-in-lean-185-first-slice"></a>

## Profiles and shims in Lean

`core/Sverify/Core/Profile.lean` states the scalar part:

* An engine evaluation gives an `Outcome`, a value or an error.
* A `Profile` gives each function's outcome; `Expr.evalP` evaluates under
  one (strictly, left to right; a `CASE` takes one branch; a lambda runs on
  every element).
* `Profile.reference` raises exactly where `Safety.lean` reports an error,
  and `Expr.evalP_reference` proves that evaluating under it is `eval`,
  raising the first error `issues` reports. So the reference is one profile
  among others.
* `Profile.duckdb s` is the reference except where DuckDB 2.0 was probed
  to differ (`python -m sverify_dev.probe`, `characterization/duckdb/probes.json`,
  FACTS R15). With `ieee_floating_point_ops` on (the default), operations on
  doubles that have no value give NaN (`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`),
  a logarithm of 0 is `-∞`, and a double divided by zero is `±∞`; `atan2(0, 0)`
  is 0; `MIN % -1` raises; `<<` raises where bits are shifted out and `>>`
  gives 0 for shifts outside 0–63. Integers divided by zero follow
  `error_on_division_by_zero` (on by default since 2.0). `duckBin` and
  `duckUn` hold the differences; the settings are `DuckDBSettings`.
* The shims are generated. A shim rewrites an expression into one
  DuckDB evaluates to the reference's outcome. Its guards are two functions
  of the model: `UnFn.raise` (always an error, `Issue.raised`; DuckDB's
  `error()`) and `UnFn.isNum` (written `x IS NOT NULL`). So a shimmed plan is
  an ordinary plan, written and run like any other. `generate_lowering`
  (`SubstraitLean/LoweringSearch.lean`) is a metaprogram that runs at build
  time. For each construct (each constructor of `UnFn` and `BinFn`, its
  parameters being the signature and options) it first tries to prove the
  engine's function equal to the reference's. Where that fails it searches
  for a guarded template, `CASE WHEN g THEN error() ELSE f(x, y) END` (or a
  constant in place of `error()`), with `g` built from NULL tests and
  comparisons with constants. Each candidate is tested on sample arguments
  under both profiles, and the first that passes is proved for all arguments
  by a tactic and added as a declaration, so the kernel checks it. A
  construct with no entry fails the build and shows as `missing` in the
  coverage report (`substrait-check --lowering-coverage`, recorded in the
  golden test `tests/lowering/duckdb.expected`). `overflow` = `SATURATE` (`UnFn.fit`, which
  DuckDB has no function for) gets a `CASE` clamping to the width's bounds,
  which the search finds among `CASE` chains over constants the reference
  gives. `SILENT`'s wrap-around, `((x + 2^(w-1)) % 2^w + 2^w) % 2^w -
  2^(w-1)` in 128-bit arithmetic, is beyond the search: it is a hand-written
  schema (`LoweringSearch.duckdbSchemas`), still proved for each width by the
  kernel and marked as such in the coverage report. So are the guards for
  DuckDB's IEEE operations, which copy the reference's error
  conditions atom for atom: `nanCase` for `+ - * / % ^` of doubles (with the
  zero divisor for `/` and `%`), `FMath.inDomain` for the elementary
  functions, `0` for `MIN % -1`, and a range check for `>>`. `<<` multiplies
  by `2ʸ` from `Lowering.pow2Chain`, proved once by induction, and wraps
  around as `SILENT` does. The proofs generalize the special codes (`±∞`,
  NaN, `±1`) to variables with their order first, so that nothing evaluates
  their 600-digit values. The search does not run in a build: `poe regen-lowering`
  (`scripts/RegenLowering.lean`) runs it and writes each entry it found, with
  its proof, to `SubstraitLean/LoweringDuckDB/On`, one module per area
  (`Native`, `Integers`, `Doubles`, `Math`, `Bits`) and a `Table`, which `lake
  build` checks in parallel. The table is for DuckDB's default settings
  (`error_on_division_by_zero` and `ieee_floating_point_ops` on), the only
  ones sverify runs DuckDB with: its SQL for DuckDB assumes them, and
  `Lowering.duckdb` exists for `Profile.duckdb {}` alone. A plan meant to run
  under other settings has no proved lowering; tables for them are tracked in
  [an issue](https://github.com/AlexanderNenninger/substrait-lean/issues/241).
  CI checks every entry's proof; a local `lake build` takes them as
  proved unless run as `lake -R -Kcheck_generated=true build`
  (`engines/Sverify/Engines/Generated.lean`). A committed table that no longer fits fails the
  build: a proof stops checking when `Profile.duckdb` changes, and the table's
  `match` is not exhaustive when a function is added. `SubstraitLean/LoweringCache.lean`
  records each construct's template for the regeneration, which tries it first. `substrait-check --lowering-table` exports the
  templates, and `sverify.sql.lowering`, a small interpreter in the trusted path,
  writes them as DuckDB SQL: the DuckDB printer asks it first (`Dialect.lowered`),
  so the guards in DuckDB's SQL are the proved ones. `SubstraitLean/Lowering.lean` proves once that
  lowering with any such table is correct: `Lowering.lower_correct` (the
  lowered expression, under the engine's profile, has the reference's
  outcome, the same value or an error), and `Lowering.lowerRel_sound` for
  plans, by `Rel.evalI_mapExprs`. A template's guards are its outer chain of
  `CASE WHEN c THEN error(m)`, `m` the reference issue's name. A writer may drop
  the guards of issues a plan never meets (`Lowering.lowerWith`): where each
  dropped guard always evaluates and fires only at its own issue
  (`Lowering.GuardsFor`), `Lowering.lowerRelWith_sound` proves the run is
  `Rel.eval`'s or raises, on every catalog, and
  `Lowering.lowerRelWith_mayIssues_sound` takes the issues to drop from
  `Rel.mayIssues`, as `Rel.guardFree_sound` does. The kept guards need no new
  proof: the template with all its guards has the reference's outcome. DuckDB's
  generated guards are proved exact (`duckdbOn.guardsFor_none`, in
  `SubstraitLean/LoweringDuckDB/On/Guards.lean`), so its SQL without guards
  (`to_sql(guards=False)`) is `Rel.duckdb_guardFree_sound`. The
  search is the same for every engine; an engine's hand-written schemas are an
  argument of `generate_lowering` (DuckDB's in
  `SubstraitLean/LoweringDuckDB/Schemas.lean`). Equality saturation (lean-egg) was
  considered and not used: it proves equalities rather than finding terms,
  it is deprecated, and it needs Lean 4.30 and Rust.

* The lift is generated too: the lowering search run backwards.
  `SubstraitLean/DuckDBSQL.lean` states what DuckDB's SQL functions mean
  (`DuckFn`, at one signature each) under `semantics="duckdb"` and
  `"reference"`: `/` of integers divides as doubles, `%` of doubles is C's
  `fmod`, `log` is base 10, and with DuckDB's semantics `±∞`, NaN where
  DuckDB gives them. It is trusted, like a profile, and tested against the
  engine (oracle A). `generate_lift` (`SubstraitLean/LiftSearch.lean`)
  searches Substrait calls (a function, its arguments as they are or cast,
  every assignment of the options the parser accepts) and calls under one or
  two guards with constants, reads each with the parser itself, tests it on
  samples and proves the first that agrees, for every argument of the
  function's types. `substrait-check --lift-table` prints the table as JSON
  (golden: `tests/lowering/duckdb-lift.expected`) for `sverify.sql_lift` to
  read. A DuckDB function without an entry fails the build, unless the spec
  refuses it with a reason (`DuckFn.refused`). The search keeps a cache,
  `SubstraitLean/LiftCache.lean` (`substrait-check --lift-cache`), of the
  templates it found and of why a function's first candidate failed; it tries
  a cached template first. A cache entry is only a hint, still read by the
  parser and proved, and one the search does not reach can be seeded by hand
  (`source = "seeded: …"`). As for the lowering, a build does not search:
  `poe regen-lift` (`scripts/RegenLift.lean`) writes each entry with its proof
  to `SubstraitLean/LiftDuckDB/Duckdb` and `Reference`, one module per area
  (`Arith`, `Math`, `Compare`, `Casts`, `Aggregates`) and a `Table`, which
  `lake build` checks in parallel; an entry that no longer fits fails there.
  The parser is `partial`, so its reading of an entry is computed when the
  entries are generated rather than proved.

For a plan `verify` proves error-free from its contract, no shim is needed:
`Profile.duckdbWritten_faithful` shows that DuckDB's profile, with IEEE
operations on, agrees with the reference wherever the reference does not
raise, so guard elimination (`Rel.guardFree_sound`) gives
`Rel.duckdb_sound`: on every catalog that meets the preconditions, the
plan evaluated with DuckDB's functions gives `Rel.eval`'s rows. Two functions
DuckDB raises on where the reference gives a value, `MIN % -1` and `<<`, are
the SQL printer's (`Profile.duckdbWritten`): it writes them out even without
guards. The catalogue's benchmark queries are checked this way
(`verified_sql`).

A plan that may raise (an overflow check, a division) is covered too, by
partial correctness. `Lowering.duckdb_exact` shows that every lowered
expression, run with DuckDB's functions, gives the reference's value on every
row where it does not raise, and `Rel.duckdb_shim_sound` lifts this to plans
(`Lowering.lowerRel`): unless an expression raises on a row it is evaluated on, DuckDB
gives `Rel.eval`'s rows. So DuckDB returns the rows a contract is proved
about, or an error, never other rows. This needs neither a contract nor guard
elimination, so it covers left joins and windows too (`looseSub`). An engine
may evaluate an expression on fewer rows than the model (a hash join, a
pushed-down filter); that skips evaluations without changing a value, which
is the engine's own correctness. `verified_sql` in the catalogue rests on
this theorem; `guard_free` is the stronger fact that nothing raises.

Trusted: that `Profile.duckdb` matches DuckDB (tested on edge cases,
`tests/test_probe.py`),
and that the SQL printer prints the shimmed plan faithfully (`isNum` as `IS
NOT NULL` included).

## Polars and Spark as profiles

Each profile refines the loose core of [core-semantics.md](core-semantics.md), option by option.

### The Polars example

Polars 2.1.0's characterization ([engines/polars/facts/README.md](../engines/polars/facts/README.md)) lists
where Polars differs from the reference. Sorted by the three kinds:

Error side, no shim for a proved plan (15). The reference raises on each,
so a proved plan never reaches Polars's behaviour:

- integer `overflow` of `+ - ×`, negate and `**` (wraps,
  [int-arith](../engines/polars/facts/polars-int-arith.json)),
  `abs(MIN)` ([int-abs](../engines/polars/facts/polars-int-abs.json)),
  `MIN / -1` and `sum` of `i32`, `i64`
  ([int-divide](../engines/polars/facts/polars-int-divide.json),
  [sum-int](../engines/polars/facts/polars-sum-int.json));
- integer division and modulus by zero (`NULL`, int-divide,
  [int-modulus](../engines/polars/facts/polars-int-modulus.json));
- doubles: `nan_creation`
  ([double-arith](../engines/polars/facts/polars-double-arith.json)),
  division by zero
  ([double-divide](../engines/polars/facts/polars-double-divide.json)),
  `x % 0`
  ([double-modulus](../engines/polars/facts/polars-double-modulus.json)),
  `on_domain_error`, `on_log_zero`
  ([math-domain](../engines/polars/facts/polars-math-domain.json)),
  `atan2(0, 0)` ([atan2](../engines/polars/facts/polars-atan2.json)),
  `±∞` in `sum`, `avg`, `variance`, `std_dev`
  ([nonfinite-aggregates](../engines/polars/facts/polars-nonfinite-aggregates.json));
- `date_range`, past 9999 and PL-2's panic
  ([date-range](../engines/polars/facts/polars-date-range.json)), and
  `substring_range`
  ([substring-range](../engines/polars/facts/polars-substring-range.json)).

Value side, shimmed (30). Seven of these are a written argument with no run-time
cost: `round(mode='half_away_from_zero')`, `nulls_last`, `nan_max`,
`strip_chars(' ')`, `explode`'s and the set operations' NULL arguments, and
the quantile's `method`. The others are shims with a cost:

- truncating division and modulus of negative integers (`//` floors,
  int-divide, int-modulus), and the sign of a double modulus (double-modulus);
- an empty `SUM` (0, [sum-float](../engines/polars/facts/polars-sum-float.json)),
  `avg` of integers ([avg-int](../engines/polars/facts/polars-avg-int.json)),
  `CORR` of one pair ([corr](../engines/polars/facts/polars-corr.json)),
  `mode`'s list ([mode](../engines/polars/facts/polars-mode.json)),
  the rank of NULL ([rank](../engines/polars/facts/polars-rank.json));
- `zero_sign` and `nan_kind` (`canon`, or `observed` up to `canon`), and `round` to negative digits
  ([round-digits](../engines/polars/facts/polars-round-digits.json));
- decimal result types and `decimal_rescale`
  ([decimal-arith](../engines/polars/facts/polars-decimal-arith.json),
  [decimal-casts](../engines/polars/facts/polars-decimal-casts.json)),
  the `i64` against `fp64` comparison, `sum`'s widening of `i8`, `i16`, and
  the implicit casts
  ([implicit-casts](../engines/polars/facts/polars-implicit-casts.json)) and
  literal types ([literal-types](../engines/polars/facts/polars-literal-types.json));
- 0-based positions of `substring`, `strpos` and `list_extract`,
  `strpos`'s NULL, a regex's NULL without a match, `reverse` by graphemes,
  and `list_null_order`.

Open, native or `observed`: `tie_pick` and `tie_order` (Polars picks
deterministically, which the reference allows), `sum_order` and `stat_algo`
(`observed` within `ε`), and `log10`, `log2` an ulp off
([log-base](../engines/polars/facts/polars-log-base.json)).

Refused: the shifts, `ntile`, `percent_rank`, `cume_dist` and seven string
functions have no Polars expression, and `<`, `min`, `max` of lists raise in
Polars where the reference does not, a raise the reference's raise set does
not cover.

So 15 of Polars's differences cost a proved plan nothing, 7 cost a
written argument, and the 23 run-time shims left each implement a value the
reference chose.

`SubstraitLean/PolarsShims.lean` proves them, each
shim of `engines/polars/src/sverify_polars/shims.py` once, as `Polars.<name>`,
against a model of Polars's own functions taken from its facts (the trusted
part, as `Profile.duckdb` is for DuckDB):

- the value shims: `int_div_trunc` and `int_mod_trunc` give `Int.tdiv` and
  `Int.tmod`, `sum_empty_null` NULL for no values, `avg_int_declared` the
  reference's truncated mean (which its clamp leaves), `round_half_away`
  `roundMag`, `one_zero` `canon` on the float codes, `strpos_chars`
  and `substring_wrap` `Text.strpos` and `Text.substrWrap`, `null_order` the
  key order `sortLe`, and `tie_order` `List.mergeSort` (any stable sort of a
  total preorder is it);
- the guards, each flagging exactly the rows or groups where the reference's
  issue is (`int_overflows`, `div_overflows`, `zero_divisor`,
  `sum_leaves_i64`, `sum_makes_nan`, `makes_infinite` and
  `agg_makes_infinite`), so a guard refuses exactly the batches the
  precondition rules out. On Polars a double `SUM` is summed in Polars's own
  order (`sum_order`), so `agg_makes_infinite` flags the groups whose own sum
  overflows, which differ from the sequential sum's only at the edge;
- the error side: `Polars.written_faithful` (Polars, with the value shims,
  agrees with the reference wherever the reference reports no issue) and
  `Rel.polars_sound` (a plan `verify` proves free of issues, up to the
  assumed ones whose guards stay, runs on Polars as `Rel.eval`).

The Polars rows of `--options` name these theorems as their evidence. The
`clustered` row stays tested, and so do the rows these theorems do not cover.

### Polars as a profile

`Profile.polars` ([PolarsProfile.lean](../SubstraitLean/PolarsProfile.lean))
is the profile `verify(semantics="polars")` checks under, and the one
`--contract` takes with `"profile": "polars"`. It is an evaluable `Profile`,
as `Profile.duckdb` is, and it takes Polars's choice option by option:

| Option | `Profile.polars` | Polars 2.1.0 | Why |
|---|---|---|---|
| `division_type` (integer `//`, `%`) | `FLOOR` | `FLOOR` ([int-divide](../engines/polars/facts/polars-int-divide.json), [int-modulus](../engines/polars/facts/polars-int-modulus.json)) | Polars's own value, so the native route needs no shim |
| `float_overflow` | `INFINITY`, with no precondition | `INFINITY` ([double-arith](../engines/polars/facts/polars-double-arith.json)) | as under DuckDB's profile |
| `overflow` (integers) | `ERROR` | `SILENT` | tightened: wrapping rarely helps a query, and a proved plan never wraps |
| `on_division_by_zero` (integers) | `ERROR` | `NULL` | tightened, as the reference |
| `nan_creation`, `on_domain_error` | `ERROR` | `NAN` | tightened, as the reference |
| every other option | the reference's | the table above | the translation keeps its written arguments and shims there |

A plan states the choice: under `semantics="polars"` the Ibis producer
writes integer `//` and `%` as `divide` and `modulus` with
`division_type: FLOOR`, the parser reads them as `Expr.floorDivOf` and
`Expr.floorModOf`, templates in the reference's truncating operations that
cannot overflow on 64-bit operands, and `Write` writes them back as the
calls. So the checker needs no profile of its own: it checks the plan the
parser reads, and the report says `"profile": "polars"`. What is proved:

- `Profile.polars_idiv`, `Profile.polars_imod`: on 64-bit integers the
  templates are Polars's `//` and `%` (`Polars.floorDiv`, `Polars.floorMod`,
  the trusted model of `PolarsShims.lean`); `Profile.polars_zero_divisor`:
  a zero divisor raises.
- `Polars.elaborate_eq`: evaluating an expression under `Profile.polars` is
  evaluating its elaboration, each `//` and `%` replaced by its template,
  under the reference. A contract proved of the parsed plan holds of the
  plan under `Profile.polars`.
- `Rel.allowed_polars_core`: `Allowed_polars ⊆ Allowed_core`, from the
  choices table.

On the routes: a plan proved under `Profile.polars` runs on Polars by
`native`, where `sverify_polars.engine` runs Polars's `//` and `%` for the stated
calls and the translation's shims elsewhere. The SQL writer computes a
stated `FLOOR` on every dialect from the truncating operations, as
`Expr.floorDivOf` and `Expr.floorModOf` do, so the written plan runs on
DuckDB, Spark and Snowflake too; the route to DuckDB is refused by the
transfer check, which fails on `division_type`. The re-check route targets the
profile too: `--contract` with `"profile": "polars"` proves the reference
plan again, its unstated `//` and `%` being the reference's `TRUNCATE`,
which the translation shims. Tested, and trusted: that Polars computes
`Polars.floorDiv` and `Polars.floorMod` (`engines/polars/tests/test_polars_profile.py` runs
it against Python's floor division on random 64-bit values), and that the
translation writes the stated calls as Polars's operators.

### Spark as a profile

`Profile.spark` ([SparkProfile.lean](../SubstraitLean/SparkProfile.lean)) is
the profile `verify(semantics="spark")` checks under, and the one
`--contract` takes with `"profile": "spark"`. Its choices table,
`Profile.spark.table` ([EngineTables.lean](../SubstraitLean/EngineTables.lean)),
records Spark 4.3.0 under `SPARK_CONF` (ANSI mode on, `TIMESTAMP_NTZ`, UTC)
from its [facts](../engines/spark/facts/). Option by option:

| Option | `Profile.spark` | Spark 4.3.0, ANSI | Why |
|---|---|---|---|
| `float_overflow` | `INFINITY`, with no precondition | `INFINITY` ([double-arith](../engines/spark/facts/spark-double-arith.json)) | as under DuckDB's and Polars's profiles |
| `overflow`, `on_division_by_zero` | `ERROR` | `ERROR` ([int-arith](../engines/spark/facts/spark-int-arith.json), [int-divide](../engines/spark/facts/spark-int-divide.json)) | native: ANSI raises where the reference raises |
| `nan_creation`, `on_domain_error` | `ERROR` | `NAN`, NULL for a logarithm of `x ≤ 0` ([math-domain](../engines/spark/facts/spark-math-domain.json)) | tightened, as the reference; a proved plan never reaches them |
| `avg_int_result` | the reference's | `FP64` ([avg-int](../engines/spark/facts/spark-avg-int.json)) | shim `int_avg_decimal` |
| `null_order` | the reference's | first for an ascending key ([null-order](../engines/spark/facts/spark-null-order.json)) | shim `null_order`, a written argument |
| every other option | the reference's | the table | native, or the writer's shims |

Spark's profile states no choice of its own in a plan, so `Profile.spark`
evaluates as the reference (`Profile.spark_eval`), and the report of a
`"profile": "spark"` request is the reference's, marked `"spark"`. What it
adds is the route: a plan proved under it runs on Spark by `native`, and
on DuckDB by `transfer` where DuckDB's choices are within Spark's at every
option the proof depends on. What is proved
([SparkShims.lean](../SubstraitLean/SparkShims.lean)):

- `Shim.sum_empty_null`, with `Spark.partial_sums_fit`: a `BIGINT` `SUM`
  on Spark raises as soon as a partial sum leaves 64 bits, which depends on
  the order of the rows ([sum-int](../engines/spark/facts/spark-sum-int.json));
  the writer sums exact `DECIMAL(38,0)` values, and no partial sum of fewer
  than 10¹⁸ 64-bit values leaves 38 digits, in any order.
- `Shim.avg_trunc`, `Shim.null_order`, `Shim.one_zero`: the other shims give
  the reference's value, by the lemmas Polars's shims share
  ([Shims.lean](../engines/Sverify/Engines/Shims.lean)).
- `Spark.written_faithful` and `Rel.spark_sound`: Spark under ANSI, as the
  writer writes it, gives `Rel.eval`'s rows for a plan whose only issues are
  assumed ones, as `Rel.polars_sound` does for Polars. Its own values on the
  error side (NaN, a `date_add` wrapped past 2³¹ days, SP-2) are where the
  reference raises.
- `Spark.decimal_negate_sub`: Spark's `-x` and `abs` round a decimal past 34
  significant digits ([SP-1](../upstream/bugs/SP-1.json)); the writer
  negates as `0 - x` there, exact where its type keeps the scale (up to 37
  digits, or 38 at scale 6 or less), and refuses a `DECIMAL(38, s)` with
  `s > 6`.
- `Rel.allowed_spark_core`: `Allowed_spark ⊆ Allowed_core`.

Decimals run on Spark at the reference's types, which are Spark's own
up to 38 digits. Past them Spark cuts the scale to no less than 6
([decimal-arith](../engines/spark/facts/spark-decimal-arith.json)),
so a sum or product whose type would pass 38 digits at a scale above 6 is
refused. A double becomes a decimal as `round(x · 10ˢ)` in doubles, through
`BIGINT`, since Spark's own cast reads the double's shortest text
(`CAST(0.145 AS DECIMAL(10,2))` is 0.15 there, 0.14 in the reference), so a
target past 18 digits is refused. Division by an integer, which an `AVG`
of decimals is, is refused: Spark's decimal quotient rounds at a scale of
its own first.

A run on Spark reads the session's settings (`sverify._engine_settings`):
ANSI mode, `timestampType`, the session time zone, `caseSensitive` and
`escapedStringLiterals` refuse every run when they differ from `SPARK_CONF`;
`legacy.statisticalAggregate`, `decimalOperations.allowPrecisionLoss` and
`legacy.percentileDiscCalculation` refuse the plans whose options they
change. A run on another Spark version warns, and on another major version is
refused. Tested, and trusted: that Spark computes as the model says
(`engines/spark/tests/test_spark_profile.py`, `engines/spark/tests/test_sql_spark.py`).

## Engine profiles from outside

A package can add an engine profile without changing sverify. The checker
takes its engines as a list of `EngineProfile`s (`engines/Sverify/Engines/Tables.lean`):
each one's choices, observation rows, the theorem its translation from the
reference rests on, and its shims' costs. `builtinEngines` holds DuckDB's,
Polars's and Spark's, and every engine-wide fact (`Epsilon.statsProvedOn`,
`EngineRobust.signKeptOn`, the `--options` and `--realizability` tables) is
computed over the list.

The package's Lean side requires this repository, states its entry, and
checks it with `#check_engine_profiles`, which fails the build unless every
theorem its rows name exists and its rows are well-formed, within the core,
consistent and evidenced. It then builds a checker of its own,
`Substrait.Checker.checkerMain (builtinEngines ++ [its entry])`, a superset of
`substrait-check`. [`SubstraitCheckExamples/DummyEngine.lean`](../SubstraitCheckExamples/DummyEngine.lean)
does this for a test profile.

Its Python side registers a `sverify.profiles.ProfilePlugin` under the
entry-point group `sverify.profiles`. That group is where sverify finds
engines, and the only place:
DuckDB and Snowflake's dialect register theirs there too, from
`sverify._builtin`, and Polars and Spark from their engine packages
(`engines/polars/` and `engines/spark/`, the distributions `sverify-polars`
and `sverify-spark`, which `sverify[polars]` and `sverify[spark]` install). `tests/test_engines_table.py` checks that with the entry points
gone sverify names no engine.

```toml
[project.entry-points."sverify.profiles"]
myengine = "my_package:PROFILE"
```

Every field but `engine` is optional:

| field | what it gives |
|---|---|
| `engine` | the engine's name, its profile's in the checker's tables |
| `versions` | the versions its facts were probed at; empty for a profile whose versions the checker carries, as sverify's own |
| `translation` | the translation from the reference, as a route line names it; empty for none, so a route takes the reference's |
| `checker` | a `substrait-check` built over `builtinEngines` and this profile |
| `settings` | the engine settings the profile assumes (`Setting`), checked before a routed run |
| `shim_text` | what each of its shims does, as a route line says it |
| `installed_version` | the engine version this process runs |
| `restore` | how the user puts a setting back |
| `runner` | runs a written plan over a `Connection`'s tables: `runner(con, plan_json, session, *, keep, finite, tie_free)` |
| `local` | a `Connection` takes the engine as the one it runs plans on |
| `optional` | outside the 1.x promise: `sverify.engines.ENGINES` leaves it out |
| `session` | recognises a session of the engine passed as `engine=` (a Spark session) |
| `modules` | the modules a run on it needs |
| `read_settings` | reads the named settings in a session, or in the one the next run uses |
| `dialect` | the `sverify.sql.Dialect` that `to_sql` writes |
| `title` | the engine's name as prose and generated tables write it (`DuckDB`) |
| `run_tables` | runs a written plan over Arrow tables by name: `run_tables(plan_json, tables, *, guard_free=False, finite=True)`; `sverify.engines.run_sharded` runs its shards with it |
| `guard_free_theorem` | the theorem that covers `run_tables(..., guard_free=True)`, the run without the checks a `guard_free` contract report discharged |
| `fallbacks` | the nodes of a written plan the engine runs outside its chosen executor (Polars's in-memory nodes of a streaming plan), which a route records and `streaming="require"` refuses |

Entries for one engine are merged field by field, so one package can add a
profile to an engine whose dialect another ships: Snowflake's dialect is
sverify's, and its profile, translation and checker come from the private
evidence repository. Two entries that set a field differently warn, and the
first one's value is kept.

Installed, a plugin's checker is the one sverify runs (`$SVERIFY_CHECKER`
still comes first), `verify(semantics=<engine>)` checks under its profile,
`sverify.routes.choose` routes plans to the engine with their class, and a
runner and a dialect give it `connect`, `run` and `to_sql` as sverify's own
engines have them (`tests/test_profile_plugins.py`,
`tests/test_engines_table.py`). An engine with a SQL dialect and no profile
gets the reference's translation, with no class claimed.

## The translations today

Each engine reaches the reference through a translation, a function from
a plan to something the engine runs. Lean proves the shims a translation
applies and that the shimmed plan refines the reference under the engine's
profile (the theorems in [Engines](#engines)); the code below that writes the
shimmed plan for the engine is trusted, and tested against `Rel.eval`:

| engine | translation | where |
|---|---|---|
| Polars | `sverify_polars.engine` (LazyFrame) | Python |
| DuckDB, Snowflake, Spark | `sverify.sql.to_sql` with a `Dialect` | Python |

A translation compensates for its engine where it can (an exact `SUM`
through `DECIMAL(38,0)`, `canonical` doubles, explicit `NULLS FIRST/LAST`,
guards that raise) and refuses the plan where it cannot (`UnsupportedError`).
"Raise rather than differ" is the standard each one is tested against:
`Rel.eval` (`lean_rows`), another engine's rows, or a raised error. Guard
elimination (`analysis/Sverify/Analysis/Guards.lean`) is the part already proved in Lean.

### Polars

Polars runs Lean's own serialisation of the checked plan: the plan as
`substrait-check --write` writes it back out from the parsed `Rel`
(`sverify.engines.written_plan`), and the delta plans of `--delta`, which use the same
writer. `sverify_polars/engine.py` translates only that small, canonical form
to a `LazyFrame` and raises `UnsupportedError` on anything else. It does not go
through Ibis's Polars backend, which would compile a different plan. The
translator pins the semantics and takes no Polars defaults:

* Filters and join conditions keep a row only when it is TRUE. `and`/`or` are
  written out as Kleene `and3`/`or3`. Equi-join keys never match on NULL.
  Semi and anti joins keep the left rows with (without) a TRUE match, so an
  anti join keeps a row whose key is NULL. Lean writes an outer join as a
  left join plus the unmatched right rows (an anti join), padded with NULLs.
* Rows come out in `Rel.eval`'s order. Joins are left-major, with a left
  join's padded row in its place, and windows emit their sorted order. Sorts
  are stable, so ties keep their input order, and `DISTINCT` keeps the first
  of each set of equal rows in place. So `FetchRel` takes the same rows as
  Lean, and the tests compare Polars with Lean row for row.
* Doubles compare, join, partition and sort with one zero and one NaN
  (`-inf < … < 0.0 < … < inf < NaN`), as the reference reads the float codes. Sorts place NULLs
  as each key says. `DISTINCT` compares rows as `Value`s: NULLs are equal,
  and so are -0.0 and 0.0, and all NaNs.
* Aggregates (`aggregateEval`): one row per group, in order of first
  occurrence (or exactly one without `GROUP BY`), grouping as `DISTINCT`
  compares. Each measure skips NULLs and the rows its `FILTER` drops;
  `DISTINCT` measures keep the first of equal values. Integer `SUM` is exact
  and raises `IntegerOverflow` outside 64 bits, where DataFusion wraps. `SUM`
  and `AVG` of doubles are the exact sum and mean rounded once
  ([correctly rounded sums](reference-semantics.md#of-doubles)),
  whatever the order of the rows.
* Strings are sequences of Unicode scalar values: `character_length`,
  `strpos` and `substring` count characters, and `substring` with
  a start below 1 keeps only the positions that exist. `LIKE` escapes with a
  backslash, and a trailing one stands for itself. `UPPER`, `LOWER` and
  regular expressions are black boxes in Lean; Polars computes them with the
  Rust code DataFusion uses.
* `date_part` and `date_trunc` follow `core/Sverify/Core/Time.lean`: parts
  within a day are integer arithmetic on the microseconds, the calendar comes
  from chrono (as in DataFusion), and `date_part` is NULL outside the years
  chrono represents.
* Integers are unbounded in Lean. Polars computes on 128 bits, and a result
  outside 64 bits raises `IntegerOverflow`, where DataFusion wraps silently
  (`2^62 + 2^62` gives `-2^63`). Integer division and remainder truncate
  toward zero, as `Int.tdiv` and `Int.tmod` do (Polars' own operators floor).
* Runtime errors are the `Issue`s of `analysis/Sverify/Analysis/Safety.lean`: division by
  zero, `MIN / -1`, bad `POWER`s, out-of-range casts, regular expressions
  that do not compile, and calendar functions outside the reference's timestamps
  (0001-01-01 to 9999-12-31). Each expression
  carries a per-row flag for each one, masked by `CASE` as `Expr.issues`
  masks it. The operator raises the matching error if a flag is set on a row
  it evaluates. Polars runs filters where the plan puts them, so a filter
  guards the projections above it. DataFusion merges filters, which is what
  `Rel.loose` models.
* Doubles divide in numpy: Polars divides a column by a constant by
  multiplying with its reciprocal, which rounds differently.

`engines/polars/tests/test_polars.py` runs every golden fixture (among them sorts,
`DISTINCT`, semi, anti and outer joins, and the string and time functions),
the window and rewrite queries of the other suites, and every delta plan of
the example pipelines on both engines. It checks Polars against DuckDB as bags and
against Lean's `Rel.eval` in order. It also has targeted tests for NULL join
keys, three-valued filters, NULL and NaN order in windows, overflow, and each
runtime error and its guards. The
incremental-view tests run on both engines.

`python/tests/test_backends.py` runs every Ibis operation the coverage
harness verifies on random tables, on Polars and DuckDB against DuckDB running
Ibis's own SQL, and generates its Snowflake SQL and runs its Spark SQL on a local Spark session; `test_text.py` and `test_time.py` run their edge
cases on all three engines.

Known gaps: the writer gives virtual tables placeholder `i64` column types and
writes `FetchRel`'s deprecated `offset`/`count`, both of which DataFusion's
consumer rejects. Doubles in a
virtual table come out as their integer codes. The translator refuses `lt`
on strings and booleans; the model compares strings by code point
([reference semantics](reference-semantics.md#strings)).

### DuckDB, through generated SQL

`engine="duckdb"` runs plans on [DuckDB](https://duckdb.org) as SQL that
`sverify.sql.to_sql(plan, DUCKDB)` generates from them. DuckDB's Substrait
extension is not used. Like Polars, DuckDB runs Lean's written plans over the
tables of `con`, which are copied into a fresh in-process database for each
run.

The SQL generator (`python/src/sverify/sql/`) reads Substrait JSON as
`Parse.lean` does. It accepts exactly the plans `substrait-check` accepts and
raises `UnsupportedError` on everything else. It then writes SQL whose result is
`Rel.eval`. The query spells out every semantic choice and leaves none to
the engine:

* subqueries name their columns `c0, c1, …`;
* integers are `BIGINT`, and overflow raises (DataFusion wraps around);
* division and remainder truncate; where DataFusion fails at run time
  (division by zero, `MIN / -1`, bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and the SQL raises;
* doubles have one zero and one NaN (`-inf < … < 0.0 < … < inf < NaN`) in
  comparisons, joins, partitions and sorts, and −0.0 is made 0.0 wherever it
  could arise;
* every `ORDER BY` key says `NULLS FIRST`/`LAST`;
* filters keep only TRUE rows; semi and anti joins are `[NOT] EXISTS` over
  the rows where the condition is TRUE;
* `DISTINCT` groups by the same keys as a window partition, so equal means
  equal as `Value`s;
* aggregates group by the same keys as `DISTINCT`; a `DISTINCT` measure
  counts the first row of each value, integer `SUM` raises outside 64 bits,
  and a `SUM` or `AVG` of doubles is the engine's own, within the plan's
  bound of the reference's correctly rounded sum
  ([correctly rounded sums](reference-semantics.md#of-doubles));
* strings: lengths and positions count characters, a negative `substring`
  start counts from the end unless the plan asks for `LEFT_OF_BEGINNING`
  (either way the start is normalized before it reaches the engine), and
  `LIKE` names its escape character;
* `date_part` and `date_trunc` use the engine's calendar functions where they
  agree with `core/Sverify/Core/Time.lean` (ISO weeks, `dow` from Sunday,
  milliseconds within the minute), and the SQL raises where DataFusion's
  calendar truncation fails;
* below a `FETCH`, a window or a sort, an ordinal column carries Lean's list
  order, so `LIMIT` and ties in sorts and windows pick Lean's rows, and a
  sorted result comes out in Lean's order.

Engine differences go through the hooks of a `Dialect`
(`sverify/sql/core/_base.py`). DuckDB's is `sverify/sql/duckdb.py`.

`python/tests/test_sql.py` checks the generator. Every golden fixture and every
delta plan of the incremental fixtures and example pipelines runs on DuckDB
with random tables. The results must agree with Lean's `Rel.eval` (row for row, in Lean's order, when `FETCH` or a window
makes order matter). The file also has targeted tests for engine traps: NULL
join keys, three-valued logic, NULL ordering in windows, refused integer
division, overflow, and NaN and signed zeros. It keeps snapshots of the
generated SQL in `python/tests/sql_snapshots/`. The incremental, window,
rewrite and ASOF differential tests run on DuckDB too.

### Snowflake

The checks below run on an emulator, [fakesnow](https://github.com/tekumara/fakesnow).
Sverify has no Snowflake profile or route yet: Snowflake runs the SQL
sverify writes.

`to_sql(plan, SNOWFLAKE)` (from `sverify.sql.snowflake`) writes checked plans
and Lean delta plans as Snowflake SQL. The SQL is written to match Lean where
Snowflake's documented behaviour differs:

* integers are `NUMBER(38,0)` and are checked against the 64-bit range;
  division and remainder truncate (through `MOD`, as `/` rounds to six
  decimals), and `CAST(double AS BIGINT)` truncates and raises out of range;
* timestamps are `TIMESTAMP_NTZ(6)`; weeks, days of the week and truncation
  to a week use the ISO functions, independent of the session's `WEEK_START`;
* backslashes and control characters in strings are escaped;
* every identifier is quoted, so create tables and columns with quoted
  lower-case names.

Where Snowflake can't match, the plan is refused (`UnsupportedError`) or the query
raises when it would answer differently:

* FETCH over a named table is refused: Snowflake tables have no row order.
  A `SUM` or `AVG` of doubles runs natively, within the plan's bound of the
  reference's correctly rounded sum
  ([correctly rounded sums](reference-semantics.md#of-doubles));
  over a moving window frame the writer adds the frame's values anew
  (`window_float_sum`).
  Windows and sorts are refused too, unless you pass `deterministic=True` to
  promise there are no ties on their keys (a contract report's
  `deterministic` says so for windows).
* Interval-valued expressions (`ts1 - ts0`) are refused: Snowflake has no
  interval type.

Time columns must be `TIMESTAMP_NTZ`, and string columns must have no
collation. `python/tests/test_sql_snowflake.py` snapshots the SQL for every
fixture and delta plan, parses it with sqlglot's Snowflake parser, and runs it
on [fakesnow](https://github.com/tekumara/fakesnow) against Lean's `Rel.eval`,
along with sorts, `DISTINCT`, aggregates, semi, anti and outer joins and
string functions.
fakesnow emulates Snowflake on DuckDB, so this checks the SQL and says nothing
about Snowflake's behaviour. To run the same checks on a real account, set `SNOWFLAKE_ACCOUNT`,
`SNOWFLAKE_USER`, a credential (`SNOWFLAKE_PASSWORD`,
`SNOWFLAKE_AUTHENTICATOR` or `SNOWFLAKE_PRIVATE_KEY_FILE`) and
`SNOWFLAKE_WAREHOUSE`/`DATABASE`/`SCHEMA`.

### Spark

`to_sql(plan, SPARK)` (from `sverify_spark.dialect`) writes checked plans and
Lean delta plans as Spark SQL, for Spark 4 and Databricks SQL. With the
`spark` extra, `sverify.engines.run(con, plan, "spark")` runs a plan over a
connection's tables on a local session (or on the session you pass as the
engine). The session needs the
settings of `SPARK_CONF`: ANSI mode
(`spark.sql.ansi.enabled`), without which an overflow wraps around and a bad
cast gives NULL, plus a pinned time zone, NTZ timestamps, case-sensitive
names and backslash escapes in string literals. The SQL matches Lean where
Spark differs:

* integers are `BIGINT`; division is `div` (`/` gives a double) and
  remainder `%`, both truncating; a `SUM` adds `DECIMAL(38,0)` values, since
  Spark raises when a partial sum overflows even if the total fits;
* doubles divided by zero raise, as the reference does (`on_division_by_zero`
  = ERROR); a plan asking for IEEE gets a `CASE` for ±inf or NaN;
  `CAST(double AS BIGINT)` is range-checked first (Spark saturates at 2⁶³);
  `FLOOR` and `CEIL` (which return `BIGINT`) keep NaN, ±inf and large values;
* timestamps are `TIMESTAMP_NTZ` and intervals `INTERVAL DAY TO SECOND`;
  `date_trunc` returns a time-zone timestamp, so truncation is computed on
  `TIMESTAMP_NTZ` and `DATE` values;
* backslashes and control characters in strings are escaped, and every
  identifier is quoted with backticks.

Spark refuses, as Snowflake does, FETCH and sorts or windows over a named
table without `deterministic=True` (tables have no row order), and so `SUM` or
`AVG` of doubles over one. It also refuses `POWER` of doubles, which is Java's
`Math.pow` (within 1 ulp of C's).

String columns must use the default `UTF8_BINARY` collation (code point
order). `engines/spark/tests/test_sql_spark.py` snapshots the SQL, parses it with
sqlglot's Spark parser, and runs the Snowflake suite's queries, the hooks
and `date_part`/`date_trunc` at the calendar's edges on a local Spark session
against `Rel.eval`; `test_backends.py` runs every coverage case there. The
session needs a JVM (Java 17 or 21: `JAVA_HOME` or `java` on `PATH`), or the
Spark tests are skipped (`poe test-spark` runs them).

<a id="decimals-27"></a>

### Decimals

The reference computes a `DECIMAL(p, s)` as its unscaled integer, exactly, and
raises where a result needs more than `p` digits. `substrait-check --write`
writes decimal plans back as Substrait's own typed calls and casts, and
refuses any it cannot (a plan whose written form does not parse back to the
same `Rel`).

Of the SQL dialects, DuckDB and Spark run decimal plans (`Dialect.decimals`;
Spark's are in [Spark as a profile](#spark-as-a-profile)), and Snowflake
refuses them. Polars runs them too, see [below](#decimals-on-polars). DuckDB computes `+`, `-` and
`×` exactly, and rounds half away from zero when a cast drops decimal places,
as the reference does. Its translation compensates where DuckDB differs:

| Reference | DuckDB by itself | Translation |
|---|---|---|
| a result has the plan's `DECIMAL(p, s)` | its own result types | `CAST(… AS DECIMAL(p, s))` around each operation |
| `×` is exact up to 38 digits | `DECIMAL(15, 2) × DECIMAL(15, 2)` is a `DECIMAL(18, 4)`, which overflows | the left operand is cast to `DECIMAL(38, s)` first |
| decimal → integer truncates toward zero | rounds half away from zero | `CAST(TRUNC(x) AS BIGINT)` |
| decimal → double is correctly rounded | converts the unscaled value and divides, which can round twice | `CAST(CAST(x AS VARCHAR) AS DOUBLE)` |
| `SUM` has ten more digits | `DECIMAL(38, s)` | cast to `DECIMAL(p + 10, s)` |
| `AVG` is a `DECIMAL(p + 4, s + 4)`, rounded half away from zero | a `DOUBLE` | `SUM` and `COUNT` divided in `HUGEINT`, rounded half away from zero, cast back to the decimal |

`Profile.duckdb` is the reference on decimals: these compensations are what
make that true of the SQL, and they are tested against `Rel.eval`
(`tests/test_ibis_decimal.py`), not proved.

#### Decimals on Polars

Polars computes every `+`, `-`, `×` and `/` of decimals as a
`Decimal(38, max(s₁, s₂))`, rounds half to even, and averages to a `Float64`
([polars-decimal-arith](../engines/polars/facts/polars-decimal-arith.json),
[polars-decimal-casts](../engines/polars/facts/polars-decimal-casts.json)).
`sverify_polars.engine` keeps each value in the plan's `Decimal(p, s)` and computes
the rest on the unscaled values (`to_physical`, an `Int128`):

| Reference | Polars by itself | Translation |
|---|---|---|
| a result of more than `p` digits raises | raises past 38 digits | checks `p` (`fit_decimal`) |
| `×` is exact at scale `s₁ + s₂` | rounds to `max(s₁, s₂)`, half to even | the product of the unscaled values, where it fits `p` digits |
| a smaller scale rounds half away from zero | half to even | `decimal_round_half_away` (`Polars.decimal_round_half_away`) |
| `AVG` is a `DECIMAL(p + 4, s + 4)`, half away from zero | a `Float64` | `SUM` and `COUNT`, divided by `decimal_div_half_away` (`Polars.decimal_div_half_away`) |
| `SUM` of no values is NULL | 0 | `sum_empty_null` |
| a double becomes `x · 10ˢ`, rounded once, then half away from zero | the same product, half to even | `round_half_away` on the product; a scale over 22, where Polars's `10ˢ` is inexact, is refused |
| decimal → double is correctly rounded, → integer truncates, comparisons are exact | the same | native |

`engines/polars/tests/test_polars_decimal.py` runs each operation's written plan on Polars
and on DuckDB against `Rel.eval`, and the 40 proved catalogue queries with
decimal columns run on Polars (`catalogue/status.json`).

#### `MIN` and `MAX` of doubles on Polars

The reference orders doubles by their codes: NaN above `+∞`, one zero.
Polars's `min` and `max` skip NaN unless every value is NaN
([polars-min-max-nan](../engines/polars/facts/polars-min-max-nan.json)),
and keep whichever zero `f64::min` picks
([polars-min-max-zero](../engines/polars/facts/polars-min-max-zero.json)),
in aggregates and over windows, on the streaming engine:

| Reference | Polars by itself | Translation |
|---|---|---|
| `MIN` is NaN only when every value is NaN | the same | `min_ignore_nan`: Polars's `min`, read with `one_zero` (`Polars.min_ignore_nan`) |
| `MAX` of a group with a NaN is NaN | skips NaN | `max_nan_greatest`: NaN where the group holds one (`Polars.max_nan_greatest`) |
| `MIN` and `MAX` of `0.0` and `-0.0` are `0.0` | `-0.0` for `min` on macOS arm64 | `one_zero` on the result |
| no values give NULL | the same | native |

`engines/polars/tests/test_polars_shims.py` runs grouped, global, filtered, `DISTINCT` and
windowed `MIN` and `MAX` of these cases on Polars, DuckDB and `Rel.eval`.
