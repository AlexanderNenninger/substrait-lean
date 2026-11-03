# Engine profiles: the reference semantics and the engines

How a proof relates to the engines that run a plan. The design work lives in
epic [#185](https://github.com/AlexanderNenninger/substrait-lean/issues/185)
(which supersedes the first design for #23), and the evidence for each engine
in [`characterization/`](../characterization/). This note sums up what was
decided there; where the two differ, #185 wins.

## The reference model

`verify` proves things about `Rel.eval`, the **reference semantics**. It is
not a model of any engine, DuckDB included. Its principles, the decided
defaults (overflow and division by zero are errors, errors mean "may raise",
rewrites are refinements) and every row of its behaviour, with its status on
`main`, are in [reference-semantics.md](reference-semantics.md).

An engine runs a plan **correctly** when, on every input, it gives
`Rel.eval`'s rows or fails.

**The size hypothesis.** Integers have their declared widths, and so do
lengths, positions and ranks. The reference assumes, as every engine's memory
guarantees, that every string has fewer than `2⁶²` characters and every
relation a window reads fewer than `2⁶²` rows. It is trusted and stated where
it is used: `Text.sizeCap` caps `CHARACTER_LENGTH`, `strpos`, `levenshtein`
and `ascii` at `2⁶²` (a cap no real string reaches), and `Rel.Small` is a
hypothesis of `Rel.mayIssues_sound`, `Rel.guardFree_sound` and
`Rel.duckdb_sound`. With it, and with input columns bounded by their types,
the range analysis proves that `ROW_NUMBER() - 1`, Ibis's `find`
(`strpos - 1`) and sverify's floor division do not overflow. It infers no
bound for arithmetic the plan does on its own values (`amount * 2`); that
still needs a precondition, or the inferred bounds of #244.

## An engine profile is a diff

An engine's characterization records only where it differs from the
reference: which options it implements natively and which need a shim, its
settings (such as DuckDB's `error_on_division_by_zero`), the widths of its
accumulators, and its frontend quirks. Translating a plan for the engine
means applying that diff: writing each function in a form the engine
evaluates to the reference result, or refusing it where no shim exists.

DuckDB is the first engine characterized this way:
[`characterization/duckdb/FACTS.md`](../characterization/duckdb/FACTS.md)
judges DuckDB's own sqllogictests and the fuzzer's findings against
Substrait's definitions and options, not against ISO SQL or DuckDB. The plan
is to state each profile in Lean and prove the shims (`shim_correct` in
#185); engine fidelity itself stays tested, not proved.

## Engine tiers

From [#211](https://github.com/AlexanderNenninger/substrait-lean/issues/211):

| Tier | Engines | Meaning |
|---|---|---|
| **1** | DuckDB | Characterized as a diff against the reference. Every reference behaviour is native, shimmed or refused, the shims are proved, and CI replays the engine's own tests plus fuzzing. In progress: until #185's profile work lands, DuckDB is Tier 1 in intent. |
| **2** | Polars, Spark, DataFusion | Run checked plans and are differentially tested against `Rel.eval` in CI, with known deviations documented. Not yet characterized or proved. Polars and Spark aim for Tier 1. |
| **3** | Snowflake | Aspirational: sverify writes the SQL and checks it on an emulator (fakesnow), never on a real account ([#63](https://github.com/AlexanderNenninger/substrait-lean/issues/63)). |

Work on the Tier 2 and 3 backends is paused until the generated lowerings
land (#241, then #271).

SQL strings go through SQLGlot and sverify's own lift (#231): DuckDB's SQL
with `sv.sql(query, semantics="duckdb" | "reference")` (`sverify.sql_lift`,
#239), whose two profiles are Python data for now. DataFusion's SQL planner
is no longer a frontend (#211); DataFusion stays an execution backend.

## Profiles and shims in Lean (#185, first slice)

`SubstraitLean/Profile.lean` states the scalar part:

* An engine evaluation gives an **`Outcome`**, a value or an error.
* A **`Profile`** gives each function's outcome; `Expr.evalP` evaluates under
  one (strictly, left to right; a `CASE` takes one branch; a lambda runs on
  every element).
* **`Profile.reference`** raises exactly where `Safety.lean` reports an error,
  and `Expr.evalP_reference` proves that evaluating under it is `eval`,
  raising the first error `issues` reports. So the reference is one profile
  among others.
* **`Profile.duckdb s`** is the reference except where DuckDB 2.0 was probed
  to differ (`python -m sverify_dev.probe`, `characterization/duckdb/probes.json`,
  FACTS R15). With `ieee_floating_point_ops` on (the default), operations on
  doubles that have no value give NaN (`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`),
  a logarithm of 0 is `-∞`, and a double divided by zero is `±∞`; `atan2(0, 0)`
  is 0; `MIN % -1` raises; `<<` raises where bits are shifted out and `>>`
  gives 0 for shifts outside 0–63. Integers divided by zero follow
  `error_on_division_by_zero` (on by default since 2.0). `duckBin` and
  `duckUn` hold the differences; the settings are `DuckDBSettings`.
* **The shims are generated** (#241). A shim rewrites an expression into one
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
  schema (`LoweringSearch.schema?`), still proved for each width by the
  kernel and marked as such in the coverage report. So are the guards for
  DuckDB's IEEE operations (#242), which copy the reference's error
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
  under other settings has no proved lowering; #241 tracks adding tables for
  them. CI checks every entry's proof; a local `lake build` takes them as
  proved unless run as `lake -R -Kcheck_generated=true build`
  (`SubstraitLean/Generated.lean`). A committed table that no longer fits fails the
  build: a proof stops checking when `Profile.duckdb` changes, and the table's
  `match` is not exhaustive when a function is added. `SubstraitLean/LoweringCache.lean`
  records each construct's template for the regeneration, which tries it first. `substrait-check --lowering-table` exports the
  templates, and `sverify.sql.lowering`, a small interpreter in the trusted path,
  writes them as DuckDB SQL: the DuckDB printer asks it first (`Dialect.lowered`),
  so the guards in DuckDB's SQL are the proved ones. `SubstraitLean/Lowering.lean` proves once that
  lowering with any such table is correct: **`Lowering.lower_correct`** (the
  lowered expression, under the engine's profile, has the reference's
  outcome, the same value or an error), and `Lowering.lowerRel_sound` for
  plans, by `Rel.evalI_mapExprs`. Equality saturation (lean-egg) was
  considered and not used: it proves equalities rather than finding terms,
  it is deprecated, and it needs Lean 4.30 and Rust.

* **The lift is generated too** (#268): the lowering search run backwards.
  `SubstraitLean/DuckDBSQL.lean` states what DuckDB's SQL functions mean
  (`DuckFn`, at one signature each) under `semantics="duckdb"` and
  `"reference"`: `/` of integers divides as doubles, `%` of doubles is C's
  `fmod`, `log` is base 10, and with DuckDB's semantics `±∞`, NaN where
  DuckDB gives them. It is trusted, like a profile, and tested against the
  engine (oracle A, #242). `generate_lift` (`SubstraitLean/LiftSearch.lean`)
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
**`Rel.duckdb_sound`**: on every catalog that meets the preconditions, the
plan evaluated with DuckDB's functions gives `Rel.eval`'s rows. Two functions
DuckDB raises on where the reference gives a value, `MIN % -1` and `<<`, are
the SQL printer's (`Profile.duckdbWritten`): it writes them out even without
guards. The catalogue's benchmark queries are checked this way
(`verified_sql`, #229).

A plan that may raise (an overflow check, a division) is covered too, by
**partial correctness**. `Lowering.duckdb_exact` shows that every lowered
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

Trusted: that `Profile.duckdb` matches DuckDB (probed on edge cases,
`tests/test_probe.py`),
and that the SQL printer prints the shimmed plan faithfully (`isNum` as `IS
NOT NULL` included). Next: relations, the
fuzzer check, writing shimmed plans for the SQL printer, and the other rows of
the DuckDB diff.

## The translations today

Each engine reaches the reference through a **translation**, a function from
a plan to something the engine runs. Until the shims of #185 replace them,
these are hand-written and tested, not proved:

| engine | translation | where |
|---|---|---|
| DataFusion | `substrait-check --write-datafusion` | `Write.writeRel (df := true)` |
| Polars | `polars_engine` (LazyFrame) | Python |
| DuckDB, Snowflake, Spark | `sverify.sql.to_sql` with a `Dialect` | Python |

A translation compensates for its engine where it can (an exact `SUM`
through `DECIMAL(38,0)`, `canonical` doubles, explicit `NULLS FIRST/LAST`,
guards that raise) and refuses the plan where it cannot (`Unsupported`).
"Raise rather than differ" is the standard each one is tested against:
`Rel.eval` (`lean_rows`), another engine's rows, or a raised error. Guard
elimination (`SubstraitLean/Guards.lean`) is the part already proved in Lean.

### Decimals (#27)

The reference computes a `DECIMAL(p, s)` as its unscaled integer, exactly, and
raises where a result needs more than `p` digits. `substrait-check --write`
writes decimal plans back as Substrait's own typed calls and casts, and
refuses any it cannot (a plan whose written form does not parse back to the
same `Rel`). DataFusion gets none: it does not compute decimals as the
reference does.

Of the SQL dialects, only DuckDB runs decimal plans (`Dialect.decimals`).
Snowflake, Spark and Polars refuse them for now. DuckDB computes `+`, `-` and
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
