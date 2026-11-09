# What a result rests on

Sverify's guarantee reaches from `sv.verify` to a theorem through the hops
below. This page lists what each hop rests on, in three tables: what the
Lean kernel checks, what a test checks, and what nothing checks.
[`python/tests/test_trusted_base.py`](../python/tests/test_trusted_base.py)
fails when a new `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe def`,
`sorry` or `native_decide` appears in the Lean sources without a row here,
and when a row names one that is gone. The axioms column is generated
(`poe trusted-base`, from `#print axioms` in `SubstraitLean/Examples.lean`
built with the generated proofs checked), and CI's `lean` job fails when it
drifts.

## The path from `verify()` to the theorem

1. `sv.verify` builds the request: the plan from the frontend (the Ibis
   producer, `python/src/sverify/ibis_substrait/`, or the SQLGlot lift,
   `python/src/sverify/sql_lift/`) and the conditions as plans
   (`python/src/sverify/contracts.py`).
2. `substrait-check --contract` reads it (`ContractCheck.parse`) and analyses
   it (`ContractCheck.Request.check`).
3. `ContractCheck.check_proved_sound` takes a postcondition the answer marks
   proved to `Knowledge.contract_sound_all` on the data.
4. The checker's answer becomes a report in one place
   (`python/src/sverify/_verdict.py`, `verdict`).
5. `Report.run` writes the plan for an engine (`python/src/sverify/sql/`,
   the Polars translator) and checks the preconditions on the data.

## Kernel-checked

The top-level theorems and what each rests on beyond Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). `FloatCode.exp_fin` is
the project's one axiom (the trusted table below).

<!-- axioms:start -->
| Theorem | Says | Module | Axioms |
|---|---|---|---|
| `contract_sound` | A proved postcondition is TRUE on every output row | `Contracts/Sound.lean` | propext, Classical.choice, Quot.sound |
| `contract_sound_all` | … in every row order the reference allows (D24) | `Contracts/Sound.lean` | propext, Classical.choice, Quot.sound |
| `contract_sound_allowed` | … on every result the reference allows, for a plan whose open measures choose no rows | `AllowedAnalysis.lean` | propext, Classical.choice, Quot.sound |
| `ContractCheck.check_proved_sound` | What `substrait-check --contract` reports proved holds on the data's every allowed order (#1088) | `ContractCheck.lean` | propext, Classical.choice, Quot.sound |
| `Rel.mayIssues_sound` | A plan with no reported issue raises no runtime error | `Safety.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.guardFree_sound` | Dropping the guards of a plan whose only issues are assumed changes no result | `Guards.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.duckdb_refines` | The generated DuckDB lowering computes the reference | `Obligations.lean` | propext, Classical.choice, Quot.sound |
| `Lowering.duckdb_exact` | Each generated lowering entry is exact | `LoweringDuckDB/On.lean` | propext, Classical.choice, Quot.sound |
| `liftDuckDB.total` | The lift of DuckDB's SQL covers every generated entry | `LiftDuckDB/Duckdb.lean` | propext, Classical.choice, Quot.sound |
| `Engine.duckdb_sound` | A proved contract holds on the model of DuckDB (default settings) | `EngineSound.lean` | propext, Classical.choice, Quot.sound |
| `Engine.polars_sound` | … on the model of Polars | `EngineSound.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Engine.spark_sound` | … on the model of Spark (the reference's today, #271) | `EngineSound.lean` | propext, Classical.choice, Quot.sound |
| `Engine.contract_sound_runs` | … on an engine's run, given the engine runs its model (`Engine.Runs`) | `EngineSound.lean` | propext, Classical.choice, Quot.sound |
| `Rel.eval_sharded` | A linear plan runs shard by shard | `Partition.lean` | propext, Classical.choice, Quot.sound |
| `Rel.incremental_sound` | A delta plan computes the change of the view | `Incremental.lean` | propext, Classical.choice, Quot.sound |
| `Refresh.no_corruption` | A sink's refreshes never apply a change to a table it was not computed from | `Refresh.lean` | propext, Quot.sound |
<!-- axioms:end -->

`docs/proofs.md` maps every module to its theorems.

## Tested

What a test checks and no proof does.

| What | The test |
|---|---|
| The parser and the writer: every plan the checker writes parses back to the same `Rel` | The golden tests, `tests/run.sh` (`tests/fixtures/`), and the CLI's own round trip |
| The checker's answers to `--contract` requests | `tests/contracts/` (`tests/run.sh`) |
| The Python mirror of the function tables (`sverify._functions`) | `python/tests/test_functions.py` against `substrait-check --functions` |
| The engine facts each engine profile states | Their probes (`characterization/<engine>/probes.json`), checked by `sverify_dev.facts` and the engine jobs |
| Native `Float` arithmetic agrees with the exact definition (D31) | `python/tests/test_float_model.py` and the `float-bounds/` project's `NativeLink` |
| The black boxes' rows (`sverify.black_box`, `SubstraitLean/BlackBox` in the core) | `python/tests/test_black_box.py` against `substrait-check --black-boxes` |
| The writers' SQL and the Polars translation compute what the lowered plan states | Golden, round-trip and differential tests ([the translations](engine-profiles.md#the-translations-today)) |
| A report survives its JSON: `Report.from_json(report.to_json())` | `python/tests/test_formats.py` |

## Trusted

What neither a proof nor a test covers. Each row names what stands in its
place, and the issue or decision that retires it.

| Construct | Names | File | What runs, or what it stands for | Retired by |
|---|---|---|---|---|
| axiom | `FloatCode.exp_fin` | `SubstraitLean/Safety.lean` | `exp` of a finite double at most 709 is finite: the platform's `libm`, within one ulp (#582) | Proved for native doubles as `NativeLink.core_exp` in `float-bounds/`; the canon PR links it |
| opaque, `implemented_by` | `upper`, `lower`, `ilike`, `regexMatch`, `regexExtract`, `regexReplace`, `md5`, `sha256` | `core/Sverify/Core/Text.lean` | The string functions the checker evaluates by compiled code (`upperAscii`, `Digest.md5`, …); no proof looks inside them | A model of each in Lean, or a row of the black-box table |
| opaque, `implemented_by` | `rawScalar`, `rawAgg`, `rawAggRaises`, `rawRaises` | `core/Sverify/Core/BlackBox.lean` | The black boxes' evaluation (`evalScalar`, …), outside the model | #1189's black-box PR (`Boxes` in `Impl`) |
| opaque | `intToDouble` | `core/Sverify/Core/Float.lean` | A conversion given with the property the proofs use; the proofs see only the property | |
| opaque | `decToDouble`, `doubleToDecimal` | `core/Sverify/Core/Conversions.lean` | The same, for decimals and doubles | |
| opaque, `implemented_by`, unsafe def | `evalSemantics`, `evalDuckAgg`, `evalDuckFn`, `evalHints`, `evalSemanticsImpl`, `evalDuckAggImpl`, `evalDuckFnImpl`, `evalHintsImpl` | `SubstraitLean/LiftSearch.lean` | The lift generator's evaluation of Lean terms while it elaborates; what it writes is a theorem the kernel checks (with `check_generated`) | |
| opaque, `implemented_by`, unsafe def | `evalProfile`, `evalUnFn`, `evalBinFn`, `evalHints`, `evalSchemas`, `evalProfileImpl`, `evalUnFnImpl`, `evalBinFnImpl`, `evalHintsImpl`, `evalSchemasImpl` | `SubstraitLean/LoweringSearch.lean` | The lowering generator's, the same | |
| opaque, `implemented_by`, unsafe def | `evalEngines`, `evalEnginesUnsafe` | `SubstraitLean/Obligations.lean` | The engine profiles' evaluation while the obligations elaborate | |
| sorry | `checkGenerated` | `engines/Sverify/Engines/Generated.lean` | With `check_generated` off (a plain `lake build`, every editable install), the generated entries' proofs are `sorryAx`; CI, the wheels and `poe prove` check them. `substrait-check --build` says which build it is (`generated proofs checked` or `unchecked`) | |
| compiled checker | `partial def` on the evaluation path, IO, `Lean.Json` | `SubstraitLean/`, `SubstraitCheck.lean`, `Main.lean` | The compiled code runs what the definitions state; a `partial def` is opaque to proofs | |
| CLI glue | `parse`, `schemaEnv`, `Report.json`, `runOn`, `serve`, `underProfile` | `SubstraitLean/ContractCheck.lean`, `SubstraitCheck.lean` | Reading the request and writing the answer; `underProfile` labels the reference's report with the profile of an engine marked `asReference` | #271 (engine profiles of their own) |
| CLI glue | `"class_basis": "computed"`, `"sorted_basis": "computed"` | `SubstraitLean/Realize.lean` | The class and the sort per engine are computed from the rows; no theorem connects them to the engine's refinement | #900 |
| ε path | `"epsilon"`, `"rows_exact"`, `"margin_checks"` | `SubstraitLean/Epsilon.lean`, `SubstraitLean/MarginCheck.lean` | The float bounds and the threshold rule (#568, #929, D35) feed the per-engine verdict and the run-time checks; `check_proved_sound` covers the analysis without them | A second lemma, as #1088 says |
| Python glue | `verdict`, `_proof_cache`, `SVERIFY_CHECKER`, `Report.from_json` | `python/src/sverify/` | The one report of an answer; a cached answer for the same request and checker binary; a checker named by the environment or a plugin; a report read back from a file | |
| frontends | The Ibis producer, the SQLGlot lift, the request builder | `python/src/sverify/ibis_substrait/`, `python/src/sverify/sql_lift/`, `python/src/sverify/contracts.py` | That the plan is the one the user meant | |
| engine facts | `docs`, `source`, `probe`, `fuzz`, `proof` | `characterization/<engine>/facts/` | What an engine computes, by provenance: its documentation, its source, a probe, a fuzzer, a proof (`engine-fact` skill) | Each fact's evidence |
| size hypothesis | `Rel.Small`, `Text.sizeCap` | `SubstraitLean/Contracts/Sound.lean`, `core/Sverify/Core/Text.lean` | Fewer than 2⁶² rows a window reads, strings under 2³² characters ([D27](core-semantics.md#d27-the-size-hypothesis-is-the-only-size-assumption)) | |
| toolchain | Lean `v4.35.0` | `lean-toolchain` | The kernel and the compiler | |

## The trusted parts in detail

- The size hypothesis. Every string has fewer than 2³² characters
  (`Text.sizeCap`, decided on
  [#336](https://github.com/AlexanderNenninger/substrait-lean/issues/336):
  DuckDB's strings hold fewer than 2³² bytes), every relation a window reads
  fewer than 2⁶² rows (`Rel.Small`), and every relation an
  aggregate reads fewer than 2⁶³, as `COUNT(*)` is a 64-bit integer
  (`Rel.sumRows`, [#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)).
  No machine's memory holds more. The theorems that need it take
  `Rel.Small` (`Rel.mayIssues_sound`, `Rel.guardFree_sound`,
  `Rel.duckdb_sound`, `Rel.polars_sound`, `Rel.spark_sound`, and the engine
  side conditions built on them, `Engine.PolarsData` in
  `SubstraitLean/EngineSound.lean`); nothing checks it on the data, so
  it is assumed of every run (#1166). With it, `ROW_NUMBER() - 1` and Ibis's
  `find` (`strpos - 1`) are proved not to overflow without a precondition, while
  `amount * 2` needs one, which sverify infers (#244). It overrides Substrait
  ([D27](core-semantics.md#d27-the-size-hypothesis-is-the-only-size-assumption)).
- The frontends produce the plan the user meant: the Ibis producer
  (`python/src/sverify/ibis_substrait/`) and the SQLGlot lift for DuckDB's
  SQL (`python/src/sverify/sql_lift/`,
  [#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231),
  [PR #252](https://github.com/AlexanderNenninger/substrait-lean/pull/252),
  #264), which writes each function's options explicitly from the source
  dialect.
- The parser and the writer, `Parse.lean` and `Write.lean`. The CLI checks
  that every plan it writes parses back to the same `Rel`, and the golden
  tests (`tests/run.sh`) run that round trip on every fixture. The parser's
  choice of function by kind is checked: `checkPlan` refuses a plan
  `Rel.inferKinds` does not type (`Rel.kinds_sound`), and since
  [D29](core-semantics.md#d29-a-value-has-its-kind) each kind has its own
  constructor of `Value`.
- The code that writes a checked plan for an engine: the SQL printers
  (`Pretty.lean`, `python/src/sverify/sql/`), a shimmed plan's `isNum` as
  `IS NOT NULL` included, and the Polars translator. Golden, round-trip and
  differential tests cover them
  ([the translations](engine-profiles.md#the-translations-today)).
- The CLI's glue, `Main.lean`, `SubstraitCheck.lean`, `ContractCheck.lean` and `ShardCheck.lean`:
  they call the checkers and print JSON. `ContractCheck.check_proved_sound`
  (#1088) takes a postcondition `check` reports proved to
  `contract_sound_all` on the data, for any data with the request's tables
  that meets its schemas, preconditions, keys and row caps; what it leaves
  trusted is the step before and after: `parse` (JSON to plans, and
  `schemaEnv`, the declared types as abstract values), `Report.json`, the
  `--serve` loop and `runOn` that call `check` and print its report, and
  `underProfile`, which labels the reference's report with the profile a
  request names for an engine marked `asReference` (until #271). On the Python side, the glue of
  incremental views (change tables, consolidation, merge).
- The exact state of a maintained `SUM` or `AVG` of doubles
  (`python/src/sverify/_exact_sum.py`, #918). Lean proves that the state, an
  integer per group, finishes to `floatSumCR` of the current rows after any
  sequence of batches (`LinearAgg.fsum_no_drift`), and the same of the
  moments of `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` (`LinearAgg.no_drift`,
  `varState_sound`, `covState_sound`, `corrState_sound`); finishing them
  ports Lean's `sqrtMag` (`sqrt_mag`). Holding that integer in
  Python, adding up each batch's contributions to it (the engine gives each
  changed row's value and weight with the checked `contrib` plan) and
  rounding it once with CPython's `int / int` (correctly rounded, ties to
  even) are trusted. `tests/test_exact_sum.py` checks the finish against the
  checker's `floatSumCR`, `floatAvgCR`, `varOf`, `covOf` and `corrOf`, NaN,
  `±∞`, `-0.0` and subnormals among the values.
- Where an engine evaluates an expression. Lean proves which rows an
  expression may raise on under `Rel.eval`; which expressions an engine
  evaluates, on which rows, is trusted. `Rel.loose` models an engine that
  evaluates an expression on more rows than the plan says (merged filters,
  eager `AND` and `OR`), and the facts record what each engine does
  ([duckdb-exec-filter-pushdown](../characterization/duckdb/facts/duckdb-exec-filter-pushdown.json),
  [DD-7](../upstream/bugs/DD-7.json); `Safety.lean`'s header).
- Doubles. Lean's `Float` is an opaque `extern` to C `double`, trusted to be
  IEEE binary64 where the model still calls it: `pow`, `log` and the other
  libm functions. The conversions between integers, decimals
  and doubles are computed exactly (`Conversions.lean`), behind `opaque`
  constants with their proved properties, and `#guard`s compare them with the
  native ones; an integer or decimal that IEEE would round to `±∞` (from
  2¹⁰²⁴ on, never for 64-bit integers or 38-digit decimals) becomes the
  largest finite double (#257). The one axiom left is `FloatCode.exp_fin`
  (`Safety.lean`, libm's `exp`). `+ − × ÷` need none since D31: they are the
  exact result rounded once (`FloatArith.lean`), and the bounds the checker
  trusted for them before (`FloatCode.add_scaled` …,
  [#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582))
  are theorems; `FloatArithCheck.lean` checks those operations against native
  doubles on every build, and each engine's fact states that its own are
  IEEE 754's. A `SUM` or `AVG` of doubles needs none since D25: `floatSumCR`'s
  bounds are theorems (`FloatExact.lean`). `VAR_*`, `STDDEV_*`, `COVAR_*` and
  `CORR` need none since D30: the reference's values are the exact moments
  rounded once (`FloatMoments.lean`), and the properties an engine's
  algorithm keeps (`StatProps.lean`) are definitions; `varOf_props`,
  `covOf_props` and `corrOf_props` are retired. `float-bounds/` proves the
  bounds over the reals for the standard model of rounding (`Arith.lean`,
  `CoreStats.lean`), and there only `NativeLink` (`Link.lean`) stays trusted:
  Lean's `Float` rounds as IEEE 754 binary64 does, and `exp` is the
  platform's `libm` within one ulp
  ([#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)).
- The models of the engines' own functions, and that each engine matches
  its profile: `Impl.Faithful` (`Guards.lean`) for the functions the SQL
  calls unguarded, `Profile.duckdb` (`DuckDBProfile.lean`, `EngineTables.lean`),
  `Profile.polars` and `Polars.*` (`PolarsProfile.lean`, `PolarsShims.lean`),
  `Profile.spark` and `Spark.*` (`SparkProfile.lean`, `SparkShims.lean`), and
  the shared shims' models `Shim.*` for each engine that writes them (`Shims.lean`),
  each from the engine's characterization facts
  (`characterization/<engine>/facts/`, [how they are judged](../characterization/README.md)).
  DuckDB's own tests are replayed and fuzzed against the model; the profiles
  are tested on the engines and trusted.
- The table formats' change feeds (`ChangeFeed`, `TableFormat.lean`), a
  hypothesis of `Rel.cdf_sound` wherever Sverify reads a Delta change data
  feed; it is proved when the change is computed from two snapshots.
- An engine's run of a proved plan. `Engine.contract_sound` proves the
  contract on the rows the engine's model computes for the translated plan
  (`r'.eval cat E.impl`), unless it raises. The chain from there to the engine's actual
  result, in order:
  1. the Lean theorem, `Engine.contract_sound` with the engine's
     `Engine.Sound` (`EngineSound.lean`); `Engine.polars_sound` also takes
     `Engine.PolarsData`, preconditions on the catalog and the size
     hypothesis;
  2. the round trip: the SQL or Polars code written for the plan is
     `E.lower` of it (#900, PR 3);
  3. the runtime checks: the schema read against `E.table`, the session
     pinned to the profile, the engine's version against the tested rows
     ([#1130](https://github.com/AlexanderNenninger/substrait-lean/issues/1130));
  4. the engine facts and replays behind each tested row of `Engine.Refines`,
     and D16's claim (`Engine.Runs`): the engine's actual result is one its
     table allows. `Engine.contract_sound_runs` carries the contract to that
     result where `transferB T Profile.reference.table E.table` holds; it
     fails at `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on
     every engine, `null_order` without a preference on Polars and Spark, and
     integer overflow on Polars, which the tolerance form of #929 covers in
     PR 3.

  An engine that raises commits nothing: a runtime obligation of the sink,
  beside D16. Raising only where the reference may is a separate claim
  (`Rel.duckdb_refines`' second part), outside this chain.

  Beside D16, the margin check of a threshold filter on a double `SUM` or
  `AVG` (#929, `Rel.marginCheck`): that the check's aggregate and the plan's
  read the same rows per group, from one snapshot, and that each group's
  `Σ|xᵢ| + n · 2⁻¹⁰²²` stays below a quarter of the largest double
  (`margin_sum`, `margin_avg`). The check's arithmetic and constants are
  proved in codes (`margin_row`, `check_sum`, `check_avg`); `float-bounds`'
  `StdModel.margin_check` is the same argument over the reals. `Report.run` makes the snapshot a condition of the run
  (`Report.check_margins`): every input the check reads is an Arrow table, a
  table DuckDB holds (`Resident`), or a Delta or Iceberg table pinned to one
  version (`Scan`, `name@vN`). An input of another kind, which may change
  between the two reads, warns, and refuses the run under the deterministic
  profile (`reproducible=`). `tests/test_margin.py` runs the check against
  its formula in Python's doubles.

  Beside D16, D35's bound: the engines' summation algorithms meet
  `SumBound` (a double `SUM` within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact
  sum), which `Rel.AllowedP` takes for every non-`EXACT` `sum_order`. It is
  justified by `float-bounds`' `StdModel.Summed.near`, `epsilon_sum_cr` and
  `Rnd.kahan_near` on the engines' facts; #1196 retires it.
- Black boxes are DuckDB's functions: each black box means the function
  DuckDB computes under its name, and keeps its row's laws, tested by
  `python/tests/test_black_box.py` (DuckDB on the SQL against DuckDB on the
  plan Lean writes back, and the laws on random data). The evaluators behind
  black boxes and regular expressions (`implemented_by` in `BlackBox.lean`,
  `Regex.lean` and `Digest.lean`, and `Text.lean`'s eight: `upper`, `lower`,
  `ilike`, `regexMatch`, `regexExtract`, `regexReplace`, `md5`, `sha256`) are
  read by no proof;
  the proofs use only each black box's declared laws. The search evaluators
  (`implemented_by` in `LoweringSearch.lean`, `LiftSearch.lean` and
  `Obligations.lean`) read profiles, functions and hints while a generator
  or a table check elaborates; no theorem reads them.
