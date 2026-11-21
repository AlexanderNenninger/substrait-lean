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
   proved to `Knowledge.contract_sound_all` on the data. The postcondition's
   plan is built by `parse` over the request's transformation (`Post.plan`):
   a plan in `ensures` that selects from anything else is refused (#1484).
   `ContractCheck.check_proved_on` carries it to the rows each engine's model
   computes, with the engine's side condition taken from the report
   (`check_proved_on_duckdb`, `check_proved_on_polars`, `check_proved_on_spark`).
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
| `contract_sound_all` | … in every row order the reference allows | `Contracts/Sound.lean` | propext, Classical.choice, Quot.sound |
| `contract_sound_allowed` | … on every result the reference allows, for a plan whose open measures choose no rows | `AllowedAnalysis.lean` | propext, Classical.choice, Quot.sound |
| `ContractCheck.check_proved_sound` | What `substrait-check --contract` reports proved holds on the data's every allowed order | `ContractCheck.lean` | propext, Classical.choice, Quot.sound |
| `ContractCheck.check_proved_on` | … on the rows an engine's model computes for the translated plan, for a plan without open measures (`closed`), under the engine's side condition | `ProvedOn.lean` | propext, Classical.choice, Quot.sound |
| `ContractCheck.check_proved_on_duckdb` | … on DuckDB's model (default route: verified under the reference, lowered by `Lowering.duckdb`), its side condition from a guard-free report without issues under the reference | `ProvedOn.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `ContractCheck.check_proved_on_polars` | … on Polars's model, its side condition from a guard-free report | `ProvedOn.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `ContractCheck.check_proved_on_spark` | … on Spark's model, its side condition from a guard-free report | `ProvedOn.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.mayIssues_sound` | A plan with no reported issue raises no runtime error | `Safety.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.mayIssues_sound_all` | … on every order of the ties the reference allows | `Safety.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.guardFree_sound` | Dropping the guards of a plan whose only issues are assumed changes no result | `Guards.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Rel.duckdb_refines` | The generated DuckDB lowering computes the reference, and a raise of the lowered plan is a raise of the reference: the second part is no part of `Engine.duckdb_sound`, and it discharges DuckDB's side condition with an empty `Rel.mayIssues` | `Obligations.lean` | propext, Classical.choice, Quot.sound |
| `Lowering.duckdb_exact` | Each generated lowering entry is exact | `DuckDB/LoweringOn.lean` | propext, Classical.choice, Quot.sound |
| `liftDuckDB.total` | The lift of DuckDB's SQL covers every generated entry | `DuckDB/Lift/Duckdb.lean` | propext, Classical.choice, Quot.sound |
| `Engine.duckdb_sound` | A proved contract holds on the model of DuckDB (default settings), given `NoRaiseSide`, which an empty `Rel.mayIssues` discharges (`Engine.duckdb_noRaise_of_mayIssues`). The model differs from the reference only in its scalar functions: its relational behaviour is the reference's, and that the engine runs it is the assumption `Engine.Runs` ([below](#the-trusted-parts-in-detail)) | `DuckDB/Engine.lean` | propext, Classical.choice, Quot.sound |
| `Engine.polars_sound` | … on the model of Polars, given `GuardFreeSide`, whose plan part the checker decides (`Engine.GuardFreePlan`) and whose data part is assumed of the data (`Engine.GuardFreeData`) (scalar functions; the model's relational behaviour is the reference's, and that the engine runs it is `Engine.Runs`) | `Polars/Engine.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Engine.spark_sound` | … on the model of Spark, given `GuardFreeSide`, whose plan part the checker decides (`Engine.GuardFreePlan`) and whose data part is assumed of the data (`Engine.GuardFreeData`) (scalar functions; the model's relational behaviour is the reference's, and that the engine runs it is `Engine.Runs`) | `Spark/Engine.lean` | propext, Classical.choice, Quot.sound, Substrait.FloatCode.exp_fin |
| `Engine.contract_sound_runs` | … on an engine's run, given the engine runs its model (`Engine.Runs`) | `Sound.lean` | propext, Classical.choice, Quot.sound |
| `Engine.contract_sound_runs_near` | … on an engine's run with open float rows, given `Rel.FloatOpenSafeP` over its table, which `Rel.floatOpenSafeP_aggregate` discharges for a root aggregate's double `SUM` and `AVG`, and `Rel.floatOpenSafeP_of_noDouble` for a closed plan without doubles; other shapes are #929's | `Sound.lean` | propext, Classical.choice, Quot.sound |
| `Rel.transfer_of_noDouble` | A result a table allows for a plan without doubles, the reference allows, where the table with the reference's choices at the options only doubles read (`floatOnlyOptions`) transfers (`transferB`) | `NoDouble.lean` | propext, Classical.choice, Quot.sound |
| `Rel.floatOpenSafeP_of_noDouble` | … and such a plan without open measures is `Rel.FloatOpenSafeP` over the table | `NoDouble.lean` | propext, Classical.choice, Quot.sound |
| `Rel.eval_sharded` | A linear plan runs shard by shard | `Partition.lean` | propext, Classical.choice, Quot.sound |
| `Rel.incremental_sound` | A delta plan computes the change of the view | `Incremental.lean` | propext, Classical.choice, Quot.sound |
| `Rel.zeval_prune` | … and over a store pruned to the columns the view reads, every row keeps its weight | `Incremental.lean` | propext, Classical.choice, Quot.sound |
| `Refresh.no_corruption` | A sink's refreshes never apply a change to a table it was not computed from | `Refresh.lean` | propext, Quot.sound |
<!-- axioms:end -->

`docs/proofs.md` maps every module to its theorems.

## Tested

What a test checks and no proof does.

| What | The test |
|---|---|
| The writer loses nothing: every plan the checker writes parses back to the same `Rel` (`parse (write r) = r`) | The CLI's own round trip (`Write.roundtrips`), and the golden tests, `tests/run.sh` (`tests/fixtures/`) |
| The parser reads an option's values apart: for a call of each function that reads options (33 of 36), the values of each option the checker accepts are written as different plans, at most one of them as the plan without the option. It does not see an option with one accepted value (44 of 65 cases), or a value read as another that the written plan does not show | `python/tests/test_parse_options.py`: one plan per function, option and value, from the coverage cases' calls (about 370 plans, 5 s) |
| The checker's answers to `--contract` requests | `tests/contracts/` (`tests/run.sh`) |
| The Python mirror of the function tables (`sverify._functions`) | `python/tests/test_functions.py` against `substrait-check --functions` |
| The engine facts each engine profile states | Their probes (`engines/duckdb/replay/probes.json`, `engines/polars/probes/` and `engines/spark/probes/`), checked by `sverify_dev.facts` and the engine jobs |
| Native `Float` arithmetic agrees with the exact definition, the exact result rounded once | `python/tests/test_float_model.py` and the `float-bounds/` project's `NativeLink` |
| DuckDB's black-box catalogue (`sverify.black_box`, `Boxes.duckdb` in `engines/duckdb/Sverify/DuckDB/Boxes.lean`), and its evaluators against DuckDB's values (`evaluated`) | `python/tests/test_black_box.py` against `substrait-check --black-boxes`, and the samples' `#guard` |
| DuckDB's black boxes keep their declared laws where the function does not raise (`Boxes.Lawful`; under it the model's value is the function's, `Boxes.Lawful.call`). Where one did not, the model's value is the row's sample, the checker panics and refuses the rows (`BlackBox.Scalar.call`, `runOn`), and D16's claim (`Engine.Runs`) fails for that call (#1484) | `python/tests/test_black_box.py`: the laws on random data, and `test_a_law_break_is_refused` through the compiled checker |
| The writers' SQL and the Polars translation compute what the lowered plan states | Golden, round-trip and differential tests ([the translations](engine-profiles.md#the-translations-today)) |
| A report survives its JSON: `Report.from_json(report.to_json())` | `python/tests/test_formats.py` |

## Trusted

What neither a proof nor a test covers. Each row names what stands in its
place, and what retires it.

| Construct | Names | File | What runs, or what it stands for | Retired by |
|---|---|---|---|---|
| axiom | `FloatCode.exp_fin` | `analysis/Sverify/Analysis/Safety.lean` | `exp` of a double whose canonical code is finite and at most 709 is finite (`-0.0` included: `exp(-0.0) = 1`): the platform's `libm`, within one ulp | Proved for native doubles as `NativeLink.core_exp` in `float-bounds/`, once the core links it |
| opaque, `implemented_by` | `ilike`, `regexMatch`, `regexExtract`, `regexReplace`, `md5`, `sha256` | `core/Sverify/Core/Text.lean` | The string functions the checker evaluates by compiled code (`ilikeAscii`, `Digest.md5`, …); no proof looks inside them | A model of each in Lean, or a row of the black-box table |
| opaque, `implemented_by` | `rawScalar`, `rawAgg`, `rawAggRaises`, `rawRaises` | `engines/duckdb/Sverify/DuckDB/Boxes.lean` | The functions of DuckDB's black-box catalogue (`evalScalar`, …), outside the model; the core holds none (#1189). A proof uses only a row's laws, which hold by the clamp and `Boxes.duckdb_wf`; where the clamp applies the compiled checker panics and refuses the rows | A model of a row in Lean, where one exists |
| structure | `DoubleStats.Correct` | `analysis/Sverify/Analysis/Pruning.lean` | What a file's double statistics mean: the minimum and maximum bound the canonical codes, as writers compare IEEE numbers: `-0.0` counts as `0.0` | |
| opaque | `intToDouble` | `core/Sverify/Core/Float.lean` | A conversion given with the property the proofs use; the proofs see only the property | |
| opaque | `decToDouble`, `doubleToDecimal` | `core/Sverify/Core/Conversions.lean` | The same, for decimals and doubles | |
| opaque, `implemented_by`, unsafe def | `evalSemantics`, `evalDuckAgg`, `evalDuckFn`, `evalHints`, `evalSemanticsImpl`, `evalDuckAggImpl`, `evalDuckFnImpl`, `evalHintsImpl` | `engines/duckdb/Sverify/DuckDB/LiftSearch.lean` | The lift generator's evaluation of Lean terms while it elaborates; what it writes is a theorem the kernel checks (with `check_generated`) | |
| opaque, `implemented_by`, unsafe def | `evalProfile`, `evalBoxes`, `evalUnFn`, `evalBinFn`, `evalHints`, `evalSchemas`, `evalProfileImpl`, `evalBoxesImpl`, `evalUnFnImpl`, `evalBinFnImpl`, `evalHintsImpl`, `evalSchemasImpl` | `engines/Sverify/Engines/LoweringSearch.lean` | The lowering generator's, the same | |
| opaque, `implemented_by`, unsafe def | `evalEngines`, `evalEnginesUnsafe` | `SubstraitLean/Obligations.lean` | The engine profiles' evaluation while the obligations elaborate | |
| sorry | `checkGenerated` | `engines/Sverify/Engines/Generated.lean` | With `check_generated` off (a plain `lake build`, every editable install), the generated entries' proofs are `sorryAx`; CI, the wheels and `poe prove` check them. `substrait-check --build` says which build it is (`generated proofs checked` or `unchecked`); the report records it as `checker.generated_proofs`, and `str(report)` says "proved by a checker whose generated proofs are unchecked" for the second | |
| compiled checker | `partial def` on the evaluation path, IO, `Lean.Json` | `SubstraitLean/`, `SubstraitCheck.lean`, `Main.lean` | The compiled code runs what the definitions state; a `partial def` is opaque to proofs | |
| CLI glue | `parse`, `schemaEnv`, `Report.json`, `runOn`, `serve`, `underProfile` | `SubstraitLean/ContractCheck.lean`, `SubstraitCheck.lean` | Reading the request and writing the answer; `underProfile` marks a request under an engine's profile pending (the reference's report, labelled `reference`) | Engine profiles of their own ([tracked](https://github.com/AlexanderNenninger/substrait-lean/issues/271)) |
| CLI glue | `"class_basis": "computed"`, `"sorted_basis": "computed"` | `SubstraitLean/Realize.lean` | The class and the sort per engine are computed from the rows; no theorem connects them to the engine's refinement | A theorem that does |
| ε path | `"epsilon"`, `"rows_exact"`, `"margin_checks"` | `SubstraitLean/Epsilon.lean`, `core/Sverify/Core/MarginCheck.lean` | The [float bounds](float-bounds.md) and the threshold rule feed the per-engine verdict and the run-time checks; `check_proved_sound` covers the analysis without them | A second lemma that covers them |
| Python glue | `verdict`, `_proof_cache`, `SVERIFY_CHECKER`, `Report.from_json` | `python/src/sverify/` | The one report of an answer; a cached answer for the same request and checker binary; a checker named by the environment or a plugin; a report read back from a file | |
| Python glue | `Observation.reads_members`, `routes.reproducibility` | `python/src/sverify/observation.py`, `python/src/sverify/routes.py` | The step from an observation to a level of determinism (D48): an observation that reads one zero and one NaN (`zeros="canon"`, `floats="plan"` or a tolerance) is met by `Report.deterministic`, the class level (`check_class_determined_sound`, and `check_class_determined_determined` for `Rel.DeterminedUpTo` at `Obs.classes`); one that reads the members asks for the exact level (`check_deterministic_sound`, `check_deterministic_determined`). The bridge from `Row.canon` to `Relation.Equiv` is proved (`Relation.Equiv_classes_of_canon_perm`); what stays trusted is that the kinds the Python side passes read every column that may hold a double as a double (`Relation.DoublesKinded`) | `Rel.kinds_sound` (`core/Sverify/Core/Kinds.lean`) gives a result's kinds; the lemma that they meet `DoublesKinded`, and `data.HasKinds` beside `DataMeets`, are P1c (#1285) |
| Python glue | `Report.check_inputs`, `Report._unchecked_requires` | `python/src/sverify/report.py` | On Polars (and Spark) a guard-free plan runs without its per-row guards, and on DuckDB the expressions the checker marked run without theirs, the check against `±∞` included (`Rel.duckdb_marks`, ruling 223); both rest on `check_inputs` deciding the theorem's `hpre` on the data the run reads: each `requires` is checked on the run's engine, a report read back with `Report.from_substrait` carries its preconditions as plans (`PlannedCondition`), and a run refuses a report with a precondition it holds no check for | A theorem that ties the checks to `hpre` |
| frontends | The Ibis producer, the SQLGlot lift, the request builder | `python/src/sverify/ibis_substrait/`, `python/src/sverify/sql_lift/`, `python/src/sverify/contracts.py` | That the plan is the one the user meant | |
| engine facts | `docs`, `source`, `probe`, `fuzz`, `proof` | `engines/<engine>/facts/` | What an engine computes, by provenance: its documentation, its source, a probe, a fuzzer, a proof (`engine-fact` skill) | Each fact's evidence |
| size hypothesis | `Rel.Small`, `Text.sizeCap` | `analysis/Sverify/Analysis/Contracts/Sound.lean`, `core/Sverify/Core/Text.lean` | Fewer than 2⁶² rows a window reads, strings under 2³² characters ([the size hypothesis](reference-semantics.md#overrides)) | |
| toolchain | Lean `v4.35.0` | `lean-toolchain` | The kernel and the compiler | |

## Stated limits

Each limit below names the theorem that is missing and where it is tracked.
Sverify's words claim no more than these theorems give
([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484)).

- The engine models are the reference's relational evaluator with each
  engine's scalar functions. A proof on an engine is a proof on that model:
  DuckDB's lowering and the shims are proved against it, and the Polars and
  Spark translations are tested. Engine profiles that evaluate their own
  relational behaviour are [#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271).
- The report's `ε` (`SubstraitLean/Epsilon.lean`, `robust`, `rows_exact`,
  `margin_checks`) has no theorem that it bounds an engine's doubles. The
  bounds hold over the reals in `float-bounds/`; the link from them to the
  core's codes is [#1196](https://github.com/AlexanderNenninger/substrait-lean/issues/1196), and `contract_sound_runs` for double
  aggregates beyond a root `SUM` or `AVG` is [#929](https://github.com/AlexanderNenninger/substrait-lean/issues/929).
- Under `semantics="reference"`, the default for SQL, the lift from SQL is
  tested Python. The generated `liftReference` entries are unused, and no
  theorem states that the reference's reading is DuckDB's value wherever the
  reference gives one (`DuckFn.reference_refines_duckdb`,
  [#2008](https://github.com/AlexanderNenninger/substrait-lean/issues/2008)).
- Dropping the `floats` component under `floats="plan"` (`floatsOk`) rests on
  `routes.observed` refusing a route for a double postcondition that is not
  robust, which is Python. `Observation.difference` has no proof that it
  matches `Value.Equiv`; its pairwise comparison with a tolerance gives false
  alarms only.
- `references` is checked on the data with SQL `=`, and `ForeignKeys.Hold`
  uses `Value` equality. The two differ at `-0.0`, `0.0` and NaN, and no
  theorem relates them.
- The generated aggregate lift entries have no `#guard` that ties their JSON to
  the proved measure, and none states that every argument is evaluated on
  every path. A script over the JSON checks both.
- The exact limbs of a maintained double sum: `limbs_grouped` is integer
  arithmetic, and nothing in Lean ties the split an engine computes to
  `exactOf` (`limbSplit_sound`). A run-time check tests each limb's normal form.
- `Rel.evalChoices` has no theorem for ordering measures.
- `UnFn.dkind` is a decimal kind without the overflow check. A parsed plan
  builds it only where its precision holds the value (`Parse.Rel.settleDivs`)
  or where nothing reads the precision (a comparison's side,
  `UnFn.apply_dkind_precision`).
- DuckDB's implicit coercions are its facts and the lift's tests.
- `Report.output` is Ibis's schema, and integer widths live in the parser.

## The trusted parts in detail

- The `evalChoices` oracle. `Rel.evalChoices` (`lean_choices`) and the Python matching of rows to its choices (`allows_rows`) check engine results against the rows the reference allows. `Rel.evalChoices_allowed` proves that what it accepts is allowed by the reference, for the plans `Rel.ChoicesSupported` holds of: those without an `aggregate` with a measure that sorts its rows (`FIRST`, `LAST`, `STRING_AGG`, `collect`, `MODE`). For the others the oracle rests on tests. The converse is false (an allowed result can be rejected where a class pick reaches a sign-sensitive expression, or an `ORDER BY` has a clustered key), so a rejection is a false alarm at worst.

- The size hypothesis. Every string has fewer than 2³² characters
  (`Text.sizeCap`, as DuckDB's strings hold fewer than 2³² bytes), every relation a window reads
  fewer than 2⁶² rows (`Rel.Small`), and every relation an
  aggregate reads fewer than 2⁶³, as `COUNT(*)` is a 64-bit integer
  (`Rel.sumRows`). `Rel.SmallAll` asks the same of every order of the ties
  the reference allows, for `Rel.mayIssues_sound_all` and
  `check_issues_sound_all`; the engine's input is one of those orders.
  `DataAssumed` in `Statements.lean` takes `Rel.SmallAll`, which gives
  `Rel.Small` (`DataAssumed.small`).
  No machine's memory holds more. The theorems that need it take
  `Rel.Small` (`Rel.mayIssues_sound`, `Rel.guardFree_sound`,
  `Rel.duckdb_sound`, `Rel.polars_sound`, `Rel.spark_sound`, and the engine
  side conditions built on them, `Engine.GuardFreeData` in
  `engines/Sverify/Engines/Sound.lean`); nothing checks it on the data, so
  it is assumed of every run. With it, `ROW_NUMBER() - 1` and Ibis's
  `find` (`strpos - 1`) are proved not to overflow without a precondition, while
  `amount * 2` needs one, which sverify infers. It overrides Substrait
  ([the size hypothesis](reference-semantics.md#overrides)).
- The frontends produce the plan the user meant: the Ibis producer
  (`python/src/sverify/ibis_substrait/`) and the SQLGlot lift for DuckDB's
  SQL (`python/src/sverify/sql_lift/`), which writes each function's options explicitly from the source
  dialect. A plugin's SQL front-end (`ProfilePlugin.sql`, a dialect's parse name and
  its lift) decides what that dialect's SQL means, so it is in the trusted base
  as DuckDB's is, and a report of SQL it read names its package and version
  (`Report.notes`).
- The parser and the writer, `Parse.lean` and `Write.lean`. The CLI checks
  that every plan it writes parses back to the same `Rel`, and the golden
  tests (`tests/run.sh`) run that round trip on every fixture. That shows the
  writer loses nothing and says nothing about whether the parser reads the
  input faithfully. The other direction, that `write (parse j)` agrees with
  `j`, has no test that compares whole plans: the writer rewrites calls (`gt`
  to `lt`, `is_not_null` to `not (is_null)`, `between` to `not` and `lt`), so
  a comparison of a plan with its written form by names is noise. What it
  checks is each option: `test_parse_options.py` states every option value on
  a call of every function that reads options, and fails where the parser
  refuses nothing and reads two values alike. The parser's
  choice of function by kind is checked: `checkPlan` refuses a plan
  `Rel.inferKinds` does not type (`Rel.kinds_sound`), and each kind has its
  own constructor of `Value` ([a value has its kind](decisions.md#d29-a-value-has-its-kind)).
- The code that writes a checked plan for an engine: the SQL printers
  (`Pretty.lean`, `python/src/sverify/sql/`), a shimmed plan's `isNum` as
  `IS NOT NULL` included, and the Polars translator. Golden, round-trip and
  differential tests cover them
  ([the translations](engine-profiles.md#the-translations-today)).
- The CLI's glue, `Main.lean`, `SubstraitCheck.lean`, `ContractCheck.lean` and `ShardCheck.lean`:
  they call the checkers and print JSON. `ContractCheck.check_proved_sound`
  takes a postcondition `check` reports proved to
  `contract_sound_all` on the data, for any data with the request's tables
  that meets its schemas, preconditions, keys and row caps; what it leaves
  trusted is the step before and after: `parse` (JSON to plans, and
  `schemaEnv`, the declared types as abstract values), `Report.json`, the
  `--serve` loop and `runOn` that call `check` and print its report, and
  `underProfile`, which marks a request under an engine's profile pending
  and returns the reference's report (an engine's own report waits for
  [#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)). On the Python side, the glue of
  incremental views (change tables, consolidation, merge, and the finish that
  turns the state back into the view's rows). The checker parses and writes
  each maintenance plan (`init`, `contrib`, `merge`, `regroup`, the finish and
  those of `_semi.py` and `_touched.py`) and does not contract-check them. A
  view's report is its batch query's, so a refresh can raise where the report
  lists no issue (`contrib`'s product at the edge of a type, `merge`'s partial
  sums); the refresh then applies nothing.
- The exact state of a maintained `SUM` or `AVG` of doubles
  (`python/src/sverify/_exact_sum.py`). Lean proves that the state, an
  integer per group, finishes to `floatSumCR` of the current rows after any
  sequence of batches (`LinearAgg.fsum_no_drift`), and the same of the
  moments of `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` (`LinearAgg.no_drift`,
  `varState_sound`, `covState_sound`, `corrState_sound`); finishing them
  ports Lean's `sqrtMag` (`sqrt_mag`). The engine holds that integer in
  limbs, rows of the group state that its `SUM` adds up per group with the
  checked plans (#1447). Trusted are: that a value's split into a mantissa
  and a grid position gives back the value, since its binary steps are
  comparisons with and products by power-of-two literals, exact in IEEE
  arithmetic (each row checks only the result's normal form, an integer
  mantissa below `2⁵³` and at least `2⁵²` for a normal value, and the finish
  refuses a row that fails; `test_the_split_is_frexp` compares the split with
  `frexp` at every power of two and its predecessor on DuckDB, Polars and
  Spark); that the limbs, read back for the touched groups, are the integer
  (`Σ v · 2^(32 j)`, which holds while a group has fewer than `2⁴¹` values,
  where the finish raises; a limb's `SUM` past 38 digits raises on DuckDB,
  on Polars' streaming engine and on Spark under ANSI, which a refresh there
  requires, and the finish refuses a NULL limb); and rounding it once with
  CPython's `int / int` (correctly rounded, ties to even).
  `tests/test_exact_sum.py` checks the limbs against the exact moments on
  DuckDB, Polars and Spark, the largest double, subnormals and `2^k - ulp`
  among the values, and the finish against the
  checker's `floatSumCR`, `floatAvgCR`, `varOf`, `covOf` and `corrOf`, NaN,
  `±∞`, `-0.0` and subnormals among the values.
- Where an engine evaluates an expression. Lean proves which rows an
  expression may raise on under `Rel.eval`; which expressions an engine
  evaluates, on which rows, is trusted. `Rel.loose` models an engine that
  evaluates an expression on more rows than the plan says (merged filters,
  eager `AND` and `OR`), `Rel.ViewAllowed` one that evaluates part of a
  condition on one input of a join before any pair exists (a pushed-down
  filter, a hash join's key), and the facts record what each engine does
  ([duckdb-exec-filter-pushdown](../engines/duckdb/facts/duckdb-exec-filter-pushdown.json),
  [DD-7](../upstream/bugs/DD-7.json); `Safety.lean`'s header).
- Doubles. Lean's `Float` is an opaque `extern` to C `double`, trusted to be
  IEEE binary64 where the model still calls it: `pow`, `log` and the other
  libm functions. The conversions between integers, decimals
  and doubles are computed exactly (`Conversions.lean`), behind `opaque`
  constants with their proved properties, and `#guard`s compare them with the
  native ones; an integer or decimal that IEEE would round to `±∞` (from
  2¹⁰²⁴ on, never for 64-bit integers or 38-digit decimals) becomes the
  largest finite double. The one axiom left is `FloatCode.exp_fin`
  (`Safety.lean`, libm's `exp`). `+ − × ÷` need none: they are the
  exact result rounded once (`FloatArith.lean`), and their bounds
  (`FloatCode.add_scaled` …) are theorems; `FloatArithCheck.lean` checks those operations against native
  doubles on every build, and each engine's fact states that its own are
  IEEE 754's. A `SUM` or `AVG` of doubles needs none: `floatSumCR`'s
  bounds are theorems (`FloatExact.lean`). `VAR_*`, `STDDEV_*`, `COVAR_*` and
  `CORR` need none: the reference's values are the exact moments
  rounded once (`FloatMoments.lean`), and the properties an engine's
  algorithm keeps (`StatProps.lean`) are definitions. `float-bounds/` proves the
  bounds over the reals for the standard model of rounding (`Arith.lean`,
  `CoreStats.lean`), and there only `NativeLink` (`Link.lean`) stays trusted:
  Lean's `Float` rounds as IEEE 754 binary64 does, and `exp` is the
  platform's `libm` within one ulp.
- The models of the engines' own functions, and that each engine matches
  its profile: `Impl.Faithful` (`Guards.lean`) for the functions the SQL
  calls unguarded, `Profile.duckdb` (`DuckDB/Profile.lean`, `EngineTables.lean`),
  `Profile.polars` and `Polars.*` (`Polars/Profile.lean`, `Polars/Shims.lean`),
  `Profile.spark` and `Spark.*` (`Spark/Profile.lean`, `Spark/Shims.lean`), and
  the shared shims' models `Shim.*` for each engine that writes them (`Shims.lean`),
  each from the engine's characterization facts
  (`engines/<engine>/facts/`, [how they are judged](../characterization/README.md)).
  DuckDB's own tests are replayed and fuzzed against the model; the profiles
  are tested on the engines and trusted.
- The table formats' change feeds (`ChangeFeed`, `TableFormat.lean`), a
  hypothesis of `Rel.cdf_sound` wherever Sverify reads a Delta change data
  feed; it is proved when the change is computed from two snapshots.
- An engine's run of a proved plan. `Engine.contract_sound` proves the
  contract on the rows the engine's model computes for the translated plan
  (`r'.eval cat E.impl`), under the engine's side condition (`Engine.NoRaiseSide` for DuckDB, `Engine.GuardFreeSide` for Polars and Spark, none for the reference). The chain from there to the engine's actual
  result, in order:
  1. the Lean theorem, `Engine.contract_sound` with the engine's
     `Engine.Sound` (`Sound.lean`); `Engine.polars_sound` and
     `Engine.spark_sound` also take `Engine.GuardFreeData`, preconditions on
     the catalog and the size hypothesis. From the checker's report it is
     `ContractCheck.check_proved_on` and its corollaries
     (`check_proved_on_duckdb`, `check_proved_on_polars`,
     `check_proved_on_spark`), each side condition taken from report fields;
  2. the round trip: the SQL or Polars code written for the plan is
     `E.lower` of it;
  3. the runtime checks: the schema read against `E.table`, the session
     pinned to the profile, the engine's version against the tested rows;
  4. the claim that the engine runs its model (`Engine.Runs`): the engine's
     actual result is one its table allows. Its evidence is the engine facts
     and replays behind each tested row of `Engine.Refines`, which the theorem
     does not carry. `Engine.contract_sound_runs` carries the contract to that
     result where `transferB T Profile.reference.table E.table` holds; it
     fails at `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on
     every engine, `null_order` without a preference on Polars and Spark, and
     integer overflow on Polars. There `Engine.contract_sound_runs_near` takes
     `Rel.FloatOpenSafeP` over the engine's table instead: every result the
     table allows is, up to the plan's observation, one of the reference's
     orders. For an aggregate at the root, `Rel.floatOpenSafeP_aggregate`
     discharges it from `Rel.SumsNear` (each double `SUM` and `AVG` the table
     allows is near the correctly rounded one over the groups it reads), and
     `Engine.polars_sum_example` applies the theorem to a double `SUM` on
     Polars with only `Engine.Runs` open. For a `SUM`, the checker's own
     tolerance covers D35's bound where `SumTolCovers` holds
     (`Measure.sumNear_of_tol`); for an `AVG`, `Rel.SumsNear` stays a
     hypothesis until track A's follow-up (rulings 135 (b) and 146). Other shapes (a double `SUM` read by
     a filter, a join or a key) are the tolerance bound
     [tracked](https://github.com/AlexanderNenninger/substrait-lean/issues/929).
     For a plan in which no double occurs (`Rel.mayDouble`) and no measure
     is open (`Rel.closedB`), `Rel.floatOpenSafeP_of_noDouble` discharges it
     where the table, with the reference's choices at the options only
     doubles read (`floatOnlyOptions`), transfers (`transferB`); the run
     plan's `near` gate checks both at each built-in engine (ruling 154).
     The rows are taken to have the request's kinds (`Catalog.HasKinds`),
     which the gate reads as `Request.tableKinds` and does not check of the
     data, and a plugin's table stays open. It stays open for plans with a double, and for plans without one that read
     an option where the table leaves the reference outside that list (an
     integer `MIN`, `MAX` or `AVG` at every built-in engine, through
     `list_null_order` and `avg_int_result`).

  An engine that raises commits nothing: a runtime obligation of the sink,
  beside `Engine.Runs`. Raising only where the reference may is a separate claim
  (`Rel.duckdb_refines`' second part), outside this chain.

  Beside `Engine.Runs`, the margin check of a threshold filter on a double `SUM` or
  `AVG` (`Rel.marginCheck`): that the check's aggregate and the plan's
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

  Beside `Engine.Runs`, the bound on
  [summation orders](float-bounds.md): `Rel.AllowedP` takes `SumBound` (a
  double `SUM` within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact sum) for every
  non-`EXACT` `sum_order`, of the codes as they are and of the canonical codes
  (`-0.0` read as `+0.0`; D35, amended 2026-11-21 by ruling 242). For the
  orders with a shape (`ANY`, `PAIRWISE`, `SEQUENTIAL`: `FloatSums`) both
  clauses are proved from the shape under the core's rounding
  (`FloatBridge.FloatSums.sumBound`, `float-bounds/FloatBridge/Sums.lean`; the
  canonical one by `FloatSums.canonV`, since IEEE addition treats the two zeros
  alike but for the sign of a zero result). For Kahan's sum (`COMPENSATED`)
  and a constant run's product (`SCALED_CONSTANT`) both are justified by
  `float-bounds`' `Rnd.kahan_near` and `TreeSum.const` over the reals; those
  algorithms written on the core's codes,
  [tracked](https://github.com/AlexanderNenninger/substrait-lean/issues/1196), retire the rest.
- Black boxes are DuckDB's functions: each black box means the function
  DuckDB computes under its name, and keeps its row's laws, tested by
  `python/tests/test_black_box.py` (DuckDB on the SQL against DuckDB on the
  plan Lean writes back, and the laws on random data). The evaluators behind
  black boxes and regular expressions (`implemented_by` in `BlackBox.lean`,
  `Regex.lean` and `Digest.lean`, and `Text.lean`'s six:
  `ilike`, `regexMatch`, `regexExtract`, `regexReplace`, `md5`, `sha256`) are
  read by no proof;
  the proofs use only each black box's declared laws, which hold of the
  model by the clamp (`Scalar.call` keeps the sample where a law breaks) and
  of DuckDB by the tests; the checker refuses rows where the clamp applies. The search evaluators
  (`implemented_by` in `LoweringSearch.lean`, `DuckDB/LiftSearch.lean` and
  `Obligations.lean`) read profiles, functions and hints while a generator
  or a table check elaborates; no theorem reads them.
