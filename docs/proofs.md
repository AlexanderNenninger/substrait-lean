# A map of the proofs

Sverify's guarantees are theorems of the Lean project in
[`SubstraitLean/`](../SubstraitLean) and
[`float-bounds/`](../float-bounds). This page names the theorems each
guarantee rests on, what each of them assumes, and the one job of every
module. [How it works](how-it-works.md) explains the checks in prose.

## The guarantees and their theorems

Each theorem below is stated over one layer of the semantics, named in the
Layer column: `eval`, `Rel.eval`'s result
([reference-semantics.md](reference-semantics.md)); `OrderAllowed`, every
row order the reference allows; `Allowed`, every result `Rel.Allowed`
allows; `AllowedP`, a profile's allowed results; `Bags`, results as
multisets; `Equiv` and `Near`, results equal up to an observation or within a
tolerance; `RefinesUpTo`, one plan refining another; `zeval`, the Z-set
evaluation of changes. An `_all` twin of a theorem over `eval` states it
over `OrderAllowed`, and `Rel.eval_orderAllowed` gives the one from the
other. Each theorem assumes the catalog is well formed (`Catalog.WF`), the
plan too (`Rel.WF`, decided by `checkWF`), and that the input rows meet the
contract's preconditions.

| Guarantee | Layer | Theorem | Module |
|---|---|---|---|
| A proved postcondition is TRUE on every output row | `eval` | `contract_sound` | `Contracts/Sound.lean` |
| … in every row order the reference allows | `OrderAllowed` | `contract_sound_all` | `Contracts/Sound.lean` |
| The same on one hypothesis, the analysis's (`Knowledge`) | `eval`, `OrderAllowed` | `Knowledge.contract_sound`, `Knowledge.contract_sound_all`, `Knowledge.duckdb_sound` | `Knowledge.lean` |
| The analysis is sound: what it knows of a relation holds of its rows | `eval`, `OrderAllowed` | `Rel.analyse_sound`, `Rel.analyse_sound_all` | `Knowledge.lean` |
| The abstract evaluation bounds every column of every row | `eval`, `OrderAllowed` | `Rel.aeval_sound`, `Rel.aeval_sound_all` | `Contracts/Sound.lean` |
| The relational facts derived through a plan hold of its rows | `eval`, `OrderAllowed` | `Rel.facts_sound`, `Rel.facts_sound_all` | `Contracts/Facts.lean` |
| A plan's row bound holds | `eval`, `OrderAllowed` | `Rel.maxRows_sound`, `Rel.maxRows_sound_all` | `Contracts/Plan.lean` |
| A derived key holds on the output | `eval`, `OrderAllowed` | `Rel.keys_sound`, `Rel.keys_sound_all` | `Keys.lean` |
| A window's result does not depend on how its ties are broken | `eval`, `OrderAllowed` | `Rel.window_deterministic`, `Rel.keyedWindows_soundAll` | `Keys.lean` |
| A plan with no reported issue raises no runtime error | `eval` | `Rel.mayIssues_sound` | `Safety.lean` |
| Row caps rule out `SUM` overflow | `eval` | `Rel.issuesCapped_sound`, `Rel.capJoins_eval` | `Rows.lean` |
| A well-formed plan on a well-formed catalog gives rows of its declared arity | `eval` | `Rel.eval_arity` | `Rel.lean` |
| The checker decides well-formedness | the plan | `Rel.checkWF_iff` | `Check.lean` |
| A well-kinded plan evaluates to its kinds | `eval` | `Rel.kinds_sound`, `Expr.kindT_sound` | `Kinds.lean` |
| The fast evaluator computes the specification | `eval` | `Rel.evalFast_eq` | `EvalFast.lean` |
| `Rel.eval` gives a result the reference allows | `eval`, `Allowed` | `Rel.eval_allowed` | `Allowed.lean` |
| Every row order the reference allows is one `Rel.Allowed` allows | `OrderAllowed`, `Allowed` | `Rel.orderAllowed_allowed` | `Ties.lean` |
| An operator that factors through the multiset has one meaning over every order; a plan without choices one multiset, an unordered `FETCH` several | `OrderAllowed`, `Bags` | `Sem.eq_iff_of_permInv`, `Measure.orderAllowed_eq`, `Rel.bags_iff_perm_eval`, `Rel.bags_fetch_two` | `Seam.lean` |
| DuckDB, under its default settings, computes the reference | `eval` | `Rel.duckdb_sound` | `DuckDBProfile.lean` |
| The generated DuckDB lowering computes the reference | `eval`, `AllowedP` | `Lowering.lowerRel_sound`, `Rel.duckdb_refines` | `Lowering.lean`, `Obligations.lean` |
| A lowered plan with the guards of issues it never meets dropped computes the reference, or raises | `eval` | `Lowering.lowerRelWith_sound`, `Lowering.lowerRelWith_mayIssues_sound` | `Lowering.lean` |
| DuckDB's templates without their guards (`to_sql(guards=False)`), for a plan with only assumed issues, compute the reference, or raise | `eval` | `Rel.duckdb_guardFree_sound`, `Lowering.duckdb_guardsFor_none` | `LoweringDuckDB.lean`, `LoweringDuckDB/On/Guards.lean` |
| Unless the shimmed plan raises, DuckDB returns a result the reference allows | `Allowed` | `Rel.duckdb_shim_allowed` | `Obligations.lean` |
| Polars, after the shims, computes the reference | `eval` | `Rel.polars_sound` and one `Polars.<shim>` lemma per shim | `PolarsShims.lean` |
| Spark under ANSI, after the shims, computes the reference | `eval` | `Rel.spark_sound` and one `Spark.<shim>` lemma per shim | `SparkShims.lean` |
| Dropping the SQL's guards changes no result: a plan whose only possible issues are integer `SUM`s runs correctly without per-row checks | `eval` | `Rel.guardFree_sound`, `Rel.evalI_eq` | `Guards.lean` |
| Binding arguments to columns before writing keeps the rows and the errors | `eval` | `Rel.evalI_bindArgs`, `Rel.eval_bindArgs`, `Rel.raises_bindArgs` | `Bind.lean` |
| Each engine profile refines the core | `AllowedP` | `Rel.allowed_duckdb_core`, `Rel.allowed_polars_core`, `Rel.allowed_substrait_core` | `EngineTables.lean`, `SubstraitProfile.lean` |
| An engine's functions are ones its table allows (`Impl.Within`): DuckDB's with IEEE operations where they do not raise, Polars's written plan; a plan that does not raise computes the same rows with them | `AllowedP` | `Profile.duckdb_withinOk`, `Polars.written_within`, `Profile.okImpl_within`, `Rel.eval_okImpl`, `Rel.AllowedE.allowedP` | `Engine.lean` |
| A verified contract holds on each engine's model (#900): where the translated plan does not raise, the rows the model of DuckDB (default settings), Polars, Spark or the reference computes for it are a result the reference allows (`Engine.Sound`), so the postconditions hold on them; on the engine's actual result, D16's claim, where the engine's choices are the reference's at the plan's options (`htr`) | `Allowed` | `Engine.duckdb_sound`, `Engine.polars_sound`, `Engine.spark_sound`, `Engine.reference_sound`, `Engine.Sound.allowedP`, `Engine.contract_sound`, `Engine.contract_sound_runs` | `EngineSound.lean` |
| Equal up to an observation: an equivalence, and a finer observation's equality implies a coarser one's | `Equiv`, `Near` | `Relation.Equiv_mono`, `Relation.Equiv_exact`, `Relation.Near_add` | `ObsEquiv.lean` |
| A rewrite refines the plan up to an observation; `optimize` up to the order of rows; an unsorted plan does not refine its `ORDER BY` twin exactly | `RefinesUpTo` | `Rel.refines_of_perm`, `Rel.refines_of_same`, `Rel.optimize_refines`, `Rel.unsorted_refinesBag_not_refines` | `Allowed.lean`, `Semantic.lean` |
| A narrowed postcondition proved on every order holds on every allowed result of a plan whose open measures nothing reads to choose rows (`Rel.FloatOpenSafe`): a closed plan (`Rel.closedB`, decidable: no `VAR_*`, `STDDEV_*`, `COVAR_*`, `CORR` or `QUANTILE_CONT`; a double `SUM` or `AVG` is closed since D25), or an aggregate over one | `Allowed` | `contract_sound_allowed`, `contract_sound_allowed_closed`, `Rel.floatOpenSafe_of_closed`, `Rel.floatOpenSafe_aggregate` | `AllowedNear.lean` |
| An open measure's allowed value, and an aggregate's allowed output, are equal up to the order of the additions to an order's | `Allowed`, `Equiv` | `Measure.Allowed.near_eval`, `measures_near`, `aggAllowed_near` | `AllowedNear.lean` |
| A postcondition that depends on nothing the observation ignores, or a comparison narrowed by the tolerance, holds on every result equal up to the observation | `Equiv` | `Expr.robust_of_depends`, `Expr.robust_of_depends_canon`, `Expr.robust_of_robustB`, `Expr.narrow_sound` | `Robust.lean` |
| Sources within a tolerance give a result within the plan's fold of it (`Rel.tol`), node after node in a pipeline; tolerances add along a chain in one cell (`M∞`) and summed over the rows (`M₁`) | `Near` | `Rel.plan_near`, `Rel.pipeline_near`, `Relation.NearT.add`, `Relation.NearL1.add` | `Lipschitz.lean` |
| Sources within an `M₁` budget give a result within the plan's `M₁` fold (`Rel.tol1`): a union adds budgets, a cross counts each side's once per row of the other, and a `SUM` or `AVG` grouped by exact keys takes its column's budget once plus a cost per input row (the groups' budgets sum within the input's) | `Near` | `Rel.plan_nearL1`, `PairsWithin.cross`, `PairsWithin.groups`, `aggregateEval_nearL1`, `Measure.l1_cell` | `LipschitzL1.lean` |
| A `SUM` or `AVG` of a tolerated column is within the fold's bound, from the column's range and the input's rows in the sources' knowledge, and a `MIN` or `MAX` within its argument's; the engine's columns of reference codes are tracked | `Near` | `Measure.tolOut_cell`, `Measure.minMaxOut_cell`, `aggregateEval_near`, `Rel.refOn`, `Rel.rowsK_sound` | `Lipschitz/Measures.lean`, `Lipschitz/Arith.lean` |
| `x ± y`, `x · y`, `x / c`, and `x / y` with `y`'s range clear of zero, of tolerated doubles (D31) are within the fold's bounds, from the operands' ranges in the sources' knowledge | `Near` | `Expr.arithTol_sound`, `Expr.tolA_sound`, `fadd_near`, `fmul_near`, `fdiv_lit_near`, `fdiv_near`, `round_pair₂` | `Lipschitz/Arith.lean` |
| A correctly rounded `SUM` or `AVG` of values paired within `e` codes is within `g·(e + 1)` (`SUM`) or `e + 1` (`AVG`) codes plus the rounding of both sides; of values whose distances sum to `D`, within `D + g` or `D + 1` (`M₁`). Both from one bound on the exact sums | `Near` | `floatSumCR_of_exact`, `floatAvgCR_of_exact`, `floatSumCR_near`, `floatAvgCR_near`, `floatSumCR_nearL1`, `floatAvgCR_nearL1`, `Measure.fsum_near`, `Measure.avg_near` | `FloatNear.lean`, `Lipschitz/Basic.lean`, `LipschitzL1.lean` |
| A result one profile allows, another allows too, option by option | `AllowedP` | `Rel.AllowedP_mono`, `Rel.AllowedP_transfer` | `AllowedP.lean`, `Transfer.lean` |
| A delta plan computes the change of the view | `zeval` | `Rel.delta_correct`, `Rel.incremental_sound` | `Incremental.lean` |
| `Rel.eval` is weighted evaluation over `Nat`: every unordered arm (filter, project, emit, cross, joins, union, sort, `DISTINCT`, semi and anti joins, unnest) at once, with the ordered and aggregate nodes read through the seam | `eval` | `Rel.eval_eq_evalK` | `WSet.lean` |
| The delta plan computes the change of the view for any weights; over a semiring, weight-1 rows give `Rel.eval`; changing the weights by a map that keeps `*` and `1` commutes with evaluation | `zeval`, `eval` | `Rel.incrementalK_sound`, `Rel.delta_evalK_eq`, `Rel.evalK_lift`, `Rel.evalK_mapW` | `WSet.lean` |
| The weight-column encoding runs Z-set plans on a bag engine | `zeval` | `Rel.weighted_eval` | `Weighted.lean` |
| Union-free terms add up to the plan | `zeval` | `Rel.zeval_terms` | `Terms.lean` |
| `COUNT`, `SUM` and `DISTINCT` are maintained from their state | `eval` | `aggregate_maintained`, `distinct_maintained` | `IncrementalAgg.lean` |
| `SUM` and `AVG` of doubles are maintained exactly, with no drift over any batches | `eval` | `floatState_sound`, `fsum_no_drift` | `IncrementalFloat.lean` |
| `MIN`, `MAX` and exact `AVG` are maintained under inserts | `eval` | `extreme_maintained`, `finish_iavg` | `IncrementalMinMax.lean` |
| Semi and anti joins are maintained from a match count | `eval` | `semi_maintained` | `IncrementalSemi.lean` |
| Recomputing only the touched groups or frames is exact | `eval` | `touched_sound`, `touched_window_sound`, `framed_sound` | `TouchedGroups.lean`, `TouchedFrames.lean` |
| Dropping final time buckets from the state changes no result | `eval` | `retention_sound`, `expiry_sound` | `Retention.lean` |
| A change feed gives the change of every view | `zeval` | `Rel.cdf_sound`, `ChangeFeed.of_diff`, `ChangeFeed.of_changed_files` | `TableFormat.lean` |
| A linear plan runs shard by shard | `eval` | `Rel.eval_sharded`, `Rel.eval_twoPhase` | `Partition.lean` |
| `--shard`'s split plans compute the plan | `eval` | `Rel.shardSplit_sound` | `Partition.lean` |
| Skipping files by their statistics changes no result | `eval` | `Rel.eval_pruned`, `stats_prune`, `strStats_prune`, `prune_sound` | `Pruning.lean`, `TableFormat.lean` |
| An implied predicate on a base table keeps every output row | `eval` | `Rel.need_sound` | `Implied.lean` |
| Contracts compose across a pipeline | `eval`, `zeval` | `Rel.stack_sound`, `Rel.chain_sound` | `Compose.lean` |
| The rows quarantine keeps meet every precondition and key | `eval` | `Catalog.kept_sound`, `kept_pre`, `kept_keys` | `Quarantine.lean` |
| Algebraic rewrites keep the result: filters merge (`Filter(Filter(r,p),q) = Filter(r, p AND q)`, under three-valued logic too), a true filter and a fetch of zero rows go, filters distribute over `UNION ALL` and push below a `ProjectRel` or into a side of a `CrossRel`, `UNION ALL` commutes up to bag equivalence, an inner join is a filtered cross product, and emitting a `ProjectRel`'s input columns removes it | `eval` | `filter_filter`, `filter_true`, `fetch_zero_none`, `filter_unionAll`, `unionAll_comm`, `join_inner_eq_filter_cross`, `filter_project_pushdown`, `filter_cross_pushdown_left`, `emit_project_identity` | `Rewrites.lean` |
| Rewrites from contract facts and keys keep the result | `eval` | `Rel.optimize_sound` | `Semantic.lean` |
| A double `SUM` or `AVG` is within the reported `epsilon` | the reals (`float-bounds/`) | `StdModel.epsilon_sum_cr`, `StdModel.epsilon_avg_cr` (against the reference's correctly rounded value, D25), `StdModel.epsilon_sum_rel`, `StdModel.epsilon_avg_rel` | `float-bounds/FloatBounds/Epsilon.lean` |
| Sharded double sums are near the sequential sum | the reals (`float-bounds/`) | `StdModel.sharded_near`, `StdModel.sharded_avg_near` | `float-bounds/FloatBounds/Shard.lean` |
| A group's double sum, in any order an engine adds, is within `(γₙ + u) · Σ(\|xᵢ\| + tiny)` of the reference's; a group passing the engine-computed check `\|fl(v − t)\| > fl(cₙ · fl(A + n · tiny))` is farther than twice that from `t`, so every evaluation of its sum lies on the reference's side of `t` | the reals (`float-bounds/`) | `StdModel.epsilon_group`, `StdModel.mag_le_absSummed`, `StdModel.check_sound`, `margin_sound`, `StdModel.margin_check` | `float-bounds/FloatBounds/Margin.lean` |
| A sink's refreshes, with crashes, late writes of crashed processes, lost acknowledgements, racing writers, other applications' commits and deploys, never apply a change to a table it was not computed from, and the sink's record names its table. They assume only that the state is reachable (`Reachable`), for a durable source and writers deciding as `Refresh.next` (`tests/test_refresh_next.py`) | the refresh protocol | `Refresh.no_corruption`, `Refresh.record_describes_table` | `Refresh.lean` |

`Examples.lean` prints the axioms of the main theorems with
`#print axioms`, so a build shows what each rests on.

## What is trusted

The theorems are about the model. What links the model to the plans and the
engines is trusted, and kept small. This list is the one home of it; the
other pages link here.

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
  they call the checkers and print JSON. On the Python side, the glue of
  incremental views (change tables, consolidation, merge).
- The exact state of a maintained `SUM` or `AVG` of doubles
  (`python/src/sverify/_exact_sum.py`, #918). Lean proves that the state, an
  integer per group, finishes to `floatSumCR` of the current rows after any
  sequence of batches (`LinearAgg.fsum_no_drift`). Holding that integer in
  Python, adding up each batch's contributions to it (the engine gives each
  changed row's value and weight with the checked `contrib` plan) and
  rounding it once with CPython's `int / int` (correctly rounded, ties to
  even) are trusted. `tests/test_exact_sum.py` checks the finish against the
  checker's `floatSumCR` and `floatAvgCR`, NaN, `±∞`, `-0.0` and subnormals
  among the values.
- Where an engine evaluates an expression. Lean proves which rows an
  expression may raise on under `Rel.eval`; which expressions an engine
  evaluates, on which rows, is trusted. `Rel.loose` models an engine that
  evaluates an expression on more rows than the plan says (merged filters,
  eager `AND` and `OR`), and the facts record what each engine does
  ([duckdb-exec-filter-pushdown](../characterization/duckdb/facts/duckdb-exec-filter-pushdown.json),
  [DD-7](../upstream/bugs/DD-7.json); `Safety.lean`'s header).
- Doubles. Lean's `Float` is an opaque `extern` to C `double`, trusted to be
  IEEE binary64 for arithmetic. The conversions between integers, decimals
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
  `Profile.polars` and `Polars.*` (`PolarsProfile.lean`, `PolarsShims.lean`)
  and `Profile.spark` and `Spark.*` (`SparkProfile.lean`, `SparkShims.lean`),
  each from the engine's characterization facts
  (`characterization/<engine>/facts/`, [how they are judged](../characterization/README.md)).
  DuckDB's own tests are replayed and fuzzed against the model; the profiles
  are tested on the engines and trusted.
- The table formats' change feeds (`ChangeFeed`, `TableFormat.lean`), a
  hypothesis of `Rel.cdf_sound` wherever Sverify reads a Delta change data
  feed; it is proved when the change is computed from two snapshots.
- An engine's run of a verified plan. `Engine.contract_sound` proves the
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
- Black boxes are DuckDB's functions: each black box means the function
  DuckDB computes under its name, and keeps its row's laws, tested by
  `python/tests/test_black_box.py` (DuckDB on the SQL against DuckDB on the
  plan Lean writes back, and the laws on random data). The evaluators behind
  black boxes and regular expressions (`implemented_by` in `BlackBox.lean`,
  `Regex.lean`, `Digest.lean`, `VarcharCasts.lean`) are read by no proof;
  the proofs use only each black box's declared laws.

## The modules

One line per module, by layer: values and expressions first, then
relations, then the checkers on them, then the tables, profiles and
generators, then the trusted reading and writing.

### Values and scalar functions

| Module | Job |
|---|---|
| `FloatFormat.lean` | Binary floating-point formats as integer codes in the SQL order |
| `Float.lean` | Doubles and timestamps as integer codes |
| `Value.lean` | Nullable values, rows and bag-semantics relations |
| `FloatMoments.lean` | Exact dyadic moments (`n Σx² − (Σx)²` and the co-moment) and correctly rounded square roots of rationals, for #918 |
| `FloatExact.lean` | `SUM` and `AVG` of doubles as the exact sum rounded once (D25), with their bounds |
| `FloatArith.lean` | `+ − × ÷` of doubles as the exact result rounded once (D31), IEEE 754's signed zeros and NaN, and their bounds (`add_scaled` …) |
| `FloatArithCheck.lean` | D31's operations against native doubles, bit for bit, on edge values, ties and every exponent |
| `BlackBox.lean` | The black-box functions' table: types, NULL handling, raising, laws |
| `VarcharCasts.lean` | Lean's evaluators of the casts from VARCHAR (black boxes, #806): DuckDB's value on a subset, the strings it rejects for sure, a panic elsewhere |
| `Digest.lean` | MD5 and SHA-256, the evaluators of two black boxes |
| `Regex.lean` | The regular-expression evaluator behind the regex black boxes |
| `Rounding.lean` | Exact `FLOOR`, `CEIL`, `ROUND` and double-to-integer casts on codes |
| `Conversions.lean` | Exact conversions between doubles, decimals and integers, with monotonicity |
| `Text.lean` | String functions and `LIKE` |
| `Time.lean` | `date_part` and `date_trunc` on the proleptic Gregorian calendar |
| `Numeric.lean` | Elementary functions of doubles and 64-bit bitwise operations |
| `Expr.lean` | Scalar expressions and their evaluation, with three-valued logic, over Lean's functions (`Impl.lean`) or an engine's (`Impl`) |
| `Order.lean` | The orders on values and rows that sorts, windows and `MIN`/`MAX` use |
| `Dedup.lean` | `dedup`, the first occurrence of each element, and its lemmas |
| `Forall2.lean` | `Forall2`, lists related element by element |
| `Reflect.lean` | Boolean checks the tables are proved with, by reflection |

### Relations and their evaluation

| Module | Job |
|---|---|
| `Window.lean` | Window functions over partitions, orders and frames |
| `Aggregate.lean` | `GROUP BY` and the measures; the trusted bounds of double sums |
| `Rel.lean` | The relational operators, arity, well-formedness and `Rel.eval`, one evaluator for the reference and an engine's functions |
| `OrderAllowed.lean` | `Rel.OrderAllowed`, the results of every order the reference leaves open, and `Rel.eval` as one of them |
| `EvalFast.lean` | A faster evaluator with hash joins, proved equal to `Rel.eval` |
| `Rewrites.lean` | Plan rewrites that keep a plan's meaning |
| `Check.lean` | `checkWF`, the executable well-formedness check |
| `Kinds.lean` | `Rel.inferKinds`, the kind checker, and its soundness |

### Incremental maintenance

| Module | Job |
|---|---|
| `WSet.lean` | Relations with weights in any `K`, `Rel.evalK`, delta rules and delta plans over `K` |
| `Incremental.lean` | Z-sets: `Rel.zeval` as `Rel.evalK` over `Int`, `Rel.zdelta` as the delta plan's output |
| `Weighted.lean` | Z-set plans as bag plans with a weight column |
| `Terms.lean` | Splitting a plan into union-free terms |
| `IncrementalAgg.lean` | Delta rules for `COUNT`, `SUM` and `DISTINCT`, over a measure's linear state (`LinState`) |
| `IncrementalFloat.lean` | The exact state of `SUM` and `AVG` of doubles, and its no-drift theorem |
| `IncrementalMinMax.lean` | Delta rules for `MIN`, `MAX` and exact `AVG` |
| `IncrementalSemi.lean` | Delta rules for semi and anti joins |
| `TouchedGroups.lean` | Recomputing only the groups a batch touches |
| `TouchedFrames.lean` | Recomputing only the window rows near a batch's changes |
| `Retention.lean` | Bounded state for time buckets under a lateness bound |
| `Refresh.lean` | The refresh protocol of a stored node, for a durable source, as a transition system; its safety from `Reachable` alone (#933) |

### Contracts, errors and keys

| Module | Job |
|---|---|
| `Write.lean` | `Rel` back to Substrait JSON, delta plans for engines (trusted) |
| `Contracts.lean` | The abstract interpreter behind contracts; re-exports its parts below |
| `Contracts/Lattice.lean` | Integer intervals (`Bound`), abstract values (`AVal`), `AVal.Mem` and `AVal.join` |
| `Contracts/Transfer.lean` | Abstract expression evaluation: `UnFn.abs`, `BinFn.abs`, `Expr.abs` |
| `Contracts/TransferSound.lean` | Its soundness, `Expr.abs_sound` |
| `Contracts/Refine.lean` | Refinement by filter conditions; `Expr.refine_sound` |
| `Contracts/Facts.lean` | Relational facts through a plan; `Rel.facts_sound` |
| `Contracts/Plan.lean` | Abstract plan evaluation: `Rel.maxRows`, `Rel.aeval` and its one pass, `Rel.lane` |
| `Contracts/Sound.lean` | `Rel.aeval_sound`, `contract_sound` |
| `Safety.lean` | Runtime errors and overflow; `Rel.mayIssues_sound` |
| `Infer.lean` | The bounds a contract needs to rule out overflow (untrusted, then proved) |
| `Rows.lean` | Row caps that rule out `SUM` overflow |
| `Keys.lean` | Derived keys and window tie-breaking |
| `Semantic.lean` | Rewrites justified by contract facts and keys |
| `Compose.lean` | Composing contracts across a pipeline |
| `Quarantine.lean` | The rows `on_violation="quarantine"` keeps |
| `Completeness.lean` | The converse of contracts for the IoT example |
| `Implied.lean` | Predicates a view implies on its base tables |

### Sharding and table formats

| Module | Job |
|---|---|
| `Partition.lean` | Sharded evaluation and two-phase aggregates |
| `Pruning.lean` | Skipping files and partitions by their statistics |
| `TableFormat.lean` | Change feeds and file statistics of Delta and Iceberg |

### Semantics as a relation, and the engine profiles

| Module | Job |
|---|---|
| `Allowed.lean` | `Rel.Allowed`, the results the reference allows |
| `Ties.lean` | Every row order the reference allows is one `Rel.Allowed` allows, and row caps keep them |
| `Knowledge.lean` | `Knowledge`, what the analysis knows of a relation, `Rel.analyse` and its one soundness theorem, the consumers on one hypothesis |
| `Choices.lean` | The values an open order allows on concrete data, a test oracle |
| `Seam.lean` | Order as an effect over the unordered core: `Lin`, `Sem`, the lifting lemma, and the multisets a plan may give (#928) |
| `StatProps.lean` | The properties any variance, covariance or correlation algorithm keeps; the written variance's NaN guard keeps them (`Stat.nanGuard_varStat`, DD-3) |
| `Functions.lean` | The function tables: names, anchors, groups, how the parser reads each |
| `Options.lean` | The option catalogue and each profile's choices |
| `AllowedP.lean` | `Rel.AllowedP`, the results a profile's table allows |
| `Observations.lean` | Observations and classes against the reference |
| `ObsEquiv.lean` | Equality up to an observation (`Relation.Equiv`), and within a tolerance (`Relation.Near`) |
| `Robust.lean` | Postconditions robust under an observation, and narrowing a comparison by a tolerance |
| `AllowedNear.lean` | Postconditions on every allowed result, every order of a double `SUM` or `AVG` among them |
| `FloatNear.lean` | Correctly rounded sums and means of doubles paired within a tolerance are near each other (#929) |
| `Engine.lean` | The Engine object (#900): an engine's profile, table, observation rows, translation and functions, with the proof that the table allows them; `AllowedE`, the per-plan `Refines` certificate |
| `EngineSound.lean` | What an engine's model is sound for (#900): `Engine.Sound` per engine, `Engine.contract_sound` on the model's rows, and `Engine.contract_sound_runs` on the actual output under the transfer check |
| `Lipschitz.lean` | Tolerance composition (#929): the fold of a plan's tolerance, `plan_near`, the pipeline rule and the `M₁` metric |
| `Lipschitz/Basic.lean` | Tolerance composition (#929): cells, rows and matchings within a tolerance, the operators row by row |
| `Lipschitz/Measures.lean` | Tolerance composition (#929): the columns of reference codes, the fold's `SUM` and `AVG` rows |
| `Lipschitz/Arith.lean` | Tolerance composition (#929): the arithmetic, `MIN` and `MAX` rows, groups and the sources' row bound |
| `LipschitzL1.lean` | The `M₁` fold (#929): budgets summed over matched rows, through filters, projections, unions, crosses and joins |
| `Profile.lean` | Engine profiles as outcomes per function; the reference is one |
| `DuckDBProfile.lean` | `Profile.duckdb` under DuckDB's settings, as the SQL printer writes it, and `Rel.duckdb_sound` |
| `Guards.lean` | Guard elimination for the SQL writers |
| `EngineTables.lean` | DuckDB's and Polars's choice tables, refining the core |
| `PolarsShims.lean` | The Polars shims, proved against a model of Polars's functions |
| `PolarsProfile.lean` | `Profile.polars`, the semantics under `semantics="polars"` |
| `SparkShims.lean` | The Spark shims, proved against a model of Spark under ANSI |
| `SparkProfile.lean` | `Profile.spark`, the semantics under `semantics="spark"` |
| `SubstraitProfile.lean` | Substrait's own semantics as a profile |
| `Transfer.lean` | The options a plan meets, and transfer between profiles |
| `Obligations.lean` | The realizability table: how each engine discharges each option |
| `Epsilon.lean` | The float tolerance of a plan's double outputs |
| `EngineRobust.lean` | Postconditions that hold on every engine's doubles: each bounded column widened by its `ε` and kept to its sign (#1045) |

### Lowering and lift

| Module | Job |
|---|---|
| `Lowering.lean` | Lowerings: tables of proved templates per engine profile |
| `Bind.lean` | Binding nested call arguments to projected columns before a plan is written (#821) |
| `LoweringHint.lean` | The hints that tell the lowering search which template to try first |
| `LoweringCache.lean` | The lowering hints (generated) |
| `LoweringSearch.lean` | `generate_lowering`, the lowering search |
| `LoweringDuckDB.lean` | The DuckDB lowering's table and its exports |
| `LoweringDuckDB/Lemmas.lean` | Lemmas the generated DuckDB lowering computes with |
| `LoweringDuckDB/Schemas.lean` | DuckDB's hand-written template schemas, for the search |
| `LoweringDuckDB/On/*.lean` | The DuckDB lowering's entries, one module per area, and their guards (generated) |
| `DuckDBSQL.lean` | What each DuckDB SQL function means under each semantics |
| `LiftHint.lean` | The hints that tell the lift search which template to try first |
| `LiftCache.lean` | The lift hints (generated) |
| `LiftSearch.lean` | `generate_lift`, the lift search |
| `LiftDuckDB.lean` | The lift's tables and their exports |
| `LiftDuckDB/Duckdb/*.lean`, `LiftDuckDB/Reference/*.lean` | The lift's entries per semantics, one module per area (generated) |
| `Generated.lean` | The `check_generated` switch for the generated modules |

### Reading, writing and the CLI

| Module | Job |
|---|---|
| `Parse.lean` | Substrait protobuf-JSON to `Rel` (trusted) |
| `Pretty.lean` | Rendering of values, expressions and plans |
| `ContractCheck.lean` | `--contract`: proving postconditions and keys from preconditions |
| `ShardCheck.lean` | `--shard`: per-shard and combining plans |
| `Examples.lean` | Concrete plans checked with `#guard`, and `#print axioms` |
| `Main.lean` | The `substrait-check` CLI: `checkerMain` over `builtinEngines` |
| `SubstraitCheck.lean` | `Checker.checkerMain`, the CLI over a list of engine profiles, which a package with a profile of its own builds on ([engine profiles from outside](engine-profiles.md#engine-profiles-from-outside)) |
| `SubstraitCheckExamples/DummyEngine.lean` | A test profile, `dummy`, added from outside and checked with `#check_engine_profiles` |
| `scripts/RegenLowering.lean`, `scripts/RegenLift.lean` | The drivers of `poe regen-lowering` and `poe regen-lift` |

### `float-bounds/`

A separate Lake project with Mathlib, which proves over the reals what the
core trusts about doubles ([float-bounds.md](float-bounds.md)).

| Module | Job |
|---|---|
| `Model.lean` | The standard model of binary64 rounding |
| `Link.lean` | `NativeLink`, the trusted link to Lean's `Float` |
| `Sum.lean` | Rounded sums and means in list order |
| `Tree.lean` | Sums in any order the reference allows |
| `Kahan.lean` | Kahan's compensated sum |
| `Core.lean` | The core's trusted sum and mean bounds, proved |
| `Epsilon.lean` | The `epsilon` bounds `--contract` reports |
| `Propagate.lean` | `epsilon` through double arithmetic |
| `Shard.lean` | Sharded sums against the sequential sum |
| `Margin.lean` | A threshold's margin, checked on the data: a group's sum against the reference's, and the check the engine computes |
| `Arith.lean` | One double operation, bounded from its inputs |
| `Moments.lean` | Exact moments and the scale of the variance bounds |
| `Variance.lean` | Variance, covariance and correlation bounds for any algorithm |
| `Textbook.lean` | The textbook one-pass algorithm |
| `TwoPass.lean`, `TwoPassRel.lean` | Lean's two-pass algorithm, absolute and relative to the variance |
| `CovTwoPass.lean` | Two-pass covariance, relative to the spread |
| `Welford.lean`, `WelfordRel.lean` | Welford's update and Chan's merge, absolute and relative |
| `MergeRel.lean`, `CovRel.lean` | Chan's merge and the covariance, relative to the spread |
| `Chan.lean`, `ChanCorr.lean` | DuckDB's `VAR_*`, `STDDEV_*` and `CORR` meet `StatProps` |
| `CoreStats.lean`, `CoreKappa.lean` | The statistical properties of `StatProps.lean`, proved over the reals; trusted facts before D30 |

## Generated modules

Each generated module starts with a header that says so and how to
regenerate it. Don't edit them by hand.

| Modules | Regenerate with | When |
|---|---|---|
| `LoweringDuckDB/On/*.lean` | `poe regen-lowering` (from `python/`) | `Profile.duckdb`, the generator or the model's functions change |
| `LiftDuckDB/Duckdb/*.lean`, `LiftDuckDB/Reference/*.lean` | `poe regen-lift` (from `python/`) | `DuckDBSQL.lean`, the generator or the model's functions change |
| `LoweringCache.lean` | `.lake/build/bin/substrait-check --lowering-cache > SubstraitLean/LoweringCache.lean` | after a regenerated lowering, to keep the search quick |
| `LiftCache.lean` | `.lake/build/bin/substrait-check --lift-cache > SubstraitLean/LiftCache.lean` | after a regenerated lift |

A build only checks the generated entries, and only when `check_generated`
is on (`Generated.lean`); CI turns it on whenever a Lean input changes. Both
regeneration tasks cap Lean at 6 GB.
