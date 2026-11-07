# A map of the proofs

Sverify's guarantees are theorems of the Lean project in
[`SubstraitLean/`](../SubstraitLean) and
[`float-bounds/`](../float-bounds). This page names the theorems each
guarantee rests on, what each of them assumes, and the one job of every
module. [How it works](how-it-works.md) explains the checks in prose.

## The guarantees and their theorems

Every theorem below is about `Rel.eval`, the reference semantics of a plan
([reference-semantics.md](reference-semantics.md)), or about `Rel.Allowed`,
the set of results the reference allows for it. Each assumes the catalog is
well formed (`Catalog.WF`), the plan too (`Rel.WF`, decided by `checkWF`),
and that the input rows meet the contract's preconditions.

| Guarantee | Theorem | Module |
|---|---|---|
| A proved postcondition is TRUE on every output row | `contract_sound` | `Contracts.lean` |
| … in every row order the reference allows | `contract_sound_all` | `Contracts.lean` |
| A derived key holds on the output | `Rel.keys_sound`, `Rel.keys_sound_all` | `Keys.lean` |
| A window's result does not depend on how its ties are broken | `Rel.window_deterministic`, `Rel.keyedWindows_soundAll` | `Keys.lean` |
| A plan with no reported issue raises no runtime error | `Rel.mayIssues_sound` | `Safety.lean` |
| Row caps rule out `SUM` overflow | `Rel.issuesCapped_sound`, `Rel.capJoins_eval` | `Rows.lean` |
| The checker decides well-formedness | `Rel.checkWF_iff` | `Check.lean` |
| A well-kinded plan evaluates to its kinds | `Rel.kinds_sound`, `Expr.kindT_sound` | `Kinds.lean` |
| The fast evaluator computes the specification | `Rel.evalFast_eq` | `EvalFast.lean` |
| `Rel.eval` gives a result the reference allows | `Rel.eval_allowed` | `Allowed.lean` |
| An operator that factors through the multiset has one meaning over every order; a plan without choices one multiset, an unordered `FETCH` several | `Sem.eq_iff_of_permInv`, `Measure.orderAllowed_eq`, `Rel.bags_iff_perm_eval`, `Rel.bags_fetch_two` | `Seam.lean` |
| DuckDB, under its default settings, computes the reference | `Rel.duckdb_sound` | `Profile.lean` |
| The generated DuckDB lowering computes the reference | `Lowering.lowerRel_sound`, `Rel.duckdb_refines` | `Lowering.lean`, `Obligations.lean` |
| Polars, after the shims, computes the reference | `Rel.polars_sound` and one `Polars.<shim>` lemma per shim | `PolarsShims.lean` |
| Spark under ANSI, after the shims, computes the reference | `Rel.spark_sound` and one `Spark.<shim>` lemma per shim | `SparkShims.lean` |
| Dropping the SQL's guards changes no result | `Rel.guardFree_sound` | `Guards.lean` |
| Binding arguments to columns before writing keeps the rows and the errors | `Rel.evalI_bindArgs`, `Rel.eval_bindArgs`, `Rel.raises_bindArgs` | `Bind.lean` |
| Each engine profile refines the core | `Rel.allowed_duckdb_core`, `Rel.allowed_polars_core`, `Rel.allowed_substrait_core` | `EngineTables.lean`, `SubstraitProfile.lean` |
| Equal up to an observation: an equivalence, and a finer observation's equality implies a coarser one's | `Relation.Equiv_mono`, `Relation.Equiv_exact`, `Relation.Near_add` | `ObsEquiv.lean` |
| A rewrite refines the plan up to an observation; `optimize` up to the order of rows; an unsorted plan does not refine its `ORDER BY` twin exactly | `Rel.refines_of_perm`, `Rel.refines_of_same`, `Rel.optimize_refines`, `Rel.unsorted_refinesBag_not_refines` | `Allowed.lean`, `Semantic.lean` |
| A narrowed postcondition proved on every order holds on every allowed result of a plan whose open measures nothing reads to choose rows (`Rel.FloatOpenSafe`): a closed plan (`Rel.closedB`, decidable: no `VAR_*`, `STDDEV_*`, `COVAR_*`, `CORR` or `QUANTILE_CONT`; a double `SUM` or `AVG` is closed since D25), or an aggregate over one | `contract_sound_allowed`, `contract_sound_allowed_closed`, `Rel.floatOpenSafe_of_closed`, `Rel.floatOpenSafe_aggregate` | `AllowedNear.lean` |
| A postcondition that depends on nothing the observation ignores, or a comparison narrowed by the tolerance, holds on every result equal up to the observation | `Expr.robust_of_depends`, `Expr.robust_of_robustB`, `Expr.narrow_sound` | `Robust.lean` |
| A result one profile allows, another allows too, option by option | `Rel.AllowedP_mono`, `Rel.AllowedP_transfer` | `AllowedP.lean`, `Transfer.lean` |
| A delta plan computes the change of the view | `Rel.delta_correct`, `Rel.incremental_sound` | `Incremental.lean` |
| The weight-column encoding runs Z-set plans on a bag engine | `Rel.weighted_eval` | `Weighted.lean` |
| Union-free terms add up to the plan | `Rel.zeval_terms` | `Terms.lean` |
| `COUNT`, `SUM` and `DISTINCT` are maintained from their state | `aggregate_maintained`, `distinct_maintained` | `IncrementalAgg.lean` |
| `MIN`, `MAX` and exact `AVG` are maintained under inserts | `extreme_maintained`, `finish_iavg` | `IncrementalMinMax.lean` |
| Semi and anti joins are maintained from a match count | `semi_maintained` | `IncrementalSemi.lean` |
| Recomputing only the touched groups or frames is exact | `touched_sound`, `touched_window_sound`, `framed_sound` | `TouchedGroups.lean`, `TouchedFrames.lean` |
| Dropping final time buckets from the state changes no result | `retention_sound`, `expiry_sound` | `Retention.lean` |
| A change feed gives the change of every view | `Rel.cdf_sound`, `ChangeFeed.of_diff`, `ChangeFeed.of_changed_files` | `TableFormat.lean` |
| A linear plan runs shard by shard | `Rel.eval_sharded`, `Rel.eval_twoPhase` | `Partition.lean` |
| `--shard`'s split plans compute the plan | `Rel.shardSplit_sound` | `Partition.lean` |
| Skipping files by their statistics changes no result | `Rel.eval_pruned`, `stats_prune`, `strStats_prune`, `prune_sound` | `Pruning.lean`, `TableFormat.lean` |
| An implied predicate on a base table keeps every output row | `Rel.need_sound` | `Implied.lean` |
| Contracts compose across a pipeline | `Rel.stack_sound`, `Rel.chain_sound` | `Compose.lean` |
| The rows quarantine keeps meet every precondition and key | `Catalog.kept_sound`, `kept_pre`, `kept_keys` | `Quarantine.lean` |
| Rewrites from contract facts and keys keep the result | `Rel.optimize_sound` | `Semantic.lean` |
| A double `SUM` or `AVG` is within the reported `epsilon` | `StdModel.epsilon_sum_cr`, `StdModel.epsilon_avg_cr` (against the reference's correctly rounded value, D25), `StdModel.epsilon_sum_rel`, `StdModel.epsilon_avg_rel` | `float-bounds/FloatBounds/Epsilon.lean` |
| Sharded double sums are near the sequential sum | `StdModel.sharded_near`, `StdModel.sharded_avg_near` | `float-bounds/FloatBounds/Shard.lean` |
| A sink's refreshes, with crashes, late writes of crashed processes, lost acknowledgements, racing writers, other applications' commits and deploys, never apply a change to a table it was not computed from, and the sink's record names its table. They assume only that the state is reachable (`Reachable`), for a durable source and writers deciding as `Refresh.next` (`tests/test_refresh_next.py`) | `Refresh.no_corruption`, `Refresh.record_describes_table` | `Refresh.lean` |

`Examples.lean` prints the axioms of the main theorems with
`#print axioms`, so a build shows what each rests on.

## What is trusted

The theorems are about the model. What links the model to the plans and the
engines is trusted, and kept small:

- The parser and the writer, `Parse.lean` and `Write.lean`. The CLI checks
  that every plan it writes parses back to the same `Rel`, and the golden
  tests (`tests/run.sh`) run that round trip on every fixture. The parser's
  choice of function by kind is checked: `checkPlan` refuses a plan
  `Rel.inferKinds` does not type (`Rel.kinds_sound`). Integer-represented
  kinds (doubles, dates, timestamps, decimals) share `Value.int` until #923,
  so the theorem tells them apart by representation only.
- The CLI's glue, `Main.lean`, `ContractCheck.lean` and `ShardCheck.lean`:
  they call the checkers and print JSON.
- The axioms about doubles, stated on scaled codes: `FloatCode.add_scaled`
  and its siblings (`Float.lean`, `div_scaled_err` among them),
  `FloatCode.exp_fin` (`Safety.lean`) and `varOf_props`, `covOf_props`,
  `corrOf_props` (`StatProps.lean`). A `SUM` or `AVG` of doubles needs none
  since D25: `floatSumCR`'s bounds are theorems (`FloatExact.lean`).
  `float-bounds/` proves the axioms over the reals for the standard model of
  rounding (`StdModel.core_add` … in `Arith.lean`, `core_var` … in
  `CoreStats.lean`), and
  there only `NativeLink` (`Link.lean`) stays trusted: Lean's `Float` rounds
  as IEEE 754 binary64 does.
- The models of the engines' own functions: `Impl.Faithful` (`Guards.lean`)
  for the functions the SQL calls unguarded, `Profile.duckdb` (`Profile.lean`,
  `EngineTables.lean`) and `Polars.*` (`PolarsShims.lean`), each from the
  engine's characterization facts (`characterization/<engine>/facts/`).
- The table formats' change feeds (`ChangeFeed`, `TableFormat.lean`), a
  hypothesis of `Rel.cdf_sound` wherever Sverify reads a Delta change data
  feed; it is proved when the change is computed from two snapshots.
- The evaluators behind black boxes and regular expressions
  (`implemented_by` in `BlackBox.lean`, `Regex.lean`, `Digest.lean`, `VarcharCasts.lean`). No
  proof reads them; the proofs use only each black box's declared laws.

## The modules

One line per module, by layer: values and expressions first, then
relations, then the checkers on them, then the tables, profiles and
generators, then the trusted reading and writing.

### Values and scalar functions

| Module | Job |
|---|---|
| `FloatFormat.lean` | Binary floating-point formats as integer codes in the SQL order |
| `Float.lean` | Doubles and timestamps as integer codes; the trusted facts of rounded arithmetic |
| `Value.lean` | Nullable values, rows and bag-semantics relations |
| `FloatExact.lean` | `SUM` and `AVG` of doubles as the exact sum rounded once (D25), with their bounds |
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
| `Incremental.lean` | Z-sets, delta rules and delta plans |
| `Weighted.lean` | Z-set plans as bag plans with a weight column |
| `Terms.lean` | Splitting a plan into union-free terms |
| `IncrementalAgg.lean` | Delta rules for `COUNT`, `SUM` and `DISTINCT` |
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
| `Contracts.lean` | The abstract interpreter behind contracts; `contract_sound` |
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
| `StatProps.lean` | The properties any variance, covariance or correlation algorithm keeps |
| `Functions.lean` | The function tables: names, anchors, groups, how the parser reads each |
| `Options.lean` | The option catalogue and each profile's choices |
| `AllowedP.lean` | `Rel.AllowedP`, the results a profile's table allows |
| `Observations.lean` | Observations and classes against the reference |
| `ObsEquiv.lean` | Equality up to an observation (`Relation.Equiv`), and within a tolerance (`Relation.Near`) |
| `Robust.lean` | Postconditions robust under an observation, and narrowing a comparison by a tolerance |
| `AllowedNear.lean` | Postconditions on every allowed result, every order of a double `SUM` or `AVG` among them |
| `Profile.lean` | Engine profiles as outcomes per function, and DuckDB's shims |
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
| `LoweringDuckDB/On/*.lean` | The DuckDB lowering's entries, one module per area (generated) |
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
| `Main.lean` | The `substrait-check` CLI |
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
| `Arith.lean` | One double operation, bounded from its inputs |
| `Moments.lean` | Exact moments and the scale of the variance bounds |
| `Variance.lean` | Variance, covariance and correlation bounds for any algorithm |
| `Textbook.lean` | The textbook one-pass algorithm |
| `TwoPass.lean`, `TwoPassRel.lean` | Lean's two-pass algorithm, absolute and relative to the variance |
| `CovTwoPass.lean` | Two-pass covariance, relative to the spread |
| `Welford.lean`, `WelfordRel.lean` | Welford's update and Chan's merge, absolute and relative |
| `MergeRel.lean`, `CovRel.lean` | Chan's merge and the covariance, relative to the spread |
| `Chan.lean`, `ChanCorr.lean` | DuckDB's `VAR_*`, `STDDEV_*` and `CORR` meet `StatProps` |
| `CoreStats.lean`, `CoreKappa.lean` | The core's trusted statistical facts, proved |

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
