# Proved optimizations beyond incremental maintenance

`sverify` checks a plan in Lean and then compiles it to an engine. This note
surveys optimizations the checker could justify with a proof, and ranks them
by what engines cannot already do. Two of them are implemented and public:

* **guard elimination**: `SubstraitLean/Guards.lean`, `Report.guard_free`,
  and `guards=False` in `sverify.engines.to_sql` (and in
  `polars_engine.run` and `duckdb_engine.run`);
* **sharded evaluation**: `SubstraitLean/Partition.lean`,
  `substrait-check --shard` and `sverify.engines.run_sharded`
  (`sverify.partition`).

The rest are filed as issues under the roadmap epic #29 (#74–#83).

## What engines already do

These optimizations need no proof from us. Engines apply them to any plan we
emit.

| | DataFusion | DuckDB | Polars | Snowflake | Spark |
|---|---|---|---|---|---|
| Predicate and projection pushdown | yes | yes | yes | yes | yes |
| Join reordering | partly (statistics-based join selection and side swaps) | yes (cost-based) | no | yes | with CBO (off by default) |
| Min/max file and row-group pruning | Parquet row groups and pages | zone maps, Parquet statistics | Parquet statistics | micro-partitions | Parquet, Delta data skipping |
| Hash-partitioned parallelism inside the engine | yes | yes | yes | yes | yes |
| Partial/final (two-phase) aggregation inside the engine | yes | yes | yes | yes | yes |

The useful question is therefore not "is this rewrite valid" but **what does
the checker know that the engine does not?** The checker knows three things:

1. **Contracts.** The preconditions are checked on the data at call time and
   composed across pipelines (`Compose.lean`). `Contracts.lean` derives value
   ranges, NULL-freedom and keys (`Keys.lean`) from them.
2. **Exact semantics.** It knows where results are exact and where an engine
   would wrap, round or fail.
3. **Guards.** The SQL we emit contains run-time checks that only we inserted,
   so only we can remove them.

## Ranking

| Rank | Candidate | Why engines cannot do it | Status |
|---|---|---|---|
| 1 | Guard elimination | The checks are ours. An engine cannot know that a `CASE WHEN b = 0 THEN error(…)` never fires. | **Public**, proved: `Report.guard_free`, `to_sql(…, guards=False)` |
| 2 | Constraint-based rewrites | Snowflake, BigQuery and Spark/Databricks keep PK/FK/UNIQUE as unenforced metadata. They use it only when the user asserts `RELY`, and the result is then silently wrong if the data disagrees. Our contracts are checked or proved. | `SubstraitLean/Semantic.lean`: DISTINCT elimination (#76), implied filters (#78), outer to inner joins (#77), join elimination (#75), GROUP BY through FDs (#79), eager aggregation (#80) |
| 3 | Sharded evaluation with exact semantics | Engines parallelise only inside one engine. Splitting work across engine instances, files or systems needs a proof that the plan commutes with the split, and the 64-bit and float catches below. | **Public**, proved, including split keys (#74): `sverify.engines.run_sharded` |
| 4 | Proved partition and file pruning | Engines prune from statistics they trust. We can prune from predicates implied by contracts, which engines do not infer, and prove pruning sound against how statistics are defined (truncated strings, NaN, NULL counts). | #81 |
| 5 | View matching and shared subplans | Needs plan equivalence across pipelines (`≈ᵣ`), which only the checker has. | #82 (later) |

## 1. Guard elimination

**Problem.** Lean's integers are unbounded, so the SQL of every dialect
checks each operation. `Snowflake` wraps `+`, `-`, `*` in an `IFF(… BETWEEN
-2^63 AND 2^63-1, …, error)`. Every dialect writes integer division and
remainder as `CASE WHEN b = 0 THEN error(…)`, and `date_trunc` gets a range
check. The Polars engine adds a `map_batches` flag check per operator and
disables predicate pushdown. Most of these checks never fire on data that
meets a contract.

**What is proved.** `SubstraitLean/Guards.lean`:

* `Impl` is an engine's own functions, without checks. `Impl.Faithful` is the
  trusted assumption: they agree with Lean wherever `UnFn.issue` and
  `BinFn.issue` report nothing. Wrapping 64-bit arithmetic is faithful,
  because it is exact in range, and so is a division that does anything at
  all on a zero divisor.
* `Expr.evalI_eq`: an expression without issues on a row evaluates the same
  with unchecked functions.
* `Rel.evalI_eq`: suppose every issue a plan can run into (`Rel.HasIssue`) is
  an integer `SUM` that may wrap. Then running it with unchecked functions
  gives `Rel.eval`. `SUM` keeps its check, because no row-level contract
  bounds a group's size.
* `Rel.guardFree_sound`: the same, derived from `Rel.mayIssues` under the
  contract's preconditions. `substrait-check --contract` reports this as
  `guard_free`, and `sverify.Report.guard_free` exposes it.
* `Rel.evalG_marks`: the same per expression. `Rel.marks` lists, per node,
  the expressions without abstract issues on the inputs `Rel.mayIssues`
  analyses them on (a filter's, join's or semi-join's condition, each of a
  projection's expressions, and an aggregate's expressions together), as a
  tree parallel to the plan. `Rel.evalG` runs those with unchecked functions
  and the rest with Lean's, and gives `Rel.eval` with no hypothesis on the
  other issues. `substrait-check --contract` reports the tree as
  `unchecked`, and `sverify.Report.unchecked` exposes it.

To keep the `SUM` case apart, `Safety.lean` reports its issue as
`Issue.sumWraps`, named "SUM overflow". `verify` assumes it away (inferred,
`Report.assumed`) and the job checks it on the data, so unlike the others, the
guards keep its check.

**A gap in the specification.** `Rel.HasIssue` evaluates filter and join
conditions on the rows of `Rel.loose`, the plan without the filters an engine
may reorder. Under a left join whose right side has a filter, `loose` can
*lose* rows: with the filter gone, a left row may find a match, so its
NULL-padded row is no longer produced. `Rel.looseSub` decides when `loose`
keeps every row, and `guard_free` requires it. On other plans the guards
stay; `test_filtered_right_side_of_a_left_join_keeps_guards` covers this
case. `Rel.mayIssues` itself is probably still sound on such plans, because
the abstract left join always allows padded rows. But `mayIssues_sound` is
stated against `HasIssue`, so it does not cover them. Strengthening
`HasIssue` to cover every evaluated row is a follow-up (#83).

**Wiring.** `Report.guard_free`. `to_sql(plan, dialect, guards=False)` drops
the division-by-zero `CASE`s, the `date_trunc` range check, Snowflake's
row-level `IFF` range checks and its `CAST(double AS BIGINT)` check. It keeps
`MIN % -1 = 0`, which is semantics rather than a check, and every `SUM` check.
`polars_engine.run(…, guards=False)` skips the per-operator `guard`. Only pass
`guards=False` for a `guard_free` plan, on data that meets its preconditions.
`to_sql(plan, dialect, unchecked=report.unchecked)` drops the checks of the
expressions `unchecked` lists and keeps the others, and every aggregate's.
The writer checks that the tree's nodes are the plan's, so a report on
another plan raises `Unsupported`. In `SELECT a // b, a * b` with
`0 ≤ a ≤ 1000` and `b ≥ 1`, the division loses its `CASE` and the product
keeps its overflow check (`test_per_expression_guards` in
`python/tests/test_guards.py`). The Polars engine still drops all of its
checks or none.

**Benchmark** (`python/scripts/bench_optimizations.py`, homelab, 10⁶ rows,
`a // b`, `a % b`, `a * 3 + b` under a filter, preconditions `0 ≤ a ≤ 10⁶`,
`1 ≤ b ≤ 1000`):

| Engine | checked | unchecked | |
|---|---|---|---|
| Polars | 281 ms | 103 ms | 2.7× |
| DuckDB | 30 ms | 26 ms | 1.1× (DuckDB checks overflow natively; only the `CASE`s go) |

**Limits found on the way.** `Bound.mul` of two non-constant ranges used to
be ⊤, so `a * b` kept its overflow guard even when both columns are bounded.
It now multiplies the corners of two finite intervals (`Bound.mem_corners`),
so such products go guard-free; a half-open range still gives ⊤. The
elimination was also all or nothing per plan; `Rel.evalG_marks` now decides
per expression (#83).

## 2. Sharded evaluation

**Setting.** The sharded tables `S` are split over shards `cs`, and every
other table is broadcast (`Sharding S K cat cs`). A table may have a
**split key** `K t`: columns on which rows of different shards never agree,
across all keyed tables (`Sharding.keyDisj`). All rows with one key value are
then on one shard, as a Delta or Iceberg partition column (or a hash of it)
guarantees. The question is when
`eval q (D₁ ⊎ … ⊎ Dₙ) ~ eval q D₁ ⊎ … ⊎ eval q Dₙ`, or something close to it.

**Proved** (`SubstraitLean/Partition.lean`, all without `sorry`):

* `Rel.eval_sharded`. A plan *linear* in `S` (`Rel.linear`) gives the union
  of its results on the shards, as bags. Linear means filters, projections,
  emits, sorts and `UNION ALL` of linear inputs. Inner joins, cross joins,
  left joins and semi/anti joins count too, when the side that is not linear
  reads only broadcast tables. For inner and cross joins that side can be
  either one; for left and semi joins it must be the right side. Literal
  tables (`VALUES`) are not linear, because every shard would repeat them.
* **With split keys,** `Rel.linear` also accepts an aggregate whose
  `GROUP BY` contains the key, and a `DISTINCT` whose columns do. No group,
  and no duplicate row, spans two shards (`aggregateEval_flatten_disjoint`,
  `dedup_flatten_disjoint`), so each shard's result is final, for every
  measure except `SUM`/`AVG` of doubles (they add in row order, and neither
  sharding nor engines keep the order). `COUNT(DISTINCT …)` grouped by the
  key is therefore fine. `Rel.keyCols` follows the key's columns through
  filters, projections (and their copies of a column, which DataFusion's
  `SELECT` lists emit), emits, joins with broadcast tables, unions and
  aggregates. `Rel.keyRows` proves that every output row carries the key of
  a row on its own shard.
* **Co-partitioned joins.** An inner, left, semi or anti join of two linear
  plans, both with split keys that the condition equates (`ON r.k = s.k`,
  possibly among other conjuncts: `Expr.eqFields`, `coCond`), runs on each
  shard. A row of one shard never matches a row of another
  (`Sharding.coDisjoint`), so the cross product keeps only same-shard pairs
  (`cross_filter_diag`), and a left join's padding and a semi join's test only
  see the row's own shard (`flatMap_rowwise`, `filter_rowwise`).
* **Windows.** A window whose `PARTITION BY` contains the split key runs on
  each shard, when its partition and sort columns form a key of its input
  (`windowEval_sharded`). The key is needed because Lean breaks ties in a
  window's sort by row order, which neither sharding nor engines keep.
  `--shard` derives the key with `Rel.keyedWindows` from `unique` columns
  declared for the tables, which `run_sharded` checks on the data.
* `twoPhase_correct`. Take `COUNT`, integer `SUM`, `MIN` and `MAX`, with or
  without `FILTER`. `MIN(DISTINCT x)` and `MAX(DISTINCT x)` are allowed too,
  since `DISTINCT` changes nothing for them (`AggFn.apply_minMax_mem`).
  `COUNT(DISTINCT k)` and `SUM(DISTINCT k)` are allowed when `k` is the whole
  split key, because then no value is on two shards (`Measure.SplitOk`). Aggregating each part by the
  grouping keys and then aggregating the partial rows by their keys
  (`keyFields`, `combineMeasures`: `COUNT` combines by `SUM`) gives the
  aggregate of the whole. This holds with and without `GROUP BY`. The NULL
  and empty-group cases come out right because both phases skip NULLs. A
  shard without the group, or with only NULL values in it, contributes a
  NULL partial (`SUM`, `MIN`, `MAX`) or `0` (`COUNT`), and both are neutral.
  A global aggregate over zero shards would give NULL instead of `COUNT = 0`,
  so at least one shard is required.
* `Rel.eval_algebraic` (#245). An algebraic aggregate is a final expression
  over a tuple of distributive partials: each shard computes the partials,
  the combining phase combines each of them as above, and the final
  expression gives the result (`aggregateEval_algFinish`). The instance is
  the integer `AVG` (`AggFn.iavg`, Substrait's `avg` of `i64` with an `i64`
  result): a `SUM` and a `COUNT` per shard (`Measure.part`,
  `Measure.part₂`), and `SUM / COUNT` truncated toward zero, NULL without
  values (`algFinal`, `Measure.final_eval`). The mean of the shards' means
  would be wrong, since shards differ in size and each mean truncates.
  The model's `iavg` clamps the mean between the smallest and largest
  value, which changes nothing only when every value is an integer
  (`clampInts_mean`), so the split needs the argument to be one. `--shard`
  reads that from the plan's column types by abstract evaluation
  (`IntArgs.ofTypes`, sound for rows of those types by
  `IntArgs.ofTypes_sound`). `AVG(DISTINCT x)` splits when `x` is the whole
  split key, like `COUNT(DISTINCT x)`. `AVG` with a double result stays
  refused (see the float sums below). `VAR_*`, `STDDEV_*`, `COVAR_*` and
  `CORR` are doubles in the model, also of integers, so the same caveat
  holds for them; their exact partials (`n`, `Σx`, `Σx²`, …) wait for the
  error bounds of #85.
* `Rel.eval_twoPhase`, `Rel.shardSplit_sound`. `Rel.shardSplit` turns a plan
  into the plan each shard runs and the plan that combines their
  concatenated results. Filters, projections and sorts above the aggregate
  (`HAVING`, renames, `ORDER BY`) move to the combining plan.
* `inI64_partial`. When all values have the same sign, every partial sum lies
  between 0 and the total, so it fits in 64 bits whenever the total does.

**The exact-semantics catches, and what we do with each:**

* **A 64-bit partial sum can overflow when the total does not, or the
  reverse.** Example: a shard with `2^62, 2^62` next to one with
  `-2^62, -2^62`. Engines differ here. DataFusion and Polars wrap, and since
  wrapping addition is associative the wrapped total is still right
  mod 2⁶⁴. Spark in ANSI mode raises on an overflowing partial sum, as
  seen while building the Spark dialect. DuckDB sums `BIGINT` into `HUGEINT`. Our dialects
  check each `SUM` (`Dialect.int_sum`), so two-phase evaluation either gives
  the exact answer or raises. It never returns a wrong value
  (`test_partial_sum_may_overflow_where_the_total_does_not`). A spurious
  failure is ruled out when all values have one sign (`inI64_partial`),
  which a contract bound such as `_.amount >= 0` gives. Wiring that bound
  into `--shard`, to say "cannot fail spuriously", is a follow-up (#83).
  The reverse case is caught: a total that leaves 64 bits fails in the
  combining `SUM`.
* **Float sums are not associative.** `SUM` and `AVG` of doubles add in list
  order in Lean (`floatSum`), and engines already return results that depend
  on their thread partitioning. A different split rounds differently, so
  `--shard` refuses these aggregates by default. With `float_order="any"` it
  splits them anyway (`floatCombine`: `SUM` of partial sums, `AVG` as summed
  sums over summed counts), within a proved bound
  ([#428](https://github.com/AlexanderNenninger/substrait-lean/issues/428)).
  Each shard also reports `SUM(|x|)`, `COUNT(x)` and `MAX(|x|)` per split
  double (`floatBoundParts`), and from them the combined `SUM` of a group of
  `n` values in `k` shards of at most `m` is within
  `(γ (m + k) + γ n) · (mag + k · 2⁻¹⁰²²)` of Lean's one-pass sum, the `AVG`
  within the same with `+ 2` in each `γ`, over `n` (`floatSplit_sum`,
  `floatSplit_avg`, proved over the reals in
  [`float-bounds/FloatBounds/Shard.lean`](float-bounds.md#sharded-sum-and-avg-stage-5)).
  The result stays `proved: false`, and `float_bounds` in `--shard`'s output
  says which output columns carry the bound; `run_sharded(...,
  tolerance=True)` gives τ per row. Everything else is still Lean's value.
  Rewriting `AVG` as `SUM / COUNT` does not help for doubles. For integers,
  `AVG(x)` is defined as the `AVG` of the converted doubles
  (`Aggregate.lean`), which is not `CAST(SUM(x)) / COUNT(x)` either. An exact
  result would need an exact accumulator, deferred with stage 6 of #85.
* **Other `DISTINCT` aggregates** are refused: a value in two shards counts
  once in the whole and twice in the parts. `DISTINCT` without the split
  key, windows and `FETCH` are refused because they look at rows of other
  shards.
* **Joins of two sharded tables** that are not co-partitioned are refused,
  and so are windows without the split key in `PARTITION BY`, or with
  possible ties.

**Wiring.** `substrait-check --shard {"plan", "sharded", "keys", "unique",
"float_order"}` returns the partial and combining plans in Lean's written
form, whether the result is proved, and with split doubles where their
bound is read (`float_bounds`), or exit code 5 with the reason. The
schema of `__partials` is trusted. `sverify.partition.split` and
`run_sharded(plan, shards, sharded=…, broadcast=…, keys=…, unique=…,
float_order=…)` run the shards on Polars in parallel threads. `run_sharded`
checks split keys and `unique` columns on the data before relying on them
(`check_keys`, `check_unique`), comparing doubles by their bits as Lean
does. `tests/test_partition.py` compares the sharded result
with the whole on random data and random splits.

**Benchmark.** On one machine, a grouped aggregate over 10⁶ rows in 8 shards
takes 157 ms against 112 ms in one Polars run (0.7×). That is expected:
Polars already parallelises a single query, and the threads share the GIL in
the Python glue. Sharding pays off where the data already lives apart:
Delta/Iceberg partitions processed where they are stored, several engines
or warehouses, or incremental maintenance of one partition at a time.

## 3. Constraint-based semantic rewrites (issues)

Snowflake does not enforce PK, FK or UNIQUE constraints; it enforces only
NOT NULL. Its optimizer eliminates joins only for constraints marked `RELY`,
which the user asserts and does not check. BigQuery's PK/FK constraints are
unenforced, Databricks' are informational (`RELY` again), and Spark itself
has none. DuckDB enforces PK, UNIQUE and FK but uses them little in its
optimizer. DataFusion uses primary keys for functional dependencies in
`GROUP BY`. Polars has no constraints. Our contracts are checked at ingestion
or proved through composition, so each rewrite below rests on facts we know
hold:

* **Join elimination** (#75, done). Take `R ⋈ S` on a condition that
  determines a key of `S` (`Keys.determines`), so each left row has at most
  one partner. A left join then gives exactly one row per left row, and so
  does an inner join on a NOT NULL foreign key (`sv.references`, as in
  #77). When an emit, a projection or an aggregate above reads no column of
  `S`, the join goes (`Rel.joinElim`, `flatMap_single`, `aggregateEval_map`).
* **DISTINCT elimination** (#76, done). If `Rel.keys` proves any key of
  `r`, its rows are pairwise distinct and `DISTINCT r` is `r`
  (`dedup_of_nodup`). The same goes for a `GROUP BY` without measures whose
  grouping expressions contain a key's columns (it becomes a projection), and
  for `fn(DISTINCT x)` when `x` alone is a key (`COUNT(DISTINCT id)` becomes
  `COUNT(id)`).

**Wiring.** `Rel.optimize` (`SubstraitLean/Semantic.lean`) applies the
rewrites bottom-up, deciding each from the analyses of the already rewritten
inputs. `Rel.optimize_sound`: on data meeting the preconditions, the result
is well-formed, has the same arity and gives the same list of rows (not just
the same bag). `substrait-check --contract` reports the rewritten plan as
`optimized`, in Lean's written form, with the names of the rewrites applied
(`rewrites`); `sverify.Report.optimized` and `Report.rewrites` expose them.
Run `optimized` instead of the transformation (`to_sql`, `duckdb_engine.run`,
`polars_engine.run`) only on data that meets the preconditions, as with
`guards=False`.
* **Outer-to-inner join conversion** (#77, done). A filter above a left
  join that is never TRUE on a padded row (`Expr.absD` with the right
  columns NULL) turns it into an inner join; engines do this case too. With a
  foreign key and NOT NULL, every left row matches, so the conversion holds
  without a filter. `sv.references(col, table, other)` declares the foreign
  key (`ForeignKeys.Hold`), checked on the data like `unique`. `Rel.origin`
  follows the join column back to a table column and `Rel.cover` checks that
  the right side keeps every value of the referenced one. The inner join is
  in the incremental fragment (`--delta`), which excludes left joins. Incremental
  views do not take `references` preconditions yet: they would have to check
  deletes from the referenced table.
* **Filters implied by CHECK constraints** (#78, done). If `Expr.absD`
  shows the condition certainly TRUE on the input's abstract rows
  (`AVal.certainlyTrue`, as for a postcondition), `filter r c` is `r`. If it
  shows the condition never TRUE (`tt = false`), the filter is an empty
  `VALUES`. This composes: a downstream re-check of an upstream guarantee
  disappears (`test_composed_pipeline_drops_the_downstream_check`).
* **GROUP BY simplification through functional dependencies** (#79, done).
  `Rel.fds` derives dependencies: input keys and aggregate groups determine
  every column, equalities in filters and inner joins and copied columns
  determine each other, and they follow emits, projections and joins
  (`Rel.fds_sound`). `Rel.fdAgg` drops each grouping column that the closure
  of the others determines and carries it through `MIN`, which is the
  group's one value, NULL included (`Measure.eval_min_const`). The groups
  stay the same (`dedup_parallel`), so the result is the same list of rows.
  **Benchmark** (`scripts/bench_optimizations.py`, laptop, 10⁶ line items,
  TPC-H Q3-style `GROUP BY l_orderkey, o_date, o_prio` after a join on the
  order key): DuckDB 57 ms as written, 67 ms by key; Polars 420 ms and
  600 ms. Neither engine gains: both hash a few more key columns more
  cheaply than they compute the `MIN`s. The rewrite may pay off on engines
  with costly wide hash keys or spilling, which is not measured here.
* **Eager aggregation below joins** (#80, done for joins on a key). Take a
  `GROUP BY` of left columns over `R ⋈ S`, where the condition determines a
  key of `S` (so each left row has at most one partner,
  `Rel.partners_le_one`) and reads only left columns that are grouped (so the
  rows of a group all have a partner or none). Then `R` is aggregated first
  and the groups are joined with `S` (`Rel.eagerAgg`): the join keeps or
  drops whole groups (`aggregateEval_filter`, `dedup_filter_map`). No
  scaling of `COUNT` or `SUM` is needed, since every multiplicity is 0 or 1.
  The general case, without a key, needs measures scaled by match counts
  (`AggFn.combine_apply` in `Partition.lean`) and is not done.
  **Benchmark** (`scripts/bench_optimizations.py`, laptop): 10⁶ line items
  grouped by order key, 4 rows per group: DuckDB 10 ms as written, 12 ms
  aggregated first; Polars 78 ms and 131 ms. With 1000 rows per group, DuckDB
  is even (4.9 ms and 4.2 ms) and Polars still slower (31 ms and 43 ms). The
  join to a small keyed table is cheap in both engines, so aggregating first
  saves little.

## 4. Partition and file pruning (#81)

`sverify.io` reads Delta and Iceberg with per-file statistics, and
`TableFormat.lean` proves that statistics bound a file's rows
(`stats_table`, `stats_bounds`). A source with a condition,
`DeltaSource(uri, where=...)` or `IcebergSource(catalog, name, where=...)`,
reads the rows on which it is TRUE and skips the data files whose statistics
rule it out. `SubstraitLean/Pruning.lean` proves the criterion:

* Shard the source by data file. A skipped file's shard holds no row on
  which the condition is TRUE, so dropping it leaves a sharding of the same
  tables (`Sharding.prune`), and every plan linear in the source gives the
  same rows from the files read (`Rel.eval_pruned`, from
  `Rel.eval_sharded`). `prune_sound` gives the rows in order.
* A file is skipped when the abstract value of the condition on the file's
  statistics cannot be TRUE (`stats_prune`, from `Expr.abs_sound`).
  `sverify.io` asks the contract checker, which proves "the condition is
  not TRUE" from the same facts (`contract_sound`) and also follows
  conjunctions and disjunctions through `refine`.
* NULL counts: a column is NULL-free only where the NULL count is 0, and
  a file whose NULL count equals its row count holds only NULLs
  (`ColStats.aval`). With deletion vectors or delete files the statistics
  describe a superset of the rows, which keeps them correct.
* NaN (#36): writers leave NaN out of a double column's minimum and
  maximum. NaN is the greatest code, so the minimum still bounds the
  column, and the maximum only where the file counts no NaN
  (`DoubleStats.colStats_correct`). Delta and pyiceberg count no NaN, so
  their double maxima are not used, and a file with maximum `1.0` and a
  NaN row is read for `x > 100`
  ([test](../python/tests/test_io_pruning.py)).
* Truncated strings: Delta and Iceberg may keep a prefix of a string bound
  (pyiceberg keeps 16 characters and increments the last one of a maximum).
  Every value is at least the minimum, and every value cut to the maximum's
  length is at most the maximum, whichever convention the writer follows
  (`StrStats.Correct`). `StrStats.mayTrue` decides `=`, `<`, `<=`, `>`,
  `>=`, `IN`, `AND` and `OR` of string columns and literals from that
  (`strPrune_sound`); `str_may_true` in `sverify.io` mirrors it, and a
  Hypothesis test checks it on truncated bounds.

Engines prune too. For `amount * 2 > 100`, pyarrow's statistics pushdown
keeps every file, and Sverify skips those with `amount <= 50` (`test_where_skips_files_the_reader_would_scan` in
`test_io_delta.py`, `test_iceberg_where_skips_files_the_reader_would_scan`
in `test_io_pruning.py`). An Iceberg refresh skips appended files the same
way.

A view can also imply a predicate on a base table that the query does not
state, and engines do not derive one. With `o.ts >= c.since` in a join of
orders and customers, and `since >= DATE '2026-01-01'` among the
customers' preconditions, only orders from 2026 on can reach the result.
`Rel.need` (`SubstraitLean/Implied.lean`) finds such predicates. It pushes
a demand down the plan through filters, emits, projections, unions and
inner joins. At a join, it refines the join condition and the demand on
the other input's abstract values (`Rel.aeval`), carrying bounds across
comparisons of two columns (`geTransfer`). Under an aggregate, a window, a
left join or a `FETCH` it gives up. `Rel.need_eval` proves that the view
gives the same result on any table that agrees with the original on the
rows passing the predicate (`SameOn`). So a node's Delta or Iceberg source
reads only those rows, adds the predicate to its `where`, and skips the
files whose statistics rule it out
(`test_a_predicate_the_view_implies_prunes_files` in
`test_io_pruning.py`). The predicate rests on the preconditions, which
every refresh establishes, and on facts that hold at every version (Delta
CHECK constraints and a source's own condition). File statistics change
between versions, so they are left out. A table whose preconditions fail
on rows the predicate drops raises in fewer cases; the result is the same.

## 5. View matching and shared subplans (#82, later)

Pipelines often recompute the same subplan, such as one filtered fact table
feeding several aggregates. The checker could find subplans equal up to
`≈ᵣ` (canonical forms from `Rewrites.lean` and `Terms.lean`), compute them
once, and answer a query from a materialised view when the query is a
filter or projection of it. Incremental views (what a node's `refresh` maintains) are the
natural targets. This needs a decision procedure for plan containment beyond
syntactic equality, so it comes after the items above.

## 6. Incremental maintenance

A node's `refresh` maintains filters, projections, inner and cross joins and
`UNION ALL` from the changes to their inputs, by delta rules Lean proves
over Z-sets (`Rel.incremental_sound` in
[`SubstraitLean/Incremental.lean`](../SubstraitLean/Incremental.lean)).
Epic #248 extends the delta rules to the operators that are not linear. Its
first stage covers `COUNT` and integer `SUM` per group, and `DISTINCT`
([`SubstraitLean/IncrementalAgg.lean`](../SubstraitLean/IncrementalAgg.lean),
[`sverify._linear`](../python/src/sverify/_linear.py)). The second covers
exact `SUM` and `AVG`, `MIN` and `MAX` per group
([`SubstraitLean/IncrementalMinMax.lean`](../SubstraitLean/IncrementalMinMax.lean)),
and semi and anti joins
([`SubstraitLean/IncrementalSemi.lean`](../SubstraitLean/IncrementalSemi.lean),
[`sverify._semi`](../python/src/sverify/_semi.py)).

`COUNT` and `SUM` per group are linear over Z-sets: each is a sum of a
row's value times its weight. So a view that ends in such an aggregate keeps
a state beside its rows, one row per group: the group's keys, its number of
input rows, and for each measure the number of values it adds up (rows that
pass its `FILTER`, with a non-NULL argument) and their exact sum. A batch
adds each changed row's contribution to the state of its group, and the
view's rows of the groups it touches are finished from the new state:
`COUNT` is the number of values, and `SUM` is NULL without values and the
sum otherwise. A group is in the view while it has rows, so groups appear
when their row count leaves 0 and disappear when it returns to 0.
`DISTINCT` is the same with every column a key and no measures: a count per
row, and a row is in the view while its count is positive.

Lean proves that the old state plus the state of the change finishes to the
aggregate of the new input, against `Rel.eval`, with the groups that appear
and disappear (`LinearAgg.aggregate_maintained`), and the same for
`DISTINCT` (`LinearAgg.distinct_maintained`). The change only needs the
right weights, so a change feed that deletes and re-inserts a row is fine
(`ChangeFeed`). The maintenance reads the change and the touched groups'
state, never the view's input, where touched-group recompute
(`TouchedGroups.touched_sound`) scans the input for the groups a batch
touches.

An integer `SUM` that may leave 64 bits is assumed to fit and checked on
the data while the job runs (`Report.assumed`). The maintained sum is the
exact sum of the group's values, and the engine's `SUM` that adds the
contributions to it raises when it leaves 64 bits, so the check is the same
as on a full recompute. A row's value times its weight must fit 64 bits too.

With retention (`arrives_within`), the state drops the groups of the
retired buckets with the view's rows, and the contributions to final
buckets are left out: an admissible batch changes none of them, and a
source's expiry deletes only their rows (`Retention.expiry_sound`).

A view is maintained this way when it ends in such an aggregate or
`DISTINCT`, under filters, projections and sorts of its rows that keep the
keys, and the aggregate's input has delta rules. `status()` reports it as
maintained, like a view with delta rules. The tests
([`test_linear.py`](../python/tests/test_linear.py)) compare every refresh
with a full recompute over random change streams on DuckDB, Polars and
DataFusion.

`AVG` of exact types is a `SUM`, a `COUNT` and a division (#245). A
`DECIMAL` `AVG` is, in the model, an aggregate of the `SUM` and the `COUNT`
with a projection that divides them at four more decimal places
(`Parse.decimalAvgs`), so the state of `SUM` maintains it, and the view
divides the group's sum by its count when it finishes the row, with the
same `sverify_decimal_div` a full recompute runs. A projection of a
maintained aggregate that keeps its keys is maintained
(`ExtremeAgg.map_maintained`). A `DECIMAL` `SUM` keeps its sum at the type
of the full `SUM`, ten more digits, so it raises where a full recompute
does. An integer `AVG` with an integer result (`AggFn.iavg`) finishes from
the same state as `SUM / COUNT` truncated (`ExtremeAgg.finish_iavg`). Ibis
types `mean()` of integers as a double, which, like a double `SUM`, is
left to touched-group recompute (#85).

`MIN` and `MAX` are linear under inserts: the `MIN` of a group's old values
and the inserted ones is the `MIN` of the two (`minMax_combine`). A
deleted extreme leaves no trace of the next one in the state, though. So
the state keeps each `MIN` or `MAX` measure's extreme beside the counts and
sums, and a batch merges the groups it only inserts into, and recomputes
from the new input the groups it deletes from, a semi-join on their keys
as touched-group recompute does. Lean proves the result is the aggregate of
the new input, for any mix of `COUNT`, `SUM`, `MIN` and `MAX`
(`ExtremeAgg.extreme_maintained`). A time-series rollup whose batches only
insert never reads its input.

A semi join keeps the left rows with a match on the right, and an anti join
those without. Whether a left row has a match is whether the weight of the
right rows that match it is positive, and that weight is linear in the
right side. So a view that ends in a semi or anti join on equal keys keeps a
count of the right rows per key (rows with a NULL key match nothing), and a
batch changes the view by

* the left side's change, kept where the new counts keep it;
* the old left rows of the keys whose count leaves 0, which a semi join
  emits and an anti join retracts;
* the old left rows of the keys whose count returns to 0, the other way
  round.

Lean proves that the old view plus this change has the weights of the new
view, for any join condition (`SemiDelta.semi_maintained`), and that the
count of an equi-join only depends on the left row's key
(`SemiDelta.matchCount_by_key`). The right side is never read, and the left
side only for the keys whose count crosses 0. The filters and projections
above the join pass the weights through. A condition other than equal keys,
or a key that is a double, is recomputed and diffed. The tests
([`test_semi.py`](../python/tests/test_semi.py)) compare every refresh with
a full recompute over random change streams on both sides, on DuckDB,
Polars and DataFusion.

A failed commit leaves the state of every view as it was, the counts per
key and the extremes included (#515): the commit swaps them in with the
rest, and puts them back on any error
([`test_io_delta.py`](../python/tests/test_io_delta.py)).

A window of aggregates over bounded RANGE frames of one time column
(`sverify._touched.Framed`) is maintained by recomputing the rows near the
change. A window row depends only on the rows of its partition whose time
lies in its frame (`TouchedFrames.outRow_local` in
[`SubstraitLean/TouchedFrames.lean`](../SubstraitLean/TouchedFrames.lean)).
So for frames from `start` to `end` around each row, `start ≤ 0 ≤ end`, and
a batch whose changed rows lie in the touched partitions at times
`[t0, t1]`, the output rows outside `[t0 - end, t1 - start]` keep their
values, and the rows inside come out the same from the input narrowed to
the touched partitions and the times `[t0 - end + start, t1 - start + end]`
(`TouchedFrames.framed_batch`). Like the touched partitions
(`TouchedGroups.touched_window_sound`), it needs no two input rows tied on
the partition and time columns. The tests
([`test_touched_frames.py`](../python/tests/test_touched_frames.py)) compare
every refresh with a full recompute, duplicate and NULL times included.

Later stages of #248, each with its own delta rule:

* global aggregates (no `GROUP BY`), one output row even on an empty input;
* double `SUM` and `AVG` with deletes, whose error grows with every change
  (#85);
* left joins, which retract their NULL-padded rows when a match arrives;
* windows.
