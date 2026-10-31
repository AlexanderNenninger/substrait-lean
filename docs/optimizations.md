# Proved optimizations beyond incremental maintenance

`sverify` checks a plan in Lean and then compiles it to an engine. This note
surveys optimizations the checker could justify with a proof, and ranks them
by what engines cannot already do. Two of them are prototyped:

* **guard elimination**: `SubstraitLean/Guards.lean`, plus `guards=False`
  in `sverify.sql.to_sql`, `polars_engine.run` and `duckdb_engine.run`;
* **sharded evaluation**: `SubstraitLean/Partition.lean`,
  `substrait-check --shard` and `sverify.partition`.

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
| 1 | Guard elimination | The checks are ours. An engine cannot know that a `CASE WHEN b = 0 THEN error(…)` never fires. | **Prototype**, proved |
| 2 | Constraint-based rewrites | Snowflake, BigQuery and Spark/Databricks keep PK/FK/UNIQUE as unenforced metadata. They use it only when the user asserts `RELY`, and the result is then silently wrong if the data disagrees. Our contracts are checked or proved. | `SubstraitLean/Semantic.lean`: DISTINCT elimination (#76), implied filters (#78), outer to inner joins (#77), join elimination (#75), GROUP BY through FDs (#79); #80 open |
| 3 | Sharded evaluation with exact semantics | Engines parallelise only inside one engine. Splitting work across engine instances, files or systems needs a proof that the plan commutes with the split, and the 64-bit and float catches below. | **Prototype**, proved, including split keys (#74) |
| 4 | Proved partition and file pruning | Engines prune from statistics they trust. We can prune from predicates implied by contracts, which engines do not infer, and prove pruning sound against how statistics are defined (truncated strings, NaN, NULL counts). | #81 |
| 5 | View matching and shared subplans | Needs plan equivalence across pipelines (`≈ᵣ`), which only the checker has. | #82 (later) |

## 1. Guard elimination (prototype)

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

To keep the `SUM` case apart, `Safety.lean` now reports its issue as a new
`Issue.sumWraps`. Its name is still "may wrap around", so outputs are
unchanged.

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

**Benchmark** (`python/scripts/bench_optimizations.py`, homelab, 10⁶ rows,
`a // b`, `a % b`, `a * 3 + b` under a filter, preconditions `0 ≤ a ≤ 10⁶`,
`1 ≤ b ≤ 1000`):

| Engine | checked | unchecked | |
|---|---|---|---|
| Polars | 281 ms | 103 ms | 2.7× |
| DuckDB | 30 ms | 26 ms | 1.1× (DuckDB checks overflow natively; only the `CASE`s go) |

**Limits found on the way.** `Bound.mul` of two non-constant ranges is ⊤, so
`a * b` keeps its overflow guard even when both columns are bounded. Interval
multiplication would let more plans go guard-free. The elimination is also
all or nothing per plan; per-expression elimination is a follow-up. Both are in #83.

## 2. Sharded evaluation (prototype)

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
  `--shard` **refuses** these aggregates by default. With
  `float_order="any"` it splits them anyway (`floatCombine`: `SUM` of
  partial sums, `AVG` as summed sums over summed counts). The result is
  marked `proved: false`: the double sums round as the split makes them,
  and everything else is still Lean's value. Rewriting `AVG` as `SUM / COUNT`
  does not help for doubles. For integers, `AVG(x)` is defined as the `AVG`
  of the converted doubles (`Aggregate.lean`), which is not
  `CAST(SUM(x)) / COUNT(x)` either. Supporting it needs an exact accumulator.
  A proved error bound for the two-phase sum, which would let these run
  sharded with a stated tolerance, is the epic #85.
* **Other `DISTINCT` aggregates** are refused: a value in two shards counts
  once in the whole and twice in the parts. `DISTINCT` without the split
  key, windows and `FETCH` are refused because they look at rows of other
  shards.
* **Joins of two sharded tables** that are not co-partitioned are refused,
  and so are windows without the split key in `PARTITION BY`, or with
  possible ties.

**Wiring.** `substrait-check --shard {"plan", "sharded", "keys", "unique",
"float_order"}` returns the partial and combining plans in Lean's written
form and whether the result is proved, or exit code 5 with the reason. The
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
* **Eager aggregation below joins** (#80). Push `GROUP BY` below a join on a key
  (Yan and Larson), using the two-phase lemmas of `Partition.lean`
  (`AggFn.combine_apply`). Multiplicities make it subtle: `COUNT` and `SUM`
  must be scaled by match counts unless the join is on a key, which is where
  our keys come in.

## 4. Partition and file pruning (#81)

`sverify.io` reads Delta and Iceberg with per-file statistics, and
`TableFormat.lean` already proves that statistics bound a file's rows
(`stats_table`, `stats_bounds`). Two things would be proved:

* **Pruning soundness.** If `aeval` of a filter on a file's statistics is
  certainly not TRUE, the file contributes no rows. Then reading only the
  surviving files is `Rel.eval_sharded` with the pruned shards empty.
  Engines prune too. What we add is a proof against the exact statistics
  semantics: NULL counts, NaN in float min/max, and truncated string bounds
  (Delta truncates long strings in statistics, so they are only prefixes).
* **Pruning from implied predicates.** A contract on an upstream view can
  imply a predicate on a base column (for example `ts >= start` after a join
  on a key). We can push it to the scan, and engines do not derive it.

## 5. View matching and shared subplans (#82, later)

Pipelines often recompute the same subplan, such as one filtered fact table
feeding several aggregates. The checker could find subplans equal up to
`≈ᵣ` (canonical forms from `Rewrites.lean` and `Terms.lean`), compute them
once, and answer a query from a materialised view when the query is a
filter or projection of it. Incremental views (`IncrementalView`) are the
natural targets. This needs a decision procedure for plan containment beyond
syntactic equality, so it comes after the items above.
