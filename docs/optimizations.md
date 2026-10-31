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
| 2 | Constraint-based rewrites | Snowflake, BigQuery and Spark/Databricks keep PK/FK/UNIQUE as unenforced metadata. They use it only when the user asserts `RELY`, and the result is then silently wrong if the data disagrees. Our contracts are checked or proved. | #75–#80 |
| 3 | Sharded evaluation with exact semantics | Engines parallelise only inside one engine. Splitting work across engine instances, files or systems needs a proof that the plan commutes with the split, and the 64-bit and float catches below. | **Prototype**, proved; keyed splits #74 |
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
other table is broadcast (`Sharding S cat cs`). The question is when
`eval q (D₁ ⊎ … ⊎ Dₙ) ~ eval q D₁ ⊎ … ⊎ eval q Dₙ`, or something close to it.

**Proved** (`SubstraitLean/Partition.lean`, all without `sorry`):

* `Rel.eval_sharded`. A plan *linear* in `S` (`Rel.linear`) gives the union
  of its results on the shards, as bags. Linear means filters, projections,
  emits, sorts and `UNION ALL` of linear inputs. Inner joins, cross joins,
  left joins and semi/anti joins count too, when the side that is not linear
  reads only broadcast tables. For inner and cross joins that side can be
  either one; for left and semi joins it must be the right side. Literal
  tables (`VALUES`) are not linear, because every shard would repeat them.
* `twoPhase_correct`. Take `COUNT`, integer `SUM`, `MIN` and `MAX`, without
  `DISTINCT` and with or without `FILTER`. Aggregating each part by the
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
  mod 2⁶⁴. Spark in ANSI mode raises on an overflowing partial sum (see the
  Spark backend notes). DuckDB sums `BIGINT` into `HUGEINT`. Our dialects
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
  `--shard` **refuses** these aggregates. Rewriting `AVG` as `SUM / COUNT`
  does not help for doubles. For integers, `AVG(x)` is defined as the `AVG`
  of the converted doubles (`Aggregate.lean`), which is not
  `CAST(SUM(x)) / COUNT(x)` either. Supporting it needs an exact accumulator.
* **`DISTINCT` aggregates** are refused: a value in two shards counts once
  in the whole and twice in the parts. `DISTINCT` itself, windows and
  `FETCH` are refused because they look at rows of other shards.
* **Joins of two sharded tables** are refused. They are correct only when
  both sides are split on the join key (co-partitioning). The same holds for
  aggregates split on their grouping keys and windows split on their
  `PARTITION BY` keys. These need a statement of the form "rows in different
  shards differ on the key", which `Delta` and `Iceberg` partition columns
  give. This is #74.

**Wiring.** `substrait-check --shard {"plan", "sharded"}` returns the
partial and combining plans in Lean's written form, or exit code 5 with the
reason. The schema of `__partials` is trusted. `sverify.partition.split` and
`run_sharded(plan, shards, sharded=…, broadcast=…)` run the shards on Polars
in parallel threads. `tests/test_partition.py` compares the sharded result
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

* **Join elimination** (#75). Take `R ⋈ S` on an FK `R.k → S.pk`, with `S.pk` a key
  (`Keys.lean`) and `R.k` NOT NULL (`AVal.null = false`), where the output
  needs no column of `S`. Then the join is `R`. A left join on a key needs no
  FK at all. Proof obligation: a bag equation stating that each left row has
  exactly one match.
* **DISTINCT elimination** (#76). If `Rel.keys` proves a key among the output
  columns, then `DISTINCT r ~ r`. The ingredients exist already: `KeyOn` and
  `dedup` of a `Pairwise ≠` list.
* **Outer-to-inner join conversion** (#77). A filter above a left join that
  rejects NULLs on a right column turns it into an inner join. With an FK and
  NOT NULL, every left row matches, so the conversion holds without a filter.
  Engines do the filter case; the FK case needs our facts.
* **Filters implied by CHECK constraints** (#78). If `aeval` proves the condition
  certainly TRUE on the input (`AVal.certainlyTrue`), then `filter r c ~ r`.
  This is nearly free given `contract_sound`, and it composes: a downstream
  re-check of an upstream guarantee disappears.
* **GROUP BY simplification through functional dependencies** (#79). If a key
  `k ⊆ gs` determines the other grouping columns, group by `k` alone and
  carry the rest through `MIN` (or `ANY_VALUE`). This needs functional
  dependencies, which follow from keys plus projections.
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
