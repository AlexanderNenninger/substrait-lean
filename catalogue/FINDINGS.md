# Query catalogue: findings

The catalogue holds 139 real analytical queries: all 22 TPC-H queries,
8 TPC-DS, 4 SSB, 7 ClickBench, 3 JOB and 10 H2O db-benchmark queries
(54 benchmark queries), and 85 practitioner idioms from general analytics,
IoT telemetry and finance ([README.md](README.md)). Sverify's catalogue tool
(`python -m sverify_dev.catalogue`) verifies each with `substrait-check`,
runs Lean's written plan on Polars and DuckDB against DuckDB's own rows, and
writes Snowflake SQL for it (`status.json`).

The tables below are generated from the TOML and `status.json` by
`uv run python -m sverify_dev.catalogue --write-tables`, on `main` after every
merge; [INDEX.md](INDEX.md) lists every query with its status. As of
2026-11-07 the earlier prose of this file, written when DataFusion was the
reference, is retired: what the reference computes is in
[docs/reference-semantics.md](../docs/reference-semantics.md) and
[docs/core-semantics.md](../docs/core-semantics.md), what each engine does
is in its facts under [characterization/](../characterization/README.md),
and the cross-engine pitfalls are in [pitfalls.toml](pitfalls.toml) and
[docs/guide.md](../docs/guide.md).

How to read the tables:

* The engine columns compare results on small seeded synthetic tables (30
  rows per table unless `schemas.toml` fixes a size, NULL one time in ten),
  generated from `schemas.toml`'s value pools.
* Snowflake SQL is written and parsed with SQLGlot; the catalogue does not
  run it.
* Feature annotations are by hand; the test checks them against the probes
  (a verified query may not need an unsupported feature, a failure must point
  at a listed one), but a feature the probe never exercises can be mislabelled.
* Benchmark queries are paraphrased and re-expressed in Ibis with simplified
  column lists; they keep the operators and predicates of the originals.

## Tables

<!-- stats:start -->
### Status per suite

| suite | queries | verified | as DOUBLE only | rejected | upstream | DuckDB runs the SQL | Polars | DuckDB | Snowflake SQL |
|---|---|---|---|---|---|---|---|---|---|
| clickbench | 7 | 7 | 0 | 0 | 0 | 7 | 6 | 7 | 6 |
| finance | 18 | 18 | 0 | 0 | 0 | 16 | 16 | 18 | 6 |
| h2o | 10 | 10 | 0 | 0 | 0 | 10 | 8 | 10 | 8 |
| iot | 12 | 12 | 0 | 0 | 0 | 12 | 11 | 12 | 10 |
| job | 3 | 3 | 0 | 0 | 0 | 3 | 3 | 3 | 3 |
| modelling | 14 | 12 | 0 | 2 | 0 | 14 | 11 | 12 | 11 |
| product | 13 | 13 | 0 | 0 | 0 | 13 | 10 | 13 | 10 |
| ssb | 4 | 4 | 0 | 0 | 0 | 4 | 4 | 4 | 4 |
| timeseries | 15 | 14 | 0 | 1 | 0 | 15 | 14 | 14 | 14 |
| tpcds | 8 | 8 | 0 | 0 | 0 | 8 | 8 | 8 | 0 |
| tpch | 22 | 22 | 0 | 0 | 0 | 22 | 22 | 22 | 6 |
| windows | 13 | 13 | 0 | 0 | 0 | 13 | 12 | 13 | 10 |
| **all** | 139 | 136 | 0 | 3 | 0 | 137 | 125 | 136 | 88 |

### Feature frequency

How many of the 139 queries need each feature (as originally written, so subqueries an Ibis formulation rewrote into joins count), and Lean's support.

| feature | group | queries | share | Lean |
|---|---|---|---|---|
| `group_by` | aggregation | 88 | 63% | yes |
| `filter` | relational | 64 | 46% | yes |
| `sum` | aggregation | 57 | 41% | yes |
| `inner_join` | relational | 44 | 32% | yes |
| `order_by` | relational | 42 | 30% | yes |
| `decimal` | expressions | 40 | 29% | partial |
| `count` | aggregation | 28 | 20% | yes |
| `arithmetic_float` | expressions | 26 | 19% | yes |
| `min_max` | aggregation | 20 | 14% | partial |
| `limit` | relational | 20 | 14% | yes |
| `avg` | aggregation | 19 | 14% | yes |
| `date_literal` | expressions | 18 | 13% | yes |
| `interval_day_time` | expressions | 17 | 12% | yes |
| `multi_join` | relational | 17 | 12% | yes |
| `lag_lead` | windows | 15 | 11% | yes |
| `case_when` | expressions | 14 | 10% | yes |
| `global_aggregate` | aggregation | 12 | 9% | yes |
| `between` | expressions | 11 | 8% | yes |
| `date_trunc` | expressions | 11 | 8% | yes |
| `running_agg` | windows | 11 | 8% | yes |
| `range_join` | relational | 11 | 8% | yes |
| `agg_filter` | aggregation | 10 | 7% | yes |
| `left_join` | relational | 10 | 7% | yes |
| `in_list` | expressions | 10 | 7% | yes |
| `like` | expressions | 9 | 6% | yes |
| `count_distinct` | aggregation | 8 | 6% | yes |
| `self_join` | relational | 8 | 6% | yes |
| `cast_date` | expressions | 8 | 6% | partial |
| `cast_numeric` | expressions | 8 | 6% | yes |
| `agg_arithmetic` | aggregation | 8 | 6% | yes |
| `window_over_aggregate` | windows | 8 | 6% | yes |
| `row_number` | windows | 8 | 6% | yes |
| `interval_month` | expressions | 8 | 6% | yes |
| `non_equi_join` | relational | 7 | 5% | partial |
| `qualify` | windows | 7 | 5% | yes |
| `having` | aggregation | 6 | 4% | yes |
| `coalesce_nullif` | expressions | 6 | 4% | yes |
| `date_diff` | expressions | 6 | 4% | partial |
| `math_funcs` | expressions | 5 | 4% | yes |
| `project` | relational | 5 | 4% | yes |
| `arithmetic_int` | expressions | 5 | 4% | yes |
| `string_compare` | expressions | 4 | 3% | partial |
| `rows_frame` | windows | 4 | 3% | partial |
| `stddev_var` | aggregation | 4 | 3% | partial |
| `anti_join` | relational | 4 | 3% | yes |
| `date_part` | expressions | 4 | 3% | partial |
| `exists_subquery` | relational | 4 | 3% | yes |
| `window_partition_agg` | windows | 4 | 3% | yes |
| `correlated_subquery` | relational | 4 | 3% | no |
| `string_basic` | expressions | 3 | 2% | yes |
| `ntile` | windows | 3 | 2% | yes |
| `arg_max` | aggregation | 3 | 2% | yes |
| `dedup_latest` | windows | 3 | 2% | yes |
| `union_all` | relational | 3 | 2% | yes |
| `semi_join` | relational | 3 | 2% | yes |
| `cte` | relational | 3 | 2% | yes |
| `scalar_subquery` | relational | 3 | 2% | yes |
| `full_join` | relational | 2 | 1% | yes |
| `math_transcendental` | expressions | 2 | 1% | yes |
| `percentile` | aggregation | 2 | 1% | yes |
| `epoch` | expressions | 2 | 1% | partial |
| `interval_to_number` | expressions | 2 | 1% | partial |
| `cross_join` | relational | 2 | 1% | yes |
| `first_last_value` | windows | 2 | 1% | yes |
| `pivot` | relational | 2 | 1% | yes |
| `unpivot` | relational | 2 | 1% | partial |
| `asof_join` | relational | 2 | 1% | yes |
| `grouping_sets` | aggregation | 2 | 1% | yes |
| `rank` | windows | 2 | 1% | yes |
| `in_subquery` | relational | 2 | 1% | yes |
| `regex_replace` | expressions | 1 | 1% | yes |
| `offset` | relational | 1 | 1% | yes |
| `corr` | aggregation | 1 | 1% | partial |
| `unnest` | relational | 1 | 1% | partial |
| `hash` | expressions | 1 | 1% | partial |
| `recursive_cte` | relational | 1 | 1% | no |
| `generate_series` | relational | 1 | 1% | partial |
| `string_agg` | aggregation | 1 | 1% | partial |
| `time_bucket` | expressions | 1 | 1% | partial |
| `range_frame` | windows | 1 | 1% | partial |
| `timezone` | expressions | 1 | 1% | no |
| `sort_by_expression` | relational | 1 | 1% | yes |
| `not_in_subquery` | relational | 1 | 1% | yes |
| `distinct` | relational | 1 | 1% | yes |
| `dynamic_interval` | expressions | 1 | 1% | partial |

### Gaps ranked by the queries they block

*Blocks*: queries that do not verify (on their own types) and need the feature; *alone*: of those, the queries it is the only missing feature of, so closing it alone makes them verify (DECIMAL counts queries that verify only as DOUBLE). Engine refusals of verified queries are separate, below.

| feature | blocks | alone | Lean | note |
|---|---|---|---|---|
| `generate_series` | 1 | 1 | partial | constant ranges only (folded to VALUES); date ranges need month intervals or a calendar table |
| `recursive_cte` | 1 | 1 | no | DataFusion plans it (without a column list) but its Substrait producer has no RecursiveQuery; no fixpoint in the model |
| `timezone` | 1 | 1 | no |  |

### Why engines refuse verified queries

Over the 136 queries that verify (some only as DOUBLE):

| engine: reason | queries |
|---|---|
| snowflake: refused: snowflake does not compute decimals as the reference does yet (#27) | 24 |
| snowflake: refused: Snowflake tables have no row order, so FETCH and windows over a named table cannot follow the Lean mo | 8 |
| polars: refused: first() (SQL first) runs on duckdb only: run it with engine='duckdb' (Polars does not run it yet; see | 3 |
| snowflake: refused: first() (SQL first) runs on duckdb only: run it with engine='duckdb' (snowflake does not run it yet;  | 3 |
| polars: refused: std() over a window (SQL stddev_samp, stddev_pop OVER) runs on duckdb only: run it with engine='duckd | 2 |
| snowflake: refused: std() over a window (SQL stddev_samp, stddev_pop OVER) runs on duckdb only: run it with engine='duckd | 2 |
| snowflake: refused: MAX of doubles is not yet supported on snowflake; run it with engine='duckdb' (see #271, https://gith | 2 |
| snowflake: refused: Snowflake's LN is not documented to be C's libm, which the Lean model uses | 2 |
| polars: refused: median() or quantile() (SQL median, quantile_cont) runs on duckdb only: run it with engine='duckdb' ( | 2 |
| snowflake: refused: median() or quantile() (SQL median, quantile_cont) runs on duckdb only: run it with engine='duckdb' ( | 2 |
| polars: refused: re_replace() (SQL regexp_replace) runs on duckdb only: run it with engine='duckdb' (Polars does not r | 1 |
| snowflake: refused: re_replace() (SQL regexp_replace) runs on duckdb only: run it with engine='duckdb' (snowflake does no | 1 |
| polars: refused: corr runs on duckdb only: run it with engine='duckdb' (Polars does not run it yet; see #271, https:// | 1 |
| snowflake: refused: corr runs on duckdb only: run it with engine='duckdb' (snowflake does not run it yet; see #271, https | 1 |
| polars: refused: hexdigest('md5') (SQL md5) runs on duckdb only: run it with engine='duckdb' (Polars does not run it y | 1 |
| snowflake: refused: hexdigest('md5') (SQL md5) runs on duckdb only: run it with engine='duckdb' (snowflake does not run i | 1 |
| polars: refused: group_concat() (SQL string_agg) runs on duckdb only: run it with engine='duckdb' (Polars does not run | 1 |
| snowflake: refused: group_concat() (SQL string_agg) runs on duckdb only: run it with engine='duckdb' (snowflake does not  | 1 |
| snowflake: refused: Snowflake has no interval type, so an interval result column is refused: run it with engine='duckdb'  | 1 |

### Pitfall frequency

| pitfall | queries | backend_semantics.py entries |
|---|---|---|
| `tie_order` | 44 | – |
| `null_join_keys` | 19 | N4 |
| `empty_aggregate` | 16 | A1 |
| `timezone_dst` | 14 | – |
| `division_by_zero` | 13 | I4, I5, F5 |
| `decimal_scale` | 12 | – |
| `float_sum_order` | 12 | F8 |
| `window_default_frame` | 11 | O4 |
| `gap_threshold` | 11 | – |
| `null_aggregate` | 11 | A2 |
| `float_nan` | 8 | F1, F2, F3, F4 |
| `null_ordering` | 8 | O1, O2 |
| `rank_semantics` | 6 | – |
| `integer_division` | 4 | I1, I3 |
| `count_distinct_null` | 3 | A3 |
| `string_collation` | 3 | S7, S4 |
| `percentile_method` | 3 | – |
| `not_in_null` | 3 | N2 |
| `limit_without_order` | 2 | – |
| `int_overflow` | 2 | I6, I7, I8 |
| `week_definition` | 2 | T1, T2, T4 |
| `implicit_coercion` | 2 | I1 |
| `regex_dialect` | 1 | S6 |
| `duration_vs_interval` | 1 | – |
| `degenerate_statistic` | 1 | – |
| `null_at_extreme` | 1 | – |
| `eager_evaluation` | 1 | – |
| `like_escape` | 1 | S5 |
| `substr_index` | 1 | S1, S2, S3 |
<!-- stats:end -->
