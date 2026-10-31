# Findings

<!-- stats:start -->
### Status per suite

| suite | queries | verified | as DOUBLE only | rejected | upstream | DataFusion runs | Polars | DuckDB | Snowflake SQL |
|---|---|---|---|---|---|---|---|---|---|
| clickbench | 7 | 6 | 0 | 1 | 0 | 7 | 0 | 0 | 0 |
| h2o | 10 | 8 | 0 | 2 | 0 | 10 | 4 | 4 | 4 |
| job | 3 | 3 | 0 | 0 | 0 | 3 | 0 | 0 | 0 |
| modelling | 14 | 10 | 0 | 0 | 4 | 11 | 6 | 6 | 6 |
| product | 13 | 8 | 0 | 4 | 1 | 12 | 1 | 1 | 1 |
| ssb | 4 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |
| timeseries | 15 | 10 | 0 | 3 | 2 | 13 | 3 | 3 | 3 |
| tpcds | 8 | 0 | 3 | 5 | 0 | 8 | 0 | 0 | 0 |
| tpch | 22 | 2 | 6 | 12 | 2 | 22 | 0 | 0 | 0 |
| windows | 13 | 5 | 0 | 8 | 0 | 13 | 3 | 3 | 2 |
| **all** | 109 | 56 | 9 | 35 | 9 | 103 | 17 | 17 | 16 |

### Feature frequency

How many of the 109 queries need each feature (as originally written, so subqueries an Ibis formulation rewrote into joins count), and Lean's support.

| feature | group | queries | share | Lean |
|---|---|---|---|---|
| `group_by` | aggregation | 69 | 63% | yes |
| `filter` | relational | 51 | 47% | yes |
| `sum` | aggregation | 43 | 39% | yes |
| `inner_join` | relational | 43 | 39% | yes |
| `order_by` | relational | 42 | 39% | yes |
| `decimal` | expressions | 25 | 23% | no |
| `count` | aggregation | 23 | 21% | yes |
| `limit` | relational | 20 | 18% | yes |
| `date_literal` | expressions | 17 | 16% | yes |
| `multi_join` | relational | 17 | 16% | yes |
| `arithmetic_float` | expressions | 17 | 16% | yes |
| `avg` | aggregation | 15 | 14% | yes |
| `global_aggregate` | aggregation | 12 | 11% | yes |
| `min_max` | aggregation | 11 | 10% | partial |
| `between` | expressions | 10 | 9% | yes |
| `case_when` | expressions | 10 | 9% | yes |
| `interval_day_time` | expressions | 10 | 9% | yes |
| `in_list` | expressions | 10 | 9% | yes |
| `like` | expressions | 9 | 8% | yes |
| `agg_filter` | aggregation | 9 | 8% | yes |
| `count_distinct` | aggregation | 8 | 7% | yes |
| `left_join` | relational | 8 | 7% | yes |
| `interval_month` | expressions | 8 | 7% | no |
| `row_number` | windows | 7 | 6% | yes |
| `window_over_aggregate` | windows | 7 | 6% | yes |
| `date_trunc` | expressions | 6 | 6% | partial |
| `qualify` | windows | 6 | 6% | yes |
| `lag_lead` | windows | 6 | 6% | yes |
| `range_join` | relational | 6 | 6% | yes |
| `cast_numeric` | expressions | 6 | 6% | yes |
| `running_agg` | windows | 6 | 6% | no |
| `project` | relational | 5 | 5% | yes |
| `cast_date` | expressions | 5 | 5% | partial |
| `self_join` | relational | 5 | 5% | yes |
| `string_compare` | expressions | 4 | 4% | partial |
| `having` | aggregation | 4 | 4% | yes |
| `arithmetic_int` | expressions | 4 | 4% | yes |
| `math_funcs` | expressions | 4 | 4% | yes |
| `non_equi_join` | relational | 4 | 4% | partial |
| `anti_join` | relational | 4 | 4% | yes |
| `date_part` | expressions | 4 | 4% | partial |
| `exists_subquery` | relational | 4 | 4% | no |
| `window_partition_agg` | windows | 4 | 4% | no |
| `correlated_subquery` | relational | 4 | 4% | no |
| `string_basic` | expressions | 3 | 3% | yes |
| `union_all` | relational | 3 | 3% | yes |
| `coalesce_nullif` | expressions | 3 | 3% | yes |
| `semi_join` | relational | 3 | 3% | yes |
| `date_diff` | expressions | 3 | 3% | yes |
| `cte` | relational | 3 | 3% | yes |
| `scalar_subquery` | relational | 3 | 3% | no |
| `percentile` | aggregation | 2 | 2% | no |
| `stddev_var` | aggregation | 2 | 2% | no |
| `pivot` | relational | 2 | 2% | yes |
| `unpivot` | relational | 2 | 2% | partial |
| `dedup_latest` | windows | 2 | 2% | yes |
| `ntile` | windows | 2 | 2% | no |
| `asof_join` | relational | 2 | 2% | yes |
| `rows_frame` | windows | 2 | 2% | no |
| `grouping_sets` | aggregation | 2 | 2% | no |
| `rank` | windows | 2 | 2% | no |
| `in_subquery` | relational | 2 | 2% | yes |
| `regex_replace` | expressions | 1 | 1% | no |
| `offset` | relational | 1 | 1% | yes |
| `corr` | aggregation | 1 | 1% | no |
| `unnest` | relational | 1 | 1% | no |
| `hash` | expressions | 1 | 1% | no |
| `recursive_cte` | relational | 1 | 1% | no |
| `generate_series` | relational | 1 | 1% | partial |
| `string_agg` | aggregation | 1 | 1% | no |
| `time_bucket` | expressions | 1 | 1% | no |
| `range_frame` | windows | 1 | 1% | no |
| `timezone` | expressions | 1 | 1% | no |
| `full_join` | relational | 1 | 1% | yes |
| `cross_join` | relational | 1 | 1% | yes |
| `not_in_subquery` | relational | 1 | 1% | no |
| `arg_max` | aggregation | 1 | 1% | no |
| `distinct` | relational | 1 | 1% | yes |
| `dynamic_interval` | expressions | 1 | 1% | no |
| `first_last_value` | windows | 1 | 1% | no |

### Gaps ranked by the queries they block

*Blocks*: queries that do not verify (on their own types) and need the feature; *alone*: of those, the queries it is the only missing feature of, so closing it alone makes them verify (DECIMAL counts queries that verify only as DOUBLE). Engine refusals of verified queries are separate, below.

| feature | blocks | alone | Lean | note |
|---|---|---|---|---|
| `decimal` | 25 | 9 | no | Values are refused ("cast them to DOUBLE"), SUM of DECIMAL too; the catalogue also probes each such query with DOUBLE in their place |
| `interval_month` | 8 | 2 | no | "month and year intervals are not supported" |
| `running_agg` | 6 | 3 | no |  |
| `window_partition_agg` | 4 | 1 | no |  |
| `date_part` | 3 | 0 | partial | timestamps only; EPOCH and DATE columns refused |
| `ntile` | 2 | 2 | no |  |
| `percentile` | 2 | 1 | no | Ibis cannot even compile quantile for DataFusion |
| `rank` | 2 | 1 | no |  |
| `rows_frame` | 2 | 1 | no |  |
| `grouping_sets` | 2 | 0 | no |  |
| `scalar_subquery` | 2 | 0 | no | DataFusion's Substrait producer cannot convert it; rewrite as a cross join with a one-row aggregate |
| `stddev_var` | 2 | 0 | no |  |
| `arg_max` | 1 | 1 | no | first_value aggregates are refused |
| `corr` | 1 | 1 | no |  |
| `dynamic_interval` | 1 | 1 | no | Ibis as_interval compiles to CAST(CAST(n AS VARCHAR) \|\| ' day' AS INTERVAL), refused as a string cast |
| `generate_series` | 1 | 1 | partial | constant ranges only (folded to VALUES); date ranges need month intervals or a calendar table |
| `hash` | 1 | 1 | no |  |
| `not_in_subquery` | 1 | 1 | no | refused: DataFusion gets NULLs in the subquery wrong |
| `range_frame` | 1 | 1 | no |  |
| `recursive_cte` | 1 | 1 | no | DataFusion plans it (without a column list) but its Substrait producer has no RecursiveQuery; no fixpoint in the model |
| `regex_replace` | 1 | 1 | no |  |
| `string_agg` | 1 | 1 | no |  |
| `time_bucket` | 1 | 1 | no | Ibis cannot compile TimestampBucket for DataFusion; DATE_BIN is refused by the checker |
| `timezone` | 1 | 1 | no |  |
| `unnest` | 1 | 1 | no | DataFusion's Substrait producer has no Unnest |
| `first_last_value` | 1 | 0 | no |  |
| `min_max` | 1 | 0 | partial | integers, strings, dates and timestamps; MIN/MAX of doubles and DECIMAL are refused |

### Why engines refuse verified queries

Over the 65 queries that verify (some only as DOUBLE):

| engine: reason | queries |
|---|---|
| duckdb: refused: aggregate functions (GROUP BY with measures or expressions) are not translated yet | 47 |
| polars: refused: aggregate functions (GROUP BY with measures) are not translated yet | 47 |
| snowflake: refused: aggregate functions (GROUP BY with measures or expressions) are not translated yet | 47 |
| duckdb: refused: comparison of time with interval; cast one side first | 1 |
| polars: refused: lt of Datetime(time_unit='us', time_zone=None) and Duration(time_unit='us') | 1 |
| snowflake: refused: comparison of time with interval; cast one side first | 1 |
| snowflake: refused: Snowflake has no interval values, so timestamp - timestamp is refused | 1 |

### Pitfall frequency

| pitfall | queries | DataFusion quirks |
|---|---|---|
| `tie_order` | 29 | O2, O3, O5 |
| `empty_aggregate` | 12 | N4 |
| `null_join_keys` | 12 | N5, N6 |
| `timezone_dst` | 9 | T2, T3, T4, T5 |
| `float_sum_order` | 9 | F9 |
| `division_by_zero` | 9 | I2, F4 |
| `null_ordering` | 8 | O1 |
| `null_aggregate` | 8 | – |
| `window_default_frame` | 6 | O4 |
| `decimal_scale` | 6 | – |
| `gap_threshold` | 5 | T5 |
| `rank_semantics` | 5 | – |
| `float_nan` | 4 | F1, F2, F3, F7, F8 |
| `integer_division` | 4 | I3 |
| `count_distinct_null` | 3 | N6 |
| `string_collation` | 3 | S1, S4, S6 |
| `not_in_null` | 3 | N2, N3 |
| `limit_without_order` | 2 | O3 |
| `percentile_method` | 2 | – |
| `week_definition` | 2 | – |
| `implicit_coercion` | 2 | F6, I10, I11 |
| `regex_dialect` | 1 | – |
| `int_overflow` | 1 | I1, I6 |
| `eager_evaluation` | 1 | E1, E2, E4, E5 |
| `like_escape` | 1 | – |
| `substr_index` | 1 | S3 |
<!-- stats:end -->
