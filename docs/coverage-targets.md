# Coverage targets for 1.0

Sverify 1.0 covers the SQL and Ibis constructs that real pipelines use, and
lists the rest with a reason. This page is that list
([#743](https://github.com/AlexanderNenninger/substrait-lean/issues/743)),
the decision behind each entry, and the number that tracks it. The roadmap
([#757](https://github.com/AlexanderNenninger/substrait-lean/issues/757), M4)
sets the bar: coverage is high, and hard blockers are skipped and listed.

Each construct gets one of three marks:

- in: real queries need it, and the model can state it. 1.0 waits for it.
- skipped: a hard blocker. The table gives the reason and, where there is
  one, the workaround that verifies today.
- after 1.0: wanted, and not a gate.

## The number

```bash
uv run python -m sverify_dev.coverage --targets
```

prints the share of the in-for-1.0 constructs that sverify covers, by area,
with the issue of each one left. On 2026-11-05 it was 27 of 60 (45 %).

A construct is covered when its probe verifies: a DuckDB SQL query that the
lift reads and the checker accepts, and, where the Ibis API has the same
construct, the case of the README's coverage table. The targets and their
probes live in
[`sverify_dev/coverage_targets/`](../python/tools/sverify_dev/coverage_targets/),
one file per area, and
[`tests/test_coverage_targets.py`](../python/tests/test_coverage_targets.py)
pins what each probe gives. A pull request that covers a target flips its
`covered` in the area's file and its row on this page. CI prints the number in
the summary of the `test (core 1/3)` job, and
[M6](https://github.com/AlexanderNenninger/substrait-lean/milestone/6) makes it
a gate.

## What the list weighs

Real queries decide what is in. The sources, measured on 2026-11-05:

- The query catalogue ([`catalogue/status.json`](../catalogue/status.json)):
  135 of 139 queries verify. Its 139 queries name the features they need
  ([`catalogue/features.toml`](../catalogue/features.toml)); the counts in
  the tables below are how many queries need each one. The four rejected are
  `dbt-org-hierarchy` (`WITH RECURSIVE`), `dbt-generate-date-spine`
  (`generate_series`), `dbt-unpivot-longer` (`UNNEST`) and
  `ts-local-day-revenue` (`AT TIME ZONE`).
- The Ibis API (epic [#60](https://github.com/AlexanderNenninger/substrait-lean/issues/60)):
  184 of 211 probed operations verify (the README's coverage table).
- dbt: the cross-database macros of dbt and dbt_utils (`date_spine`,
  `unpivot`, `generate_surrogate_key`, `split_part`, `listagg`, `bool_or`,
  `any_value`, `dateadd`), and the shop example, whose
  [proof status](../dbt/examples/shop/PROOF-STATUS.md) lists what blocks each
  test left. Those blockers are proof gaps: string value
  sets ([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708)),
  keys through point-in-time joins
  ([#814](https://github.com/AlexanderNenninger/substrait-lean/issues/814)),
  `md5`, which is not injective, and `WITH RECURSIVE`.
- The patterns of the examples and the agent skill
  ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749),
  [#765](https://github.com/AlexanderNenninger/substrait-lean/issues/765)):
  double-entry bookkeeping, dedup and latest row per key, sessionization,
  funnels and retention, SCD types 1, 2 and 4, running balances,
  time-weighted averages and gap filling.
- The phone template's Eurostat pipeline
  ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)):
  wide tables to unpivot, values as text with `:` for missing and flags to
  split off.
- DuckDB's sqllogictest replay (`sverify_dev.slt`, the ledgers in
  [`characterization/duckdb/`](../characterization/duckdb/README.md), DuckDB
  2.0.0): 86,155 queries agree, 168 disagree, 22,368 are refused and 12,984
  skipped. The replay tests DuckDB's edge cases more than it samples real
  use, so its counts break ties. Of the refusals, 3,932 are out of scope
  (DuckDB's catalog functions, file readers, sequences, settings, aggregate
  states) and 680 are names the harness cannot resolve.

The measurement found one thing worth stating on its own: the SQL lift
trails the Ibis producer. Regex functions, `right`, `lpad`, `string_agg`,
`bool_or`, ordered `first` and `last`, `epoch`, `make_date` and RANGE frames
over intervals verify from Ibis and are refused from SQL. Closing that gap is
most of the cheap work left, and it matters to dbt users, who write SQL.

## Targets by area

The areas are those of the code
(the `add-function` skill, `.claude/skills/add-function/SKILL.md`). "Today"
is what the probe gives.

### Relations

6 of 13 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| filter, project, group, having, order, limit | in | covered | catalogue: group_by 88, filter 64, order_by 42, limit 20 |  |
| inner, left, full, semi and anti joins | in | covered | catalogue: inner_join 44, multi_join 17, left_join 10, anti_join 4 |  |
| range joins | in | covered | catalogue: range_join 11; SCD 2 ([#763](https://github.com/AlexanderNenninger/substrait-lean/issues/763)); dbt shop orders_with_city |  |
| CTEs and uncorrelated subqueries | in | covered | catalogue: cte 3, in_subquery 2, scalar_subquery 2; dbt models are CTE chains |  |
| set operations | in | covered | catalogue: union_all 3, intersect_except; dbt_utils.union_relations |  |
| GROUPING SETS and ROLLUP | in | covered | catalogue: grouping_sets 2 (TPC-DS) |  |
| VALUES in FROM | in | covered | dbt mapping tables; catalogue values (Ibis memtables); replay ~80 | [#803](https://github.com/AlexanderNenninger/substrait-lean/issues/803) |
| correlated EXISTS and NOT EXISTS | in | — | replay 1,340 (all correlated subqueries); dbt anti-joins for new rows | [#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345) |
| DISTINCT ON | in | — | dedup pattern ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749), [#765](https://github.com/AlexanderNenninger/substrait-lean/issues/765)); catalogue dedup_latest 3; replay 64 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| GROUP BY ALL and ORDER BY ALL | in | — | DuckDB style SQL; replay 124 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| range() and generate_series() with constant bounds | in | — | catalogue dbt-generate-date-spine; dbt_utils.date_spine; gap filling ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749)); replay 965 | [#321](https://github.com/AlexanderNenninger/substrait-lean/issues/321) |
| UNPIVOT | in | covered | catalogue dbt-unpivot-longer, unpivot 2; Eurostat's wide tables ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)); dbt_utils.unpivot | [#804](https://github.com/AlexanderNenninger/substrait-lean/issues/804) |
| ASOF JOIN | in | covered | catalogue asof_join 2 (through sverify.asof_join); time-weighted pattern ([#765](https://github.com/AlexanderNenninger/substrait-lean/issues/765)); replay 105 | [#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805) |
| correlated scalar subqueries, ANY and ALL | skipped | — | replay 1,340 with EXISTS; Ibis correlated scalar subquery | [#813](https://github.com/AlexanderNenninger/substrait-lean/issues/813) |
| WITH RECURSIVE | skipped | — | catalogue dbt-org-hierarchy; dbt shop org_depth; replay 243 | [#320](https://github.com/AlexanderNenninger/substrait-lean/issues/320) |
| SAMPLE and POSITIONAL JOIN | skipped | — | replay 145; Ibis sample |  |
| LIMIT by an expression or a subquery | after 1.0 | — | Ibis limit expression, limit count(); replay 39 | [#503](https://github.com/AlexanderNenninger/substrait-lean/issues/503) |
| scalar subquery of many rows, with the error reported | after 1.0 | — | Ibis scalar subquery, many rows | [#504](https://github.com/AlexanderNenninger/substrait-lean/issues/504) |
| row values: (a, b) IN (SELECT …), row comparisons | after 1.0 | — | replay ~110 | [#349](https://github.com/AlexanderNenninger/substrait-lean/issues/349) |

### Core

4 of 6 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| arithmetic, CASE, COALESCE, NULLIF, comparisons | in | covered | catalogue: arithmetic_float 26, case_when 14, coalesce_nullif 6, between 11 |  |
| math functions | in | covered | catalogue: math_funcs 5, math_transcendental 2 |  |
| decimal arithmetic and aggregates | in | covered | catalogue: decimal 40 (TPC-H, TPC-DS, finance); double-entry pattern ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749)) |  |
| round of a decimal | in | — | money rounding: round(price * 1.19, 2); replay 28 | [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27) |
| DuckDB aliases: if, iff, len, substr, arbitrary | in | — | DuckDB style SQL; replay (binder tests) | [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328) |
| fp32 (FLOAT) | skipped | — | replay 427; Parquet files written by ML tools | [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417) |
| now, current_date, random, uuid | skipped | — | Ibis now, today, random, uuid | [#58](https://github.com/AlexanderNenninger/substrait-lean/issues/58) |
| unsigned integers and HUGEINT | after 1.0 | — | replay 1,495, mostly DuckDB's own type tests | [#350](https://github.com/AlexanderNenninger/substrait-lean/issues/350) |
| printf, format, signbit | in | covered | labels, zero-padded codes; replay 80 |  |
| age, base64, octet_length and other scalars | after 1.0 | — | replay ~60 | [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328) |

### Casts

3 of 6 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| numeric casts: integer, double, decimal | in | covered | catalogue: cast_numeric 8 |  |
| CAST(DOUBLE AS INTEGER), which DuckDB rounds | in | — | CAST(amount * 100 AS BIGINT) for cents; catalogue cast_numeric 8; replay 76 | [#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322) |
| decimal to a smaller scale | in | — | CAST(x AS DECIMAL(10, 2)) after arithmetic; replay 25 | [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27) |
| casts to VARCHAR | in | — | dbt surrogate keys and hash diffs (md5 of casts), dbt_utils.unpivot, labels; replay 184 | [#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346) |
| casts from VARCHAR, and TRY_CAST | in | covered | Eurostat values ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)); CSV sources; Ibis try_cast string | [#806](https://github.com/AlexanderNenninger/substrait-lean/issues/806) |
| DATE as TIMESTAMP: the cast, date_trunc and DATE ± INTERVAL of a date column | in | covered | monthly rollups over DATE columns (catalogue date_trunc 11); dbt.dateadd | [#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807) |
| casts of a double to VARCHAR | after 1.0 | — | labels; replay (part of 184) | [#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346) |

### Strings

5 of 5 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| basic string functions | in | covered | catalogue: string_basic 3, like 9; dbt cross-db macros |  |
| md5 and sha256 | in | covered | catalogue hash 1; dbt surrogate keys |  |
| regexp_matches, regexp_extract, regexp_replace | in | covered | catalogue regex_replace (ClickBench q28, through Ibis); Eurostat flags; Ibis re_* verify | [#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808) |
| split_part, string_split and concat_ws | in | covered | dbt.split_part; concat_ws surrogate keys; Eurostat | [#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808) |
| right, lpad and rpad | in | covered | dbt.right; Ibis right, lpad, rpad verify | [#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808) |
| hash() | skipped | — | Ibis hash |  |
| JSON | skipped | — | catalogue json (none verified); event payloads |  |
| translate, URL parts, LIKE ESCAPE, GLOB | after 1.0 | — | Ibis translate, host; replay ~150 | [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328) |

### Temporal

5 of 10 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| date_trunc and date parts of a timestamp | in | covered | catalogue: date_trunc 11, date_part 4 |  |
| constant intervals on timestamps, date literals | in | covered | catalogue: interval_day_time 17, date_literal 18, interval_month 8 |  |
| date_diff in days, date - date | in | covered | catalogue date_diff 6; retention pattern |  |
| DATE ± INTEGER | in | — | dbt.dateadd on DuckDB; replay 57 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| date_diff in hours, minutes, months; epoch | in | covered | sessionization, time-weighted averages, cohorts ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749), [#765](https://github.com/AlexanderNenninger/substrait-lean/issues/765)); catalogue epoch 2 | [#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809) |
| make_date, last_day, dayname, monthname | in | covered | Ibis date from columns; calendar dimensions | [#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809) |
| timestamp - timestamp, and intervals from columns | in | — | sessionization gaps (ts - lag(ts) > INTERVAL 30 MINUTE); Ibis timestamp delta, column intervals; replay 307 | [#342](https://github.com/AlexanderNenninger/substrait-lean/issues/342) |
| strptime, try_strptime, strftime | in | — | dates as text in raw data; Eurostat periods ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)); Ibis string to timestamp; replay 243 | [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347) |
| time_bucket | in | — | catalogue time_bucket 1; metrics rollups; replay 74 | [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347) |
| timestamps at s, ms and ns precision | in | — | Parquet and Arrow sources (the homelab cycling demo); replay 137 | [#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323) |
| time zones: AT TIME ZONE, TIMESTAMPTZ | skipped | — | catalogue ts-local-day-revenue; replay 46 |  |
| INTERVAL output columns as months, days and microseconds | after 1.0 | — | DuckDB's types/interval tests | [#342](https://github.com/AlexanderNenninger/substrait-lean/issues/342) |
| overlapping group_by_dynamic, rolling windows over time | after 1.0 | — | Ibis group_by_dynamic (overlapping) | [#294](https://github.com/AlexanderNenninger/substrait-lean/issues/294) |

### Nested

1 of 2 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| list literals, indexing, UNNEST | in | covered | catalogue unnest 1; Ibis lists |  |
| len, list_contains, computed list elements | in | covered | tag filters on list columns; replay (part of 1,724 list refusals) | [#812](https://github.com/AlexanderNenninger/substrait-lean/issues/812) |
| lambdas and other list functions | after 1.0 | — | replay ~1,500 | [#348](https://github.com/AlexanderNenninger/substrait-lean/issues/348) |
| vector functions | after 1.0 | — | embeddings pipelines; replay 53 | [#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327) |
| structs and MAP | after 1.0 | — | replay 1,229 | [#349](https://github.com/AlexanderNenninger/substrait-lean/issues/349) |
| VARIANT, BLOB, geometry | skipped | — | replay 1,619 |  |

### Aggregates

5 of 9 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| sum, count, avg, min, max, count distinct, FILTER | in | covered | catalogue: sum 57, count 28, min_max 20, avg 19, agg_filter 10, count_distinct 8 |  |
| stddev, variance, corr | in | covered | catalogue: stddev_var 4, corr 1; float pattern ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749)) |  |
| median, quantile_cont, quantile_disc | in | covered | catalogue percentile 2 (H2O q6); p95 rollups ([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)'s comment) |  |
| arg_max, arg_min, max_by | in | covered | catalogue arg_max 3; latest row per key |  |
| string_agg, listagg, list, array_agg | in | covered | catalogue string_agg 1; dbt.listagg; Ibis group_concat, collect verify | [#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810) |
| bool_and, bool_or | in | covered | dbt.bool_or; Ibis any, all verify | [#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810) |
| first and last with ORDER BY | in | covered | catalogue first_last_value 2; Ibis first, last ordered | [#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810) |
| any_value | in | — | dbt.any_value; replay 56 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| approximate aggregates | after 1.0 | — | catalogue approx_distinct; Ibis approx_nunique, approx_median | [#469](https://github.com/AlexanderNenninger/substrait-lean/issues/469) |
| statistics as black boxes: mad, entropy, kurtosis, sem, product | in | covered | metrics rollups; replay ~100 |  |
| histogram and other MAP results | after 1.0 | — | replay ~80 | [#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326) |
| collect with NULLs kept | after 1.0 | — | Ibis collect include_null | [#505](https://github.com/AlexanderNenninger/substrait-lean/issues/505) |

### Windows

5 of 9 in for 1.0 covered.

| Construct | 1.0 | Today | Used by | Issue |
|---|---|---|---|---|
| row_number, rank, dense_rank, ntile | in | covered | catalogue: row_number 8, ntile 3, rank 2; dedup pattern |  |
| lag and lead | in | covered | catalogue lag_lead 15; sessionization, counter resets |  |
| running and ROWS-frame aggregates | in | covered | catalogue: running_agg 11, rows_frame 4; running balance pattern |  |
| aggregates over windows and over aggregates | in | covered | catalogue: window_over_aggregate 8, window_partition_agg 4 |  |
| first_value, last_value | in | covered | catalogue first_last_value 2 |  |
| QUALIFY | in | — | catalogue qualify 7 (written as subqueries); dedup pattern; replay 62 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| named WINDOW | in | — | replay 71 | [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) |
| RANGE frames with an INTERVAL offset | in | covered | rolling 7 days (catalogue range_frame 1); Ibis rolling sum (interval) verifies | [#811](https://github.com/AlexanderNenninger/substrait-lean/issues/811) |
| IGNORE NULLS | in | covered | gap filling, last observation carried forward ([#749](https://github.com/AlexanderNenninger/substrait-lean/issues/749), [#765](https://github.com/AlexanderNenninger/substrait-lean/issues/765)) | [#811](https://github.com/AlexanderNenninger/substrait-lean/issues/811) |

## Skipped and listed

| Construct | Why | Issue |
|---|---|---|
| correlated scalar subqueries, ANY and ALL | decorrelating needs the count bug handled and at most one row proved per outer row ([#504](https://github.com/AlexanderNenninger/substrait-lean/issues/504)); a join with a grouped aggregate verifies today | [#813](https://github.com/AlexanderNenninger/substrait-lean/issues/813) |
| WITH RECURSIVE | a fixpoint in the model, with termination; the shop's test on it is not provable without an acyclic hierarchy anyway | [#320](https://github.com/AlexanderNenninger/substrait-lean/issues/320) |
| SAMPLE and POSITIONAL JOIN | random, or row order, which a table does not have |  |
| fp32 (FLOAT) | the model computes in binary64; rounding to binary32 after each step needs a model of its own. Cast FLOAT columns to DOUBLE at the source | [#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417) |
| now, current_date, random, uuid | another value on every run, so no proof covers it; pass the date in as a value (dynamic parameters, [#354](https://github.com/AlexanderNenninger/substrait-lean/issues/354)) | [#58](https://github.com/AlexanderNenninger/substrait-lean/issues/58) |
| hash() | the engine's own hash, which changes between versions; md5 or sha256 verify |  |
| JSON | no JSON type in the model; flatten JSON at the source into typed columns |  |
| time zones: AT TIME ZONE, TIMESTAMPTZ | needs the time zone database in the model; store UTC and convert at the edge |  |
| VARIANT, BLOB, geometry | types outside the model |  |

## After 1.0

The rows marked "after 1.0" above are wanted and stay in the
[After 1.0](https://github.com/AlexanderNenninger/substrait-lean/milestone/9)
milestone: `LIMIT` by an expression, the error of a scalar subquery of many
rows, row values, unsigned integers and `HUGEINT`, the rest of DuckDB's
scalars, doubles cast to text, `INTERVAL` output columns, overlapping time
windows, lambdas and list functions, vector functions, structs and `MAP`,
approximate aggregates, `histogram` and `collect` with NULLs.

## Batches

The work left on the in-for-1.0 rows splits into pull-request-sized batches,
one per area, so that sessions can take one each without conflicts. Each
names the files it edits; batches 1 and 5 both edit `sql_lift/_base.py`, in
different functions (`_Lift`'s sources, and `_AGGREGATES` and `_RANKING`).

| Batch | Area | Issues | Files |
|---|---|---|---|
| 1 | relations: lift rewrites | [#803](https://github.com/AlexanderNenninger/substrait-lean/issues/803) VALUES, [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319) DISTINCT ON, GROUP BY ALL and ORDER BY ALL, [#804](https://github.com/AlexanderNenninger/substrait-lean/issues/804) UNPIVOT, [#805](https://github.com/AlexanderNenninger/substrait-lean/issues/805) ASOF JOIN | `sql_lift/relations.py`, `_base.py` (`_Lift`), `tests/test_sql_lift.py` |
| 2 | relations: new inputs and decorrelation | [#321](https://github.com/AlexanderNenninger/substrait-lean/issues/321) `range` and `generate_series`, [#345](https://github.com/AlexanderNenninger/substrait-lean/issues/345) correlated `EXISTS` and `NOT EXISTS` | `sql_lift/relations.py`, `Parse.lean` (virtual tables), the catalogue's date spine |
| 3 | casts | [#346](https://github.com/AlexanderNenninger/substrait-lean/issues/346) to VARCHAR, [#806](https://github.com/AlexanderNenninger/substrait-lean/issues/806) from VARCHAR, [#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322) rounding casts, [#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27) decimal rescale and `round`, [#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807) DATE as TIMESTAMP | `sql_lift/casts.py`, the casts in `Expr.lean` and `Parse.lean`, the writers' casts |
| 4 | strings | [#808](https://github.com/AlexanderNenninger/substrait-lean/issues/808), and the aliases of [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328) (`if`, `len`, `substr`, `arbitrary`) | `sql_lift/strings.py`, `_functions.py`, `tests/test_sql_lift_strings.py` |
| 5 | aggregates and windows | [#810](https://github.com/AlexanderNenninger/substrait-lean/issues/810), [#811](https://github.com/AlexanderNenninger/substrait-lean/issues/811), and [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319)'s `any_value`, `QUALIFY` and named `WINDOW` | `sql_lift/_base.py` (`_AGGREGATES`, `_RANKING`) |
| 6 | temporal: lift | [#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809), [#319](https://github.com/AlexanderNenninger/substrait-lean/issues/319)'s DATE ± INTEGER | `sql_lift/temporal.py`, `tests/test_sql_lift_temporal.py` |
| 7 | temporal: model | [#347](https://github.com/AlexanderNenninger/substrait-lean/issues/347) `strptime`, `strftime`, `time_bucket`; [#323](https://github.com/AlexanderNenninger/substrait-lean/issues/323) precisions; [#342](https://github.com/AlexanderNenninger/substrait-lean/issues/342) `timestamp - timestamp` and column intervals | `Time.lean`, `sql_lift/temporal.py`, the writers' temporal code |
| 8 | nested | [#812](https://github.com/AlexanderNenninger/substrait-lean/issues/812) | `sql_lift/nested.py`, `sql/core/nested.py` |

Batches 6 and 7 both edit `sql_lift/temporal.py`; run them one after the
other. Each batch ends with its targets' `covered` flipped and this page's
rows updated.
