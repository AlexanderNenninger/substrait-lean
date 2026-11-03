# datafusion: facts

Generated from [facts/](facts/) by `uv run python -m sverify_dev.facts --write`; do not edit by hand. One JSON document per finding, in the format of [fact.schema.json](../fact.schema.json). Version checked: 51.0.0.

| Id | Finding | Area | Status | Verdict | ≈ entries | Last checked |
|---|---|---|---|---|---:|---|
| [datafusion-S3](#datafusion-s3) | The Substrait producer drops `VALUES` rows | relations | no-finding | refused by the replay |  | 2026-11-01 |
| [datafusion-S4](#datafusion-s4) | Decimal literals become doubles | decimals | no-finding | frontend |  | 2026-11-01 |
| [datafusion-S6](#datafusion-s6) | The SQL frontend plans another query | relations | open | frontend |  | 2026-11-01 |

## <a id="datafusion-s3"></a>datafusion-S3. The Substrait producer drops `VALUES` rows

datafusion 51.0.0 · relations · no-finding · frontend · `VALUES`, `VirtualTable`

DataFusion 51 writes `FROM (VALUES …)` as an empty virtual table.

Reference:

The replay refuses these plans (`producer: VALUES written as an empty virtual table`).

Checked:

- 2026-11-01, replay, by sverify_dev.slt, DuckDB 2.0.0's tests on DataFusion 51's plans (commit 7dbf2f7). Recorded as S3 of characterization/duckdb/FACTS.md.

## <a id="datafusion-s4"></a>datafusion-S4. Decimal literals become doubles

datafusion 51.0.0 · decimals · no-finding · frontend · `decimal literal`

DataFusion's SQL reads `99999999999999999999.99999` as a double, so `100000000000000000000 > 99999999999999999999.99999` is false.

Reference:

A decimal literal is a decimal.

Checked:

- 2026-11-01, replay, by sverify_dev.slt, DuckDB 2.0.0's tests on DataFusion 51's plans (commit 7dbf2f7): [cast/decimal_float_cast.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/cast/decimal_float_cast.test) (line 10). Recorded as S4.

## <a id="datafusion-s6"></a>datafusion-S6. The SQL frontend plans another query

datafusion 51.0.0 · relations · open · frontend · `EXCEPT ALL`, `FETCH FIRST`, `COUNT(DISTINCT) OVER`, `FILTER (WHERE)`, `GROUP BY`, `NATURAL JOIN`

In these cases `Rel.eval` and DuckDB running the written plan agree with each other, and both differ from DuckDB, because the plan DataFusion writes is not the query. Each is a plan sverify checks for a query the user did not write.

- `EXCEPT ALL` is planned as a left anti join, which loses multiplicities: `[1, 1, 2, 3] EXCEPT ALL [1, 3]` gives `[2]`, not `[1, 2]` (`setops/test_pg_union.test:339,350`).
- `FETCH FIRST n ROWS ONLY` is dropped: the plan has no limit (`parser/fetch_first.test`).
- The Substrait producer drops `DISTINCT` and `FILTER (WHERE …)` of a window aggregate: `COUNT(DISTINCT s) OVER (…)` counts every row (`window/test_window_distinct.test:76`, `window/test_naive_aggregation.test:204`, `window/test_streaming_window.test:223`).
- `GROUP BY k, k` writes two grouping expressions, and the projection above reads the aggregate's columns shifted by one (`aggregate/group/test_group_by.test:149`). Either the producer or Lean's reading of a repeated grouping expression is wrong; this needs reading.
- `SELECT *` of a `NATURAL JOIN` keeps both copies of the join columns (`catalog/case_insensitive_using.test:123-138`).

Reference:

The plan should be the query's.

Checked:

- 2026-11-01, replay, by sverify_dev.slt, DuckDB 2.0.0's tests on DataFusion 51's plans (commit 7dbf2f7): [setops/test_pg_union.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/setops/test_pg_union.test) (lines 339,350); [parser/fetch_first.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/parser/fetch_first.test); [window/test_window_distinct.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/window/test_window_distinct.test) (line 76); [window/test_naive_aggregation.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/window/test_naive_aggregation.test) (line 204); [window/test_streaming_window.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/window/test_streaming_window.test) (line 223); [aggregate/group/test_group_by.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/aggregate/group/test_group_by.test) (line 149); [catalog/case_insensitive_using.test](https://github.com/duckdb/duckdb/blob/d54cbbe3df17e8e5ce68312f483b4155836112aa/test/sql/catalog/case_insensitive_using.test) (lines 123-138). Recorded as S6.
