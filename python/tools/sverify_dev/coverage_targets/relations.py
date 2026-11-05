"""Relations: joins, subqueries, set operations, inputs (`sql_lift/relations.py`
and `_base.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "relations"

TARGETS = [
    target(
        AREA,
        "filter, project, group, having, order, limit",
        "in",
        "catalogue: group_by 88, filter 64, order_by 42, limit 20",
        True,
        sql="SELECT name, sum(qty) FROM t WHERE flag GROUP BY name HAVING sum(qty) > 10 "
        "ORDER BY 2 DESC LIMIT 5 OFFSET 1",
    ),
    target(
        AREA,
        "inner, left, full, semi and anti joins",
        "in",
        "catalogue: inner_join 44, multi_join 17, left_join 10, anti_join 4",
        True,
        sql="SELECT t.id, u.region FROM t FULL JOIN u ON t.name = u.name",
    ),
    target(
        AREA,
        "range joins",
        "in",
        "catalogue: range_join 11; SCD 2 (#763); dbt shop orders_with_city",
        True,
        sql="SELECT t.id, u.region FROM t JOIN u ON t.name = u.name AND t.d >= u.lo AND t.d < u.hi",
    ),
    target(
        AREA,
        "CTEs and uncorrelated subqueries",
        "in",
        "catalogue: cte 3, in_subquery 2, scalar_subquery 2; dbt models are CTE chains",
        True,
        sql="WITH x AS (SELECT name, sum(qty) s FROM t GROUP BY name) "
        "SELECT * FROM x WHERE name IN (SELECT name FROM u)",
    ),
    target(
        AREA,
        "set operations",
        "in",
        "catalogue: union_all 3, intersect_except; dbt_utils.union_relations",
        True,
        sql="SELECT name FROM t UNION ALL SELECT name FROM u EXCEPT SELECT region FROM u",
    ),
    target(
        AREA,
        "GROUPING SETS and ROLLUP",
        "in",
        "catalogue: grouping_sets 2 (TPC-DS)",
        True,
        sql="SELECT name, qty, sum(amount) FROM t GROUP BY GROUPING SETS ((name), (qty))",
    ),
    target(
        AREA,
        "VALUES in FROM",
        "in",
        "dbt mapping tables; catalogue values (Ibis memtables); replay ~80",
        True,
        sql="SELECT * FROM (VALUES (1, 'a'), (2, 'b')) v(k, s)",
        issue=803,
    ),
    target(
        AREA,
        "correlated EXISTS and NOT EXISTS",
        "in",
        "replay 1,340 (all correlated subqueries); dbt anti-joins for new rows",
        False,
        sql="SELECT t.id FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.name = t.name)",
        issue=345,
    ),
    target(
        AREA,
        "DISTINCT ON",
        "in",
        "dedup pattern (#749, #765); catalogue dedup_latest 3; replay 64",
        False,
        sql="SELECT DISTINCT ON (name) name, amount FROM t ORDER BY name, ts DESC",
        issue=319,
    ),
    target(
        AREA,
        "GROUP BY ALL and ORDER BY ALL",
        "in",
        "DuckDB style SQL; replay 124",
        False,
        sql="SELECT name, sum(qty) FROM t GROUP BY ALL ORDER BY ALL",
        issue=319,
    ),
    target(
        AREA,
        "range() and generate_series() with constant bounds",
        "in",
        "catalogue dbt-generate-date-spine; dbt_utils.date_spine; gap filling (#749); replay 965",
        False,
        sql="SELECT CAST(x AS DATE) AS day FROM UNNEST(generate_series("
        "TIMESTAMP '2024-01-01', TIMESTAMP '2024-01-31', INTERVAL '1 day')) AS g(x)",
        issue=321,
    ),
    target(
        AREA,
        "UNPIVOT",
        "in",
        "catalogue dbt-unpivot-longer, unpivot 2; Eurostat's wide tables (#771); dbt_utils.unpivot",
        True,
        sql="SELECT id, k, v FROM (SELECT id, qty, amount FROM t) "
        "UNPIVOT (v FOR k IN (qty, amount))",
        issue=804,
    ),
    target(
        AREA,
        "ASOF JOIN",
        "in",
        "catalogue asof_join 2 (through sverify.asof_join); time-weighted pattern (#765); "
        "replay 105",
        True,
        sql="SELECT a.id, b.id AS b_id FROM t a ASOF JOIN t b ON a.name = b.name AND a.ts >= b.ts",
        issue=805,
    ),
    target(
        AREA,
        "correlated scalar subqueries, ANY and ALL",
        "skipped",
        "replay 1,340 with EXISTS; Ibis correlated scalar subquery",
        False,
        sql="SELECT id FROM t a WHERE amount > (SELECT avg(amount) FROM t b WHERE b.name = a.name)",
        ibis="correlated scalar subquery",
        issue=813,
        why="decorrelating needs the count bug handled and at most one row proved per outer row "
        "(#504); a join with a grouped aggregate verifies today",
    ),
    target(
        AREA,
        "WITH RECURSIVE",
        "skipped",
        "catalogue dbt-org-hierarchy; dbt shop org_depth; replay 243",
        False,
        sql="WITH RECURSIVE c(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM c WHERE n < 10) "
        "SELECT n FROM c",
        issue=320,
        why="a fixpoint in the model, with termination; the shop's test on it is not provable "
        "without an acyclic hierarchy anyway",
    ),
    target(
        AREA,
        "SAMPLE and POSITIONAL JOIN",
        "skipped",
        "replay 145; Ibis sample",
        False,
        sql="SELECT * FROM t USING SAMPLE 10",
        ibis="sample",
        why="random, or row order, which a table does not have",
    ),
    target(
        AREA,
        "LIMIT by an expression or a subquery",
        "after",
        "Ibis limit expression, limit count(); replay 39",
        False,
        ibis="limit count()",
        issue=503,
    ),
    target(
        AREA,
        "scalar subquery of many rows, with the error reported",
        "after",
        "Ibis scalar subquery, many rows",
        False,
        ibis="scalar subquery, many rows",
        issue=504,
    ),
    target(
        AREA,
        "row values: (a, b) IN (SELECT …), row comparisons",
        "after",
        "replay ~110",
        False,
        sql="SELECT id FROM t WHERE (name, qty) IN (SELECT name, 1 FROM u)",
        issue=349,
        why="a semi join on the columns verifies today",
    ),
]
