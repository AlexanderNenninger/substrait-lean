"""The strings a column can hold (#708), and keys through `UNION ALL` (#436).

Lean's description of a string column (`AVal.strs`) lists its strings while
they are few: constants, `IN` lists and `=` filters narrow it, `<>` and
`NOT IN` take strings out, and `CASE`, `COALESCE`, joins, grouping and
`UNION ALL` carry it through. dbt's `accepted_values` maps to
`c IS NULL OR c IN (...)`, which these prove. The four shop cases are the
tests of sverify-dbt's example project they unlock.
"""

import ibis
import pytest

import sverify as sv

T = {"t": {"s": "VARCHAR", "k": "BIGINT"}}


def _proved(sql, requires, ensures, tables=T, semantics="duckdb"):
    report = sv.verify(sql, tables=tables, semantics=semantics, requires=requires, ensures=ensures)
    return [c.proved for c in report.ensures]


@pytest.mark.parametrize(
    ("sql", "requires", "ensures"),
    [
        ("SELECT 'a' AS s FROM t", [], "s = 'a'"),
        ("SELECT s FROM t WHERE s <> 'c'", ["s IN ('a', 'b', 'c')"], "s IN ('a', 'b')"),
        ("SELECT s FROM t", ["s IN ('a', 'b')"], "s IS NULL OR s IN ('a', 'b')"),
        ("SELECT s FROM t", ["s IN ('a', 'b')"], "s IN ('b', 'a')"),
        (
            "SELECT s FROM t WHERE s NOT IN ('a', 'b')",
            ["s IN ('a', 'b', 'c', 'd')"],
            "s IN ('c', 'd')",
        ),
        ("SELECT s FROM t WHERE s = 'x'", [], "s = 'x'"),
        ("SELECT s FROM t WHERE s IN ('x', 'y')", [], "s <> 'z'"),
        (
            "SELECT CASE WHEN k > 0 THEN 'up' ELSE 'down' END AS s FROM t",
            [],
            "s IN ('up', 'down')",
        ),
        ("SELECT coalesce(s, 'none') AS s FROM t", ["s IN ('a', 'b')"], "s IN ('a', 'b', 'none')"),
        (
            "SELECT s, count(*) AS n FROM t GROUP BY s",
            ["s IS NULL OR s IN ('a', 'b')"],
            "s IS NULL OR s IN ('a', 'b')",
        ),
        (
            "SELECT x.s, y.s AS s2 FROM t x JOIN t y ON x.k = y.k",
            ["s IN ('a', 'b')"],
            "s2 IN ('a', 'b')",
        ),
    ],
)
def test_a_strings_values_are_proved(sql, requires, ensures):
    assert _proved(sql, {"t": requires}, [ensures]) == [True]


@pytest.mark.parametrize(
    ("sql", "requires", "ensures"),
    [
        # Nothing is known of `s`.
        ("SELECT s FROM t", [], "s IN ('a', 'b')"),
        # `<> 'c'` leaves `a` and `b`, and `b` is not allowed.
        ("SELECT s FROM t WHERE s <> 'c'", ["s IN ('a', 'b', 'c')"], "s = 'a'"),
        # NULL passes the precondition and the filter.
        ("SELECT s FROM t", ["s IS NULL OR s IN ('a', 'b')"], "s IN ('a', 'b')"),
        # Either branch of the CASE.
        ("SELECT CASE WHEN k > 0 THEN 'up' ELSE 'down' END AS s FROM t", [], "s = 'up'"),
        # `s` may be NULL, so `coalesce` may give `none`.
        ("SELECT coalesce(s, 'none') AS s FROM t", ["s IS NULL OR s = 'a'"], "s = 'a'"),
    ],
)
def test_a_string_outside_its_values_is_not_proved(sql, requires, ensures):
    assert _proved(sql, {"t": requires}, [ensures]) == [False]


def test_many_strings_fall_back_to_any_string():
    # Past 64 strings Lean forgets them: no proof, and no error.
    values = ", ".join(f"'v{i}'" for i in range(70))
    assert _proved("SELECT s FROM t", {"t": [f"s IN ({values})"]}, ["s <> 'w'"]) == [False]
    few = ", ".join(f"'v{i}'" for i in range(60))
    assert _proved("SELECT s FROM t", {"t": [f"s IN ({few})"]}, ["s <> 'w'"]) == [True]


def test_the_report_names_the_strings():
    report = sv.verify(
        "SELECT s FROM t WHERE s <> 'c'",
        tables=T,
        semantics="duckdb",
        requires={"t": ["s IS NULL OR s IN ('a', 'b', 'c')"]},
    )
    assert report.facts["s"] == "one of the strings 'a', 'b' or NULL"


# The shop project of sverify-dbt (examples/shop): its models, and the
# conditions sverify-dbt maps their tests and their sources' tests to.

ORDERS = {
    "order_id": "BIGINT",
    "customer_id": "BIGINT",
    "order_ts": "TIMESTAMP",
    "status": "VARCHAR",
    "amount": "DOUBLE",
}


def test_shop_stg_orders_accepted_values():
    report = sv.verify(
        "SELECT order_id, customer_id, order_ts, status, amount FROM orders "
        "WHERE status <> 'cancelled'",
        tables={"orders": ORDERS},
        semantics="duckdb",
        requires={
            "orders": ["status IS NULL OR status IN ('placed', 'shipped', 'returned', 'cancelled')"]
        },
        ensures=["status IS NULL OR status IN ('placed', 'shipped', 'returned')"],
    )
    assert report.proved, str(report)


def test_shop_events_unioned_accepted_values():
    report = sv.verify(
        "SELECT user_id, event_ts AS ts, event_name AS name, "
        "CAST(NULL AS DOUBLE) AS amount, 'events' AS source FROM events "
        "UNION ALL "
        "SELECT customer_id AS user_id, order_ts AS ts, 'order' AS name, amount, "
        "'orders' AS source FROM stg_orders",
        tables={
            "events": {"user_id": "BIGINT", "event_ts": "TIMESTAMP", "event_name": "VARCHAR"},
            "stg_orders": ORDERS,
        },
        semantics="duckdb",
        ensures=["source IS NULL OR source IN ('events', 'orders')", "source IS NOT NULL"],
    )
    assert report.proved, str(report)


SALES_BY_QUARTER = " UNION ALL ".join(
    f"SELECT region, 'q{i}' AS quarter, q{i} AS sales FROM sales_wide" for i in range(1, 5)
)
SALES_WIDE = {
    "sales_wide": {
        "region": "VARCHAR",
        "q1": "BIGINT",
        "q2": "BIGINT",
        "q3": "BIGINT",
        "q4": "BIGINT",
    }
}


def test_shop_sales_by_quarter_accepted_values():
    report = sv.verify(
        SALES_BY_QUARTER,
        tables=SALES_WIDE,
        semantics="duckdb",
        ensures=["quarter IS NULL OR quarter IN ('q1', 'q2', 'q3', 'q4')"],
    )
    assert report.proved, str(report)
    assert report.facts["quarter"] == "one of the strings 'q1', 'q2', 'q3', 'q4'"


def test_shop_sales_by_quarter_unique_region_quarter():
    report = sv.verify(
        SALES_BY_QUARTER,
        tables=SALES_WIDE,
        semantics="duckdb",
        requires={"sales_wide": ["region IS NOT NULL", sv.unique("region")]},
        ensures=[sv.unique("region", "quarter")],
    )
    assert report.proved, str(report)


def test_a_union_whose_branches_share_a_tag_has_no_key():
    sql = (
        "SELECT region, 'q1' AS quarter FROM sales_wide "
        "UNION ALL SELECT region, 'q1' AS quarter FROM sales_wide"
    )
    report = sv.verify(
        sql,
        tables=SALES_WIDE,
        requires={"sales_wide": [sv.unique("region")]},
        ensures=[sv.unique("region", "quarter")],
    )
    assert not report.proved


def test_a_union_needs_a_key_of_each_branch():
    sql = (
        "SELECT region, 'q1' AS quarter FROM sales_wide "
        "UNION ALL SELECT region, 'q2' AS quarter FROM sales_wide"
    )
    report = sv.verify(sql, tables=SALES_WIDE, ensures=[sv.unique("region", "quarter")])
    assert not report.proved


def test_a_rollup_written_as_a_union_keeps_its_keys():
    # #436: each branch is unique on its group keys, and `level` tells them apart.
    jobs = ibis.table({"workflow": "!string", "job": "!string"}, name="jobs")
    a = jobs.group_by(["workflow", "job"]).aggregate(n=jobs.count())
    b = jobs.group_by("workflow").aggregate(n=jobs.count())
    u = a.select(level=ibis.literal(0), workflow=a.workflow, job=a.job.cast("string"), n=a.n).union(
        b.select(level=ibis.literal(1), workflow=b.workflow, job=ibis.null("string"), n=b.n)
    )
    assert sv.verify(u, ensures=[sv.unique("level", "workflow", "job")]).proved
    assert not sv.verify(u, ensures=[sv.unique("workflow")]).proved
