"""Window functions in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`): oracles A and C, and the refusals."""

import json

import ibis
import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    # A double's negation in a plan with decimals is written back as it reads
    # (TPC-DS q89's `-(sum_sales - avg_monthly_sales)`).
    "SELECT customer, s, -(s - avg(s) OVER ()) AS x"
    " FROM (SELECT customer, sum(cost) AS s FROM orders GROUP BY customer)",
    # DuckDB's AVG of a DECIMAL is a DOUBLE: the exact sum by the count, over
    # a window too, and arithmetic with it is in doubles (TPC-DS q89).
    "SELECT customer, avg(cost) OVER (PARTITION BY customer) AS a FROM orders",
    "SELECT id, cost - avg(cost) OVER (PARTITION BY customer) AS dev FROM orders",
    # Window functions; ties only where the function is the same on them.
    "SELECT id, row_number() OVER (PARTITION BY customer ORDER BY id) AS rn,"
    " rank() OVER (ORDER BY customer) AS r, dense_rank() OVER (ORDER BY customer) AS d"
    " FROM orders",
    "SELECT id, lag(amount) OVER (ORDER BY id) AS p, lead(amount, 2, -1) OVER (ORDER BY id DESC)"
    " AS n, first_value(amount) OVER (PARTITION BY customer ORDER BY id) AS f FROM orders",
    "SELECT id, sum(amount) OVER (PARTITION BY customer) AS s, avg(price) OVER () AS a,"
    " sum(amount) OVER (ORDER BY id) AS run,"
    " max(amount) OVER (ORDER BY id ROWS BETWEEN 1 PRECEDING AND 1 FOLLOWING) AS m FROM orders",
    "SELECT id, ntile(2) OVER (ORDER BY id) AS nt, percent_rank() OVER (ORDER BY id) AS pr,"
    " cume_dist() OVER (ORDER BY id) AS cd, lag(amount * 2) OVER (ORDER BY id) AS l2 FROM orders",
    "SELECT customer, sum(amount) AS s, rank() OVER (ORDER BY sum(amount) DESC) AS r,"
    " avg(sum(amount)) OVER () AS a FROM orders GROUP BY customer",
    # A plain ranking ignores the frame, empty or not (#625).
    "SELECT id, rank() OVER (ORDER BY customer ROWS BETWEEN 1 PRECEDING AND 2 PRECEDING) AS r,"
    " cume_dist() OVER (ORDER BY customer ROWS BETWEEN 3 FOLLOWING AND 1 FOLLOWING) AS c"
    " FROM orders",
    # Computed window partitions.
    "SELECT id, rank() OVER (PARTITION BY amount % 2 ORDER BY -amount, id) AS r FROM orders",
    # #811: IGNORE NULLS (last observation carried forward), and RANGE frames
    # with INTERVAL offsets over timestamps and dates.
    "SELECT id, last_value(qty IGNORE NULLS) OVER (ORDER BY id"
    " ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) AS locf,"
    " first_value(price IGNORE NULLS) OVER (ORDER BY id"
    " ROWS BETWEEN CURRENT ROW AND UNBOUNDED FOLLOWING) AS nxt,"
    " last_value(customer RESPECT NULLS) OVER (ORDER BY id) AS lv FROM orders",
    "SELECT id, sum(amount) OVER (ORDER BY placed"
    " RANGE BETWEEN INTERVAL 7 DAY PRECEDING AND CURRENT ROW) AS wk,"
    " count(*) OVER (ORDER BY day RANGE BETWEEN INTERVAL 31 DAYS PRECEDING"
    " AND INTERVAL '1' DAY FOLLOWING) AS n,"
    " max(id) OVER (ORDER BY placed RANGE BETWEEN INTERVAL '36 hours' PRECEDING"
    " AND INTERVAL 1 HOUR FOLLOWING) AS m FROM orders",
    "SELECT id, first(qty) OVER (ORDER BY id DESC) AS f, bool_or(qty > 3) OVER (ORDER BY id) AS b"
    " FROM orders",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "reference").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT sum(id) OVER w FROM orders WINDOW w AS (ORDER BY id)", "WINDOW"),
        ("SELECT count(DISTINCT id) OVER () FROM orders", "DISTINCT in a window"),
        ("SELECT sum(id) OVER (ORDER BY id GROUPS 1 PRECEDING) FROM orders", "GROUPS frames"),
        (
            "SELECT sum(id) OVER (ORDER BY placed RANGE INTERVAL 1 MONTH PRECEDING) FROM orders",
            "months and years",
        ),
        (
            "SELECT sum(id) OVER (ORDER BY day RANGE INTERVAL 1 HOUR PRECEDING) FROM orders",
            "whole days",
        ),
        (
            "SELECT sum(id) OVER (ORDER BY id ROWS INTERVAL 1 DAY PRECEDING) FROM orders",
            "RANGE frame",
        ),
        ("SELECT lag(qty IGNORE NULLS) OVER (ORDER BY id) FROM orders", "not supported"),
        # A ranking with its own ORDER BY ranks within the frame (#625).
        *(
            (
                f"SELECT id, {f}(ORDER BY id) OVER (ORDER BY customer {frame}) FROM orders",
                "its own ORDER BY",
            )
            for f in ("rank", "percent_rank", "cume_dist", "row_number", "dense_rank")
            for frame in (
                "ROWS BETWEEN 3 FOLLOWING AND 1 FOLLOWING",
                "ROWS BETWEEN 1 PRECEDING AND 2 PRECEDING",
                "",
            )
        ),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


@pytest.mark.parametrize(
    "query",
    [
        # `avg` of integers: the exact sum by the count, in doubles.
        "SELECT id, avg(amount) OVER (PARTITION BY customer) AS a FROM orders",
    ],
)
def test_the_generated_lift_is_duckdbs_with_nan_and_infinities(query):
    # With DuckDB's semantics, these come from Lean's generated lift table
    # (#268), which states NaN and ±inf exactly instead of refusing them.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_range_frame_bounds_overflow_as_in_duckdb():
    """DuckDB computes a RANGE frame's bounds in its integer key's type and
    raises where one leaves it (`sql_export/range_frames.test`); the plan
    raises there too, and agrees elsewhere."""
    import pyarrow as pa

    from sverify.engine import connect, put_table, run_plan, written_plan
    from sverify_dev.lift import check

    sql = "SELECT sum(x) OVER (ORDER BY x RANGE BETWEEN 1 PRECEDING AND 1 FOLLOWING) AS s FROM t"
    schema = {"t": ibis.schema({"x": "int32"})}
    ok = pa.table({"x": pa.array([1, 2, None, 5], pa.int32())})
    result = check(sql, {"t": ok})
    assert result.ok, f"{result.stage}: {result.detail}"
    con = connect()
    put_table(con, "t", pa.table({"x": pa.array([2147483647, 2147483646], pa.int32())}))
    plan = json.dumps(lift(sql, schema).plan)
    with pytest.raises(Exception, match="Overflow"):
        run_plan(con, written_plan(plan), "duckdb")


def test_range_frame_bound_guard_is_written_for_spark():
    """The guard on a RANGE frame's integer bounds (`sverify_raise`) is
    written wherever the dialect raises: DuckDB and Spark. Snowflake refuses
    it, with why (`_support._REASONS`)."""
    from sverify.engine import written_plan
    from sverify.sql import Unsupported, dialect_of, to_sql

    sql = "SELECT x, sum(x) OVER (ORDER BY x RANGE BETWEEN 1 PRECEDING AND 1 FOLLOWING) AS s FROM t"
    plan = json.loads(written_plan(json.dumps(lift(sql, {"t": ibis.schema({"x": "int32"})}).plan)))
    for name, fails in (("duckdb", "error("), ("spark", "raise_error(")):
        written = to_sql(plan, dialect_of(name), deterministic=True)
        assert fails in written and "RANGE frame bound" in written, name
    with pytest.raises(Unsupported, match="grows past what it runs"):
        to_sql(plan, dialect_of("snowflake"), deterministic=True)
