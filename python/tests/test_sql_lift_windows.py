"""Window functions in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`): oracles A and C, and the refusals."""

import json

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
    # Computed window partitions.
    "SELECT id, rank() OVER (PARTITION BY amount % 2 ORDER BY -amount, id) AS r FROM orders",
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
