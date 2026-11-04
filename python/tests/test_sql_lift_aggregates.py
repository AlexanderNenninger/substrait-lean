"""Aggregates and GROUPING SETS in DuckDB SQL through sverify's own lift
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
    # DuckDB's AVG of a DECIMAL is a DOUBLE: the exact sum by the count.
    "SELECT customer, avg(cost) AS a FROM orders GROUP BY customer",
    "SELECT avg(cost) AS a FROM orders WHERE id > 100",
    "SELECT customer, count(*) AS n, sum(amount) AS total, avg(qty) AS a, min(amount) AS lo,"
    " max(day) AS last, sum(cost) AS c, count(DISTINCT qty) AS dq"
    " FROM orders GROUP BY customer HAVING count(*) >= 1 ORDER BY total DESC",
    "SELECT qty, count(*) FROM orders GROUP BY 1 ORDER BY 2 DESC, 1",
    "SELECT count(*) AS n, sum(qty) AS s FROM orders WHERE amount > 100",
    # DISTINCT and FILTER in aggregates.
    "SELECT customer, count(DISTINCT qty) AS n, sum(DISTINCT amount) AS s,"
    " sum(amount) FILTER (WHERE amount > 2) AS big, count(*) FILTER (WHERE qty IS NULL) AS nq"
    " FROM orders GROUP BY customer",
    # Grouping sets: one aggregate per set, UNION ALL'd; GROUPING() is a
    # constant of each.
    "SELECT customer, qty, sum(amount) AS s, count(*) AS n FROM orders"
    " GROUP BY ROLLUP (customer, qty)",
    "SELECT customer, qty, GROUPING(customer) AS g, GROUPING(customer, qty) AS gg, avg(price) AS p"
    " FROM orders GROUP BY CUBE (customer, qty)",
    "SELECT customer, day, count(*) AS n FROM orders"
    " GROUP BY GROUPING SETS ((customer, day), (customer), ())",
    "SELECT customer, qty, sum(amount) AS s FROM orders GROUP BY customer, ROLLUP (qty)"
    " HAVING GROUPING(qty) = 1 OR sum(amount) > 4",
    "SELECT customer, GROUPING(customer) AS g,"
    " rank() OVER (PARTITION BY GROUPING(customer) ORDER BY sum(amount)) AS r"
    " FROM orders GROUP BY ROLLUP (customer) ORDER BY g DESC, customer",
    "SELECT customer, sum(amount) AS s FROM orders WHERE id > 99 GROUP BY ROLLUP (customer)",
    # A double constant is its code in Lean; the plan's literal says double,
    # so its SUM is a double one, without the integer SUM's guard (#341).
    "SELECT SUM('inf'::DOUBLE), SUM('-inf'::DOUBLE), SUM('nan'::DOUBLE)",
    "SELECT customer, sum(2.5::DOUBLE) AS s, avg(CAST(1 AS DOUBLE)) AS a FROM orders"
    " GROUP BY customer",
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
        ("SELECT GROUPING(id) FROM orders GROUP BY ROLLUP (customer)", "GROUPING of"),
        ("SELECT id, customer FROM orders GROUP BY id", "GROUP BY"),
        # DuckDB reads `amount` in HAVING as the column, SQLGlot as the alias.
        (
            "SELECT amount + 1 AS amount FROM orders GROUP BY amount HAVING amount = 5",
            "both an input column and an output alias",
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
        "SELECT customer, avg(amount) AS a, avg(qty) AS q, avg(DISTINCT qty) AS d"
        " FROM orders GROUP BY customer",
    ],
)
def test_the_generated_lift_is_duckdbs_with_nan_and_infinities(query):
    # With DuckDB's semantics, these come from Lean's generated lift table
    # (#268), which states NaN and ±inf exactly instead of refusing them.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_duckdb_avg_of_a_nullable_integer_cannot_divide_by_zero():
    # A group whose values are all NULL counts 0: the quotient is NULL (#434).
    import ibis

    import sverify as sv

    jobs = ibis.table({"workflow": "!string", "duration_s": "int64"}, name="jobs")
    query = "SELECT workflow, avg(duration_s) AS a FROM jobs GROUP BY workflow"
    report = sv.verify(sv.sql(query, jobs=jobs, semantics="duckdb"))
    assert not [i for i in report.issues if "division by zero" in str(i)], report
    con = ibis.duckdb.connect()
    con.raw_sql(
        "CREATE TABLE jobs AS SELECT * FROM (VALUES ('a', NULL::BIGINT), ('b', 4))"
        " t(workflow, duration_s)"
    )
    rows = sv.sql(query, jobs=con.table("jobs"), semantics="duckdb").order_by("workflow")
    assert rows.to_pyarrow().to_pylist() == [
        {"workflow": "a", "a": None},
        {"workflow": "b", "a": 4.0},
    ]


def test_covariance_of_a_double_constant_is_of_that_double():
    # `Parse.parseMeasure` converts an integer side, but a double constant
    # is its code, which only the plan's literal calls a double (#341).
    import pyarrow as pa

    from sverify.engine import connect, plan_json, run_plan, written_plan
    from sverify.testing import inline_tables, lean_values

    con = connect()
    con.arrow["t"] = pa.table({"f": [1.0, 2.0, 4.0], "g": [2.5, 2.5, 2.5]})
    t = con.table("t")
    plan = json.loads(written_plan(plan_json(con, t.aggregate(c=t.f.cov(t.g, how="pop")))))
    measure = plan["relations"][0]["root"]["input"]["aggregate"]["measures"][0]["measure"]
    measure["arguments"][1]["value"] = {"literal": {"fp64": 2.5}}
    plan = json.dumps(plan)
    lean = lean_values(
        json.dumps(inline_tables(json.loads(plan), {"t": [(1.0, 2.5), (2.0, 2.5), (4.0, 2.5)]}))
    )
    assert lean == [(0.0,)]
    assert run_plan(con, plan).to_pylist() == [{"c": 0.0}]
