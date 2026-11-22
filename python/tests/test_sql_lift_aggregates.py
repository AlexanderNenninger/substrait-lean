"""Aggregates and GROUPING SETS in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`): oracles A and C, and the refusals."""

import json

import ibis
import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify import Verdict
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
    # The variance family (#433), of integers and doubles; each engine's own
    # algorithm, with the reference's generic properties.
    "SELECT customer, stddev_samp(amount) AS sd, stddev_pop(price) AS sp, var_samp(qty) AS vs,"
    " var_pop(amount) AS vp, stddev(price) AS s, variance(amount) AS v"
    " FROM orders GROUP BY customer",
    "SELECT covar_samp(amount, price) AS cs, covar_pop(qty, amount) AS cp, corr(price, qty) AS r"
    " FROM orders",
    # DuckDB's CORR is NaN for one pair or a constant side, where the
    # reference's is NULL (`duckdb-corr`); of no pairs it is NULL.
    "SELECT customer, corr(price, qty) AS r, corr(amount, 2) AS k,"
    " corr(price, amount) FILTER (WHERE id > 2) AS f FROM orders GROUP BY customer",
    # H2O's groupby q9.
    "SELECT customer, qty, power(corr(price, amount), 2) AS r2 FROM orders GROUP BY customer, qty",
    "SELECT covar_pop(price, amount) FILTER (WHERE id > 2) AS c FROM orders",
    "SELECT customer, qty, stddev_samp(amount) AS sd, count(*) AS n FROM orders"
    " GROUP BY ROLLUP (customer, qty)",
    # Exact quantiles, the mode and arg_min/arg_max (#53). DuckDB's median of
    # strings is the 0.5 quantile_disc, and `quantile` is `quantile_disc`; its
    # median of a date or timestamp interpolates and is refused (#2153).
    "SELECT customer, median(amount) AS m, median(price) AS mp, quantile_cont(qty, 0.25) AS q"
    " FROM orders GROUP BY customer",
    "SELECT quantile_disc(amount, 0.5) AS d, quantile_disc(customer, 0.75) AS s,"
    " quantile(day, 0.3) AS dd, median(customer) AS mc, quantile_cont(price, 1) AS top FROM orders",
    "SELECT customer, mode(qty ORDER BY qty) AS m, mode(customer ORDER BY customer DESC) AS c"
    " FROM orders GROUP BY customer",
    "SELECT customer, arg_min(id, price) AS a, arg_max(day, amount) AS b FROM orders"
    " GROUP BY customer",
    "SELECT median(price) FILTER (WHERE id > 1) AS m, quantile_cont(DISTINCT amount, 0.9) AS q"
    " FROM orders",
    # #810: string_agg skips NULLs; list, first and last keep them, as DuckDB
    # does; bool_and and bool_or are min and max of booleans.
    "SELECT customer, string_agg(customer, '-' ORDER BY id) AS s, list(qty ORDER BY id) AS l,"
    " bool_and(amount > 2) AS ba, bool_or(qty > 3) AS bo FROM orders GROUP BY customer",
    # `arbitrary` is DuckDB's other name of `first` (#328).
    "SELECT id, arbitrary(customer) AS a FROM orders GROUP BY id",
    "SELECT first(qty ORDER BY id) AS f, last(qty ORDER BY id DESC) AS l,"
    " first(price ORDER BY placed) AS fp, last(customer ORDER BY day) AS lc,"
    " list(customer ORDER BY id) AS lst, array_agg(qty ORDER BY amount DESC) AS aa,"
    " string_agg(customer ORDER BY id) AS sa FROM orders",
    "SELECT customer, first(id ORDER BY amount) FILTER (WHERE qty IS NOT NULL) AS f,"
    " last(day ORDER BY id) AS d FROM orders GROUP BY customer",
    "SELECT list(customer ORDER BY id) FILTER (WHERE id > 1) AS l, first(qty ORDER BY id) AS f,"
    " bool_or(qty > 3) AS b FROM orders WHERE id > 10",
    # `any_value`: a non-NULL value of the group (#319), here the only one.
    "SELECT customer, any_value(customer) AS a, any_value(qty) FILTER (WHERE id < 0) AS n"
    " FROM orders GROUP BY customer",
    "SELECT any_value(id) AS a FROM orders WHERE id = 1",
    # It skips NULLs, in the ORDER BY's order (unique ids).
    "SELECT customer, any_value(qty ORDER BY id) AS f, any_value(qty ORDER BY id DESC) AS l"
    " FROM orders GROUP BY customer",
    "SELECT any_value(price ORDER BY placed) AS p, any_value(customer ORDER BY id) AS c"
    " FROM orders",
    # A key that is the alias of a constant: `qualify` writes its position
    # (`GROUPING SETS ((1), ())`), which is the select list's first column.
    "SELECT count(k) AS c, sum(k) AS s FROM (SELECT 7 AS k FROM orders"
    " GROUP BY GROUPING SETS ((k), ())) s",
    "SELECT 7 AS k, customer, count(*) AS n FROM orders GROUP BY ROLLUP (k, customer)",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "portable").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


def test_median_of_a_float_is_refused_as_it_interpolates():
    schemas = {"t": ibis.schema({"f": "float32", "g": "float64"})}
    with pytest.raises(Refused, match="DuckDB interpolates it"):
        lift("SELECT median(f) FROM t", schemas)
    lift("SELECT median(g) FROM t", schemas)


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
        ("SELECT stddev_samp(cost) FROM orders", "of a DECIMAL is not supported"),
        ("SELECT var_pop(customer) FROM orders", "variance of"),
        ("SELECT corr(customer, amount) FROM orders", "corr of"),
        (
            "SELECT covar_pop(amount, qty) OVER (PARTITION BY customer) FROM orders",
            "over a window is not supported",
        ),
        ("SELECT mode(qty) FROM orders", "breaks ties in the engine's order"),
        ("SELECT median(cost) FROM orders", "no engine gives one value for it"),
        # DuckDB interpolates it (2024-01-05 12:00:00), the lower middle is another value (#2153).
        ("SELECT median(day) FROM orders", "DuckDB interpolates it"),
        ("SELECT median(placed) FROM orders", "DuckDB interpolates it"),
        ("SELECT quantile_cont(amount, -0.5) FROM orders", "between 0 and 1"),
        ("SELECT quantile_cont(amount, [0.25, 0.5]) FROM orders", "one number"),
        ("SELECT arg_min(id, amount + 1) FROM orders", "orders by a column only"),
        ("SELECT arg_max(id, amount, 2) FROM orders", "n best"),
        ("SELECT median(amount) OVER (PARTITION BY customer) FROM orders", "over a window"),
        ("SELECT string_agg(amount, ',') FROM orders", "cast it to VARCHAR"),
        ("SELECT string_agg(customer, customer) FROM orders", "constant separator"),
        ("SELECT bool_and(amount) FROM orders", "not supported"),
        ("SELECT list(cost ORDER BY id) FROM orders", "DECIMAL"),
        ("SELECT first(qty ORDER BY amount + 1) FROM orders", "ORDER BY a column only"),
        ("SELECT any_value(DISTINCT id) FROM orders", "DISTINCT"),
        ("SELECT arg_min_null(id, qty) FROM orders", r"arg_min_null\(\) is not supported yet"),
        ("SELECT bitstring_agg(id) FROM orders", "BIT string"),
        ("SELECT histogram_exact(id, [1, 2]) FROM orders", "MAP"),
        ("SELECT list(qty) OVER (ORDER BY id) FROM orders", "over a window"),
        # SQLGlot reads EXPORT_STATE as an alias (upstream/bugs/SG-9.json).
        ("SELECT first(qty ORDER BY id) EXPORT_STATE FROM orders", "EXPORT_STATE"),
        ("SELECT sum(qty) export_state FROM orders", "EXPORT_STATE"),
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
    con._arrow["t"] = pa.table({"f": [1.0, 2.0, 4.0], "g": [2.5, 2.5, 2.5]})
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


def test_stddev_samp_of_an_integer_is_proved_as_ibiss():
    # The issue's repro: what Ibis's `t.duration_s.std()` proves, the SQL
    # lift proves too (#433).
    import ibis

    import sverify as sv

    jobs = ibis.table({"workflow": "!string", "duration_s": "int64"}, name="jobs")
    query = "SELECT workflow, stddev_samp(duration_s) AS sd FROM jobs GROUP BY workflow"
    report = sv.verify(query, tables={"jobs": jobs})
    assert str(report.facts["sd"]) == "a double ≥ 0.0 or NULL", report
    ibis_report = sv.verify(jobs.group_by("workflow").aggregate(sd=jobs.duration_s.std()))
    assert report.facts == ibis_report.facts
    plan = lift(query, {"jobs": jobs.schema()}).plan
    measure = plan["relations"][0]["root"]["input"]["aggregate"]["measures"][0]["measure"]
    assert measure["options"] == [{"name": "distribution", "preference": ["SAMPLE"]}]


def test_corr_of_one_pair_is_nan_with_duckdbs_semantics_and_null_with_the_reference():
    # `duckdb-corr`: DuckDB's CORR of one pair is NaN, the reference's NULL.
    import math

    from sverify.testing import lean_values
    from sverify_dev import slt

    query = "SELECT corr(price, qty) AS r FROM orders WHERE id = 1"
    rows = {n: [tuple(r.values()) for r in t.to_pylist()] for n, t in TABLES.items()}

    def lean(semantics):
        plan = lift(query, SCHEMAS, semantics).plan
        return lean_values(json.dumps(slt._typed_inline(plan, rows, None)))

    ((r,),) = lean("duckdb")
    assert math.isnan(r)
    assert lean("portable") == [(None,)]


# `SUM` and `AVG` of doubles with infinities and NaN (#341), through oracles A and C.
_NONFINITE = [
    "SELECT sum(x) AS s, avg(x) AS a FROM (SELECT 'inf'::DOUBLE AS x UNION ALL"
    " SELECT '-inf'::DOUBLE UNION ALL SELECT 1.0) t",
    "SELECT sum(x) AS s, avg(x) AS a FROM (SELECT 'inf'::DOUBLE AS x UNION ALL SELECT 1.0"
    " UNION ALL SELECT 2.5) t",
    "SELECT sum(x) AS s, avg(x) AS a FROM (SELECT '-inf'::DOUBLE AS x UNION ALL SELECT 1.0"
    " UNION ALL SELECT NULL::DOUBLE) t",
    "SELECT sum(x) AS s, avg(x) AS a FROM (SELECT 'nan'::DOUBLE AS x UNION ALL"
    " SELECT 'inf'::DOUBLE) t",
    "SELECT sum(x) AS s, avg(x) AS a FROM (VALUES (1.5), (NULL), (2.0)) t(x)",
    "SELECT sum(x) AS s, avg(x) AS a FROM (VALUES (1.5), (2.0)) t(x) WHERE x > 10",
]


@pytest.mark.parametrize("query", _NONFINITE)
def test_sum_and_avg_of_doubles_with_infinities_agree_with_duckdb(query):
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_sum_of_both_infinities_is_no_domain_error_under_duckdbs_semantics():
    import ibis

    import sverify as sv

    t = ibis.table({"f": "float64"}, name="f")
    for fn in ("sum", "avg"):
        query = f"SELECT {fn}(f) AS v FROM f"
        duck = sv.verify(sv.sql(query, f=t, semantics="duckdb"))
        ref = sv.verify(sv.sql(query, f=t, semantics="portable"))
        assert not [i for i in duck.issues if "domain error" in str(i)], (fn, duck)
        assert [i for i in ref.issues if "domain error" in str(i)], (fn, ref)


def test_sum_of_an_expression_keeps_its_overflow_check_under_duckdbs_semantics():
    """The guarded sum's argument is the expression itself (`SUM(f + 1.0)`), not only a column.
    An unbounded column no longer gives `PROVED` with no issues: DuckDB's running
    sum overflows where the exact sum, which the model gives, does not (ruling
    200 A4(2)); the check is assumed, and the run makes it."""
    import ibis

    import sverify as sv

    t = ibis.table({"f": "float64"}, name="f")
    report = sv.verify(sv.sql("SELECT sum(f + 1.0) AS v FROM f", f=t, semantics="duckdb"))
    assert report.verdict == Verdict.PROVED_WITH_CHECKS, report


@pytest.mark.parametrize(
    ("fn", "values"),
    [("avg", [1e308, 1e308]), ("sum", [1e308, 1e308, -1e308])],
)
def test_a_double_sum_that_overflows_is_refused_under_duckdbs_semantics(fn, values):
    """DuckDB's `avg(1e308, 1e308)` is `inf` where the model gives `1e308`: the run
    refuses the batch instead of returning DuckDB's value (ruling 200 A4(2), R3)."""
    import ibis

    import sverify as sv
    from sverify import connect
    from sverify.conditions import PreconditionError

    t = ibis.table({"f": "float64"}, name="f")
    report = sv.verify(sv.sql(f"SELECT {fn}(f) AS v FROM f", f=t, semantics="duckdb"))
    con = connect()
    con.create("f", t.schema(), [(v,) for v in values])
    with pytest.raises(PreconditionError, match="overflows"):
        report.run(con)


@pytest.mark.parametrize("fn", ["sum", "avg"])
def test_a_double_sum_checks_for_a_nan_total_with_no_nan_input(fn):
    """Finite inputs whose partial sums overflow in both directions give NaN: no
    input is infinite, so the `±∞` test passes. The written SQL tests the total for
    NaN where no input is NaN (ruling 200 A4(3))."""
    import ibis

    import sverify as sv
    from sverify.sql import to_sql

    t = ibis.table({"f": "float64"}, name="f")
    plan = sv.verify(sv.sql(f"SELECT {fn}(f) AS v FROM f", f=t, semantics="portable"))
    assert plan.internal_plan is not None
    written = to_sql(plan.internal_plan, "duckdb")
    assert "isnan" in written.lower() and "overflow to infinity" in written, written


def test_the_lift_table_states_the_plain_sum_for_the_reference_and_three_measures_for_duckdb():
    import subprocess

    from sverify._checker import checker_path

    out = subprocess.run(
        [str(checker_path()), "--lift-table"], capture_output=True, text=True, check=True
    ).stdout
    aggregates = {
        (e["semantics"], e["construct"]): e["aggregate"] for e in json.loads(out)["aggregates"]
    }
    assert len(aggregates[("reference", "sum(DOUBLE)")]["measures"]) == 1
    assert len(aggregates[("duckdb", "sum(DOUBLE)")]["measures"]) == 3


def test_quantile_disc_of_a_decimal_beyond_2_pow_53_selects_exactly():
    """`quantile_disc` of a DECIMAL whose unscaled value exceeds 2^53 is an
    exact selection from the group (#1921)."""
    from decimal import Decimal

    import pyarrow as pa

    from _pipelines import arrow_table

    rows = [(Decimal("9007199254740993.01"),), (Decimal("9007199254740993.03"),), (None,)]
    tables = {"t": arrow_table(pa.schema([pa.field("d", pa.decimal128(20, 2))]), rows)}
    result = check("SELECT quantile_disc(d, 0.5) AS q, quantile_disc(d, 1) AS top FROM t", tables)
    assert result.ok, f"{result.stage}: {result.detail}"
