"""DECIMAL in the reference model (#27): a decimal is its unscaled integer.

The expected values follow the reference's rules (decided on #27, from how
DuckDB, Polars, Spark and DataFusion compute decimals): `+`, `-` and `×` are
exact; a smaller scale rounds half away from zero; to an integer truncates
toward zero; `AVG` is a `DECIMAL(p + 4, s + 4)` rounded half away from zero;
a double becomes `round(x · 10ˢ)` computed in doubles. DataFusion only writes
the plans.
"""

import json
from decimal import Decimal as D

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, put_table, run_checker, run_plan, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("datafusion")

TABLES = {
    "t": pa.table(
        {
            "a": pa.array([D("12.35"), D("-0.05"), D("-12.35"), None], pa.decimal128(10, 2)),
            "b": pa.array([D("1.5"), D("2.5"), D("-3.5"), D("3.0")], pa.decimal128(5, 1)),
            "i": pa.array([3, -7, 2, 0], pa.int64()),
            "f": pa.array([0.125, -2.675, 0.145, 2.5], pa.float64()),
        }
    ),
    "g": pa.table(
        {
            "k": pa.array([1, 1, 1, 2, 2, 3], pa.int64()),
            "x": pa.array(
                [D("0.01"), D("0.01"), D("0.00"), D("-0.05"), None, None], pa.decimal128(10, 2)
            ),
        }
    ),
}
ROWS = {name: [tuple(r.values()) for r in t.to_pylist()] for name, t in TABLES.items()}
SCHEMAS = {
    "t": {"a": "decimal(10,2)", "b": "decimal(5,1)", "i": "int64", "f": "float64"},
    "g": {"k": "int64", "x": "decimal(10,2)"},
}


#: The tables in Ibis, for what the SQL lift does not read: `avg` of a
#: decimal (DuckDB's is a double; the model's a decimal at scale + 4) and
#: casts that round in DuckDB but truncate in the reference.
T = ibis.table(SCHEMAS["t"], name="t")
G = ibis.table(SCHEMAS["g"], name="g")


@pytest.fixture(scope="module")
def con():
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    return c


def lean(con, query: str | ibis.Table) -> list[tuple]:
    """`Rel.eval`'s rows, decimals as `Decimal`s printed at their scale."""
    plan = json.loads(
        substrait_json(con, query) if isinstance(query, str) else to_substrait_json(query)
    )
    rows = lean_values(json.dumps(inline_tables(plan, ROWS)))
    return [tuple(str(v) if isinstance(v, D) else v for v in r) for r in rows]


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # Exact, at the larger scale (`+`, `-`) and the sum of the scales (`×`).
        ("SELECT a + b AS r FROM t", ["13.85", "2.45", "-15.85", None]),
        ("SELECT a - b AS r FROM t", ["10.85", "-2.55", "-8.85", None]),
        ("SELECT a * b AS r FROM t", ["18.525", "-0.125", "43.225", None]),
        ("SELECT a * i AS r FROM t", ["37.05", "0.35", "-24.70", None]),
        ("SELECT -a AS r FROM t", ["-12.35", "0.05", "12.35", None]),
        (T.select(r=T.a.abs()), ["12.35", "0.05", "12.35", None]),
        # Compared at one scale.
        ("SELECT a > b AS r FROM t", [True, False, False, None]),
        ("SELECT a = CAST('12.35' AS DECIMAL(10,2)) AS r FROM t", [True, False, False, None]),
        # A smaller scale rounds half away from zero; an integer truncates.
        (T.select(r=T.a.cast("decimal(10, 1)")), ["12.4", "-0.1", "-12.4", None]),
        (T.select(r=T.a.cast("int64")), [12, 0, -12, None]),
        ("SELECT CAST(i AS DECIMAL(10,2)) AS r FROM t", ["3.00", "-7.00", "2.00", "0.00"]),
        ("SELECT CAST(a AS DOUBLE) AS r FROM t", [12.35, -0.05, -12.35, None]),
        # `round(x · 10ˢ)` in doubles: -2.675 · 100 is -267.5 there, 0.145 · 100
        # just below 14.5.
        ("SELECT CAST(f AS DECIMAL(10,2)) AS r FROM t", ["0.13", "-2.68", "0.14", "2.50"]),
    ],
)
def test_values(con, sql, expected):
    assert [r[0] for r in lean(con, sql)] == expected


def test_sum_min_max(con):
    assert lean(con, "SELECT sum(a) AS s, min(a) AS lo, max(b) AS hi FROM t") == [
        ("-0.05", "-12.35", "3.0")
    ]


def test_avg_rounds_half_away_from_zero(con):
    """`DECIMAL(10, 2)` averages are `DECIMAL(14, 6)`: 0.02 / 3 is 0.006667."""
    by_k = G.group_by("k").aggregate(v=G.x.mean(), s=G.x.sum(), n=G.x.count()).order_by("k")
    assert lean(con, by_k) == [
        (1, "0.006667", "0.02", 3),
        (2, "-0.050000", "-0.05", 1),
        (3, None, None, 0),
    ]
    assert lean(con, G.aggregate(v=G.x.mean())) == [("-0.007500",)]


def test_duckdb_sql_averages_a_decimal_as_a_double(con):
    """DuckDB types the `AVG` of a DECIMAL as a DOUBLE: the exact sum, as a
    double, by the count; NULL without values."""
    sql = "SELECT k, avg(x) AS v, sum(x) AS s, count(x) AS n FROM g GROUP BY k ORDER BY k"
    assert lean(con, sql) == [
        (1, 0.006667, "0.02", 3),
        (2, -0.05, "-0.05", 1),
        (3, None, None, 0),
    ]
    assert lean(con, "SELECT avg(x) AS v FROM g") == [(-0.0075,)]


def test_avg_over_a_window(con):
    """Over a window too: the frame's `SUM` by its `COUNT`, at scale 6."""
    windowed = G.select("k", v=G.x.mean().over(group_by="k")).order_by("k")
    assert lean(con, windowed) == [
        (1, "0.006667"),
        (1, "0.006667"),
        (1, "0.006667"),
        (2, "-0.050000"),
        (2, "-0.050000"),
        (3, None),
    ]


@pytest.mark.parametrize(
    ("sql", "errors"),
    [
        # A column holds at most its precision's digits, so these fit.
        ("SELECT a + b AS r FROM t", []),
        ("SELECT CAST(a AS DECIMAL(20,4)) AS r FROM t", []),
        (T.select(r=T.a.cast("int64")), []),
        (G.group_by("k").aggregate(v=G.x.mean()), []),
        # These may not. DuckDB types a product of two decimals of up to 18
        # digits as DECIMAL(18, s), and raises past 18 digits.
        ("SELECT a * b * a AS r FROM t", ["overflow"]),
        ("SELECT CAST(a AS DECIMAL(4,2)) AS r FROM t", ["overflow"]),
        ("SELECT CAST(f AS DECIMAL(10,2)) AS r FROM t", ["cast out of range", "overflow"]),
    ],
)
def test_verify_reports_overflow_where_it_can_happen(sql, errors):
    report = sv.verify(sql, tables=SCHEMAS) if isinstance(sql, str) else sv.verify(sql)
    assert [i.kind for i in report.errors] == errors


def test_decimal_sum_does_not_wrap():
    """Engines add decimals in 128 bits, unlike `BIGINT`s."""
    report = sv.verify("SELECT sum(a) AS s FROM t", tables=SCHEMAS)
    assert report.errors == [] and report.warnings == []


def test_decimal_plans_are_written_but_not_for_datafusion(con):
    """Stage 2: decimal plans are written back as typed calls and casts for
    the engines; DataFusion does not compute decimals as the reference does."""
    plan = substrait_json(con, "SELECT a + b AS r FROM t")
    code, out, _ = run_checker(("--write",), plan)
    assert code == 0 and "decimal" in out
    code, _, err = run_checker(("--write-datafusion",), plan)
    assert code == 1 and "#27" in err


def test_abs_of_a_double_next_to_decimals_is_written(con):
    """A plan with decimals is written only if it reads back the same; `ABS`
    and negation of a double are written as `abs` and `negate` (q89)."""
    t = ibis.table(SCHEMAS["t"], name="t")
    expr = t.select(s=t.a + t.a, g=(t.f - 1.0).abs(), n=-(t.f - 1.0))
    written = written_plan(to_substrait_json(expr))
    got = [tuple(r.values()) for r in run_plan(con, written, "duckdb").to_pylist()]
    fs = [r[3] for r in ROWS["t"]]
    assert sorted(g for _, g, _ in got) == sorted(abs(f - 1.0) for f in fs)
    assert sorted(n for _, _, n in got) == sorted(-(f - 1.0) for f in fs)


def test_a_not_in_subquery_next_to_decimals_is_written(con):
    """A plan with decimals is written only if it reads back the same. A NOT IN
    subquery's CASE used to grow on every reading (#238, TPC-H Q16)."""
    u = ibis.table({"i": "int64"}, name="u")
    t = ibis.table(SCHEMAS["t"], name="t")
    expr = t.filter(~t.i.isin(u.i)).select("i", s=t.a + t.a)
    plan = to_substrait_json(expr)
    written = written_plan(plan)
    assert written_plan(written) == written_plan(written_plan(written))
    put_table(con, "u", pa.table({"i": pa.array([3], pa.int64())}))
    got = sorted(r["i"] for r in run_plan(con, written, "duckdb").to_pylist())
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), {**ROWS, "u": [(3,)]})))
    assert got == sorted(r[0] for r in lean) == [-7, 0, 2]


def test_report_shows_decimals_at_their_scale():
    """A decimal's bound is shown in its digits, with its type, not as its
    unscaled integer (#250, TPC-H Q6's `revenue`)."""
    li = ibis.table({"p": "decimal(15,2)", "d": "decimal(15,2)"}, name="lineitem")
    sql = "SELECT sum(p * d) AS revenue FROM lineitem WHERE p >= 900 AND d >= 0.05"
    report = sv.verify(sv.sql(sql, dialect="duckdb", lineitem=li))
    assert report.facts["revenue"] == "a decimal(38, 4) ≥ 45.0000 or NULL"
    assert "revenue: a decimal(38, 4) ≥ 45.0000 or NULL" in str(report)
    t = ibis.table({"a": "decimal(10,2)"}, name="t")
    # Ibis types `a + a` at `a`'s precision; the model's exact sum needs one more.
    assert sv.verify(t.select(b=t.a + t.a)).facts["b"] == (
        "a decimal(11, 2) in [-199999999.98, 199999999.98] or NULL"
    )
