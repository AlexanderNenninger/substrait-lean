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

import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, put_table, run_checker, substrait_json
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


@pytest.fixture(scope="module")
def con():
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    return c


def lean(con, sql: str) -> list[tuple]:
    """`Rel.eval`'s rows, decimals as `Decimal`s printed at their scale."""
    plan = json.loads(substrait_json(con, sql))
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
        ("SELECT abs(a) AS r FROM t", ["12.35", "0.05", "12.35", None]),
        # Compared at one scale.
        ("SELECT a > b AS r FROM t", [True, False, False, None]),
        ("SELECT a = CAST('12.35' AS DECIMAL(10,2)) AS r FROM t", [True, False, False, None]),
        # A smaller scale rounds half away from zero; an integer truncates.
        ("SELECT CAST(a AS DECIMAL(10,1)) AS r FROM t", ["12.4", "-0.1", "-12.4", None]),
        ("SELECT CAST(a AS BIGINT) AS r FROM t", [12, 0, -12, None]),
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
    sql = "SELECT k, avg(x) AS v, sum(x) AS s, count(x) AS n FROM g GROUP BY k ORDER BY k"
    assert lean(con, sql) == [
        (1, "0.006667", "0.02", 3),
        (2, "-0.050000", "-0.05", 1),
        (3, None, None, 0),
    ]
    assert lean(con, "SELECT avg(x) AS v FROM g") == [("-0.007500",)]


@pytest.mark.parametrize(
    ("sql", "message"),
    [
        ("SELECT a / b AS r FROM t", "divide of DECIMAL is not supported yet"),
        ("SELECT avg(a) OVER () AS r FROM t", "avg of DECIMAL over a window"),
    ],
)
def test_refused(con, sql, message):
    code, out, err = run_checker((), substrait_json(con, sql))
    assert code != 0 and message in out + err


@pytest.mark.parametrize(
    ("sql", "errors"),
    [
        # A column holds at most its precision's digits, so these fit.
        ("SELECT a + b AS r FROM t", []),
        ("SELECT a * b * a AS r FROM t", []),
        ("SELECT CAST(a AS DECIMAL(20,4)) AS r FROM t", []),
        ("SELECT CAST(a AS BIGINT) AS r FROM t", []),
        ("SELECT k, avg(x) AS v FROM g GROUP BY k", []),
        # These may not.
        ("SELECT CAST(a AS DECIMAL(4,2)) AS r FROM t", ["overflow"]),
        ("SELECT CAST(f AS DECIMAL(10,2)) AS r FROM t", ["cast out of range", "overflow"]),
    ],
)
def test_verify_reports_overflow_where_it_can_happen(sql, errors):
    assert [i.kind for i in sv.verify(sql, tables=SCHEMAS).errors] == errors


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
