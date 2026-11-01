"""The reference model's decisions (#185), finding by finding.

`characterization/duckdb/FACTS.md` judges DuckDB and the Lean model against
Substrait's semantics. Each test here pins what `Rel.eval` and `verify` do
for one of its findings (R1…R14), on a plan DataFusion's SQL producer
writes, and checks the value against DataFusion where it agrees with the
reference.
"""

import json

import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, put_table, run_sql, substrait_json
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("datafusion")

DAY = 86_400_000_000

#: Each table's rows, temporal values as their codes (µs, days).
ROWS = {
    "f": [(7.5,), (0.0,), (None,)],
    "t": [(0,), (18387 * DAY + 13 * 3600 * 10**6,)],
}
TABLES = {
    "f": pa.table({"x": [r[0] for r in ROWS["f"]]}),
    "t": pa.table({"ts": pa.array([r[0] for r in ROWS["t"]], pa.timestamp("us"))}),
}


@pytest.fixture(scope="module")
def con():
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    return c


def lean(con, sql: str) -> list[tuple]:
    """`Rel.eval`'s rows, temporal values as their codes."""
    plan = json.loads(substrait_json(con, sql))
    return lean_values(json.dumps(inline_tables(plan, ROWS)))


def nan_equal(rows: list[tuple]) -> list[tuple]:
    return [tuple("NaN" if isinstance(v, float) and v != v else v for v in r) for r in rows]


NAN = float("nan")


# R4 (#203): `modulus` of doubles is C's `fmod`, as DataFusion computes `%`
# (the integer one read the codes): the sign of the dividend; by zero, an error.
@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        ("SELECT x % 2.0 AS m FROM f", [(1.5,), (0.0,), (None,)]),
        ("SELECT -x % 2.0 AS m FROM f", [(-1.5,), (0.0,), (None,)]),
        ("SELECT x % -2.0 AS m FROM f", [(1.5,), (0.0,), (None,)]),
        ("SELECT x % CAST('inf' AS DOUBLE) AS m FROM f", [(7.5,), (0.0,), (None,)]),
        ("SELECT CAST('inf' AS DOUBLE) % 2.0 AS m FROM f LIMIT 1", [(NAN,)]),
        ("SELECT CAST('nan' AS DOUBLE) % 2.0 AS m FROM f LIMIT 1", [(NAN,)]),
        # The filter proves the divisor is not zero.
        ("SELECT x % x AS m FROM f WHERE x <> 0.0", [(0.0,)]),
        # Exact: `a - b * trunc(a / b)` in doubles gives 0.0.
        ("SELECT CAST('1e308' AS DOUBLE) % 3.0 AS m FROM f LIMIT 1", [(2.0,)]),
    ],
)
def test_modulus_of_doubles_is_fmod(con, sql, expected):
    assert nan_equal(lean(con, sql)) == nan_equal(expected)
    by_datafusion = [tuple(r.values()) for r in run_sql(con, sql).to_pylist()]
    assert nan_equal(by_datafusion) == nan_equal(expected)


@pytest.mark.parametrize(
    ("sql", "errors"),
    [
        ("SELECT x % 0.0 AS m FROM f", ["division by zero"]),
        ("SELECT 1.5 % x AS m FROM f", ["division by zero"]),
        ("SELECT 1.5 % x AS m FROM f WHERE x <> 0.0", []),
    ],
)
def test_modulus_of_doubles_by_zero_is_an_error(sql, errors):
    """As on integers; `verify` proves it absent where the plan rules a zero
    divisor out (DataFusion gives NaN)."""
    assert [i.kind for i in sv.verify(sql, tables={"f": {"x": "float64"}}).errors] == errors


# R7 (#205): an aggregate of a double constant adds doubles, not their codes.
@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        ("SELECT sum(CAST('inf' AS DOUBLE)) AS s FROM f", [(float("inf"),)]),
        ("SELECT sum(CAST('-inf' AS DOUBLE)) AS s FROM f", [(float("-inf"),)]),
        ("SELECT sum(1.5) AS s FROM f", [(4.5,)]),
        ("SELECT avg(2.5) AS a FROM f", [(2.5,)]),
        ("SELECT avg(42) OVER () AS a FROM f", [(42.0,)] * 3),
        ("SELECT sum(2.5) OVER () AS a FROM f", [(7.5,)] * 3),
    ],
)
def test_aggregates_of_double_constants(con, sql, expected):
    assert lean(con, sql) == expected
    assert [tuple(r.values()) for r in run_sql(con, sql).to_pylist()] == expected


# R10 (#206): a date is days and a timestamp microseconds; casts convert.
@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        ("SELECT CAST(DATE '2020-05-05' AS TIMESTAMP) AS v FROM t LIMIT 1", 18387 * DAY),
        ("SELECT CAST(TIMESTAMP '2020-05-05 13:00:00' AS DATE) AS v FROM t LIMIT 1", 18387),
        # Rounds down, before 1970 too.
        ("SELECT CAST(TIMESTAMP '1969-12-31 13:00:00' AS DATE) AS v FROM t LIMIT 1", -1),
        ("SELECT CAST(CAST(DATE '1969-12-31' AS TIMESTAMP) AS DATE) AS v FROM t LIMIT 1", -1),
        (
            "SELECT CAST(TIMESTAMP '2020-05-05 13:00:00' AS TIME) AS v FROM t LIMIT 1",
            13 * 3600 * 10**6,
        ),
        (
            "SELECT COALESCE(DATE '2020-05-05', TIMESTAMP '2020-05-06 01:00:00') AS v "
            "FROM t LIMIT 1",
            18387 * DAY,
        ),
    ],
)
def test_casts_between_dates_and_timestamps(con, sql, expected):
    assert lean(con, sql) == [(expected,)]


def test_timestamps_compared_with_dates(con):
    """DataFusion casts the date to a timestamp at midnight."""
    sql = "SELECT ts >= DATE '2020-05-05' AS a, ts < DATE '2020-05-06' AS b FROM t"
    assert lean(con, sql) == [(False, True), (True, True)]
    assert [tuple(r.values()) for r in run_sql(con, sql).to_pylist()] == lean(con, sql)
