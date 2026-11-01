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
from sverify.engine import (
    connect,
    put_table,
    run_checker,
    run_plan,
    run_sql,
    substrait_json,
    written_plan,
)
from sverify.incremental import arrow_rows
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("datafusion")

DAY = 86_400_000_000
NAN = float("nan")

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


# R5 (#204): a double divided by zero raises unless the plan asks otherwise.
DIV_ROWS = [(1.0, 0.0), (-1.0, 0.0), (0.0, 0.0), (NAN, 0.0), (None, 0.0), (1.0, None), (6.0, 3.0)]
INF = float("inf")


def divide_plan(con, mode: str | None) -> str:
    """`x / y` over `d`, with `on_division_by_zero` = `mode` (omitted if None)."""
    plan = json.loads(substrait_json(con, "SELECT x / y AS q FROM d"))

    def walk(node):
        if isinstance(node, dict):
            if "scalarFunction" in node and mode is not None:
                node["scalarFunction"]["options"] = [
                    {"name": "on_division_by_zero", "preference": [mode]}
                ]
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return json.dumps(plan)


@pytest.fixture(scope="module")
def dcon():
    c = connect()
    put_table(c, "d", pa.table({"x": [r[0] for r in DIV_ROWS], "y": [r[1] for r in DIV_ROWS]}))
    return c


def nan_safe(rows: list[tuple]) -> list[tuple]:
    return [tuple("NaN" if isinstance(v, float) and v != v else v for v in r) for r in rows]


def test_double_division_by_zero_may_fail():
    tables = {"f": {"x": "float64", "y": "float64"}}
    report = sv.verify("SELECT x / y AS q FROM f", tables=tables)
    assert [str(i) for i in report.errors] == ["division by zero: ($0 /. $1)"]
    for sql, req in [
        ("SELECT CASE WHEN y <> 0 THEN x / y END AS q FROM f", []),
        ("SELECT x / NULLIF(y, 0) AS q FROM f", []),
        ("SELECT x / y AS q FROM f", ["y > 0"]),
        ("SELECT x / 2.0 AS q FROM f", []),
    ]:
        assert sv.verify(sql, requires={"f": req}, tables=tables).issues == [], sql


@pytest.mark.parametrize(
    ("mode", "by_zero"),
    [
        ("IEEE", [INF, -INF, NAN, NAN, None]),
        ("LIMIT", [INF, -INF, INF, NAN, None]),
        ("NULL", [None, None, None, NAN, None]),
    ],
)
def test_double_division_options(dcon, mode, by_zero):
    """IEEE, LIMIT and NULL are a `CASE` on the divisor, which every engine runs."""
    plan = divide_plan(dcon, mode)
    rows = {"d": DIV_ROWS}
    expected = nan_safe([(v,) for v in [*by_zero, None, 2.0]])
    assert nan_safe(lean_values(json.dumps(inline_tables(json.loads(plan), rows)))) == expected
    assert issues(plan) == []
    written = written_plan(plan)
    for engine in ("duckdb", "polars"):
        assert nan_safe(arrow_rows(run_plan(dcon, written, engine))) == expected, engine


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_double_division_by_zero_raises(dcon, engine):
    assert issues(divide_plan(dcon, None)) == ["division by zero"]
    with pytest.raises(Exception, match="(?i)division by zero|divide by zero"):
        run_plan(dcon, written_plan(divide_plan(dcon, None)), engine)


def issues(plan: str) -> list[str]:
    """`verify`'s issues for a plan (`substrait-check --contract`, no conditions)."""
    contract = {"requires": [], "ensures": [], "transform": json.loads(plan), "keys": {},
                "ensures_keys": [], "references": {}}  # fmt: skip
    code, out, err = run_checker(("--contract",), json.dumps(contract))
    assert code in (0, 4), err
    return [i["kind"] for i in json.loads(out)["issues"]]


@pytest.mark.parametrize("op", ["/", "%"])
def test_integer_division_by_zero_may_ask_for_null(op):
    con = connect()
    put_table(con, "i", pa.table({"a": pa.array([7, None, 7], pa.int64()), "b": [2, 0, 0]}))
    plan = json.loads(substrait_json(con, f"SELECT a {op} b AS q FROM i"))
    # `MIN / -1` overflows; the option changes only the zero divisor.
    overflow = ["overflow"] if op == "/" else []
    assert issues(json.dumps(plan)) == ["division by zero", *overflow]
    for node in _dicts(plan):
        if "scalarFunction" in node:
            node["scalarFunction"]["options"] = [
                {"name": "on_division_by_zero", "preference": ["NULL"]}
            ]
    plan_json = json.dumps(plan)
    assert issues(plan_json) == overflow
    expected = [(3 if op == "/" else 1,), (None,), (None,)]
    rows = {"i": [(7, 2), (None, 0), (7, 0)]}
    assert lean_values(json.dumps(inline_tables(plan, rows))) == expected
    for engine in ("duckdb", "polars"):
        assert arrow_rows(run_plan(con, written_plan(plan_json), engine)) == expected, engine


def _dicts(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _dicts(v)
    elif isinstance(node, list):
        for v in node:
            yield from _dicts(v)
