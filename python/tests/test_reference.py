"""The reference model's decisions (#185), finding by finding.

`characterization/duckdb/FACTS.md` judges DuckDB and the Lean model against
Substrait's semantics. Each test here pins what `Rel.eval` and `verify` do
for one of its findings (R1…R14), on a plan DataFusion's SQL producer
writes, and checks the value against DataFusion where it agrees with the
reference.
"""

import json

import ibis
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
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import arrow_rows
from sverify.sql_lift import lift
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


def refusal(con, sql: str) -> str:
    """The checker's message refusing `sql`."""
    code, out, err = run_checker((), substrait_json(con, sql))
    assert code != 0
    return out + err


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
        # `x` may be infinite too, and `fmod(±∞, y)` would be NaN (#257).
        ("SELECT x % 0.0 AS m FROM f", ["division by zero", "domain error"]),
        ("SELECT 1.5 % x AS m FROM f", ["division by zero"]),
        ("SELECT 1.5 % x AS m FROM f WHERE x <> 0.0", []),
    ],
)
def test_modulus_of_doubles_by_zero_is_an_error(sql, errors):
    """As on integers; `verify` proves it absent where the plan rules a zero
    divisor out (DataFusion gives NaN)."""
    assert [i.kind for i in sv.verify(sql, tables={"f": {"x": "float64"}}).errors] == errors


# #256: the remainder of doubles is sverify's own `sverify_fmod`, as
# Substrait's `modulus` has no double impl. Lean reads both and writes it;
# DataFusion runs it as its own `%`.
def declared(plan: str) -> set[str]:
    return {e["extensionFunction"]["name"] for e in json.loads(plan)["extensions"]}


def test_the_written_remainder_of_doubles_is_sverify_fmod(con):
    sql = "SELECT x % 2.0 AS m FROM f WHERE x < 1e300"
    written = written_plan(substrait_json(con, sql))
    assert "sverify_fmod" in declared(written)
    assert lean_values(json.dumps(inline_tables(json.loads(written), ROWS))) == [(1.5,), (0.0,)]
    for engine in ("duckdb", "polars", "datafusion"):
        assert arrow_rows(run_plan(con, written, engine)) == [(1.5,), (0.0,)], engine


def test_the_frontends_write_sverify_fmod():
    t = ibis.table({"x": "float64", "i": "int64"}, name="t")
    assert "sverify_fmod" in declared(to_substrait_json(t.select(m=t.x % 2.5)))
    assert "sverify_fmod" not in declared(to_substrait_json(t.select(m=t.i % 2)))
    lifted = lift("SELECT x % 2.5 AS m FROM t", {"t": t.schema()}, "reference")
    assert "sverify_fmod" in declared(json.dumps(lifted.plan))


def test_sverify_fmod_takes_doubles(con):
    plan = json.loads(written_plan(substrait_json(con, "SELECT x % 2.0 AS m FROM f")))
    (fmod,) = (
        e["extensionFunction"]["functionAnchor"]
        for e in plan["extensions"]
        if e["extensionFunction"]["name"] == "sverify_fmod"
    )
    project = plan["relations"][0]["root"]["input"]["project"]
    call = project["expressions"][0]
    while "scalarFunction" in call and call["scalarFunction"]["functionReference"] != fmod:
        call = call["scalarFunction"]["arguments"][0]["value"]
    call["scalarFunction"]["arguments"] = [
        {"value": {"literal": {"i64": "7"}}},
        {"value": {"literal": {"i64": "2"}}},
    ]
    code, out, err = run_checker((), json.dumps(plan))
    assert code != 0 and "sverify_fmod takes doubles" in out + err


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
    # `∞ / ∞` would be NaN, which no operation creates (#257).
    assert [str(i) for i in report.errors] == [
        "division by zero: ($0 /. $1)",
        "domain error: ($0 /. $1)",
    ]
    finite = ["x < 1e300", "x > -1e300"]
    for sql, req in [
        ("SELECT CASE WHEN y <> 0 THEN x / y END AS q FROM f", finite),
        ("SELECT x / NULLIF(y, 0) AS q FROM f", finite),
        ("SELECT x / y AS q FROM f", [*finite, "y > 0"]),
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
    # Only `∞ / ∞`, which would be NaN (#257): the dividend is not bounded.
    assert issues(plan) == ["domain error"]
    written = written_plan(plan)
    for engine in ("duckdb", "polars"):
        assert nan_safe(arrow_rows(run_plan(dcon, written, engine))) == expected, engine


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_double_division_by_zero_raises(dcon, engine):
    assert issues(divide_plan(dcon, None)) == ["division by zero", "domain error"]
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


# R11 (#207): lists are ordered lexicographically; a NULL element that decides
# the comparison makes it NULL, two NULLs at a position are equal.
LISTS = [
    ([1, None], [2], True),
    ([1, None], [1, 3], None),
    ([None, 1], [None, 2], True),
    ([1], [1, 2], True),
    ([1, 2], [1, 2], False),
    ([], [1], True),
    ([2], [], False),
    (None, [1], None),
]


def test_lists_compare_lexicographically():
    con = connect()
    ty = pa.list_(pa.int64())
    put_table(
        con,
        "l",
        pa.table(
            {"a": pa.array([r[0] for r in LISTS], ty), "b": pa.array([r[1] for r in LISTS], ty)}
        ),
    )
    plan = substrait_json(con, "SELECT a < b AS lt, b > a AS gt FROM l")
    expected = [(r[2], r[2]) for r in LISTS]
    rows = {"l": [(r[0], r[1]) for r in LISTS]}
    assert lean_values(json.dumps(inline_tables(json.loads(plan), rows))) == expected
    written = written_plan(plan)
    assert arrow_rows(run_plan(con, written, "duckdb")) == expected
    # Polars has no list order, and DataFusion's puts NULL first: both refuse.
    for engine in ("polars", "datafusion"):
        with pytest.raises(Exception, match="list_lt"):
            run_plan(con, written, engine)


def test_lists_of_lists_are_not_ordered():
    con = connect()
    ty = pa.list_(pa.list_(pa.int64()))
    put_table(con, "n", pa.table({"a": pa.array([[[1]]], ty), "b": pa.array([[[2]]], ty)}))
    assert "lists of lists" in refusal(con, "SELECT a < b AS lt FROM n")


# R13 (#209): `substring` with a negative start counts from the end unless the
# plan asks for LEFT_OF_BEGINNING.
SUBSTRINGS = [(-2, "lo", ""), (-10, "he", ""), (0, "h", "h"), (2, "el", "el"), (-6, "h", "")]


def substring_plan(con, start: int | None, length: int, option: str | None) -> str:
    put_table(con, "s", pa.table({"s": ["hello"], "a": pa.array([start], pa.int64())}))
    plan = json.loads(substrait_json(con, f"SELECT substring(s, a, {length}) AS x FROM s"))
    for node in _dicts(plan):
        if "scalarFunction" in node and option:
            node["scalarFunction"]["options"] = [{"name": "negative_start", "preference": [option]}]
    return json.dumps(plan)


@pytest.mark.parametrize(("start", "wrapped", "left"), SUBSTRINGS)
@pytest.mark.parametrize("option", [None, "WRAP_FROM_END", "LEFT_OF_BEGINNING"])
def test_substring_negative_start(start, wrapped, left, option):
    con = connect()
    length = 7 if start == -10 else 2
    plan = substring_plan(con, start, length, option)
    expected = [(left if option == "LEFT_OF_BEGINNING" else wrapped,)]
    rows = {"s": [("hello", start)]}
    assert lean_values(json.dumps(inline_tables(json.loads(plan), rows))) == expected
    written = written_plan(plan)
    for engine in ("duckdb", "polars"):
        assert arrow_rows(run_plan(con, written, engine)) == expected, engine
    if option == "LEFT_OF_BEGINNING":
        assert arrow_rows(run_plan(con, written, "datafusion")) == expected
    else:
        # DataFusion's own substring puts a negative start left of the beginning.
        with pytest.raises(Exception, match="negative start"):
            run_plan(con, written, "datafusion")


def test_substring_negative_start_error_is_refused():
    con = connect()
    plan = substring_plan(con, -2, 2, "ERROR")
    code, out, err = run_checker((), plan)
    assert code != 0 and "negative_start" in out + err


# R6 (#209): `avg` of integers follows the plan's declared output type; an
# integer one is the mean truncated toward zero, NULL for a group without values.
AVG_ROWS = [(1, -7), (1, -8), (2, 7), (2, 8), (3, None), (4, 5)]


def int_avg_plan(con, sql: str) -> str:
    put_table(
        con,
        "v",
        pa.table({"g": pa.array([r[0] for r in AVG_ROWS], pa.int64()),
                  "a": pa.array([r[1] for r in AVG_ROWS], pa.int64())}),
    )  # fmt: skip
    plan = json.loads(substrait_json(con, sql))
    i64 = {"i64": {"nullability": "NULLABILITY_NULLABLE"}}
    for node in _dicts(plan):
        for key in ("measure", "windowFunction"):
            if key in node:
                # Substrait's `avg` of `i64`: an `i64` argument and result
                # (DataFusion casts the argument to a double).
                node[key]["outputType"] = i64
                for a in node[key].get("arguments", []):
                    if "cast" in a["value"]:
                        a["value"] = a["value"]["cast"]["input"]
    return json.dumps(plan)


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        (
            "SELECT g, avg(a) AS m FROM v GROUP BY g ORDER BY g",
            [(1, -7), (2, 7), (3, None), (4, 5)],
        ),
        (
            "SELECT g, avg(a) OVER (PARTITION BY g) AS m FROM v ORDER BY g, a",
            [(1, -7), (1, -7), (2, 7), (2, 7), (3, None), (4, 5)],
        ),
    ],
)
def test_integer_avg_truncates(sql, expected):
    con = connect()
    plan = int_avg_plan(con, sql)
    rows = {"v": AVG_ROWS}
    assert lean_values(json.dumps(inline_tables(json.loads(plan), rows))) == expected
    # The mean of 64-bit integers is one too: nothing may go wrong.
    assert issues(plan) == []
    written = written_plan(plan)
    for engine in ("duckdb", "polars"):
        assert sorted(arrow_rows(run_plan(con, written, engine)), key=str) == sorted(
            expected, key=str
        ), engine
    with pytest.raises(Exception, match="no integer result"):
        run_plan(con, written, "datafusion")


def test_integer_avg_with_a_double_result_is_the_mean():
    con = connect()
    put_table(con, "w", pa.table({"a": pa.array([1, 2], pa.int64())}))
    plan = substrait_json(con, "SELECT avg(a) AS m FROM w")
    assert lean_values(json.dumps(inline_tables(json.loads(plan), {"w": [(1,), (2,)]}))) == [(1.5,)]


# R12 (#208): FLOAT (fp32) is a 32-bit double. Reading, comparing and widening
# one is exact; arithmetic on it and casts to it round to 32 bits, which is
# not modelled yet, so they are refused.
F32_SINGLE = float(pa.scalar(2e38, pa.float32()).as_py())


@pytest.fixture(scope="module")
def f32():
    c = connect()
    put_table(c, "s", pa.table({"x": pa.array([1.5, 2e38], pa.float32()), "d": [0.1, 3e38]}))
    return c


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        ("SELECT x > 0.1 AS b FROM s", [(True,), (True,)]),
        ("SELECT CAST(x AS DOUBLE) AS y FROM s", [(1.5,), (F32_SINGLE,)]),
        ("SELECT x * d AS m FROM s", [(1.5 * 0.1,), (F32_SINGLE * 3e38,)]),
        ("SELECT sum(x) AS t FROM s", [(1.5 + F32_SINGLE,)]),
        # A FLOAT literal is the single-precision value of its digits.
        (
            "SELECT CAST(0.1 AS FLOAT) AS t FROM s LIMIT 1",
            [(float(pa.scalar(0.1, pa.float32()).as_py()),)],
        ),
    ],
)
def test_floats_read_compare_and_widen_exactly(f32, sql, expected):
    written = written_plan(substrait_json(f32, sql))
    for engine in ("duckdb", "polars", "datafusion"):
        got = arrow_rows(run_plan(f32, written, engine))
        assert [
            tuple(float(v) if isinstance(v, float) else v for v in r) for r in got
        ] == expected, engine


@pytest.mark.parametrize(
    ("sql", "message"),
    [
        ("SELECT x + x AS s FROM s", "add of FLOAT"),
        ("SELECT sqrt(x) AS r FROM s", "sqrt of FLOAT"),
        ("SELECT CAST(d AS FLOAT) AS y FROM s", "casts to FLOAT"),
    ],
)
def test_float_arithmetic_is_refused(f32, sql, message):
    code, out, err = run_checker((), substrait_json(f32, sql))
    assert code != 0 and message in out + err


# R14 (#257): no operation creates a NaN. Where IEEE would make one from
# numbers (`inf - inf`, `0 * inf`, `inf / inf`, `fmod(inf, y)`, a negative
# base to a fractional power, `sin(inf)`, a double `SUM` of `inf` and
# `-inf`), the reference raises a domain error; a NaN in the input stays NaN.
FINITE = ["x < 1e300", "x > -1e300", "y < 1e300", "y > -1e300"]


@pytest.mark.parametrize(
    ("sql", "requires", "errors"),
    [
        ("SELECT x + y AS v FROM f", [], ["domain error"]),
        ("SELECT x + y AS v FROM f", FINITE, []),
        ("SELECT x - y AS v FROM f", [], ["domain error"]),
        ("SELECT x * y AS v FROM f", [], ["domain error"]),
        ("SELECT x * y AS v FROM f", FINITE, []),
        # Infinity plus a number is infinity, never NaN.
        ("SELECT x + 1.5 AS v FROM f", [], []),
        ("SELECT power(x, 0.5) AS v FROM f", [], ["domain error"]),
        ("SELECT power(x, 0.5) AS v FROM f", ["x >= 0"], []),
        ("SELECT power(x, 2.0) AS v FROM f", [], []),
        ("SELECT sin(x) AS v FROM f", [], ["domain error"]),
        ("SELECT sin(x) AS v FROM f", FINITE, []),
        ("SELECT sum(x) AS v FROM f", [], ["domain error"]),
        ("SELECT sum(x) AS v FROM f", ["x >= 0"], []),
        # An integer converts to a finite double.
        ("SELECT avg(CAST(i AS DOUBLE)) AS v FROM f", [], []),
    ],
)
def test_nan_creation_is_a_domain_error(sql, requires, errors):
    tables = {"f": {"x": "float64", "y": "float64", "i": "int64"}}
    report = sv.verify(sql, requires={"f": requires}, tables=tables)
    assert [i.kind for i in report.issues] == errors


INF_ROWS = [(INF, -INF, 0.0), (1.5, 2.0, 3.0), (NAN, 1.0, 1.0)]


@pytest.fixture(scope="module")
def icon():
    c = connect()
    put_table(c, "n", pa.table({k: [r[j] for r in INF_ROWS] for j, k in enumerate("xyz")}))
    return c


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT x + y AS v FROM n",
        "SELECT x - x AS v FROM n",
        "SELECT x * z AS v FROM n",
        "SELECT x / y AS v FROM n WHERE y <> 0.0",
        "SELECT sin(x) AS v FROM n",
        "SELECT power(z - 5.0, 0.5) AS v FROM n",
    ],
)
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_engines_raise_where_ieee_would_make_a_nan(icon, sql, engine):
    with pytest.raises(Exception, match="(?i)domain|NaN"):
        run_plan(icon, written_plan(substrait_json(icon, sql)), engine)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_nan_in_the_input_stays_nan(icon, engine):
    sql = "SELECT x + y AS v FROM n WHERE z > 0.5"
    got = nan_safe(arrow_rows(run_plan(icon, written_plan(substrait_json(icon, sql)), engine)))
    assert got == [(3.5,), ("NaN",)]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_double_sum_of_both_infinities_raises(icon, engine):
    sql = "SELECT sum(v) AS s FROM (SELECT x AS v FROM n UNION ALL SELECT y AS v FROM n)"
    with pytest.raises(Exception, match="(?i)domain|NaN"):
        run_plan(icon, written_plan(substrait_json(icon, sql)), engine)
    sql = "SELECT sum(y) AS s, avg(x) AS a FROM n"
    got = nan_safe(arrow_rows(run_plan(icon, written_plan(substrait_json(icon, sql)), engine)))
    assert got == [(-INF, "NaN")]
