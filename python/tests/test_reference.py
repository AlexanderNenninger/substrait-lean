"""The reference model's decisions (#185), finding by finding.

`engines/duckdb/facts/` judges DuckDB and the Lean model against
Substrait's semantics. Each test here pins what `Rel.eval` and `verify` do
for one of its findings (R1…R14), on the plan sverify's lift writes for DuckDB's
SQL with the reference's semantics (`semantics="reference"`), and checks the
value against DuckDB where it agrees with the reference.
"""

import json

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _engines import PROFILED
from sverify.engine import (
    connect,
    put_table,
    run_checker,
    run_plan,
    written_plan,
)
from sverify.engine import substrait_json as lift_json
from sverify.engines import ENGINES
from sverify.errors import PreconditionError, RouteError
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import arrow_rows
from sverify.sql_lift import lift
from sverify.testing import duckdb_sql, inline_tables, lean_values

DAY = 86_400_000_000
NAN = float("nan")

#: Each table's rows, temporal values as their codes (µs, days).
ROWS = {
    "f": [(7.5,), (0.0,), (None,)],
    "t": [(0,), (18387 * DAY + 13 * 3600 * 10**6,)],
    "n": [(None,), (None,)],
}
TABLES = {
    "f": pa.table({"x": [r[0] for r in ROWS["f"]]}),
    "t": pa.table({"ts": pa.array([r[0] for r in ROWS["t"]], pa.timestamp("us"))}),
    "n": pa.table({"x": pa.array([None, None], pa.float64())}),
}


def substrait_json(con, sql: str) -> str:
    """The plan of `sql` with the reference's semantics."""
    return lift_json(con, sql, "reference")


def verify(sql: str, tables: dict, requires: list | None = None) -> sv.Report:
    """`sv.verify` of `sql` with the reference's semantics, without inferred
    preconditions: the errors the model reports."""
    inputs = {n: ibis.table(s, name=n) for n, s in tables.items()}
    return sv.verify(
        sv.sql(sql, semantics="reference", **inputs),
        requires={n: requires or [] for n in tables},
        on_inferred="off",
    )


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


# R4 (#203): `modulus` of doubles is C's `fmod`
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
    by_duckdb = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
    assert nan_equal(by_duckdb) == nan_equal(expected)


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
    divisor out (IEEE gives NaN)."""
    assert [i.kind for i in verify(sql, {"f": {"x": "float64"}}).errors] == errors


# #256: the remainder of doubles is sverify's own `sverify_fmod`, as
# Substrait's `modulus` has no double impl. Lean reads both and writes it.
def declared(plan: str) -> set[str]:
    return {e["extensionFunction"]["name"] for e in json.loads(plan)["extensions"]}


def test_the_written_remainder_of_doubles_is_sverify_fmod(con):
    sql = "SELECT x % 2.0 AS m FROM f WHERE x < 1e300"
    written = written_plan(substrait_json(con, sql))
    assert "sverify_fmod" in declared(written)
    assert lean_values(json.dumps(inline_tables(json.loads(written), ROWS))) == [(1.5,), (0.0,)]
    for engine in ENGINES:
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
    assert [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()] == expected


# D26 (#922): two equalities for NULL. Grouping, `DISTINCT` and set
# operations take all NULLs as one value; a predicate's `=` never matches one.
@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        ("SELECT DISTINCT x FROM n", [(None,)]),
        ("SELECT a.x FROM n AS a JOIN n AS b ON a.x = b.x", []),
    ],
)
def test_two_equalities_for_null(con, sql, expected):
    assert lean(con, sql) == expected
    assert [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()] == expected


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
    """DuckDB casts the date to a timestamp at midnight."""
    sql = "SELECT ts >= DATE '2020-05-05' AS a, ts < DATE '2020-05-06' AS b FROM t"
    assert lean(con, sql) == [(False, True), (True, True)]
    assert [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()] == lean(con, sql)


# R5 (#204): a double divided by zero raises unless the plan asks otherwise.
DIV_ROWS = [(1.0, 0.0), (-1.0, 0.0), (0.0, 0.0), (NAN, 0.0), (None, 0.0), (1.0, None), (6.0, 3.0)]
INF = float("inf")


def divide_plan(con, mode: str | None) -> str:
    """`x / y` over `d`, with `on_division_by_zero` = `mode` (omitted if None)."""
    plan = json.loads(substrait_json(con, "SELECT x / y AS q FROM d"))

    def walk(node):
        if isinstance(node, dict):
            if "scalarFunction" in node and mode is None:
                node["scalarFunction"].pop("options", None)
            elif "scalarFunction" in node:
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
    # The reference's `/` raises on a zero divisor; DuckDB's gives ±inf or
    # NaN (`on_division_by_zero` IEEE), which raises nothing. `∞ / ∞` would
    # be NaN, which no operation creates (#257).
    f = ibis.table({"x": "float64", "y": "float64"}, name="f")

    def ref(sql: str) -> ibis.Table:
        return sv.sql(sql, semantics="reference", f=f)

    report = sv.verify(ref("SELECT x / y AS q FROM f"), on_inferred="off")
    assert [str(i) for i in report.errors] == [
        "division by zero: x / y",
        "domain error: x / y",
        "overflow to infinity: x / y",
    ]
    duckdb = sv.verify("SELECT x / y AS q FROM f", tables={"f": f}, semantics="duckdb")
    assert "division by zero" not in [i.kind for i in duckdb.errors]
    finite = ["x < 1e300", "x > -1e300"]
    for sql, req in [
        ("SELECT CASE WHEN y <> 0 THEN x / y END AS q FROM f", finite),
        ("SELECT x / y AS q FROM f", [*finite, "y > 0"]),
        ("SELECT x / 2.0 AS q FROM f", []),
    ]:
        assert sv.verify(ref(sql), requires={"f": req}).issues == [], sql


@pytest.mark.parametrize(
    ("mode", "by_zero"),
    [
        ("IEEE", [INF, -INF, NAN, NAN, None]),
        ("LIMIT", [INF, -INF, INF, NAN, None]),
        ("NULL", [None, None, None, NAN, None]),
    ],
)
def test_double_division_options(dcon, mode, by_zero):
    """IEEE is IEEE division (D39), LIMIT and NULL a `CASE` on the divisor;
    every engine runs them. IEEE's `0 / 0` creates a NaN, which raises in the
    reference (D37) and is NaN on DuckDB and Polars."""
    plan = divide_plan(dcon, mode)
    expected = nan_safe([(v,) for v in [*by_zero, None, 2.0]])
    nan_made = [mode == "IEEE" and r == (0.0, 0.0) for r in DIV_ROWS]
    rows = [r for r, n in zip(DIV_ROWS, nan_made, strict=True) if not n]
    want = [v for v, n in zip(expected, nan_made, strict=True) if not n]
    assert nan_safe(lean_values(json.dumps(inline_tables(json.loads(plan), {"d": rows})))) == want
    # Only `∞ / ∞` (and IEEE's `0 / 0`), which would be NaN (#257), and an
    # overflow to `±∞` (#575): the dividend is not bounded.
    assert issues(plan) == ["domain error", "overflow to infinity"]
    written = written_plan(plan)
    con = connect()
    put_table(con, "d", pa.table({"x": [r[0] for r in rows], "y": [r[1] for r in rows]}))
    for engine in ("duckdb", "polars"):
        assert nan_safe(arrow_rows(run_plan(con, written, engine))) == want, engine
        if any(nan_made):
            with pytest.raises(Exception, match="domain error|make a NaN"):
                run_plan(dcon, written, engine)


@pytest.mark.parametrize("engine", PROFILED)
def test_double_division_by_zero_raises(dcon, engine):
    assert issues(divide_plan(dcon, None)) == [
        "division by zero",
        "domain error",
        "overflow to infinity",
    ]
    with pytest.raises(Exception, match="(?i)division by zero|divide by zero"):
        run_plan(dcon, written_plan(divide_plan(dcon, None)), engine)


def issues(plan: str) -> list[str]:
    """`verify`'s issues for a plan (`substrait-check --contract`, no conditions)."""
    contract = {"requires": [], "ensures": [], "transform": json.loads(plan), "keys": {},
                "ensures_keys": [], "references": {}}  # fmt: skip
    code, out, err = run_checker(("--contract",), json.dumps(contract))
    assert code in (0, 4), err
    return [i["kind"] for i in json.loads(out)["issues"]]


@pytest.mark.parametrize("op", ["//", "%"])
def test_integer_division_by_zero_may_ask_for_null(op):
    con = connect()
    put_table(con, "i", pa.table({"a": pa.array([7, None, 7], pa.int64()), "b": [2, 0, 0]}))
    plan = json.loads(substrait_json(con, f"SELECT a {op} b AS q FROM i"))
    # `MIN / -1` overflows; the option changes only the zero divisor.
    overflow = ["overflow"] if op == "//" else []
    assert issues(json.dumps(plan)) == ["division by zero", *overflow]
    for node in _dicts(plan):
        if "scalarFunction" in node:
            node["scalarFunction"]["options"] = [
                {"name": "on_division_by_zero", "preference": ["NULL"]}
            ]
    plan_json = json.dumps(plan)
    assert issues(plan_json) == overflow
    expected = [(3 if op == "//" else 1,), (None,), (None,)]
    rows = {"i": [(7, 2), (None, 0), (7, 0)]}
    assert lean_values(json.dumps(inline_tables(plan, rows))) == expected
    for engine in ("duckdb", "polars"):
        assert arrow_rows(run_plan(con, written_plan(plan_json), engine)) == expected, engine


@pytest.mark.parametrize(
    ("division_type", "expected"),
    [(None, [(-1,), (1,)]), ("TRUNCATE", [(-1,), (1,)]), ("FLOOR", [(1,), (1,)])],
)
def test_modulus_takes_an_explicit_truncate(division_type, expected):
    """`modulus`'s remainder takes the dividend's sign, `division_type` =
    TRUNCATE, which a plan may also state; with FLOOR it takes the divisor's,
    as Polars's does (`Profile.polars`, `engines/polars/Sverify/Polars/Profile.lean`)."""
    con = connect()
    put_table(con, "i", pa.table({"a": pa.array([-7, 7], pa.int64())}))
    plan = json.loads(substrait_json(con, "SELECT a % 2 AS m FROM i"))
    if division_type:
        for node in _dicts(plan):
            if "scalarFunction" in node:
                node["scalarFunction"]["options"] = [
                    {"name": "division_type", "preference": [division_type]}
                ]
    code, out, err = run_checker((), json.dumps(plan))
    assert code == 0, err or out
    assert lean_values(json.dumps(inline_tables(plan, {"i": [(-7,), (7,)]}))) == expected


I64_MIN, I64_MAX = -(2**63), 2**63 - 1


@pytest.mark.parametrize(
    ("op", "mode", "expected"),
    [
        ("+", "SILENT", [I64_MIN, I64_MAX, 3, None]),
        ("+", "SATURATE", [I64_MAX, I64_MIN, 3, None]),
        ("-", "SILENT", [0, I64_MAX, 3, None]),
        ("*", "SATURATE", [I64_MAX, I64_MAX, 0, None]),
        ("*", "SILENT", [I64_MAX, I64_MIN, 0, None]),
    ],
)
def test_integer_overflow_may_ask_to_wrap_or_clamp(op, mode, expected):
    """`overflow` = SILENT wraps around and SATURATE clamps, when the plan asks
    (#241, `UnFn.fit`): nothing raises. DuckDB runs them through the generated
    lowering's templates; the other engines refuse them for now."""
    con = connect()
    rows = [(I64_MAX, 1), (I64_MIN, -1), (3, 0), (None, 0)]
    if op == "-":
        rows = [(I64_MAX, I64_MAX), (I64_MIN, 1), (3, 0), (None, 0)]
    columns = {k: pa.array([r[j] for r in rows], pa.int64()) for j, k in enumerate("ab")}
    put_table(con, "i", pa.table(columns))
    plan = json.loads(substrait_json(con, f"SELECT a {op} b AS q FROM i"))
    assert issues(json.dumps(plan)) == ["overflow"]
    for node in _dicts(plan):
        if "scalarFunction" in node:
            node["scalarFunction"]["options"] = [{"name": "overflow", "preference": [mode]}]
    plan_json = json.dumps(plan)
    assert issues(plan_json) == []
    want = [(v,) for v in expected]
    assert lean_values(json.dumps(inline_tables(plan, {"i": rows}))) == want
    written = written_plan(plan_json)
    assert arrow_rows(run_plan(con, written, "duckdb")) == want
    with pytest.raises(Exception, match="overflow"):
        run_plan(con, written, "polars")


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
    # Polars has no list order: it refuses.
    with pytest.raises(Exception, match="list_lt"):
        run_plan(con, written, "polars")


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
    for engine in ENGINES:
        assert arrow_rows(run_plan(con, written, engine)) == expected, engine


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
                # Substrait's `avg` of `i64`: an `i64` argument and result.
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
    for engine in ENGINES:
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
# Nor `±inf` (#575): an operation on finite doubles that overflows raises,
# which the checker rules out only for a `SUM` or `AVG` of bounded values
# over a bounded number of rows.
FINITE = ["x < 1e300", "x > -1e300", "y < 1e300", "y > -1e300"]
INFINITE = "overflow to infinity"


@pytest.mark.parametrize(
    ("sql", "requires", "errors"),
    [
        ("SELECT x + y AS v FROM f", [], ["domain error", INFINITE]),
        # Within 1e300 each, the sum stays below the largest double (#582).
        ("SELECT x + y AS v FROM f", FINITE, []),
        ("SELECT x - y AS v FROM f", [], ["domain error", INFINITE]),
        ("SELECT x * y AS v FROM f", [], ["domain error", INFINITE]),
        ("SELECT x * y AS v FROM f", FINITE, [INFINITE]),
        # Infinity plus a number is infinity, never NaN.
        ("SELECT x + 1.5 AS v FROM f", [], [INFINITE]),
        ("SELECT power(x, 0.5) AS v FROM f", [], ["domain error", INFINITE]),
        ("SELECT power(x, 0.5) AS v FROM f", ["x >= 0"], [INFINITE]),
        ("SELECT power(x, 2.0) AS v FROM f", [], [INFINITE]),
        ("SELECT sin(x) AS v FROM f", [], ["domain error"]),
        ("SELECT sin(x) AS v FROM f", FINITE, []),
        ("SELECT exp(x) AS v FROM f", FINITE, [INFINITE]),
        ("SELECT sum(x) AS v FROM f", [], ["domain error", INFINITE]),
        ("SELECT sum(x) AS v FROM f", ["x >= 0"], [INFINITE]),
        # Values within 2⁴⁰⁰ over at most 2³² rows sum to a finite double (#85).
        ("SELECT sum(x) AS v FROM f", ["x < 1e100", "x > -1e100", sv.max_rows(1000)], []),
        # An integer converts to a finite double, and the reference's mean
        # is the exact mean rounded once (D25, #1160): within the values'
        # bound, with no row cap.
        ("SELECT avg(CAST(i AS DOUBLE)) AS v FROM f", [], []),
    ],
)
def test_nan_creation_is_a_domain_error(sql, requires, errors):
    tables = {"f": {"x": "float64", "y": "float64", "i": "int64"}}
    report = verify(sql, tables, requires)
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
@pytest.mark.parametrize("engine", PROFILED)
def test_engines_raise_where_ieee_would_make_a_nan(icon, sql, engine):
    # Spark refuses `sin` and `power`, which are Java's, before it runs.
    with pytest.raises(Exception, match=r"(?i)domain|NaN|StrictMath|Math\.pow"):
        run_plan(icon, written_plan(substrait_json(icon, sql)), engine)


@pytest.mark.parametrize("engine", PROFILED)
def test_a_nan_in_the_input_stays_nan(icon, engine):
    sql = "SELECT x + y AS v FROM n WHERE z > 0.5"
    got = nan_safe(arrow_rows(run_plan(icon, written_plan(substrait_json(icon, sql)), engine)))
    assert got == [(3.5,), ("NaN",)]


@pytest.mark.parametrize("engine", PROFILED)
def test_a_double_sum_of_both_infinities_raises(icon, engine):
    n = icon.table("n")
    both = n.select(v=n.x).union(n.select(v=n.y))
    plan = to_substrait_json(both.aggregate(s=both.v.sum()))
    with pytest.raises(Exception, match="(?i)domain|NaN"):
        run_plan(icon, written_plan(plan), engine)
    sql = "SELECT sum(y) AS s, avg(x) AS a FROM n"
    got = nan_safe(arrow_rows(run_plan(icon, written_plan(substrait_json(icon, sql)), engine)))
    assert got == [(-INF, "NaN")]


def test_not_in_subquery_means_what_sql_means():
    """The checker lifts `NOT IN (subquery)` with SQL's NULL rules, so a NULL
    in the subquery leaves no rows."""
    c = connect()
    put_table(c, "n", pa.table({"x": pa.array([1, None, 2], pa.int64())}))
    put_table(c, "s", pa.table({"y": pa.array([1, None], pa.int64())}))
    plan = substrait_json(c, "SELECT x FROM n WHERE x NOT IN (SELECT y FROM s)")

    def lean(s: list[tuple]) -> list[tuple]:
        rows = {"n": [(1,), (None,), (2,)], "s": s}
        return lean_values(json.dumps(inline_tables(json.loads(plan), rows)))

    assert lean([(1,), (None,)]) == []
    assert lean([(1,)]) == [(2,)]
    assert lean([]) == [(1,), (None,), (2,)]


def test_lean_prints_integers_beyond_64_bits():
    """`Rel.eval`'s integers are unbounded: `MAX + 1` is printed as itself, not
    as a double's code (#72)."""
    c = connect()
    put_table(c, "mx", pa.table({"a": pa.array([2**63 - 1], pa.int64())}))
    plan = json.loads(substrait_json(c, "SELECT a + 1 AS s, -a AS n FROM mx WHERE a > 0"))
    assert lean_values(json.dumps(inline_tables(plan, {"mx": [(2**63 - 1,)]}))) == [
        (2**63, -(2**63) + 1)
    ]
    plan = json.loads(substrait_json(c, "SELECT -a AS n FROM mx"))
    assert lean_values(json.dumps(inline_tables(plan, {"mx": [(-(2**63),)]}))) == [(2**63,)]


@pytest.mark.parametrize("engine", PROFILED)
def test_overflow_to_infinity_is_the_references_precondition(engine):
    """#575: `Issue.infinite` is a precondition of the reference. A plan
    verified under DuckDB's semantics, which allows ±inf, assumes nothing and
    runs without the check; the reference's plan refuses the batch."""
    con = connect()
    put_table(con, "f", pa.table({"x": [1e308, 1.0], "y": [10.0, 2.0]}))
    sql = "SELECT x * y AS v FROM f"
    tables = {"f": con.table("f")}
    duck = sv.verify(sql, tables=tables, semantics="duckdb")
    assert INFINITE not in [i.kind for i in duck.issues + duck.assumed]
    # And proved: DuckDB's `0 · inf` is NaN, which the lift's `CASE` writes
    # and `verify` sees guards the product (#702).
    assert duck.proved
    out = duck.run(con, engine)
    assert out.column("v").to_pylist() == [INF, 2.0]
    ref = sv.verify(sql, tables=tables)
    assert [i.kind for i in ref.assumed] == [INFINITE]
    # Not proved (`x * y` may be 0 · inf), so refused unless asked (#655);
    # then refused before the run: the assumption is checked on the data
    # first, on Polars as on DuckDB.
    with pytest.raises(RouteError, match="not verified: may fail: domain error: x \\* y"):
        ref.run(con, engine)
    with pytest.raises(PreconditionError, match="stays finite.*refused before the run"):
        ref.run(con, engine, unverified=True)
    with pytest.raises(Exception, match="overflow"):
        ref.run(con, engine, check_requires=False, unverified=True)


def test_bounds_rule_out_overflow_to_infinity():
    """#582: a double `+`, `-`, `*`, `/` or `exp` whose inputs' bounds keep
    the exact result well below the largest double is finite
    (`FloatCode.add_scaled` …, `FloatCode.exp_fin`, proved in `float-bounds`),
    so the reference assumes nothing there. Chains are bounded too."""
    tables = {"f": {"x": "float64", "y": "float64"}}
    kinds = lambda sql, req: [i.kind for i in verify(sql, tables, req).issues]  # noqa: E731
    sqls = [
        "SELECT x * 1.1 AS v FROM f",
        "SELECT x + y AS v FROM f",
        "SELECT x - y AS v FROM f",
        "SELECT (x + y) * x AS v FROM f",
        "SELECT x / y AS v FROM f",
        "SELECT exp(x) AS v FROM f",
    ]
    for sql in sqls:
        assert INFINITE in kinds(sql, []), sql
    req = ["x >= -1000000", "x <= 1000000", "y >= 1", "y <= 10"]
    for sql in sqls[:-1]:
        assert INFINITE not in kinds(sql, req), sql
    # `exp` overflows past about 709.78.
    assert INFINITE not in kinds("SELECT exp(x) AS v FROM f", ["x <= 709"])
    assert INFINITE in kinds("SELECT exp(x) AS v FROM f", ["x <= 710"])
    # A divisor that may be near zero may still overflow.
    assert INFINITE in kinds("SELECT x / y AS v FROM f", ["x >= 0", "x <= 1000000", "y > 0"])


# Spark refuses a double `power` (Java's `Math.pow`), so not on Spark.
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_power_of_minus_infinity_to_a_fraction_is_a_domain_error(engine):
    """`power(-inf, y)` for a finite non-integer `y` raises in the reference
    (`negInfPow`): IEEE gives +inf or 0, as DuckDB does, and Polars's `** 0.5`
    NaN (fact duckdb-R15-power-neginf). A bound on the base rules it out; an
    integer exponent keeps IEEE's value."""
    tables = {"f": {"x": "float64", "y": "float64", "i": "int64"}}
    kinds = lambda sql, req: [i.kind for i in verify(sql, tables, req).issues]  # noqa: E731
    assert "domain error" in kinds("SELECT power(x, 1.5) AS v FROM f", [])
    assert "domain error" not in kinds("SELECT power(x, 1.5) AS v FROM f", ["x >= 0"])
    assert "domain error" not in kinds("SELECT power(x, 2.0) AS v FROM f", [])
    con = connect()
    put_table(con, "n", pa.table({"x": [-INF, 4.0]}))
    plan = written_plan(substrait_json(con, "SELECT power(x, 0.5) AS v FROM n"))
    with pytest.raises(Exception, match="domain|would make a NaN"):
        run_plan(con, plan, engine)
    ok = written_plan(substrait_json(con, "SELECT power(x, 2.0) AS v FROM n"))
    assert run_plan(con, ok, engine).column("v").to_pylist() == [INF, 16.0]


@pytest.mark.parametrize(
    ("dtype", "lo"),
    [(pa.int8(), -(2**7)), (pa.int16(), -(2**15)), (pa.int32(), -(2**31)), (pa.int64(), I64_MIN)],
)
def test_abs_of_the_smallest_integer_raises_at_its_width(dtype, lo):
    """`abs` of a column's smallest value does not fit its type, at every
    width: `abs(-128::TINYINT)` raises in DuckDB, where the model gave 128
    (#616). `verify` reports it, and a bound above the minimum rules it out."""
    con = connect()
    put_table(con, "i", pa.table({"a": pa.array([lo + 1, None], dtype)}))
    plan = substrait_json(con, "SELECT abs(a) AS q FROM i")
    assert issues(plan) != []
    tables = {"i": {"a": str(ibis.dtype(dtype))}}
    assert not verify("SELECT abs(a) AS q FROM i", tables).proved
    assert verify("SELECT abs(a) AS q FROM i", tables, [f"a >= {lo + 1}"]).proved
    # In range: the largest value; DuckDB on the written plan agrees.
    want = [(-(lo + 1),), (None,)]
    rows = {"i": [(lo + 1,), (None,)]}
    assert lean_values(json.dumps(inline_tables(json.loads(plan), rows))) == want
    assert arrow_rows(run_plan(con, written_plan(plan), "duckdb")) == want
    # The minimum raises on DuckDB, natively and on the written plan.
    put_table(con, "i", pa.table({"a": pa.array([lo], dtype)}))
    with pytest.raises(Exception, match="(?i)overflow|out of range"):
        run_plan(con, written_plan(plan), "duckdb")
    with pytest.raises(Exception, match="(?i)overflow|out of range"):
        duckdb_sql(con, "SELECT abs(a) AS q FROM i")


def test_quantile_cont_between_opposite_infinities_is_a_domain_error():
    """`QUANTILE_CONT` interpolating between `-inf` and `+inf` creates a NaN
    (IEEE and DuckDB give NaN, the model's clamp gave `+inf`, #561): the
    reference raises there (D21), a precondition rules it out, and the
    written plan raises on DuckDB. Neighbours of one infinity interpolate."""
    tables = {"f": {"x": "float64", "y": "float64", "i": "int64"}}
    sql = "SELECT quantile_cont(x, 0.5) AS m FROM f"
    assert "domain error" in [i.kind for i in verify(sql, tables).issues]
    assert "domain error" not in [i.kind for i in verify(sql, tables, ["x < 1e300"]).issues]
    con = connect()
    put_table(con, "q", pa.table({"x": [None, INF, -INF]}))
    plan = written_plan(substrait_json(con, "SELECT quantile_cont(x, 0.5) AS m FROM q"))
    with pytest.raises(Exception, match="domain error"):
        run_plan(con, plan, "duckdb")
    put_table(con, "q", pa.table({"x": [-INF, -INF, 0.0, INF]}))
    assert run_plan(con, plan, "duckdb").column("m").to_pylist() == [-INF]
