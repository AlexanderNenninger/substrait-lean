"""Operations the parser rewrites into modelled ones (`IN` lists, `COALESCE`,
`NULLIF`, `GREATEST`/`LEAST`, `ABS`, `RIGHT JOIN`, `LIMIT … OFFSET`) mean what
DataFusion means by them: Lean's semantics of the rewrite agrees with
DataFusion, and the rewritten plan, written back out, runs on DataFusion with
the same result."""

import json
import math

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import (
    connect,
    create_table,
    put_table,
    run_checker,
    run_sql,
    run_substrait_json,
    substrait_json,
)
from sverify.testing import canonical, duckdb_rows, inline_tables, lean_rows

R = ibis.schema({"a": "int64", "b": "int64", "c": "int64"})
S = ibis.schema({"b": "int64", "d": "int64"})

QUERIES = [
    "SELECT a, b, c, COALESCE(a, b, c) AS x FROM r",
    "SELECT a, b, NULLIF(a, b) AS x FROM r",
    "SELECT GREATEST(a, b, c) AS x, LEAST(a, b) AS y FROM r",
    "SELECT a, ABS(a) AS x FROM r",
    "SELECT a FROM r WHERE a IN (1, -2, b)",
    "SELECT a FROM r WHERE a NOT IN (1, -2)",
    "SELECT a FROM r WHERE a IN (1, NULL)",
    "SELECT a, b FROM r WHERE COALESCE(a, 0) > LEAST(b, 1)",
    "SELECT r.a, s.d FROM r RIGHT JOIN s ON r.b = s.b",
    "SELECT s.d, r.c FROM r RIGHT JOIN s ON r.b = s.b AND r.a > s.d",
]

small = st.one_of(st.none(), st.integers(-3, 3))
tables = st.tuples(
    st.lists(st.tuples(small, small, small), max_size=8),
    st.lists(st.tuples(small, small), max_size=5),
)


@pytest.mark.parametrize("sql", QUERIES)
@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=tables)
def test_lean_semantics_match_datafusion(sql, rows):
    r, s = rows
    con = connect()
    create_table(con, "r", R, r)
    create_table(con, "s", S, s)
    expected = [tuple(x.values()) for x in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": r, "s": s})
    lean = lean_rows(json.dumps(plan))
    assert canonical(lean) == canonical(expected)
    assert canonical(duckdb_rows(json.dumps(plan))) == canonical(lean)


def test_limit_offset_takes_the_right_number_of_rows():
    con = connect()
    rows = [(i, i, i) for i in range(6)]
    create_table(con, "r", R, rows)
    plan = inline_tables(
        json.loads(substrait_json(con, "SELECT a FROM r LIMIT 3 OFFSET 4")), {"r": rows}
    )
    assert lean_rows(json.dumps(plan)) == duckdb_rows(json.dumps(plan)) == [(4,), (5,)]


def written(plan_json: str) -> str:
    code, out, err = run_checker(("--write",), plan_json)
    assert code == 0, err
    return out


#: Doubles where the rewrites could go wrong: signed zeros and NaNs, infinities.
DOUBLES = [None, 0.0, -0.0, 1.5, -1.5, math.inf, -math.inf, math.nan, -2.0]
TYPED = [
    "SELECT v, ABS(v) AS x FROM f",
    "SELECT v, w, GREATEST(v, w) AS x, LEAST(v, w) AS y FROM f",
    "SELECT v, COALESCE(v, w, 0) AS x, NULLIF(v, w) AS y FROM f",
    "SELECT v FROM f WHERE v IN (1.5, -2, 0.0)",
    "SELECT name, COALESCE(name, 'none') AS x, NULLIF(name, '') AS y FROM f",
    "SELECT name FROM f WHERE name NOT IN ('a', '')",
]


@pytest.mark.parametrize("sql", TYPED)
def test_written_plans_run_on_datafusion(sql):
    con = connect()
    pairs = [(v, w) for v in DOUBLES for w in DOUBLES]
    names = ["a", "", None, "b"]
    table = pa.table(
        {
            "v": [v for v, _ in pairs],
            "w": [w for _, w in pairs],
            "name": [names[i % len(names)] for i in range(len(pairs))],
        },
        schema=pa.schema([("v", pa.float64()), ("w", pa.float64()), ("name", pa.string())]),
    )
    put_table(con, "f", table)
    plan = substrait_json(con, sql)
    got = run_substrait_json(con, written(plan)).to_pylist()
    want = run_sql(con, sql).to_pylist()
    assert canonical(tuple(r.values()) for r in got) == canonical(tuple(r.values()) for r in want)
    on_duckdb = duckdb_rows(plan, {"f": table})
    assert canonical(on_duckdb) == canonical(tuple(r.values()) for r in want)


#: The contract checker reads the rewrites' conditions: each `CASE` branch is
#: evaluated knowing whether its condition is TRUE, and `OR`s refine filters.
T = ibis.table({"qty": "int64", "id": "int64", "amount": "float64"}, name="t")


@pytest.mark.parametrize(
    ("label", "expr", "ensures", "facts"),
    [
        (
            "clip",
            T.select(x=T.qty.clip(0, 10)),
            [_.x.isnull() | ((_.x >= 0) & (_.x <= 10))],
            {"x": "an integer in [0, 10] or NULL"},
        ),
        (
            "abs",
            T.select(x=T.qty.abs(), y=(T.qty - T.id).abs(), z=T.amount.abs()),
            [_.x.isnull() | (_.x >= 0), _.y.isnull() | (_.y >= 0), _.z.isnull() | (_.z >= 0)],
            {"x": "an integer ≥ 0 or NULL", "z": "a double ≥ 0.0 or NULL"},
        ),
        (
            "isin",
            T.filter(T.qty.isin([1, 2, 3])).select("qty"),
            [_.qty >= 1, _.qty <= 3, _.qty.notnull()],
            {"qty": "an integer in [1, 3]"},
        ),
        (
            "greatest, least",
            T.select(x=ibis.greatest(T.qty, 0), y=ibis.least(T.qty, 100)),
            [_.x >= 0, _.y <= 100],
            {"x": "an integer ≥ 0", "y": "an integer ≤ 100"},
        ),
        ("fill_null", T.select(x=T.qty.fill_null(5)), [_.x.notnull()], {"x": "any integer"}),
    ],
)
def test_contracts_see_through_rewrites(label, expr, ensures, facts):
    report = sv.verify(expr, ensures=ensures)
    assert report.proved, f"{label}: {report}"
    for col, fact in facts.items():
        assert report.facts[col] == fact, label


def test_clip_keeps_its_bounds_given_non_null_input():
    report = sv.verify(
        T.select(x=T.qty.clip(0, 10)),
        requires={"t": [_.qty.notnull()]},
        ensures=[_.x.notnull(), _.x <= 10],
    )
    assert report.proved, str(report)
