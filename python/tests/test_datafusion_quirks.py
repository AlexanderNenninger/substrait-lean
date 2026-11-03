"""DataFusion as a backend, pinned (section 8 of `catalogue/backend_semantics.py`).

DataFusion is an engine here, not a SQL frontend: the plans come from
sverify's lift of DuckDB's SQL (`sverify.sql_lift`), and DataFusion runs
them through its own Substrait consumer and optimizer.

The first half pins what DataFusion's kernels do where sverify relies on or
works around them (the total order on doubles, truncating division, which
operations fail and which wrap around), so an upgrade that changes one of
them fails here. The second half pins DataFusion running checked plans,
against `verify` and the model: the notebook's E and D entries, and the
rewrites of the plan Lean writes for DataFusion's consumer.
"""

import json
from pathlib import Path

import ibis
import numpy as np
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import (
    canonical,
    collect,
    connect,
    put_table,
    run_plan,
    run_substrait_json,
    substrait_json,
)
from sverify.engines import written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify.incremental import arrow_rows
from sverify.testing import inline_tables, lean_rows, lean_values

pytestmark = pytest.mark.backend("datafusion")

FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"


def ints(**cols: list) -> pa.Table:
    return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})


TABLES = {
    "s": ints(y=[1, None]),
    "f": pa.table({"v": [1.0, float("nan"), 0.0, float("inf"), float("-inf"), None]}),
    "t": ints(a=[5, 0], b=[1, 0]),
    "m": ints(a=[-(2**63), 5]),
    "mx": ints(a=[2**63 - 1]),
    "dm": ints(a=[-7, 7], b=[2, -2]),
    "mixed": pa.table({"a": pa.array([1], pa.int64()), "f": [0.5]}),
    "i32": pa.table({"a": pa.array([2**31 - 1], pa.int32()), "b": pa.array([1], pa.int32())}),
    "str": pa.table({"s": ["b", "B", "a", "", "é", "z"]}),
    "bools": pa.table({"b": [False, True, None]}),
    "nanp": pa.table(
        {
            "v": pa.array(
                np.array([0x7FF8000000000001, 0x7FF8000000000000], np.uint64).view(np.float64)
            )
        }
    ),
}


@pytest.fixture(scope="module")
def con():
    """The tables as the model has them (`put_table`: one zero, one NaN), and
    in DataFusion as they are, so that its own answers show its own order."""
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    ctx = c._datafusion_session
    for name, t in TABLES.items():
        ctx.deregister_table(name)
        ctx.register_record_batches(name, [t.to_batches()])
    return c


def rows(con, sql: str) -> list[tuple]:
    return arrow_rows(con._datafusion_session.sql(sql).to_arrow_table())


def nan_aware(rows: list[tuple]) -> list[tuple]:
    return [tuple("NaN" if isinstance(v, float) and v != v else v for v in r) for r in rows]


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # Doubles: Arrow's total order, NaN = NaN, -0.0 < 0.0.
        (
            "SELECT v, v = v, -v = v, -v < v FROM f WHERE v = 0 OR isnan(v) ORDER BY v",
            [(0.0, True, False, True), ("NaN", True, False, True)],
        ),
        (
            "SELECT w FROM (SELECT v AS w FROM f UNION ALL SELECT -v FROM f) "
            "WHERE w > 1e308 OR w = 0 OR w < -1e308 ORDER BY w",
            # `w = 0` misses -0.0: they are different doubles.
            [("NaN",), (-np.inf,), (-np.inf,), (0.0,), (np.inf,), (np.inf,), ("NaN",)],
        ),
        ("SELECT max(v) AS mx FROM f", [("NaN",)]),
        ("SELECT a.v = b.v FROM nanp a CROSS JOIN nanp b", [(True,), (False,), (False,), (True,)]),
        ("SELECT count(DISTINCT v) FROM nanp", [(2,)]),
        # Integers: truncating division, silent wrap-around of + - *.
        ("SELECT a / b, a % b FROM dm", [(-3, -1), (-3, 1)]),
        ("SELECT a + 1, -a, a * 2 FROM mx", [(-(2**63), -(2**63) + 1, -2)]),
        ("SELECT a % -1 FROM m", [(0,), (0,)]),
        ("SELECT a + b, arrow_typeof(a + b) FROM i32", [(-(2**31), "Int32")]),
        # Strings: byte order.
        ("SELECT s FROM str ORDER BY s", [("",), ("B",), ("a",), ("b",), ("z",), ("é",)]),
    ],
)
def test_datafusion_behaviour(con, sql, expected):
    assert nan_aware(rows(con, sql)) == nan_aware(expected)


@pytest.mark.parametrize(
    ("sql", "error"),
    [
        ("SELECT a / b FROM t", "DivideByZero"),
        ("SELECT a % b FROM t", "DivideByZero"),
        ("SELECT a / -1 FROM m", "Overflow"),
        ("SELECT abs(a) FROM m", "overflow"),
        ("SELECT CAST(a AS INT) FROM m", "Can't cast"),
        ("SELECT CAST(v AS BIGINT) FROM f WHERE isnan(v)", "Cast"),
    ],
)
def test_datafusion_fails(con, sql, error):
    with pytest.raises(Exception, match=error):
        rows(con, sql)


def on_datafusion(con, sql: str) -> list[tuple]:
    """DataFusion running the checked plan the lift writes for `sql`."""
    return arrow_rows(run_plan(con, written_plan(substrait_json(con, sql)), "datafusion"))


def claims(sql: str, table: str, requires=(), ensures=()) -> sv.Report:
    return sv.verify(
        sql,
        requires={table: list(requires)},
        ensures=list(ensures),
        tables={table: ibis.Schema.from_pyarrow(TABLES[table].schema)},
        counterexamples=0,
        infer=False,  # what the model reports, without the bounds it would infer (#244)
    )


@pytest.mark.parametrize(
    ("sql", "requires", "errors"),
    [
        # E1, E2, E4: DataFusion evaluates both sides of AND, merges filters
        # and rewrites a boolean CASE into AND; `verify` reports the error.
        ("SELECT a FROM t WHERE b <> 0 AND a // b > 1", ["a >= 0"], ["division by zero"]),
        (
            "SELECT a FROM (SELECT * FROM t WHERE b <> 0) WHERE a // b > 1",
            ["a >= 0"],
            ["division by zero"],
        ),
        (
            "SELECT a FROM t WHERE CASE WHEN b <> 0 THEN a // b > 1 ELSE false END",
            ["a >= 0"],
            ["division by zero"],
        ),
    ],
)
def test_guards_datafusion_does_not_respect_are_reported(con, sql, requires, errors):
    assert [i.kind for i in claims(sql, "t", requires).errors] == errors
    with pytest.raises(Exception, match="DivideByZero"):
        on_datafusion(con, sql)


def test_guards_that_hold_on_datafusion(con):
    """E3: a numeric CASE stays lazy. E5: on the version sverify pins,
    DataFusion does not evaluate COALESCE's later arguments where an earlier
    one is not NULL; `verify` reports the division either way."""
    sql = "SELECT CASE WHEN b <> 0 THEN a // b END AS q FROM t"
    assert claims(sql, "t", ["a >= 0"]).errors == []
    assert on_datafusion(con, sql) == [(5,), (None,)]
    sql = "SELECT coalesce(b, a // b) AS c FROM t"
    assert "division by zero" in [i.kind for i in claims(sql, "t", ["b IS NOT NULL"]).errors]
    assert on_datafusion(con, sql) == [(1,), (0,)]


def test_int_vs_double_comparison(con):
    """D1: the lift writes the cast DataFusion's own plans left out."""
    sql = "SELECT a, f, a > f AS gt FROM mixed"
    report = claims(sql, "mixed", ["a = 1", "f = 0.5"], ["NOT gt"])
    assert not report.ensures[0].proved
    assert on_datafusion(con, sql) == [(1, 0.5, True)]


@pytest.mark.parametrize(
    ("sql", "table", "wrapped"),
    [
        ("SELECT a + b AS s FROM i32", "i32", [(-(2**31),)]),
        ("SELECT -a AS x FROM m", "m", [(-(2**63),), (-5,)]),
    ],
)
def test_datafusion_wraps_where_the_model_raises(con, sql, table, wrapped):
    """D2, D11: `verify` reports the overflow, and DuckDB and Polars raise,
    but DataFusion running the plan wraps around without an error."""
    assert "overflow" in [i.kind for i in claims(sql, table).errors]
    assert on_datafusion(con, sql) == wrapped
    plan = written_plan(substrait_json(con, sql))
    for engine in ("duckdb", "polars"):
        with pytest.raises(Exception):  # noqa: B017 - each engine raises its own
            run_plan(con, plan, engine)


@pytest.mark.parametrize(
    ("sql", "table"),
    [
        # D5: strings compare by code point (UTF-8 byte order).
        ("SELECT s, s < 'b' AS lt, s >= 'B' AS ge, s > 'é' AS gt FROM str", "str"),
        # FALSE < TRUE.
        ("SELECT b, b < TRUE AS lt, b >= FALSE AS ge, b > b AS gt FROM bools", "bools"),
        # D10: one zero and one NaN, also after negating.
        ("SELECT v, -v AS w, -v = v AS eq FROM f ORDER BY w", "f"),
    ],
)
def test_datafusion_runs_plans_as_the_model(con, sql, table):
    plan = json.loads(substrait_json(con, sql))
    lean = lean_values(json.dumps(inline_tables(plan, {table: arrow_rows(TABLES[table])})))
    assert nan_aware(on_datafusion(con, sql)) == nan_aware(lean)


def test_lean_writes_the_current_fetch_fields(con):
    """DataFusion's protobuf no longer has the deprecated
    `FetchRel.offset`/`count`; Lean writes `offsetExpr`/`countExpr`."""
    plan = written_plan(substrait_json(con, "SELECT y FROM s ORDER BY y LIMIT 1"))
    assert '"countExpr"' in plan and '"count":' not in plan
    assert arrow_rows(run_substrait_json(con, plan)) == [(1,)]


@pytest.mark.skipif(not FIXTURES.is_dir(), reason="the repository's tests/fixtures is not here")
def test_lean_writes_virtual_tables_with_their_types(con):
    """A VirtualTable's `baseSchema` used to be placeholder `i64` columns,
    which DataFusion checks the rows against."""
    plan = (FIXTURES / "virtual_left_join.json").read_text()
    rows = arrow_rows(run_substrait_json(con, written_plan(plan)))
    assert sorted(rows, key=str) == sorted(lean_rows(plan), key=str)


def test_integer_sum_fails_instead_of_wrapping(con):
    """DataFusion's integer SUM wraps around past 64 bits, where `Rel.eval`'s
    is exact. The plan Lean writes for DataFusion sums as DECIMAL(38,0) and
    casts back, which fails instead (#24); within range it agrees."""
    mx = ibis.table({"a": "int64"}, name="mx")
    twice = mx.select("a").union(mx.select("a"))
    over = written_plan(to_substrait_json(twice.aggregate(s=twice.a.sum())))
    assert arrow_rows(run_substrait_json(con, over)) == [(-2,)]  # wrapped around
    with pytest.raises(Exception, match="out of range Int64"):
        run_plan(con, over, "datafusion")
    sql = "SELECT b, sum(a) AS s, count(*) AS c FROM dm GROUP BY b"
    within = written_plan(substrait_json(con, sql))
    translated = sorted(arrow_rows(run_plan(con, within, "datafusion")))
    assert (
        translated
        == sorted(arrow_rows(run_substrait_json(con, within)))
        == [(-2, 7, 1), (2, -7, 1)]
    )


@pytest.mark.parametrize(
    "sql, expected",
    [
        (
            "SELECT 'x' AS c FROM s UNION ALL SELECT CAST(NULL AS VARCHAR) FROM s",
            ["x", "x", None, None],
        ),
        (
            "WITH RECURSIVE r AS (SELECT 0 AS d UNION ALL SELECT d + 1 FROM r WHERE d < 2) "
            "SELECT d FROM r",
            [0, 1, 2],
        ),
    ],
)
def test_union_batches_differ_in_nullability(con, sql, expected):
    """A `UNION ALL` gives record batches whose schemas differ in nullability
    (and, for a recursive CTE, in column names), which DataFusion's own
    `to_arrow_table()` fails to concatenate; `engine.collect` reconciles
    them, here and for plans (`run_substrait_json`)."""
    with pytest.raises(Exception, match="Schema at index 1 was different"):
        con._datafusion_session.sql(sql).to_arrow_table()
    expected = sorted([(v,) for v in expected], key=str)
    assert (
        sorted(arrow_rows(canonical(collect(con._datafusion_session.sql(sql)))), key=str)
        == expected
    )
    if "RECURSIVE" not in sql:  # the lift has no recursive queries
        plan = substrait_json(con, sql)
        assert sorted(arrow_rows(run_substrait_json(con, plan)), key=str) == expected


@pytest.mark.parametrize("join", ["JOIN", "LEFT JOIN"])
@pytest.mark.parametrize("cond", ["l.a = l.b", "r.y = r.y", "l.a + 0 = l.b AND r.y = r.y"])
def test_join_conditions_over_one_input(con, join, cond):
    """#98: DataFusion's consumer takes every `=` of a join condition for a key
    pair across the inputs, and fails on one over a single input. The plan
    Lean writes for DataFusion filters that input instead, or (the left input
    of a left join) writes the conjunct as a `CASE`."""
    tables = {"l": ints(a=[1, 1, 2, None], b=[1, 2, 2, 3]), "r": ints(y=[1, 2, None])}
    for name, t in tables.items():
        put_table(con, name, t)
    sql = f"SELECT l.a, l.b, r.y FROM l {join} r ON l.a = r.y AND {cond}"
    plan = written_plan(substrait_json(con, sql))
    with pytest.raises(Exception, match="FieldNotFound"):
        run_substrait_json(con, plan)
    rows = {name: arrow_rows(t) for name, t in tables.items()}
    lean = lean_rows(json.dumps(inline_tables(json.loads(plan), rows)))
    got = arrow_rows(run_plan(con, plan, "datafusion"))
    assert sorted(got, key=str) == sorted(lean, key=str)
    assert any(r[2] is not None for r in lean)


def test_nan_payloads_are_canonical_on_a_connection():
    """DataFusion's order tells NaN payloads apart, the model has one NaN.
    A connection stores every NaN as the same one (`engine.canonical`)."""
    c = connect()
    put_table(c, "nanp", TABLES["nanp"])
    assert rows(c, "SELECT count(DISTINCT v) FROM nanp") == [(1,)]
