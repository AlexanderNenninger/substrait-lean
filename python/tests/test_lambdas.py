"""Higher-order functions on lists with lambdas (#94): Substrait's `any_match`,
`all_match`, `transform` and `filter`.

Lambdas are closed for now: the body reads its parameter and constants.
Ibis's `contains(v)` is `any_match(l, x -> x IS NOT DISTINCT FROM v)` (decided
on #94: Polars' meaning, within the spec), so `v` is a constant. Polars runs
them; the SQL engines and DataFusion refuse them.
"""

import json

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.ibis_substrait import Unsupported
from sverify.incremental import arrow_rows
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("polars")

LISTS = [[1, 2, 3], [], None, [1, None], [None], [2, None]]
NESTED = [[[1], [2, 3]], [], None, [[1, None], None], [None], [[]]]
T = pa.table(
    {
        "id": pa.array(range(len(LISTS)), pa.int64()),
        "l": pa.array(LISTS, pa.list_(pa.int64())),
        "ll": pa.array(NESTED, pa.list_(pa.list_(pa.int64()))),
    }
)
ROWS = {"t": [tuple(r.values()) for r in T.to_pylist()]}


@pytest.fixture(scope="module")
def con():
    c = connect()
    put_table(c, "t", T)
    return c


def both(con, expr) -> list[tuple]:
    """The plan's rows from `Rel.eval` and from Polars, which must agree."""
    plan = plan_json(con, expr)
    lean = lean_values(json.dumps(inline_tables(json.loads(plan), ROWS)))
    polars = arrow_rows(run_plan(con, written_plan(plan), "polars"))
    assert sorted(map(repr, polars)) == sorted(map(repr, lean))
    return sorted(lean, key=repr)


@pytest.mark.parametrize(
    ("value", "expected"),
    [
        # Found; not found; NULL for a NULL list. A NULL element matches
        # only NULL (IS NOT DISTINCT FROM).
        (1, [True, False, None, True, False, False]),
        (2, [True, False, None, False, False, True]),
        (None, [False, False, None, True, True, True]),
    ],
)
def test_contains(con, value, expected):
    t = con.table("t")
    rows = both(con, t.select(t.id, x=t.l.contains(ibis.literal(value, "int64"))))
    assert [x for _, x in rows] == expected


def test_transform(con):
    t = con.table("t")
    rows = both(con, t.select(t.id, x=t.l.map(lambda v: v * 2)))
    assert [x for _, x in rows] == [[2, 4, 6], [], None, [2, None], [None], [4, None]]


def test_filter_keeps_true_only(con):
    t = con.table("t")
    rows = both(con, t.select(t.id, x=t.l.filter(lambda v: v > 1)))
    assert [x for _, x in rows] == [[2, 3], [], None, [], [], [2]]


def test_nested_lambdas(con):
    t = con.table("t")
    rows = both(con, t.select(t.id, x=t.ll.map(lambda v: v.contains(1))))
    assert [x for _, x in rows] == [[True, False], [], None, [True, None], [None], [False]]


def test_in_a_filter(con):
    t = con.table("t")
    assert both(con, t.filter(t.l.contains(1)).select(t.id)) == [(0,), (3,)]


def test_an_error_in_the_body_is_an_error_of_the_row(con):
    c = connect()
    put_table(c, "b", pa.table({"l": pa.array([[1, 2], [2**62, 1]], pa.list_(pa.int64()))}))
    b = c.table("b")
    expr = b.select(x=b.l.map(lambda v: v * 2))
    assert "may wrap around: ($0 * 2)" in str(sv.verify(expr))
    with pytest.raises(Exception, match="multiply leaves 64 bits"):
        run_plan(c, written_plan(plan_json(c, expr)), "polars")


@pytest.mark.parametrize(
    ("make", "message"),
    [
        (lambda t: t.l.map(lambda v: v + t.id), "reads the table's columns"),
        (lambda t: t.l.contains(t.id), "constant value"),
    ],
)
def test_lambdas_are_closed(con, make, message):
    t = con.table("t")
    with pytest.raises(Unsupported, match=message):
        plan_json(con, t.select(x=make(t)))


@pytest.mark.parametrize(
    ("engine", "message"),
    [("duckdb", "lambdas have no SQL form yet"), ("datafusion", "DataFusion does not run")],
)
def test_other_engines_refuse(con, engine, message):
    t = con.table("t")
    w = written_plan(plan_json(con, t.select(x=t.l.contains(1))))
    with pytest.raises(Exception, match=message):
        run_plan(con, w, engine)
