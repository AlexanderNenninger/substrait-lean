"""Higher-order functions on lists with lambdas (#94): Substrait's `any_match`,
`all_match`, `transform` and `filter`.

A lambda's body reads its parameter and the enclosing row (D28,
`docs/core-semantics.md`); Ibis writes closed lambdas only, and Polars runs
only those. Ibis's `contains(v)` is `any_match(l, x -> x IS NOT DISTINCT FROM v)` (decided
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
    # A lambda's `$0` is its element, not a column: Lean's notation stays.
    assert "may fail: overflow: ($0 * 2)" in str(sv.verify(expr))
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


@pytest.mark.parametrize(("engine", "message"), [("duckdb", "lambdas have no SQL form yet")])
def test_other_engines_refuse(con, engine, message):
    t = con.table("t")
    w = written_plan(plan_json(con, t.select(x=t.l.contains(1))))
    with pytest.raises(Exception, match=message):
        run_plan(con, w, engine)


def _ref(field: int, param: bool = False) -> dict:
    root = "lambdaParameterReference" if param else "rootReference"
    return {
        "value": {"selection": {"directReference": {"structField": {"field": field}}, root: {}}}
    }


def _hof(anchor: int, op: int) -> dict:
    """`f(l, x -> op(x, c))` over the row `(c, l)`: the body reads the row's `c`."""
    body = {"scalarFunction": {"functionReference": op, "arguments": [_ref(0, True), _ref(0)]}}
    lam = {"lambda": {"parameters": {"types": [{"i64": {}}]}, "body": body}}
    return {"scalarFunction": {"functionReference": anchor, "arguments": [_ref(1), {"value": lam}]}}


#: `transform(l, x -> x + c)` and `filter(l, x -> x > c)`: lambdas that read
#: the row (D28), as Substrait writes them.
CAPTURING = {
    "extensions": [
        {"extensionFunction": {"functionAnchor": i, "name": n}}
        for i, n in enumerate(["transform", "add", "filter", "gt"], start=1)
    ],
    "relations": [
        {
            "root": {
                "names": ["shifted", "above"],
                "input": {
                    "project": {
                        "common": {"emit": {"outputMapping": [2, 3]}},
                        "input": {
                            "read": {
                                "namedTable": {"names": ["u"]},
                                "baseSchema": {
                                    "names": ["c", "l"],
                                    "struct": {
                                        "types": [{"i64": {}}, {"list": {"type": {"i64": {}}}}]
                                    },
                                },
                            }
                        },
                        "expressions": [_hof(1, 2), _hof(3, 4)],
                    }
                },
            }
        }
    ],
}


def test_a_lambda_reads_the_row():
    """D28: the body sees the enclosing row."""
    rows = {"u": [(10, [1, 20]), (0, [-1, None]), (5, None)]}
    got = lean_values(json.dumps(inline_tables(CAPTURING, rows)))
    assert sorted(got, key=repr) == sorted(
        [([11, 30], [20]), ([-1, None], []), (None, None)], key=repr
    )


def test_polars_refuses_a_lambda_that_reads_the_row(con):
    put_table(
        con,
        "u",
        pa.table({"c": pa.array([1], pa.int64()), "l": pa.array([[1]], pa.list_(pa.int64()))}),
    )
    with pytest.raises(Exception, match="reads only its own parameter"):
        run_plan(con, written_plan(json.dumps(CAPTURING)), "polars")
