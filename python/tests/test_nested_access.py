"""Struct fields, list elements and `cardinality` (#94).

The reference rules (decided on #94, from Substrait's spec and the backends):
a list element is zero-based, negative from the end and NULL out of range
(Substrait's `ListElement`); `cardinality` counts NULL elements and is NULL
for a NULL list; a NULL struct's fields are NULL. Polars runs them; the SQL
engines and DataFusion refuse them for now.
"""

import json

import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_checker, run_plan, written_plan
from sverify.ibis_substrait import Unsupported
from sverify.incremental import arrow_rows
from sverify.testing import inline_tables, lean_values

pytestmark = pytest.mark.backend("polars")

S = pa.struct([("a", pa.int64()), ("b", pa.string())])
LISTS = [[1, 2, 3], [], None, [1, None], [None]]
STRUCTS = [{"a": 1, "b": "x"}, None, {"a": None, "b": None}, {"a": 4, "b": "y"}, None]
T = pa.table(
    {
        "id": pa.array(range(len(LISTS)), pa.int64()),
        "l": pa.array(LISTS, pa.list_(pa.int64())),
        "s": pa.array(STRUCTS, S),
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


def test_list_elements(con):
    t = con.table("t")
    expr = t.select(t.id, second=t.l[1], last=t.l[-1], out=t.l[3], before=t.l[-4])
    assert both(con, expr) == [
        (0, 2, 3, None, None),
        (1, None, None, None, None),
        (2, None, None, None, None),
        (3, None, None, None, None),
        (4, None, None, None, None),
    ]


def test_cardinality_counts_null_elements(con):
    t = con.table("t")
    assert both(con, t.select(t.id, n=t.l.length())) == [(0, 3), (1, 0), (2, None), (3, 2), (4, 1)]


def test_struct_fields(con):
    t = con.table("t")
    expr = t.select(t.id, a=t.s.a, b=t.s.b)
    assert both(con, expr) == [
        (0, 1, "x"),
        (1, None, None),
        (2, None, None),
        (3, 4, "y"),
        (4, None, None),
    ]


def test_a_field_alone_is_not_a_column(con):
    # Only plain column references become an emit; `s.a` is not column 0.
    t = con.table("t")
    assert both(con, t.select(a=t.s.a)) == [(1,), (4,), (None,), (None,), (None,)]


def test_access_in_a_filter(con):
    t = con.table("t")
    expr = t.filter(t.l.length() >= 2).select(t.id, first=t.l[0])
    assert both(con, expr) == [(0, 1), (3, 1)]


def test_a_list_element_needs_a_constant_index(con):
    t = con.table("t")
    with pytest.raises(Unsupported, match="constant index"):
        plan_json(con, t.select(x=t.l[t.l.length() - 1]))


def test_a_field_outside_the_struct_is_refused(con):
    t = con.table("t")
    plan = json.loads(plan_json(con, t.select(a=t.s.a)))
    text = json.dumps(plan).replace(
        '"structField": {"field": 0}}, "expression"', '"structField": {"field": 2}}, "expression"'
    )
    assert text != json.dumps(plan)
    code, _, err = run_checker((), text)
    assert code != 0 and "field 2 of a struct of 2 fields" in err


@pytest.mark.parametrize(
    ("engine", "message"),
    [
        ("duckdb", "struct columns have no SQL form yet"),
        ("datafusion", "DataFusion does not run struct fields"),
    ],
)
def test_other_engines_refuse(con, engine, message):
    t = con.table("t")
    w = written_plan(plan_json(con, t.select(a=t.s.a, n=t.l.length())))
    with pytest.raises(Exception, match=message):
        run_plan(con, w, engine)
