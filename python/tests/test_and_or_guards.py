"""`AND` and `OR` read as guards (D50): in `p AND q` the raising operations of
`q` run only where `p` is not FALSE, in `p OR q` only where `p` is not TRUE."""

import ibis
import pyarrow as pa
import pytest

import sverify as sv

pytestmark = pytest.mark.backend("duckdb")

ORDERS = ibis.table({"qty": "!int64", "total": "!int64"}, name="orders")
SCHEMA = {"orders": ibis.schema({"qty": "!int64", "total": "!int64"})}


def _needs(report):
    return [n.code for n in report.needs if "qty" in n.code]


def test_the_reviews_example_is_proved_without_a_precondition_in_ibis():
    t = ORDERS.filter((ORDERS.qty != 0) & (ORDERS.total // ORDERS.qty > 1)).select(ORDERS.qty)
    assert _needs(sv.verify(t, ensures=[])) == []


def test_the_reviews_example_is_proved_without_a_precondition_in_sql():
    report = sv.verify(
        "SELECT qty FROM orders WHERE qty <> 0 AND total // qty > 1", tables=SCHEMA, ensures=[]
    )
    assert _needs(report) == []


def test_the_eager_reading_still_needs_the_precondition_under_duckdb_semantics():
    report = sv.verify(
        "SELECT qty FROM orders WHERE qty <> 0 AND total // qty > 1",
        tables=SCHEMA,
        ensures=[],
        semantics="duckdb",
    )
    assert _needs(report) != []


def test_an_or_guards_its_right_operand():
    t = ORDERS.filter((ORDERS.qty == 0) | (ORDERS.total // ORDERS.qty > 1)).select(ORDERS.qty)
    assert _needs(sv.verify(t, ensures=[])) == []


def test_a_nested_and_guards_every_later_operand():
    t = ORDERS.filter(
        (ORDERS.qty > 0) & (ORDERS.total > 0) & (ORDERS.total // ORDERS.qty > 1)
    ).select(ORDERS.qty)
    assert _needs(sv.verify(t, ensures=[])) == []


def test_a_nullable_column_is_guarded_too():
    o = ibis.table({"qty": "int64", "total": "!int64"}, name="orders")
    t = o.filter((o.qty != 0) & (o.total // o.qty > 1)).select(o.total)
    assert [n.code for n in sv.verify(t, ensures=[]).needs if "qty" in n.code] == []


def test_the_lifted_plan_runs_as_the_eager_one_where_nothing_raises():
    con = sv.connect()
    rows = pa.table({"qty": [0, 1, 2, 3, 5], "total": [7, 3, 4, 9, 0]})
    con.put("orders", rows)
    sql = "SELECT qty, total FROM orders WHERE qty <> 0 AND total // qty > 1"
    report = sv.verify(sql, tables={"orders": con.table("orders")}, ensures=[])
    got = sorted(report.run(con, unverified=True).to_pylist(), key=lambda r: r["qty"])
    assert got == [{"qty": 1, "total": 3}, {"qty": 2, "total": 4}, {"qty": 3, "total": 9}]


def _nest(wrappers: int):
    """`x <> 0 AND 10 // x > 1`, under `wrappers` more connectives (`OR` and `AND`
    in turn, so none merges with its neighbour), each with a plain operand."""
    t = ibis.table({"x": "int64", "z": "int64"}, name="t")
    e = (t.x != 0) & ((10 // t.x) > 1)
    for i in range(wrappers):
        e = ((t.z > 0) | e) if i % 2 == 0 else ((t.z > 0) & e)
    return t.filter(e)


def test_the_lift_guards_the_top_levels_of_a_nest_and_no_more():
    """D50 interim cap (`LIFT_LEVELS`): a guard at the deepest lifted level is proved,
    one level further down is read eagerly and its division needs a precondition."""
    from sverify.plan_json import LIFT_LEVELS

    inner = sv.verify(_nest(LIFT_LEVELS - 1), on_inferred="off")
    assert inner.verdict == sv.Verdict.PROVED, str(inner)
    outer = sv.verify(_nest(LIFT_LEVELS), on_inferred="off")
    assert outer.verdict != sv.Verdict.PROVED
    assert [e.kind for e in outer.errors] == ["division by zero"]
