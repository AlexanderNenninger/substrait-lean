"""`AND` and `OR` read as guards (D50): in `p AND q` the raising operations of
`q` run only where `p` is not FALSE, in `p OR q` only where `p` is not TRUE."""

import time

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


#: The levels of a nest the parser lifts with the chain (`Parse.liftLevels`); deeper,
#: a filter's chains are bound in levels below it (D50-d).
LIFT_LEVELS = 3


def test_the_lift_guards_the_top_levels_of_a_nest_and_binds_the_rest():
    """A guard at the deepest lifted level is proved. One level further down the
    filter's chains are bound (D50-d); until the analysis reads a guarded column
    (D50-d3c) the division there needs a precondition."""
    inner = sv.verify(_nest(LIFT_LEVELS - 1), on_inferred="off")
    assert inner.verdict == sv.Verdict.PROVED, str(inner)
    outer = sv.verify(_nest(LIFT_LEVELS), on_inferred="off")
    assert outer.verdict != sv.Verdict.PROVED
    assert [e.kind for e in outer.errors] == ["division by zero"]


@pytest.mark.parametrize("wrappers", [4, 5, 8])
def test_a_deep_nest_is_bound_and_checks_in_time_linear_in_depth(wrappers):
    """Beyond the cap a filter's chains are bound in levels below it (D50-d), each
    operand written once: depth 8 checks as a depth 4 nest did before (5,171 s
    with the chain, #1681), and the plan grows with the operands, not with 2^depth."""
    start = time.perf_counter()
    report = sv.verify(_nest(wrappers), on_inferred="off")
    assert time.perf_counter() - start < 60
    # Until the analysis reads a guarded column (D50-d3c) the division needs a precondition.
    assert [e.kind for e in report.errors] == ["division by zero"]


def test_a_bound_filter_runs_as_the_lifted_one():
    """The bound plan keeps the rows the lift keeps (`Rel.guardedFilter_eval`), on DuckDB."""
    con = sv.connect()
    rows = pa.table({"x": [0, 1, 2, 5, 20], "z": [0, 1, 0, 1, 0]})
    con.put("t", rows)
    t = con.table("t")
    e = (t.x != 0) & ((10 // t.x) > 1)
    for i in range(5):
        e = ((t.z > 0) | e) if i % 2 == 0 else ((t.z > 0) & e)
    report = sv.verify(t.filter(e), ensures=[], on_inferred="off")
    got = sorted(report.run(con, unverified=True).to_pylist(), key=lambda r: (r["x"], r["z"]))
    want = sorted(t.filter(e).to_pyarrow().to_pylist(), key=lambda r: (r["x"], r["z"]))
    assert got == want


def test_a_deep_nest_in_a_projection_is_bound_and_runs_as_the_lifted_one():
    """A projected `AND`/`OR` nest deeper than the cap is bound below the projection
    (`Rel.guardedProject_eval`): it checks in time and DuckDB computes the lifted values."""
    con = sv.connect()
    rows = pa.table({"x": [0, 1, 2, 5, 20], "z": [0, 1, 0, 1, 0]})
    con.put("t", rows)
    t = con.table("t")
    e = (t.x != 0) & ((10 // t.x) > 1)
    for i in range(8):
        e = ((t.z > 0) | e) if i % 2 == 0 else ((t.z > 0) & e)
    expr = t.select(t.x, flag=e)
    start = time.perf_counter()
    report = sv.verify(expr, ensures=[], on_inferred="off")
    assert time.perf_counter() - start < 60
    got = sorted(report.run(con, unverified=True).to_pylist(), key=lambda r: r["x"])
    want = sorted(expr.to_pyarrow().to_pylist(), key=lambda r: r["x"])
    assert got == want
