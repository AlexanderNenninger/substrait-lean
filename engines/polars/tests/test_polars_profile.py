"""`Profile.polars` (#444, `engines/polars/Sverify/Polars/Profile.lean`): `//` and
`%` floor, as Polars's own do.

Lean proves that the checker's reading of a call that states
`division_type: FLOOR` is `Polars.floorDiv` and `Polars.floorMod` on 64-bit
integers (`Profile.polars_idiv`, `Profile.polars_imod`). That Polars computes
them is the trusted part, from its facts (polars-int-divide,
polars-int-modulus); these tests run it natively against Python's `//` and
`%`, which floor too.
"""

from __future__ import annotations

import json
import math

import ibis
import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import _support, routes
from sverify.engine import connect, put_table, run_plan, written_plan

MIN, MAX = -(2**63), 2**63 - 1
#: The preconditions `verify` infers: `i >= -9 * 10**18` (so `MIN // -1`
#: cannot overflow) and `j != 0`.
LOW = -9 * 10**18

dividends = st.one_of(st.integers(LOW, MAX), st.sampled_from([LOW, -1, 0, 1, MAX]))
divisors = st.one_of(st.integers(MIN, MAX), st.sampled_from([MIN, -2, -1, 1, 2, MAX])).filter(
    lambda j: j != 0
)


@pytest.fixture(scope="module")
def report() -> sv.Report:
    con = sv.connect()
    con.put("t", pa.table({"i": pa.array([1], pa.int64()), "j": pa.array([1], pa.int64())}))
    t = con.table("t")
    r = sv.verify(
        t.select(m=t.i % t.j, q=t.i // t.j),
        requires={"t": [_.i >= LOW, _.j != 0]},
        semantics="polars",
    )
    assert r.proved, str(r)
    return r


@settings(max_examples=50, deadline=None)
@given(rows=st.lists(st.tuples(dividends, divisors), min_size=1, max_size=20))
def test_native_floor_agrees_with_floor_division(report: sv.Report, rows) -> None:
    con = sv.connect()
    i, j = zip(*rows, strict=True)
    con.put("t", pa.table({"i": pa.array(i, pa.int64()), "j": pa.array(j, pa.int64())}))
    out = report.run(con, "polars", route="native")
    assert out.column("m").to_pylist() == [a % b for a, b in rows]
    assert out.column("q").to_pylist() == [a // b for a, b in rows]
    assert report.routes["polars"].kind == "native"


def test_written_plan_states_floor(report: sv.Report) -> None:
    """Lean writes the calls back with their option, and no engine refuses
    them: the SQL writer computes `FLOOR` from truncating operations."""
    plan = json.loads(written_plan(report.internal_plan or ""))
    calls = []

    def walk(node: object) -> None:
        if isinstance(node, dict):
            call = node.get("scalarFunction")
            if isinstance(call, dict) and any(
                o.get("name") == "division_type" and o.get("preference") == ["FLOOR"]
                for o in call.get("options", [])
            ):
                calls.append(node)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    assert len(calls) == 2
    for engine in ("duckdb", "spark", "snowflake", "polars"):
        _support.check(plan, engine)


def _run_written(report: sv.Report, rows: list[tuple[int, int]], engine: str) -> pa.Table:
    con = connect()
    i, j = zip(*rows, strict=True)
    put_table(con, "t", pa.table({"i": pa.array(i, pa.int64()), "j": pa.array(j, pa.int64())}))
    return run_plan(con, written_plan(report.internal_plan or ""), engine)


@settings(max_examples=50, deadline=None)
@given(rows=st.lists(st.tuples(dividends, divisors), min_size=1, max_size=20))
def test_written_floor_runs_on_duckdb(report: sv.Report, rows) -> None:
    """The written plan on DuckDB, whose `//` and `%` truncate: the SQL
    writer's `FLOOR` (`Expr.floorDivOf`, `Expr.floorModOf`) gives Polars's
    values, which `Profile.polars_idiv` and `Profile.polars_imod` prove are
    the checker's."""
    out = _run_written(report, rows, "duckdb")
    assert out.column("m").to_pylist() == [a % b for a, b in rows]
    assert out.column("q").to_pylist() == [a // b for a, b in rows]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_written_floor_raises(report: sv.Report, engine: str) -> None:
    """Negative operands and the ends of 64 bits floor; a zero divisor
    raises, and so does `MIN // -1`, whose quotient leaves 64 bits."""
    edges = [(-7, 2), (7, -2), (-7, -2), (0, -3), (MIN, 1), (MIN, 2), (MAX, -1), (MAX, MIN)]
    out = _run_written(report, edges, engine)
    assert out.column("q").to_pylist() == [a // b for a, b in edges]
    assert out.column("m").to_pylist() == [a % b for a, b in edges]
    for bad in ([(1, 0)], [(MIN, -1)]):
        with pytest.raises(Exception, match="(?i)zero|overflow|64 bits"):
            _run_written(report, bad, engine)


def test_routes_from_polars(report: sv.Report) -> None:
    """Native on Polars; refused on Spark until the checker reports under
    Spark's profile (#1288), naming the reference as the way; refused on
    DuckDB by the transfer check, with the reason."""
    assert routes.choose(report, "polars").kind == "native"
    s = routes.choose(report, "spark")
    assert s.refused and "semantics='reference'" in s.reason, s
    r = routes.choose(report, "duckdb")
    assert r.refused and "division_type: polars gives FLOOR" in r.reason, r


# --- `%` of doubles ------------------------------------------------------------

#: The rows of polars-double-modulus: `x - y * floor(x / y)`, the divisor's sign,
#: and a zero remainder of +0.0 (`-0.0 % y` too).
DOUBLE_ROWS = [
    (7.0, -3.0, -2.0), (-7.0, 3.0, 2.0), (7.0, 3.0, 1.0), (-7.0, -3.0, -1.0),
    (5.5, -2.0, -0.5), (0.0, 3.0, 0.0), (-0.0, 3.0, 0.0), (-4.0, 2.0, 0.0), (49.0, 49.0, 0.0),
]  # fmt: skip


def _double_table() -> pa.Table:
    x, y, _ = zip(*DOUBLE_ROWS, strict=True)
    return pa.table({"x": pa.array(x, pa.float64()), "y": pa.array(y, pa.float64())})


def _double_report(con: sv.Connection, semantics: str, divisor) -> sv.Report:
    t = con.table("t")
    return sv.verify(
        t.select(m=t.x % (t.y if divisor is None else divisor)),
        requires={"t": [_.y != 0, _.x > -1e300, _.x < 1e300, _.y > -1e300, _.y < 1e300]},
        semantics=semantics,
    )


def test_double_modulus_floors_natively() -> None:
    """Under `semantics="polars"`, `%` of doubles by a column is Polars's own:
    the rows of polars-double-modulus (`Profile.polars_fmod`), zeros +0.0."""
    con = sv.connect()
    con.put("t", _double_table())
    report = _double_report(con, "polars", None)
    out = report.run(con, "polars", route="native").column("m").to_pylist()
    assert out == [r[2] for r in DOUBLE_ROWS]
    assert all(str(v) == str(float(r[2])) for v, r in zip(out, DOUBLE_ROWS, strict=True))
    assert report.routes["polars"].kind == "native"


@pytest.mark.parametrize(
    "divisor",
    [
        pytest.param(lambda t: 3.0, id="literal"),
        # `with_columns(w=lit(49.0))` keeps `w` a scalar (polars-scalar-divisor).
        pytest.param(lambda t: ibis.literal(49.0), id="projected literal"),
    ],
)
def test_double_modulus_by_a_scalar_is_refused(divisor) -> None:
    """A divisor that may reach the kernel as a scalar takes Polars's
    reciprocal kernel, where `49.0 % 49.0` is 49.0 (polars-scalar-divisor): the
    translation refuses it and says so."""
    con = sv.connect()
    con.put("t", _double_table())
    t = con.table("t")
    report = sv.verify(
        t.mutate(w=divisor(t)).select(m=_.x % _.w),
        requires={"t": [_.y != 0, _.x > -1e300, _.x < 1e300, _.y > -1e300, _.y < 1e300]},
        semantics="polars",
    )
    with pytest.raises(Exception, match="may be a scalar"):
        report.run(con, "polars")


def test_double_modulus_by_a_projected_column_is_native() -> None:
    """A column projected from a column stays one."""
    xs, ys = [7.0, -7.0, 5.5, 0.0, -0.0, 49.0], [3.0, 3.0, 2.0, 3.0, 3.0, 49.0]
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array(xs), "y": pa.array(ys)}))
    t = con.table("t")
    report = sv.verify(
        t.mutate(w=t.y * 1.0).select(m=_.x % _.w),
        requires={"t": [_.y >= 1.0, _.y <= 1000.0, _.x > -1e300, _.x < 1e300]},
        semantics="polars",
    )
    out = report.run(con, "polars", route="native").column("m").to_pylist()
    assert out == [x - y * math.floor(x / y) for x, y in zip(xs, ys, strict=True)]


def test_double_modulus_is_refused_under_the_reference() -> None:
    """The reference's `%` of doubles truncates (C's `fmod`): no exact form on
    Polars (#1270)."""
    con = sv.connect()
    con.put("t", _double_table())
    report = _double_report(con, "reference", None)
    with pytest.raises(Exception, match="polars-double-modulus"):
        report.run(con, "polars")
