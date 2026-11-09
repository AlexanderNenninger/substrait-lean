"""`Profile.polars` (#444, `engines/polars/Sverify/Polars/Profile.lean`): integer `//`
and `%` floor, as Polars's own do.

Lean proves that the checker's reading of a call that states
`division_type: FLOOR` is `Polars.floorDiv` and `Polars.floorMod` on 64-bit
integers (`Profile.polars_idiv`, `Profile.polars_imod`). That Polars computes
them is the trusted part, from its facts (polars-int-divide,
polars-int-modulus); these tests run it natively against Python's `//` and
`%`, which floor too.
"""

from __future__ import annotations

import json

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
