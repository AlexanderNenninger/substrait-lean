"""`Profile.polars` (#444, `SubstraitLean/PolarsProfile.lean`): integer `//`
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

import sverify as sv
from sverify import _support, routes
from sverify.engine import written_plan

MIN, MAX = -(2**63), 2**63 - 1
#: `verify` infers `i >= -9 * 10**18` (so `MIN // -1` cannot overflow) and
#: `j != 0`.
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
    r = sv.verify(t.select(m=t.i % t.j, q=t.i // t.j), semantics="polars")
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
    """Lean writes the calls back with their option, and every engine but
    Polars refuses them."""
    plan = json.loads(written_plan(report.plan or ""))
    calls = []

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "scalarFunction" in node and _support.floors(node["scalarFunction"]):
                calls.append(node)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    assert len(calls) == 2
    for engine in ("duckdb", "datafusion", "spark"):
        with pytest.raises(ValueError, match="division_type FLOOR"):
            _support.check(plan, engine)
    _support.check(plan, "polars")


def test_routes_from_polars(report: sv.Report) -> None:
    """Native on Polars; refused on DuckDB, with the reason."""
    assert routes.choose(report, "polars").kind == "native"
    r = routes.choose(report, "duckdb")
    assert r.refused and "division_type FLOOR" in r.reason
