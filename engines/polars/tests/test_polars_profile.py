"""`Profile.polars` (#444, `engines/polars/Sverify/Polars/Profile.lean`): `//` and
`%` floor, as Polars's own do.

Lean proves that the checker's reading of a call that states
`division_type: FLOOR` is `Polars.floorDiv` and `Polars.floorMod` on 64-bit
integers (`Profile.polars_idiv`, `Profile.polars_imod`). That Polars computes
them is the trusted part, from its facts (polars-int-divide,
polars-int-modulus); these tests run it against Python's `//` and `%`, which
floor too.

A `semantics="polars"` request is reported as pending (#271): the report is
the reference's, and the plan runs on Polars by the translated route, which
`Rel.polars_sound` licenses. The plan states `FLOOR`, and Polars's executor runs
its own `//` and `%` for it, whatever the route.
"""

from __future__ import annotations

import json
import math

import numpy as np
import polars as pl
import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import _support, routes
from sverify.engine import connect, put_table, run_plan, written_plan
from sverify.errors import ProfilePendingWarning

pytestmark = pytest.mark.filterwarnings("ignore::sverify.errors.ProfilePendingWarning")

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
    assert r.verdict == sv.Verdict.PROVED, str(r)
    return r


@settings(max_examples=50, deadline=None)
@given(rows=st.lists(st.tuples(dividends, divisors), min_size=1, max_size=20))
def test_floor_run_agrees_with_floor_division(report: sv.Report, rows) -> None:
    con = sv.connect()
    i, j = zip(*rows, strict=True)
    con.put("t", pa.table({"i": pa.array(i, pa.int64()), "j": pa.array(j, pa.int64())}))
    out = report.run(con, "polars")
    assert out.column("m").to_pylist() == [a % b for a, b in rows]
    assert out.column("q").to_pylist() == [a // b for a, b in rows]
    assert report.routes["polars"].kind == "translated"


def test_floor_run_over_mixed_signs(report: sv.Report) -> None:
    """A guard-free plan: its `//` and `%` give Polars's own values, floored."""
    rows = [(-7, 2), (7, -2), (-7, -2), (7, 2), (0, 3), (-1, MAX), (LOW, -1), (MAX, MIN)]
    con = sv.connect()
    i, j = zip(*rows, strict=True)
    con.put("t", pa.table({"i": pa.array(i, pa.int64()), "j": pa.array(j, pa.int64())}))
    assert report._guard_free
    out = report.run(con, "polars")
    assert out.column("m").to_pylist() == [a % b for a, b in rows]
    assert out.column("q").to_pylist() == [a // b for a, b in rows]


def test_the_native_route_is_refused_until_the_generated_lowering(report: sv.Report) -> None:
    """The report is the reference's, so `native` (verified under the engine's own
    profile) is not available (#271)."""
    con = sv.connect()
    con.put("t", pa.table({"i": pa.array([1], pa.int64()), "j": pa.array([1], pa.int64())}))
    with pytest.raises(routes.RouteError):
        report.run(con, "polars", route="native")


def test_a_polars_request_is_reported_as_pending() -> None:
    """The report is the reference's and the checker warns (#271)."""
    con = sv.connect()
    con.put("t", pa.table({"i": pa.array([1], pa.int64()), "j": pa.array([1], pa.int64())}))
    t = con.table("t")
    with pytest.warns(ProfilePendingWarning, match="polars"):
        r = sv.verify(
            t.select(q=t.i // t.j), requires={"t": [_.i >= LOW, _.j != 0]}, semantics="polars"
        )
    assert r.verdict == sv.Verdict.PROVED and r.semantics == "portable"


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
    """Translated on Polars, DuckDB and Spark: the report is the reference's
    until the checker reports under each engine's profile (#1288, #271)."""
    assert routes.choose(report, "polars").kind == "translated"
    assert routes.choose(report, "duckdb").kind == "translated"
    assert routes.choose(report, "spark").kind == "translated"


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


def test_double_modulus_floors() -> None:
    """Under `semantics="polars"`, `%` of doubles by a column is Polars's own:
    the rows of polars-double-modulus (`Profile.polars_fmod`), zeros +0.0."""
    con = sv.connect()
    con.put("t", _double_table())
    report = _double_report(con, "polars", None)
    out = report.run(con, "polars").column("m").to_pylist()
    assert out == [r[2] for r in DOUBLE_ROWS]
    assert all(str(v) == str(float(r[2])) for v, r in zip(out, DOUBLE_ROWS, strict=True))
    assert report.routes["polars"].kind == "translated"


def test_double_modulus_is_the_floor_formula_over_divide() -> None:
    """Polars's `%` of doubles is `x - d * floor(x / d)` over its own `/`,
    whichever kernel `/` takes (polars-double-modulus): no row differs, for a
    column and a literal divisor, in memory and on streaming."""
    rng = np.random.default_rng(0)
    n = 20_000
    x = rng.standard_normal(n) * 10.0 ** rng.integers(-5, 6, n)
    y = rng.standard_normal(n) * 10.0 ** rng.integers(-5, 6, n)
    df = pl.DataFrame({"x": x, "y": y})
    divisors = (pl.col("y"), pl.lit(7.3), pl.col("y") * 2, pl.col("y").abs(), pl.col("y").max())
    for divisor in divisors:
        for engine in ("in-memory", "streaming"):
            out = (
                df.lazy()
                .select(
                    m=pl.col("x") % divisor,
                    f=pl.col("x") - divisor * (pl.col("x") / divisor).floor(),
                )
                .collect(engine=engine)
            )
            both = out.filter(out["m"].is_not_nan() | out["f"].is_not_nan())
            assert (both["m"] == both["f"]).all(), (divisor, engine)


def test_double_modulus_by_a_literal_runs() -> None:
    """A literal divisor is `/` by a scalar (`approx`, polars-scalar-divisor): the
    written plan runs its four calls."""
    con = sv.connect()
    con.put("t", _double_table())
    t = con.table("t")
    report = sv.verify(
        t.select(m=t.x % 3.0),
        requires={"t": [_.x > -1e300, _.x < 1e300]},
        semantics="polars",
    )
    out = report.run(con, "polars").column("m").to_pylist()
    assert out == [x - 3.0 * math.floor(x / 3.0) for x, _y, _m in DOUBLE_ROWS]


@pytest.mark.parametrize(
    ("x", "y"),
    [
        (1.0, 0.0),  # a zero divisor: Polars gives NaN, the profile raises (D21)
        (1.0, math.inf),
        (math.inf, 3.0),
        (1e308, 1e-10),  # an intermediate that overflows: `-inf`
        (1.7976931348623157e308, 3.0),
        (2.0, 5e-324),  # a subnormal divisor
    ],
)
def test_double_modulus_error_rows_are_refused(x: float, y: float) -> None:
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array([x]), "y": pa.array([y])}))
    t = con.table("t")
    report = sv.verify(
        t.select(m=t.x % t.y), requires={"t": [_.y != 0]}, semantics="polars", on_inferred="warn"
    )
    with pytest.raises(Exception, match="(?i)zero|infinite|overflow|subnormal|domain|precondition"):
        report.run(con, "polars")


def test_double_modulus_is_refused_under_the_reference() -> None:
    """The reference's `%` of doubles truncates (C's `fmod`): no exact form on
    Polars (#1270)."""
    con = sv.connect()
    con.put("t", _double_table())
    report = _double_report(con, "portable", None)
    with pytest.raises(Exception, match="polars-double-modulus"):
        report.run(con, "polars")


def test_the_floor_templates_are_exported_from_lean() -> None:
    """The writer renders Lean's `FLOOR` templates (#1202): the export has the
    three, over fields 0 and 1."""
    from sverify.sql import lowering

    table = lowering.floor_table()
    assert set(table) == {"div", "mod", "fmod"}
    assert table["fmod"]["fn"] == "fsub"
    assert "if" in table["div"]
    assert "if" in table["mod"]
