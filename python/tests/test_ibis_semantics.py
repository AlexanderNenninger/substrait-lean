"""The meaning `verify` gives the Ibis operations whose result depends on the
Ibis backend (`docs/ibis-semantics.md`, chapter 15 of the notebook tour).

Each expression goes through the vendored producer, as `verify` compiles it,
and Lean's evaluation (`Rel.eval`) must give the documented rows: the meaning
is the producer's, not any backend's. Where the documented meaning is an
error, Lean's contract report must say so; where it is a refusal, the
producer or the checker must refuse.
"""

import json
import math

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, plan_json, put_table, run_checker
from sverify.ibis_substrait import Unsupported
from sverify.testing import inline_tables, lean_values

T = pa.table(
    {
        "a": pa.array([-7, 7, 5], pa.int64()),
        "b": pa.array([2, -2, 3], pa.int64()),
        "s": ["é", "🎉", None],
        "v": [2.5, -2.5, -0.0],
        "x": pa.array([1, None, 1], pa.int64()),
    }
)


@pytest.fixture(scope="module")
def con():
    c = connect()
    put_table(c, "t", T)
    return c


def lean(con, expr) -> list[tuple]:
    rows = [tuple(r.values()) for r in con.arrow["t"].to_pylist()]
    plan = inline_tables(json.loads(plan_json(con, expr)), {"t": rows})
    return lean_values(json.dumps(plan))


def close(got: list[tuple], expected: list[tuple]) -> bool:
    """Lean prints doubles with six decimals."""

    def same(g: object, e: object) -> bool:
        if isinstance(e, float) and isinstance(g, float):
            return math.isclose(g, e, abs_tol=1e-6)
        return g == e

    return len(got) == len(expected) and all(
        len(g) == len(e) and all(same(x, y) for x, y in zip(g, e, strict=True))
        for g, e in zip(got, expected, strict=True)
    )


#: (label, expression over `t`, the documented rows)
MEANINGS = [
    ("mod truncates", lambda t: t.select(r=t.a % t.b), [(-1,), (1,), (2,)]),
    ("floor division", lambda t: t.select(r=t.a // t.b), [(-4,), (-4,), (1,)]),
    ("length counts code points", lambda t: t.select(r=t.s.length()), [(1,), (1,), (None,)]),
    (
        "find is 0-based, NULL for NULL",
        lambda t: t.select(r=t.s.find("🎉")),
        [(-1,), (0,), (None,)],
    ),
    ("substr is 0-based", lambda t: t.select(r=t.s.substr(0, 1)), [("é",), ("🎉",), (None,)]),
    (
        "like escapes with a backslash",
        lambda t: t.select(r=t.s.like("\\%")),
        [(False,), (False,), (None,)],
    ),
    ("nunique skips NULL", lambda t: t.aggregate(r=t.x.nunique()), [(1,)]),
    ("round half away from zero", lambda t: t.select(r=t.v.round()), [(3,), (-3,), (0,)]),
    ("cast to int64 truncates", lambda t: t.select(r=t.v.cast("int64")), [(2,), (-2,), (0,)]),
    ("one zero", lambda t: t.select(r=t.v == 0.0), [(False,), (False,), (True,)]),
    ("== null is IS NULL", lambda t: t.select(r=t.x == ibis.null()), [(False,), (True,), (False,)]),
    (
        "row_number is 0-based",
        lambda t: t.select("a", r=ibis.row_number().over(order_by=t.a)).order_by("a"),
        [(-7, 0), (5, 1), (7, 2)],
    ),
    (
        "NULLs last in a descending sort",
        lambda t: t.select("x").order_by(ibis.desc("x")),
        [(1,), (1,), (None,)],
    ),
]


@pytest.mark.parametrize(("label", "build", "rows"), MEANINGS, ids=[m[0] for m in MEANINGS])
def test_producer_gives_the_documented_meaning(con, label, build, rows):
    got = lean(con, build(con.table("t")))
    assert close(got, rows), f"{label}: {got}"


def test_division_by_zero_is_an_error(con):
    t = con.table("t")
    for expr in (t.select(r=t.a % (t.b - t.b)), t.select(r=t.a // (t.b - t.b))):
        assert "division by zero" in [i.kind for i in sv.verify(expr).errors]


def test_cast_of_a_double_out_of_range_is_an_error(con):
    t = con.table("t")
    assert "cast out of range" in [i.kind for i in sv.verify(t.select(r=t.v.cast("int64"))).errors]


def test_refused_operations(con):
    t = con.table("t")
    code, out, err = run_checker((), plan_json(con, t.aggregate(r=t.v.max())))
    assert code != 0 and "max of doubles is not supported" in err + out
    ts = ibis.timestamp("2024-05-05 00:00:00")
    with pytest.raises(Unsupported, match="TimestampDelta"):
        plan_json(con, t.select(r=ts.delta(ibis.timestamp("2024-05-06 00:00:00"), unit="hour")))


def test_day_of_week_index_starts_on_monday(con):
    t = con.table("t")
    sunday, monday = ibis.timestamp("2024-05-05 00:00:00"), ibis.timestamp("2024-05-06 00:00:00")
    expr = t.select(s=sunday.day_of_week.index(), m=monday.day_of_week.index())
    assert lean(con, expr) == [(6, 0)] * 3
