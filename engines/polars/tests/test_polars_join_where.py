"""A join without an equality key on Polars: its range comparisons go to a
range join (`join_where`), the rest of the condition filters the matches as
before (#1447 item 6, rulings 162 and 164).

The range join gives the pairs a cross join and a filter give
(polars-join-where), so every result is the old path's. Where a conjunct
that is not a range comparison may raise, the run raises on a pair that
passes the range comparisons and returns on one that fails them: such a pair
is in no result the reference allows (`isTrue_and3`, D16)."""

from __future__ import annotations

import functools
import math
import re

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.engine import plan_json_over, written_plan
from sverify_polars import engine as polars_engine

T = ibis.table({"a": "float64", "i": "int64"}, name="t")
U = ibis.table({"b": "float64", "j": "int64"}, name="u")

CONDITIONS = {
    "gt": T.a > U.b,
    "ge": T.a >= U.b,
    "lt mirrored": U.b < T.a,
    "two": (T.i >= U.j) & (T.i < U.j + 3),
    "range and other": (T.a > U.b) & ((T.i + U.j) % 2 == 0),
    "not a range": (T.a > U.b) | (T.i == U.j),
}
HOWS = ("inner", "left", "semi", "anti")


@functools.cache
def plan(cond: str, how: str) -> str:
    return written_plan(plan_json_over({}, T.join(U, CONDITIONS[cond], how=how)))


def tables(ts: list[tuple], us: list[tuple]) -> dict[str, pa.Table]:
    return {
        "t": pa.table(
            {"a": [r[0] for r in ts], "i": [r[1] for r in ts]}, schema=T.schema().to_pyarrow()
        ),
        "u": pa.table(
            {"b": [r[0] for r in us], "j": [r[1] for r in us]}, schema=U.schema().to_pyarrow()
        ),
    }


def cross_and_filter(monkeypatch: pytest.MonkeyPatch, p: str, ts: dict) -> pa.Table:
    """The old path: every pair, then the condition."""
    with monkeypatch.context() as m:
        m.setattr(polars_engine.Translator, "range_conjunct", lambda *_: None)
        return polars_engine.run(p, ts)


def rows(t: pa.Table) -> list[tuple]:
    return [
        tuple(("nan",) if isinstance(v, float) and math.isnan(v) else v for v in r.values())
        for r in t.to_pylist()
    ]


doubles = st.one_of(
    st.none(), st.sampled_from([0.0, -0.0, 1.5, -1.5, math.nan, math.inf, -math.inf])
)
ints = st.one_of(st.none(), st.integers(-3, 3))


@settings(
    max_examples=100, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(
    cond=st.sampled_from(sorted(CONDITIONS)),
    how=st.sampled_from(HOWS),
    ts=st.lists(st.tuples(doubles, ints), max_size=6),
    us=st.lists(st.tuples(doubles, ints), max_size=6),
)
def test_the_range_join_gives_the_cross_joins_rows(monkeypatch, cond, how, ts, us):
    """Old path against new on the same inputs: NULLs, NaN, both zeros,
    infinities, duplicates and empty sides; inner, left, semi and anti."""
    p, data = plan(cond, how), tables(ts, us)
    assert rows(polars_engine.run(p, data)) == rows(cross_and_filter(monkeypatch, p, data))


@pytest.mark.parametrize("cond", ["gt", "two"])
def test_a_range_conjunct_runs_as_a_streaming_range_join(cond):
    """The translation's frame plans a range join, which the streaming
    engine runs natively, with no in-memory fallback (polars-join-where)."""
    lf, _ = polars_engine._translate(plan(cond, "inner"), tables([(1.0, 1)], [(0.0, 0)]), True)
    dot = lf.show_graph(engine="streaming", plan_stage="physical", raw_output=True)
    labels = set(re.findall(r'label="([^"\\]*)', dot))
    assert "range-join" in labels and "cross-join" not in labels


def test_a_condition_without_a_range_comparison_keeps_the_cross_join():
    lf, _ = polars_engine._translate(
        plan("not a range", "inner"), tables([(1.0, 1)], [(0.0, 0)]), True
    )
    dot = lf.show_graph(engine="streaming", plan_stage="physical", raw_output=True)
    assert "cross-join" in set(re.findall(r'label="([^"\\]*)', dot))


# A conjunct that raises on a zero divisor beside the range comparison.
RAISING = (T.a > U.b) & ((T.i // (T.i - U.j)) > 0)


@pytest.mark.parametrize("how", HOWS)
@pytest.mark.parametrize(
    ("a", "b"),
    [(1.0, 2.0), (None, 2.0), (1.0, None), (math.nan, math.nan), (1.0, math.nan)],
    ids=["below", "NULL left", "NULL right", "NaN against NaN", "below NaN"],
)
def test_a_pair_that_fails_the_range_comparison_does_not_raise(how, a, b):
    """`a > b` is not TRUE for the one pair (NaN is above every number and
    equal to itself), so its zero divisor is in no allowed result: the run
    returns."""
    p = written_plan(plan_json_over({}, T.join(U, RAISING, how=how)))
    polars_engine.run(p, tables([(a, 1)], [(b, 1)]))


@pytest.mark.parametrize("how", HOWS)
def test_a_pair_that_passes_the_range_comparison_raises(monkeypatch, how):
    p = written_plan(plan_json_over({}, T.join(U, RAISING, how=how)))
    data = tables([(5.0, 1)], [(2.0, 1)])
    if how == "left":
        # The left join returns here on main too, by either path; DuckDB
        # raises (#1857). Until then it gives the old path's rows.
        old = cross_and_filter(monkeypatch, p, data)
        assert rows(polars_engine.run(p, data)) == rows(old)
        return
    with pytest.raises(Exception, match="divide by zero"):
        polars_engine.run(p, data)
