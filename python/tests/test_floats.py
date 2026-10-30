"""Doubles and timestamps: contracts and incremental views."""

import datetime as dt
import math

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv

ERR = -9999.0
s1 = ibis.table({"ts": "timestamp", "value": "float64"}, name="s1")
s2 = ibis.table({"ts": "timestamp", "value": "float64"}, name="s2")


def windows(a, b):
    ca = a.filter((a.value != ERR) & ~a.value.isnan())
    cb = b.filter((b.value != ERR) & ~b.value.isnan())
    wide = ca.join(cb, ca.ts == cb.ts).select(ts=ca.ts, v1=ca.value, v2=cb.value)
    w0, w1 = wide.view(), wide.view()
    return w0.join(w1, w1.ts == w0.ts + ibis.interval(seconds=60)).select(
        t0=w0.ts, t1=w1.ts, v=w0.v1, s=w0.v1 * 2.0 + w1.v2
    )


def test_float_and_timestamp_contracts():
    report = sv.verify(
        windows(s1, s2),
        requires={"s1": [sv.unique("ts")], "s2": [sv.unique("ts")]},
        ensures=[
            _.v != ERR,
            ~_.v.isnan(),
            _.t1 > _.t0,
            "t1 - t0 = INTERVAL 60 SECOND",
            sv.unique("t0"),
            "t1 - t0 = INTERVAL 61 SECOND",  # wrong on purpose
        ],
    )
    assert [c.proved for c in report.ensures] == [True] * 5 + [False]
    assert report.facts["t0"] == "any timestamp"


def test_float_ranges_are_exact_at_the_boundary():
    pos = s1.filter(s1.value > 0.5).select("value")
    report = sv.verify(pos, ensures=[_.value >= 0.5, _.value > 0.5, _.value > 0.6])
    assert [c.proved for c in report.ensures] == [True, True, False]
    assert report.facts["value"] == "a double > 0.5"


def test_nan_is_largest_like_datafusion():
    # DataFusion orders NaN above every number, so `value > 0` keeps NaN rows.
    report = sv.verify(s1.filter(s1.value > 0).select("value"), ensures=[~_.value.isnan()])
    assert not report.proved


values = st.sampled_from([0.0, -0.0, 0.5, 1.5, ERR, math.nan, math.inf, -math.inf, 1e300, None])
minutes = st.integers(0, 4)


@pytest.mark.parametrize("engine", sv.ENGINES)
@settings(max_examples=25, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_incremental_view_with_floats_matches_recompute(engine, data):
    con = sv.connect()
    db = con
    t = lambda m: dt.datetime(2024, 1, 1, 0, m)  # noqa: E731
    rows = st.lists(st.tuples(minutes.map(t), values), max_size=5, unique_by=lambda r: r[0])
    for name in ["s1", "s2"]:
        sv.create_table(con, name, s1.schema(), data.draw(rows))
    view = sv.IncrementalView(con, windows(db.table("s1"), db.table("s2")), "w", engine)

    def same(a, b):
        # NaN != NaN, so compare the rows' text.
        return sorted(map(repr, a)) == sorted(map(repr, b))

    assert same(view.rows(), view.recompute())
    for _step in range(data.draw(st.integers(1, 3))):
        changes = {}
        for name in ["s1", "s2"]:
            current = sv.table_rows(con, name)
            pick = st.lists(st.sampled_from(current), unique=True, max_size=2)
            gone = data.draw(pick) if current else []
            taken = {r[0] for r in current} - {r[0] for r in gone}
            new = [r for r in data.draw(rows) if r[0] not in taken]
            changes[name] = sv.Changes(inserts=new, deletes=gone)
        view.apply(changes)
        assert same(view.rows(), view.recompute())


hr = ibis.table({"user_id": "int64", "ts": "timestamp", "bpm": "float64"}, name="hr")
sessions = ibis.table(
    {"user_id": "int64", "start": "timestamp", "end": "timestamp"}, name="sessions"
)


def in_session(h, w):
    valid = h.filter((h.bpm >= 30) & (h.bpm <= 230))
    return valid.join(
        w, (valid.user_id == w.user_id) & (valid.ts >= w.start) & (valid.ts < w.end)
    ).select(valid.user_id, valid.ts, valid.bpm, w.start, w.end)


def test_integer_constants_compared_with_doubles():
    # `bpm >= 30` reaches the plan with an integer 30; it means the double 30.0.
    report = sv.verify(in_session(hr, sessions), ensures=[_.bpm >= 30, _.bpm > 29.5, _.bpm > 31])
    assert [c.proved for c in report.ensures] == [True, True, False]
    assert report.facts["bpm"] == "a double ≥ 30.0 and ≤ 230.0"


def test_column_comparisons_imply_not_null():
    report = sv.verify(in_session(hr, sessions), ensures=[_.ts >= _.start, _.ts < _.end])
    assert report.proved


@pytest.mark.parametrize("engine", sv.ENGINES)
def test_incremental_view_with_integer_constants(engine):
    con = sv.connect()
    t = lambda m: dt.datetime(2024, 5, 1, 7, m)  # noqa: E731
    sv.create_table(con, "hr", hr.schema(), [(1, t(0), 72.0), (1, t(10), -1.0)])
    sv.create_table(con, "sessions", sessions.schema(), [(1, t(0), t(30))])
    view = sv.IncrementalView(con, in_session(con.table("hr"), con.table("sessions")), "v", engine)
    view.apply({"hr": sv.Changes(inserts=[(1, t(20), 160.0), (1, t(25), 0.0)])})
    assert [r[2] for r in view.rows()] == [72.0, 160.0]
    assert view.rows() == view.recompute()


@pytest.mark.parametrize("engine", sv.ENGINES)
def test_signed_zeros_are_different_rows(engine):
    """DataFusion keeps -0.0 and 0.0 apart; so must the view's bookkeeping."""
    con = sv.connect()
    t = dt.datetime(2024, 1, 1)
    sv.create_table(con, "s1", s1.schema(), [(t, -0.0)])
    table = con.table("s1")
    view = sv.IncrementalView(con, table.filter(table.value.notnull()), "v", engine)
    view.apply({"s1": sv.Changes(inserts=[(t, 0.0)], deletes=[(t, -0.0)])})
    assert repr(view.rows()) == repr(view.recompute()) == repr([(t, 0.0)])
