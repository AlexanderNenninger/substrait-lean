"""ASOF joins: the same results as a reference implementation, Lean's
semantics agree with DataFusion and DuckDB, and the ASOF guarantees are proved."""

import datetime as dt
import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, create_table, run_sql, substrait_json, to_sql
from sverify.testing import canonical, duckdb_rows, inline_tables, lean_rows

INT_SCHEMA = {"device": "int64", "ts": "int64"}
T0 = dt.datetime(2024, 5, 1, 7, 0)


def reference(left, right, tolerance, how):
    """ASOF by definition: per left row, the latest right row of the same
    device at or before it, at most `tolerance` earlier."""
    out = []
    for d, t, a in left:
        matches = [
            r
            for r in right
            if d is not None
            and t is not None
            and r[0] == d
            and r[1] is not None
            and t - tolerance <= r[1] <= t
        ]
        if matches:
            best = max(matches, key=lambda r: r[1])
            out.append((d, t, a, best[1], best[2]))
        elif how == "left":
            out.append((d, t, a, None, None))
    return out


def keyed(value):
    return st.lists(
        st.tuples(
            st.one_of(st.none(), st.integers(0, 2)), st.one_of(st.none(), st.integers(0, 12)), value
        ),
        max_size=10,
        unique_by=lambda r: (r[0], r[1]),
    )


def tables(con, left, right, ts="int64"):
    create_table(con, "acc", ibis.schema({"device": "int64", "ts": ts, "ax": "int64"}), left)
    create_table(con, "gyr", ibis.schema({"device": "int64", "ts": ts, "gx": "int64"}), right)
    return con.table("acc"), con.table("gyr")


@pytest.mark.parametrize("how", ["left", "inner"])
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(left=keyed(st.integers(0, 9)), right=keyed(st.integers(0, 9)))
def test_asof_join_matches_reference(how, left, right):
    con = connect()
    acc, gyr = tables(con, left, right)
    result = sv.asof_join(acc, gyr, on="ts", by="device", tolerance=3, how=how)
    got = [tuple(r.values()) for r in result.to_pyarrow().to_pylist()]
    assert canonical(got) == canonical(reference(left, right, 3, how))


@pytest.mark.parametrize("how", ["left", "inner"])
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(left=keyed(st.integers(0, 9)), right=keyed(st.integers(0, 9)))
def test_lean_semantics_of_asof_match_datafusion(how, left, right):
    con = connect()
    acc, gyr = tables(con, left, right)
    sql = to_sql(sv.asof_join(acc, gyr, on="ts", by="device", tolerance=3, how=how))
    expected = [tuple(r.values()) for r in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"acc": left, "gyr": right})
    lean = lean_rows(json.dumps(plan))
    assert canonical(lean) == canonical(expected)
    assert duckdb_rows(json.dumps(plan)) == lean


acc_t = ibis.table({"device": "int64", "ts": "timestamp", "ax": "float64"}, name="acc")
gyr_t = ibis.table({"device": "int64", "ts": "timestamp", "gx": "float64"}, name="gyr")
TOL = ibis.interval(milliseconds=10)
KEYS = {
    "acc": [sv.unique("device", "ts"), _.device.notnull(), _.ts.notnull()],
    "gyr": [sv.unique("device", "ts")],
}
GUARANTEES = [
    sv.unique("device", "ts"),
    _.ts_right.isnull() | (_.ts_right <= _.ts),
    _.ts_right.isnull() | (_.ts_right >= _.ts - TOL),
]


@pytest.mark.parametrize("how", ["left", "inner"])
def test_asof_guarantees_are_proved(how):
    report = sv.verify(
        sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL, how=how),
        requires=KEYS,
        ensures=GUARANTEES,
    )
    assert report.proved, str(report)


def test_ties_on_the_right_are_refused():
    """Two gyroscope readings at the same instant: which one is "the latest"
    is up to DataFusion, so nothing is claimed."""
    report = sv.verify(
        sv.asof_join(acc_t, gyr_t, on="ts", by="device", tolerance=TOL),
        requires={"acc": KEYS["acc"]},
        ensures=GUARANTEES[:1],
    )
    assert not report.deterministic
    assert not report.proved


def test_aligning_100hz_with_130hz():
    """An accelerometer at 100 Hz and a gyroscope at 130 Hz: each
    accelerometer sample gets the latest gyroscope sample, at most 10 ms old."""
    con = connect()
    acc = [(1, T0 + dt.timedelta(microseconds=10_000 * i), float(i)) for i in range(100)]
    gyr = [(1, T0 + dt.timedelta(microseconds=round(1e6 * i / 130)), float(i)) for i in range(130)]
    create_table(con, "acc", acc_t.schema(), acc)
    create_table(con, "gyr", gyr_t.schema(), gyr)

    @sv.transform(requires=KEYS, ensures=GUARANTEES)
    def aligned(acc, gyr):
        return sv.asof_join(acc, gyr, on="ts", by="device", tolerance=TOL)

    rows = aligned(con.table("acc"), con.table("gyr")).to_pyarrow().to_pylist()
    report = aligned.last_report
    assert report is not None and report.proved
    assert len(rows) == 100
    # The gyroscope samples every 7.7 ms, so every sample finds a partner.
    assert all(r["ts_right"] is not None for r in rows)
    assert max(r["ts"] - r["ts_right"] for r in rows) <= dt.timedelta(milliseconds=10)
