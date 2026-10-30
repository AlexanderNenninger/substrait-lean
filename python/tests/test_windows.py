"""Window functions: Lean's semantics agree with DataFusion, contracts see
through LAG/LEAD/ROW_NUMBER, and ties in the window order are refused."""

import json
import subprocess

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import (
    checker_path,
    connect,
    create_table,
    run_sql,
    run_substrait_json,
    substrait_json,
    to_sql,
)
from sverify.testing import canonical, inline_tables, lean_rows

SCHEMA = ibis.schema({"s": "int64", "t": "int64", "v": "int64"})

#: Window queries over `r(s, t, v)`; (s, t) is a key of every test table, so
#: each ORDER BY is total within its partition and the result is determined.
QUERIES = [
    "SELECT s, t, v, LAG(v) OVER (PARTITION BY s ORDER BY t) AS w FROM r",
    "SELECT s, t, LEAD(v, 2, -1) OVER (PARTITION BY s ORDER BY t DESC) AS w FROM r",
    "SELECT s, t, ROW_NUMBER() OVER (ORDER BY s, t NULLS FIRST) AS w FROM r",
    "SELECT t, LAG(t, 0) OVER (PARTITION BY s ORDER BY t DESC NULLS LAST) AS w FROM r",
    "SELECT s, t, LEAD(t) OVER (PARTITION BY s ORDER BY t) - t AS gap,"
    " ROW_NUMBER() OVER (PARTITION BY s ORDER BY t) AS rn FROM r WHERE v IS NOT NULL",
]


keyed_tables = st.lists(
    st.tuples(
        st.one_of(st.none(), st.integers(0, 2)),
        st.one_of(st.none(), st.integers(0, 6)),
        st.one_of(st.none(), st.integers(-5, 5)),
    ),
    max_size=10,
    unique_by=lambda r: (r[0], r[1]),
)


@pytest.mark.parametrize("sql", QUERIES)
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=keyed_tables)
def test_lean_semantics_match_datafusion(sql, rows):
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    expected = [tuple(r.values()) for r in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    assert canonical(lean_rows(json.dumps(plan))) == canonical(expected)


def test_written_window_plans_run_on_datafusion():
    con = connect()
    rows = [(1, 3, 10), (1, 1, 20), (2, 5, None), (1, 2, 30), (None, 4, 40)]
    create_table(con, "r", SCHEMA, rows)
    for sql in QUERIES:
        written = subprocess.run(
            [str(checker_path()), "--write", "/dev/stdin"],
            input=substrait_json(con, sql),
            capture_output=True,
            text=True,
            check=True,
        ).stdout
        got = [tuple(r.values()) for r in run_substrait_json(con, written).to_pylist()]
        want = [tuple(r.values()) for r in run_sql(con, sql).to_pylist()]
        assert canonical(got) == canonical(want), sql


readings = ibis.table({"sensor": "int64", "ts": "timestamp", "value": "float64"}, name="readings")
by_sensor = ibis.window(group_by=readings.sensor, order_by=readings.ts)
KEYED = {"readings": [sv.unique("sensor", "ts"), _.sensor.notnull(), _.ts.notnull()]}


def with_neighbours(r):
    valid = r.filter(r.value.notnull() & (r.value > 0))
    w = ibis.window(group_by=valid.sensor, order_by=valid.ts)
    return valid.select(
        valid.sensor,
        valid.ts,
        valid.value,
        prev_ts=valid.ts.lag().over(w),
        prev=valid.value.lag().over(w),
        next_ts=valid.ts.lead().over(w),
        rn=ibis.row_number().over(w),
    )


def test_window_postconditions_are_proved():
    report = sv.verify(
        with_neighbours(readings),
        requires=KEYED,
        ensures=[
            _.rn >= 0,
            _.prev.isnull() | (_.prev > 0),
            _.prev_ts.isnull() | (_.prev_ts <= _.ts),
            _.next_ts.isnull() | (_.next_ts >= _.ts),
            sv.unique("sensor", "ts"),
        ],
    )
    assert report.proved, str(report)
    assert report.deterministic
    assert report.facts["rn"] == "an integer ≥ 0"
    assert report.facts["prev"] == "a double > 0.0 or NULL"


def test_lag_is_null_on_the_first_row():
    report = sv.verify(with_neighbours(readings), requires=KEYED, ensures=[_.prev > 0])
    assert report.unproved[0].value == "TRUE or NULL"


def test_ties_in_the_window_order_are_refused():
    """Without a key on (sensor, ts), two readings may share a timestamp and
    DataFusion picks which one is LAG's: nothing is claimed."""
    report = sv.verify(
        with_neighbours(readings),
        requires={"readings": [_.sensor.notnull(), _.ts.notnull()]},
        ensures=[_.rn >= 0, sv.unique("sensor", "ts")],
    )
    assert not report.deterministic
    assert not report.proved
    assert all(c.value.startswith("undetermined") for c in report.ensures)


def test_a_key_on_the_order_column_alone_suffices():
    report = sv.verify(
        with_neighbours(readings), requires={"readings": [sv.unique("ts")]}, ensures=[_.rn >= 0]
    )
    assert report.proved


def test_strict_order_under_a_key():
    """With a key on (sensor, ts), the previous reading is strictly earlier
    and the gap is positive, also through a computed column."""

    @sv.transform(
        requires=KEYED,
        ensures=[
            _.prev_ts.isnull() | (_.prev_ts < _.ts),
            _.next_ts.isnull() | (_.next_ts > _.ts),
            _.gap.isnull() | (_.gap > ibis.interval(seconds=0)),
        ],
    )
    def gaps(readings):
        n = with_neighbours(readings)
        return n.mutate(gap=n.ts - n.prev_ts)

    gaps(readings)
    report = gaps.last_report
    assert report is not None and report.proved, str(report)
    assert report.facts["gap"] == "an interval ≥ 0:00:00.000001 or NULL"


def test_strict_order_needs_an_offset():
    """`LAG(ts, 0)` is the row itself, and one microsecond is all a key gives."""
    w = ibis.window(group_by=readings.sensor, order_by=readings.ts)
    e = readings.mutate(
        same=readings.ts.lag(0).over(w), gap=readings.ts - readings.ts.lag().over(w)
    )
    report = sv.verify(
        e,
        requires=KEYED,
        ensures=[_.same < _.ts, _.gap.isnull() | (_.gap >= ibis.interval(seconds=1))],
    )
    assert [c.proved for c in report.ensures] == [False, False]


def test_windows_are_not_incremental():
    con = connect()
    create_table(con, "readings", readings.schema(), [])
    with pytest.raises(sv.NotIncremental):
        sv.IncrementalView(con, to_sql(with_neighbours(readings)), "v")
