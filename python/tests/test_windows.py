"""Window functions: Lean's semantics agree with DataFusion and with DuckDB
(in Lean's row order), contracts see through LAG/LEAD/ROW_NUMBER, and ties in
the window order are refused. Ranks, NTILE (DataFusion's), frames over rows
and over the sort key's values, and aggregates over them agree with DataFusion
too, on tables with ties and NULL keys where the result does not depend on
the order of ties."""

import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import (
    connect,
    create_table,
    run_checker,
    run_sql,
    run_substrait_json,
    substrait_json,
    to_sql,
)
from sverify.errors import NotIncremental
from sverify.ibis_substrait import Unsupported, to_substrait
from sverify.incremental import IncrementalView
from sverify.testing import canonical, duckdb_rows, inline_tables, lean_rows, lean_values

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
    lean = lean_rows(json.dumps(plan))
    assert canonical(lean) == canonical(expected)
    assert duckdb_rows(json.dumps(plan)) == lean


def test_written_window_plans_run_on_datafusion():
    con = connect()
    rows = [(1, 3, 10), (1, 1, 20), (2, 5, None), (1, 2, 30), (None, 4, 40)]
    create_table(con, "r", SCHEMA, rows)
    for sql in QUERIES:
        code, written, err = run_checker(("--write",), substrait_json(con, sql))
        assert code == 0, err
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
    with pytest.raises(NotIncremental):
        IncrementalView(con, to_sql(with_neighbours(readings)), "v")


# --------------------------------------------------------------------------
# Ranks, NTILE, frames (`Window.lean`): any table, ties and NULL keys included

#: These depend on the sort keys' values only (ties are peers, RANGE frames
#: are conditions on the key), or on the whole partition: determined
#: whatever the order of ties.
TIE_FREE_QUERIES = [
    "SELECT s, t, RANK() OVER (PARTITION BY s ORDER BY t) AS a,"
    " DENSE_RANK() OVER (PARTITION BY s ORDER BY t DESC NULLS FIRST) AS b,"
    " PERCENT_RANK() OVER (PARTITION BY s ORDER BY t) AS c,"
    " CUME_DIST() OVER (ORDER BY t NULLS FIRST) AS d FROM r",
    "SELECT s, t, SUM(v) OVER (PARTITION BY s ORDER BY t) AS a,"
    " COUNT(v) OVER (PARTITION BY s) AS b, MAX(v) OVER (ORDER BY t DESC) AS c FROM r",
    "SELECT s, t, COUNT(*) OVER (ORDER BY t DESC RANGE BETWEEN CURRENT ROW AND CURRENT ROW) AS b,"
    " MAX(v) OVER (ORDER BY t RANGE BETWEEN CURRENT ROW AND UNBOUNDED FOLLOWING) AS c FROM r",
]
#: These follow the rows' order: determined where (s, t) is a key.
ORDERED_QUERIES = [
    "SELECT s, t, NTILE(3) OVER (PARTITION BY s ORDER BY t) AS a,"
    " NTILE(5) OVER (ORDER BY s, t) AS b FROM r",
    "SELECT s, t, SUM(v) OVER (PARTITION BY s ORDER BY t ROWS BETWEEN 1 PRECEDING AND 1 FOLLOWING)"
    " AS a, FIRST_VALUE(v) OVER (PARTITION BY s ORDER BY t ROWS 2 PRECEDING) AS b,"
    " LAST_VALUE(v) OVER (PARTITION BY s ORDER BY t) AS c,"
    " NTH_VALUE(v, 2) OVER (ORDER BY s, t ROWS BETWEEN UNBOUNDED PRECEDING AND 1 FOLLOWING) AS d,"
    " COUNT(v) OVER (ORDER BY s, t ROWS BETWEEN 2 FOLLOWING AND 3 FOLLOWING) AS e FROM r",
]

any_tables = st.lists(
    st.tuples(
        st.one_of(st.none(), st.integers(0, 2)),
        st.one_of(st.none(), st.integers(0, 6)),
        st.one_of(st.none(), st.integers(-5, 5)),
    ),
    max_size=10,
)


def lean_and_datafusion(sql: str, rows: list[tuple]) -> tuple[list, list]:
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    out = run_sql(con, sql)
    expected = [
        tuple((round(v, 6) if v != 0 else 0.0) if isinstance(v, float) else v for v in r.values())
        for r in out.to_pylist()
    ]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    return lean_values(json.dumps(plan)), expected


@pytest.mark.parametrize("sql", TIE_FREE_QUERIES)
@settings(max_examples=30, deadline=None)
@given(rows=any_tables)
def test_tie_free_windows_match_datafusion(sql, rows):
    lean, expected = lean_and_datafusion(sql, rows)
    assert canonical(lean) == canonical(expected)


@pytest.mark.parametrize("sql", ORDERED_QUERIES)
@settings(max_examples=30, deadline=None)
@given(rows=keyed_tables)
def test_ordered_windows_match_datafusion(sql, rows):
    lean, expected = lean_and_datafusion(sql, rows)
    assert canonical(lean) == canonical(expected)


def test_ntile_is_datafusions():
    """DataFusion's NTILE is ⌊i · min(k, n) / n⌋ + 1, not the SQL standard's
    buckets: 6 rows in 4 tiles are 1 1 2 3 3 4 (DuckDB: 1 1 2 2 3 4)."""
    sql = "SELECT t, NTILE(4) OVER (ORDER BY t) AS n FROM r"
    rows = [(0, t, 0) for t in range(6)]
    lean, expected = lean_and_datafusion(sql, rows)
    assert sorted(lean) == sorted(expected) == [(0, 1), (1, 1), (2, 2), (3, 3), (4, 3), (5, 4)]
    lean, _ = lean_and_datafusion(sql, rows[:2])
    assert sorted(lean) == [(0, 1), (1, 2)]


def test_sliding_double_aggregates_are_refused():
    """DataFusion averages a sliding frame that has become empty to NaN, sums
    its doubles by retracting rows (rounding differently), and keeps a MIN
    of a frame left with NULLs only: refused; a running frame (from UNBOUNDED
    PRECEDING) is fine."""
    con = connect()
    create_table(
        con, "f", ibis.schema({"t": "int64", "v": "float64"}), [(1, 0.0), (2, None), (3, None)]
    )
    sliding = (
        "SELECT t, AVG(v) OVER (ORDER BY t ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) AS a FROM f"
    )
    assert any(r["a"] != r["a"] for r in run_sql(con, sliding).to_pylist())  # NaN
    code, out, err = run_checker((), substrait_json(con, sliding))
    assert code != 0 and "sliding frame" in out + err
    running = "SELECT t, AVG(v) OVER (ORDER BY t ROWS UNBOUNDED PRECEDING) AS a FROM f"
    assert run_checker((), substrait_json(con, running))[0] == 0
    stale = "SELECT t, MIN(v) OVER (ORDER BY t ROWS CURRENT ROW) AS m FROM f"
    assert [r["m"] for r in run_sql(con, stale).to_pylist()] == [0.0, 0.0, 0.0]
    assert run_checker((), substrait_json(con, stale))[0] != 0


def test_window_sums_may_wrap():
    """An integer SUM over a frame wraps around in DataFusion (`Issue.sumWraps`)."""
    report = sv.verify("SELECT s, SUM(v) OVER (PARTITION BY s) AS w FROM r", tables={"r": SCHEMA})
    assert "may wrap around" in [i.kind for i in report.warnings]


R = ibis.table(SCHEMA, name="r")
#: RANGE frames with offsets, which only Ibis writes faithfully (DataFusion's
#: Substrait producer drops them: `engine.substrait_json` refuses those).
RANGE_EXPRS = [
    R.select(
        "s",
        "t",
        a=R.v.sum().over(ibis.range_window(group_by="s", order_by="t", preceding=2, following=1)),
        b=R.v.count().over(ibis.range_window(order_by=ibis.desc("t"), preceding=1, following=0)),
        c=R.v.max().over(ibis.range_window(order_by="t", preceding=0, following=3)),
    ),
]


@pytest.mark.parametrize("i", range(len(RANGE_EXPRS)))
@settings(max_examples=30, deadline=None)
@given(rows=any_tables)
def test_range_frames_match_datafusion(i, rows):
    expr = RANGE_EXPRS[i]
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    expected = [tuple(r.values()) for r in run_sql(con, to_sql(expr)).to_pylist()]
    lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"r": rows})))
    assert canonical(lean) == canonical(expected)


def test_sql_range_offsets_are_refused():
    con = connect()
    create_table(con, "r", SCHEMA, [])
    sql = "SELECT COUNT(*) OVER (ORDER BY t RANGE BETWEEN 1 PRECEDING AND CURRENT ROW) AS b FROM r"
    with pytest.raises(Unsupported, match="RANGE"):
        substrait_json(con, sql)
