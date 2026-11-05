"""Window functions: Lean's semantics agree with DuckDB (also in Lean's row
order), DataFusion runs the plans Lean writes, contracts see through
LAG/LEAD/ROW_NUMBER, and ties in the window order are refused. Ranks, NTILE
(the SQL standard's), frames over rows and over the sort key's values, and
aggregates over them agree with DuckDB too, on tables with ties and NULL keys
where the result does not depend on the order of ties."""

import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import (
    collect,
    connect,
    create_table,
    run_checker,
    run_plan,
    run_substrait_json,
    substrait_json,
    written_plan,
)
from sverify.errors import NotIncremental
from sverify.ibis_substrait import to_substrait
from sverify.incremental import IncrementalView
from sverify.testing import (
    canonical,
    duckdb_ibis,
    duckdb_rows,
    duckdb_sql,
    inline_tables,
    lean_rows,
    lean_values,
)

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
def test_lean_semantics_match_duckdb(sql, rows):
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    expected = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
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
        want = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
        assert canonical(got) == canonical(want), sql


readings = ibis.table({"sensor": "int64", "ts": "timestamp", "value": "float64"}, name="readings")
by_sensor = ibis.window(group_by=readings.sensor, order_by=readings.ts)
#: `ts - prev_ts` fits in 64 bits for timestamps since 1970 (#202).
SINCE_1970 = _.ts >= ibis.timestamp("1970-01-01 00:00:00")
KEYED = {"readings": [sv.unique("sensor", "ts"), _.sensor.notnull(), _.ts.notnull(), SINCE_1970]}


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


@pytest.mark.slow
def test_ties_in_the_window_order_hold_for_every_order():
    """Without a key on (sensor, ts), two readings may share a timestamp and
    the engine picks which one is LAG's. A postcondition that holds for
    every order is proved (D24), one that needs the key is not, and the
    report names the window."""
    report = sv.verify(
        with_neighbours(readings),
        requires={"readings": [_.sensor.notnull(), _.ts.notnull()]},
        ensures=[_.rn >= 0, sv.unique("sensor", "ts")],
    )
    assert not report.deterministic
    rn, key = report.ensures
    assert rn.proved
    assert not key.proved and key.value == "not shown to be a key"
    assert [p.op for p in report._tie_places] == ["window"]
    assert "with no key among those columns" in report._tie_places[0].what


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
    report = gaps.report
    assert report is not None and report.proved, str(report)
    assert report.facts["gap"] == "an interval ≥ 0:00:00.000001 or NULL"


@pytest.mark.slow
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
        IncrementalView(con, ibis.to_sql(with_neighbours(readings), dialect="duckdb"), "v")


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


def lean_and_duckdb(sql: str, rows: list[tuple]) -> tuple[list, list]:
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    out = duckdb_sql(con, sql)
    expected = [
        tuple((round(v, 6) if v != 0 else 0.0) if isinstance(v, float) else v for v in r.values())
        for r in out.to_pylist()
    ]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    return lean_values(json.dumps(plan)), expected


@pytest.mark.parametrize("sql", TIE_FREE_QUERIES)
@settings(max_examples=30, deadline=None)
@given(rows=any_tables)
def test_tie_free_windows_match_duckdb(sql, rows):
    lean, expected = lean_and_duckdb(sql, rows)
    assert canonical(lean) == canonical(expected)


@pytest.mark.parametrize("sql", ORDERED_QUERIES)
@settings(max_examples=30, deadline=None)
@given(rows=keyed_tables)
def test_ordered_windows_match_duckdb(sql, rows):
    lean, expected = lean_and_duckdb(sql, rows)
    assert canonical(lean) == canonical(expected)


def test_ntile_is_the_sql_standards():
    """NTILE deals the rows out as the SQL standard says (`ntileOf`), as
    DuckDB does: the first `n % k` buckets hold one row more, so 6 rows in 4
    tiles are 1 1 2 2 3 4. (DataFusion's own NTILE gives 1 1 2 3 3 4.)"""
    sql = "SELECT t, NTILE(4) OVER (ORDER BY t) AS n FROM r"
    rows = [(0, t, 0) for t in range(6)]
    lean, expected = lean_and_duckdb(sql, rows)
    assert sorted(lean) == sorted(expected) == [(0, 1), (1, 1), (2, 2), (3, 2), (4, 3), (5, 4)]
    lean, _ = lean_and_duckdb(sql, rows[:2])
    assert sorted(lean) == [(0, 1), (1, 2)]


@pytest.mark.parametrize(("n", "k"), [(10, 4), (7, 3), (3, 5), (12, 5), (1, 1)])
def test_ntile_on_every_engine(n, k):
    """Lean's written plan: DuckDB and Spark write NTILE natively, Polars deals
    the buckets itself; DataFusion, whose NTILE differs, is refused."""
    con = connect()
    t = ibis.table({"t": "int64"}, name="w")
    create_table(con, "w", t.schema(), [(i,) for i in range(n)])
    expr = t.select("t", b=ibis.ntile(k).over(order_by=t.t)).order_by("t")
    plan = json.dumps(to_substrait(expr))
    q, r = divmod(n, k)
    # Ibis's ntile counts buckets from 0.
    expected = [(i, i // (q + 1) if i < r * (q + 1) else (i - r * (q + 1)) // q + r)
                for i in range(n)]  # fmt: skip
    rows = [(i,) for i in range(n)]
    assert sorted(lean_values(json.dumps(inline_tables(json.loads(plan), {"w": rows})))) == expected
    written = written_plan(plan)
    for engine in ("duckdb", "polars"):
        got = sorted(tuple(r.values()) for r in run_plan(con, written, engine).to_pylist())
        assert got == expected, engine
    with pytest.raises(Exception, match="DataFusion's NTILE"):
        run_plan(con, written, "datafusion")


@pytest.mark.backend("datafusion")
def test_sliding_double_aggregates_are_refused():
    """DataFusion averages a sliding frame that has become empty to NaN, sums
    its doubles by retracting rows (rounding differently), and keeps a MIN
    of a frame left with NULLs only: the checker verifies these plans, and
    `--write-datafusion` refuses them; a running frame (from UNBOUNDED
    PRECEDING) is fine (#506)."""
    con = connect()
    create_table(
        con, "f", ibis.schema({"t": "int64", "v": "float64"}), [(1, 0.0), (2, None), (3, None)]
    )
    sliding = (
        "SELECT t, AVG(v) OVER (ORDER BY t ROWS BETWEEN 1 PRECEDING AND CURRENT ROW) AS a FROM f"
    )
    assert any(
        r["a"] != r["a"] for r in collect(con._datafusion_session.sql(sliding)).to_pylist()
    )  # NaN
    assert run_checker((), substrait_json(con, sliding))[0] == 0
    code, out, err = run_checker(("--write-datafusion",), substrait_json(con, sliding))
    assert code != 0 and "sliding frame" in out + err
    running = "SELECT t, AVG(v) OVER (ORDER BY t ROWS UNBOUNDED PRECEDING) AS a FROM f"
    assert run_checker(("--write-datafusion",), substrait_json(con, running))[0] == 0
    stale = "SELECT t, MIN(v) OVER (ORDER BY t ROWS CURRENT ROW) AS m FROM f"
    assert [r["m"] for r in collect(con._datafusion_session.sql(stale)).to_pylist()] == [
        0.0,
        0.0,
        0.0,
    ]
    assert run_checker(("--write-datafusion",), substrait_json(con, stale))[0] != 0


def test_window_sums_may_wrap():
    """An integer SUM over a frame may leave 64 bits (`Issue.sumWraps`), where
    the reference raises. `verify` assumes it does not and the job checks it
    on the data; without inference it is an error."""
    query = "SELECT s, SUM(v) OVER (PARTITION BY s) AS w FROM r"
    report = sv.verify(query, tables={"r": SCHEMA})
    assert "SUM overflow" in [i.kind for i in report.assumed]
    strict = sv.verify(query, tables={"r": SCHEMA}, on_inferred="off")
    assert "SUM overflow" in [i.kind for i in strict.errors]
    assert not strict.proved


@pytest.mark.parametrize("fn", ["sum", "mean", "std", "var"])
def test_a_window_sum_of_both_infinities_is_a_domain_error(fn):
    """A frame holding `+inf` and `-inf` would sum to NaN, which no operation
    creates (#257): reported as for a grouped SUM, and ruled out by bounds.
    A variance's deviations are NaN for one infinity already."""
    r = ibis.table({"s": "int64", "x": "float64"}, name="r")
    w = ibis.window(group_by="s", order_by="x")
    expr = r.select("s", w=getattr(r.x, fn)().over(w))
    report = sv.verify(expr)
    assert "domain error" in [i.kind for i in report.errors]
    assert not report.proved
    bounded = sv.verify(expr, requires={"r": [_.x < 1e300, _.x > -1e300]})
    assert "domain error" not in [i.kind for i in bounded.issues]


R = ibis.table(SCHEMA, name="r")
#: RANGE frames with offsets, written by sverify's Ibis producer.
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
def test_range_frames_match_duckdb(i, rows):
    expr = RANGE_EXPRS[i]
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    expected = [tuple(r.values()) for r in duckdb_ibis(con, expr).to_pylist()]
    lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"r": rows})))
    assert canonical(lean) == canonical(expected)


def test_sql_range_offsets_are_the_sort_keys_distance():
    """A RANGE frame with an offset holds the rows whose sort key is within
    it (DataFusion's SQL producer dropped such offsets; the lift writes them)."""
    sql = (
        "SELECT t, COUNT(*) OVER (ORDER BY t RANGE BETWEEN 1 PRECEDING AND CURRENT ROW) AS b FROM r"
    )
    rows = [(0, t, 0) for t in (1, 2, 4, 5, 7)] + [(1, 2, 0)]
    lean, expected = lean_and_duckdb(sql, rows)
    assert sorted(lean) == sorted(expected) == [(1, 1), (2, 3), (2, 3), (4, 1), (5, 2), (7, 1)]


# --------------------------------------------------------------------------
# Rolling means, MIN over a sliding frame, a window sum of an expression (#506)

W = ibis.table(
    ibis.schema({"s": "int64", "k": "int64", "ts": "timestamp", "v": "float64", "q": "int64"}),
    name="w",
)
#: Ibis expressions the checker used to refuse: frames not from UNBOUNDED
#: PRECEDING with an AVG or MIN, and an aggregate of an expression.
SLIDING_EXPRS = [
    W.select("k", m=W.v.mean().over(ibis.window(order_by="ts", preceding=2, following=0))),
    W.select(
        "k",
        m=W.v.mean().over(
            ibis.range_window(order_by="ts", preceding=ibis.interval(minutes=5), following=0)
        ),
    ),
    W.select("k", a=W.q.min().over(ibis.window(order_by="ts", preceding=1, following=1))),
    W.select("k", "s", a=(W.q * 2).sum().over(group_by="s")),
    # `varOf` over a frame (#54), of a sample and of a population.
    W.select("k", d=W.v.std().over(ibis.window(order_by="ts", preceding=3, following=0))),
    W.select("k", "s", v=W.v.var(how="pop").over(group_by="s"), d=W.q.std().over(group_by="s")),
]

#: Distinct timestamps, `k` minutes in (the ROWS frames follow their order), doubles that
#: are halves (their sums are exact), and NULLs.
sliding_tables = st.lists(
    st.tuples(
        st.one_of(st.none(), st.integers(0, 2)),
        st.integers(0, 30),
        st.one_of(st.none(), st.integers(-8, 8).map(lambda k: k / 2)),
        st.one_of(st.none(), st.integers(-5, 5)),
    ),
    max_size=10,
    unique_by=lambda r: r[1],
)


def _rounded(rows: list[dict]) -> list[tuple]:
    return [
        tuple(round(v, 6) + 0.0 if isinstance(v, float) else v for v in r.values()) for r in rows
    ]


@pytest.mark.parametrize("i", range(len(SLIDING_EXPRS)))
@settings(max_examples=30, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(rows=sliding_tables)
def test_sliding_frames_and_expressions_match_duckdb(i, rows):
    """Lean's values, DuckDB running Ibis's own SQL, and DuckDB running the
    plan Lean writes agree (#506)."""
    from datetime import datetime, timedelta

    rows = [(s, m, datetime(2026, 1, 1) + timedelta(minutes=m), v, q) for s, m, v, q in rows]
    expr = SLIDING_EXPRS[i]
    con = connect()
    create_table(con, "w", W.schema(), rows)
    expected = _rounded(duckdb_ibis(con, expr).to_pylist())
    plan = to_substrait(expr)
    lean = lean_values(json.dumps(inline_tables(json.loads(json.dumps(plan)), {"w": rows})))
    assert canonical(lean) == canonical(expected)
    written = written_plan(json.dumps(plan))
    got = _rounded(run_plan(con, written, "duckdb").to_pylist())
    assert canonical(got) == canonical(expected)


def test_negative_ibis_offsets_count_the_other_way():
    """Ibis's `following=-1` is `1 PRECEDING`: the producer writes it so,
    where Ibis's own SQL writes `-1 FOLLOWING`, which DuckDB refuses
    (upstream/bugs/IB-4.json)."""
    w = ibis.window(group_by="s", order_by="t", preceding=3, following=-1)
    expr = R.select("s", "t", a=R.v.sum().over(w))
    rows = [(0, t, t * 2) for t in range(6)] + [(1, 0, 5), (1, 1, None)]
    con = connect()
    create_table(con, "r", SCHEMA, rows)
    sql = (
        "SELECT s, t, SUM(v) OVER (PARTITION BY s ORDER BY t "
        "ROWS BETWEEN 3 PRECEDING AND 1 PRECEDING) AS a FROM r"
    )
    expected = [tuple(r.values()) for r in duckdb_sql(con, sql).to_pylist()]
    plan = to_substrait(expr)
    lean = lean_rows(json.dumps(inline_tables(plan, {"r": rows})))
    assert canonical(lean) == canonical(expected)
    got = [
        tuple(r.values())
        for r in run_plan(con, written_plan(json.dumps(plan)), "duckdb").to_pylist()
    ]
    assert canonical(got) == canonical(expected)
