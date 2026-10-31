"""`date_part` and `date_trunc`.

* Lean's semantics (`SubstraitLean/Time.lean`) agrees with DataFusion, also
  for timestamps before 1970, at the ends of the years `chrono` represents
  (where `date_part` becomes NULL) and of DataFusion's nanosecond range.
* Truncating to a week, month, quarter or year outside that range is reported
  as an error, and DataFusion fails only where an error was reported.
* Polars and DuckDB, which run the plan Lean writes, agree with both, and
  fail where DataFusion does.
* Contracts use that years and truncations grow with the timestamp.
* Dates: adding days and months (clamped to the end of a shorter month),
  parts and truncation agree with DataFusion within the dates it computes,
  and fail where it does; Ibis's date operations its DataFusion SQL cannot
  run agree with Python's calendar.
* Times of day (`CAST(ts AS TIME)`, clock parts) and `strftime` agree with
  DataFusion within the years chrono represents, and fail outside them.
"""

import json
from datetime import date, datetime, timedelta

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import polars_engine
from sverify.engine import (
    connect,
    put_table,
    run_checker,
    run_plan,
    run_sql,
    substrait_json,
    to_sql,
    written_plan,
)
from sverify.ibis_substrait import Unsupported, to_substrait
from sverify.testing import canonical, inline_tables, lean_values

MIN, MAX = -(2**63), 2**63 - 1
#: DataFusion's nanosecond range, and the years `chrono` represents.
NS_MIN, NS_MAX = -9223372036854775, 9223372036854775
PART_MIN, PART_MAX = -8334601228800000000, 8210266876799999999
DAY = 86_400_000_000

PARTS = [
    "year",
    "quarter",
    "month",
    "week",
    "day",
    "hour",
    "minute",
    "second",
    "millisecond",
    "microsecond",
    "dow",
    "doy",
]
UNITS = [
    "microsecond",
    "millisecond",
    "second",
    "minute",
    "hour",
    "day",
    "week",
    "month",
    "quarter",
    "year",
]


def micros(out: pa.Table) -> list[tuple]:
    """Rows, with timestamps as microseconds (Python's datetime stops at 9999)."""
    columns = [c.cast(pa.int64()) if pa.types.is_timestamp(c.type) else c for c in out.columns]
    return [tuple(x.values()) for x in pa.table(columns, names=out.column_names).to_pylist()]


#: DuckDB's timestamps: `MAX` is its infinity, and it starts in 290309 BC.
DUCKDB_MIN = -9223372022400000000


def engines(sql: str, values: list[int | None]) -> dict[str, list[tuple]]:
    """Rows from Polars and DuckDB (on the timestamps DuckDB has)."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    plan = written_plan(substrait_json(con, sql))
    out = {"polars": micros(run_plan(con, plan, "polars"))}
    if all(v is None or DUCKDB_MIN <= v < MAX for v in values):
        out["duckdb"] = micros(run_plan(con, plan, "duckdb"))
    return out


def lean_and_datafusion(sql: str, values: list[int | None]) -> tuple[list, list]:
    """Rows from both; timestamps as microseconds."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    out = run_sql(con, sql)
    columns = [c.cast(pa.int64()) if pa.types.is_timestamp(c.type) else c for c in out.columns]
    out = pa.table(columns, names=out.column_names)
    expected = [tuple(x.values()) for x in out.to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": [(v,) for v in values]})
    return lean_values(json.dumps(plan)), expected


edges = st.sampled_from(
    [
        0,
        -1,
        1,
        MIN,
        MAX,
        PART_MIN - 1,
        PART_MIN,
        PART_MAX,
        PART_MAX + 1,
        NS_MIN,
        NS_MAX,
        951782400000005,
        -62135596800000000,
        1700000000123456,
    ]
)
anywhere = st.one_of(edges, st.integers(MIN, MAX), st.integers(-400 * 365 * DAY, 400 * 365 * DAY))


@settings(max_examples=40, deadline=None)
@given(values=st.lists(st.one_of(st.none(), anywhere), max_size=8))
def test_date_part_matches_datafusion(values):
    sql = "SELECT " + ", ".join(f"date_part('{p}', ts) AS {p}" for p in PARTS) + " FROM r"
    got, expected = lean_and_datafusion(sql, values)
    assert canonical(got) == canonical(expected)
    for engine, rows in engines(sql, values).items():
        assert canonical(rows) == canonical(expected), engine


@pytest.mark.parametrize("unit", UNITS)
@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(values=st.lists(st.one_of(st.none(), anywhere), max_size=8))
def test_date_trunc_matches_datafusion_where_no_issue(unit, values):
    sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
    # Only where there is no issue: DataFusion fails or wraps elsewhere.
    calendar = unit in ("week", "month", "quarter", "year")
    lo, hi = (NS_MIN + 400 * DAY, NS_MAX) if calendar else (MIN + DAY, MAX)
    values = [v for v in values if v is None or lo <= v <= hi]
    got, expected = lean_and_datafusion(sql, values)
    assert canonical(got) == canonical(expected)
    for engine, rows in engines(sql, values).items():
        assert canonical(rows) == canonical(expected), engine


@pytest.mark.parametrize("unit", ["week", "month", "quarter", "year"])
@pytest.mark.parametrize("ts", [NS_MAX + 1, NS_MIN - 1, NS_MIN + 1, MIN])
def test_calendar_truncation_outside_nanoseconds_fails(unit, ts):
    """`Issue.overflow`: where DataFusion fails (or computes garbage), the
    engines raise. (`NS_MIN + 1` is 1677-09-21 00:12, after its truncations.)"""
    sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
    with pytest.raises(polars_engine.Overflow):
        engines(sql, [ts])
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array([ts], pa.timestamp("us"))}))
    if ts >= DUCKDB_MIN:
        with pytest.raises(duckdb.Error, match="date_trunc"):
            run_plan(con, written_plan(substrait_json(con, sql)), "duckdb")


T = ibis.table({"ts": "timestamp", "n": "int64"}, name="t")


def kinds(expr) -> tuple[list[str], list[str]]:
    r = sv.verify(expr)
    return [i.kind for i in r.errors], [i.kind for i in r.warnings]


SINCE_2000 = T.ts.between(datetime(2000, 1, 1), datetime(2100, 1, 1))


@pytest.mark.parametrize(
    ("label", "expr", "errs", "warns"),
    [
        ("year", T.select(y=T.ts.year()), [], []),
        ("hour, unbounded", T.select(h=T.ts.truncate("h")), [], ["may wrap around"]),
        ("hour, bounded", T.filter(SINCE_2000).select(h=T.ts.truncate("h")), [], []),
        ("month, unbounded", T.select(m=T.ts.truncate("M")), ["overflow"], []),
        ("month, bounded", T.filter(SINCE_2000).select(m=T.ts.truncate("M")), [], []),
        ("week, bounded", T.filter(SINCE_2000).select(w=T.ts.truncate("W")), [], []),
    ],
)
def test_runtime_issues(label, expr, errs, warns):
    assert kinds(expr) == (errs, warns), label


def test_years_and_truncations_grow_with_the_timestamp():
    report = sv.verify(
        T.filter(T.ts >= datetime(2024, 1, 1), T.ts < datetime(2025, 1, 1)).select(
            y=T.ts.year(), m=T.ts.month(), d=T.ts.day(), t=T.ts.truncate("M")
        ),
        ensures=[_.y == 2024, _.m.between(1, 12), _.d.between(1, 31), _.t >= datetime(2024, 1, 1)],
    )
    assert report.proved, str(report)
    assert report.facts["y"] == "the integer 2024"


def test_parts_outside_chrono_may_be_null():
    report = sv.verify(T.select(y=T.ts.year()), ensures=[_.y.notnull()])
    assert not report.proved


#: Pipelines over `t(ts)`, on timestamps including the extremes.
PIPELINES = [
    T.select(m=T.ts.truncate("M")),
    T.select(y=T.ts.truncate("Y"), w=T.ts.truncate("W")),
    T.filter(T.ts >= datetime(1700, 1, 1)).select(m=T.ts.truncate("M")),
    T.filter(SINCE_2000).select(q=T.ts.truncate("Q")),
    T.select(d=T.ts.truncate("D"), y=T.ts.year()),
]


@pytest.mark.backend("datafusion")
@pytest.mark.parametrize("i", range(len(PIPELINES)))
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(values=st.lists(st.one_of(st.none(), anywhere), max_size=6))
def test_datafusion_fails_only_where_reported(i, values):
    expr = PIPELINES[i]
    reported, _warnings = kinds(expr)
    con = connect()
    put_table(
        con,
        "t",
        pa.table(
            {
                "ts": pa.array(values, pa.timestamp("us")),
                "n": pa.array([1] * len(values), pa.int64()),
            }
        ),
    )
    try:
        run_sql(con, to_sql(expr))
    except BaseException as e:  # noqa: BLE001 - DataFusion also panics here
        assert reported, f"DataFusion failed ({e}) but no error was reported"


# --------------------------------------------------------------------------
# Dates: arithmetic with days and months, parts and truncation

#: The days chrono represents (`Time.dayMin`, `Time.dayMax`), and those
#: within DataFusion's nanoseconds (`Time.nsDayMin`, `Time.nsDayMax`).
DAY_MIN, DAY_MAX = -96465292, 95026236
NS_DAY_MIN, NS_DAY_MAX = -106751, 106751

DATE_SQL = (
    "SELECT d + INTERVAL '1 month' AS a, d - INTERVAL '13 months' AS b, "
    "d + INTERVAL '3 days' AS c, d + INTERVAL '1 month 2 days' AS e, "
    "d - INTERVAL '1 month 2 days' AS f, d + INTERVAL '2 years' AS g, "
    "date_part('year', d) AS y, date_part('month', d) AS m, date_part('day', d) AS dd, "
    "date_part('dow', d) AS w, date_part('doy', d) AS doy, date_part('week', d) AS wk FROM r"
)
TRUNC_SQL = (
    "SELECT date_trunc('week', d) AS w, date_trunc('month', d) AS m, "
    "date_trunc('quarter', d) AS q, date_trunc('year', d) AS y FROM r"
)


def days_of(out: pa.Table) -> list[tuple]:
    """Rows, with dates as days and timestamps as whole days."""
    columns = []
    for c in out.columns:
        if pa.types.is_date(c.type):
            c = c.cast(pa.int32()).cast(pa.int64())
        elif pa.types.is_timestamp(c.type):
            us = c.cast(pa.timestamp("us")).cast(pa.int64()).to_pylist()
            c = pa.array([None if v is None else v // DAY for v in us], pa.int64())
        columns.append(c)
    return [tuple(x.values()) for x in pa.table(columns, names=out.column_names).to_pylist()]


def date_runs(sql: str, values: list[int | None]) -> dict[str, list[tuple]]:
    """Rows from DataFusion running `sql`, from Lean's semantics of its plan
    and from Polars and DuckDB running the plan Lean writes."""
    con = connect()
    put_table(con, "r", pa.table({"d": pa.array(values, pa.int32()).cast(pa.date32())}))
    plan = json.loads(substrait_json(con, sql))
    written = written_plan(json.dumps(plan))
    inline_tables(plan, {"r": [(v,) for v in values]})
    return {
        "datafusion": days_of(run_sql(con, sql)),
        "lean": lean_values(json.dumps(plan)),
        "polars": days_of(run_plan(con, written, "polars")),
        "duckdb": days_of(run_plan(con, written, "duckdb")),
    }


day_edges = st.sampled_from(
    [0, -1, 19753, 19782, 19813, 11016, 10957, -719162, 2932896, DAY_MIN + 800, DAY_MAX - 800]
)
dates = st.one_of(
    day_edges, st.integers(-800_000, 3_000_000), st.integers(DAY_MIN + 800, DAY_MAX - 800)
)


@settings(max_examples=25, deadline=None)
@given(values=st.lists(st.one_of(st.none(), dates), max_size=8))
def test_date_arithmetic_matches_datafusion(values):
    """Months clamp to the end of a shorter month and come before days, as in
    DataFusion; Polars and DuckDB agree."""
    runs = date_runs(DATE_SQL, values)
    expected = canonical(runs.pop("datafusion"))
    for engine, rows in runs.items():
        assert canonical(rows) == expected, engine


@settings(max_examples=30, deadline=None)
@given(values=st.lists(st.one_of(st.none(), st.integers(NS_DAY_MIN + 400, NS_DAY_MAX)), max_size=8))
def test_date_trunc_of_dates_matches_datafusion(values):
    """Within DataFusion's nanoseconds, where it truncates dates correctly."""
    runs = date_runs(TRUNC_SQL, values)
    expected = canonical(runs.pop("datafusion"))
    for engine, rows in runs.items():
        assert canonical(rows) == expected, engine


@pytest.mark.parametrize(
    ("sql", "d"),
    [
        ("SELECT d + INTERVAL '1 day' AS x FROM r", DAY_MAX),
        ("SELECT d - INTERVAL '1 day' AS x FROM r", DAY_MIN),
        ("SELECT d + INTERVAL '1 month' AS x FROM r", DAY_MAX - 10),
        ("SELECT d + INTERVAL '1 day' AS x FROM r", DAY_MAX + 5),
        ("SELECT date_trunc('month', d) AS x FROM r", NS_DAY_MAX + 1),
        ("SELECT date_trunc('day', d) AS x FROM r", NS_DAY_MIN - 1),
    ],
)
def test_dates_outside_chrono_fail(sql, d):
    """`rangeIssue`: where DataFusion panics (or truncates in wrapped
    nanoseconds), the checker reports an error and the engines raise."""
    con = connect()
    put_table(con, "r", pa.table({"d": pa.array([d], pa.int32()).cast(pa.date32())}))
    report = sv.verify(sql, tables={"r": ibis.schema({"d": "date"})})
    assert "overflow" in [i.kind for i in report.errors]
    written = written_plan(substrait_json(con, sql))
    with pytest.raises(polars_engine.Overflow):
        run_plan(con, written, "polars")
    with pytest.raises(duckdb.Error, match="sverify"):
        run_plan(con, written, "duckdb")


D = ibis.table({"d": "date", "ts": "timestamp", "n": "int64"}, name="t")


@st.composite
def d_rows(draw: st.DrawFn) -> list[tuple]:
    n = draw(st.integers(0, 6))
    day = st.one_of(st.none(), st.integers(-200_000, 200_000))
    # Within Python's years 1 to 9999.
    us = st.one_of(st.none(), st.integers(-(10**13), 10**13), st.integers(-6 * 10**16, 2 * 10**17))
    count = st.one_of(st.none(), st.integers(-1000, 1000))
    return [(draw(day), draw(us), draw(count)) for _ in range(n)]


def python_date(days: int) -> date:
    return date(1970, 1, 1) + timedelta(days=days)


def reference(d: int | None, ts: int | None, n: int | None) -> tuple:
    """What Ibis means by the operations its DataFusion SQL cannot run."""
    if ts is None:
        epoch = ms = us_ = iso_ts = None
    else:
        # Whole seconds, rounding toward zero.
        epoch = ts // 10**6 + (1 if ts < 0 and ts % 10**6 else 0)
        us_ = ts % 10**6
        ms = us_ // 1000
        iso_ts = python_date(ts // DAY).isocalendar().year
    if d is None:
        iso = delta = back = None
    else:
        iso = python_date(d).isocalendar().year
        delta = d - 19727
        back = None if n is None else d - n
    return (epoch, ms, us_, iso_ts, iso, delta, back)


@settings(max_examples=40, deadline=None)
@given(rows=d_rows())
def test_ibis_temporal_ops_match_python(rows):
    """The operations Ibis's DataFusion SQL does not run
    (`coverage.NO_DATAFUSION_SQL`), against Python's calendar."""
    expr = D.select(
        e=D.ts.epoch_seconds(),
        ms=D.ts.millisecond(),
        us=D.ts.microsecond(),
        it=D.ts.iso_year(),
        i=D.d.iso_year(),
        k=D.d.delta(ibis.literal(date(2024, 1, 5)), unit="day"),
        b=D.d - D.n.as_interval("D"),
    )
    plan = inline_tables(to_substrait(expr), {"t": rows})
    assert lean_values(json.dumps(plan)) == [reference(*r) for r in rows]


def test_comparing_durations_with_days_is_refused():
    """DataFusion compares a duration with `INTERVAL '3 days'` as (months,
    days, nanoseconds): four days are not more than three. In hours it
    compares as a number."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array([0, 4 * DAY], pa.timestamp("us"))}))
    sql = "SELECT ts FROM r WHERE ts - TIMESTAMP '1970-01-01 00:00:00' > INTERVAL '{}'"
    assert run_sql(con, sql.format("3 days")).num_rows == 0
    code, out, err = run_checker((), substrait_json(con, sql.format("3 days")))
    assert code != 0 and "interval of days or months" in out + err
    assert run_sql(con, sql.format("72 hours")).num_rows == 1
    assert run_checker((), substrait_json(con, sql.format("72 hours")))[0] == 0


def test_date_differences_are_refused():
    """DataFusion's `d - e` of dates is a duration in seconds, which it
    compares wrongly with days and fails to compare beyond ±2⁶³ ns; Ibis's
    `DateDiff` is written as `date_diff` (days) instead."""
    con = connect()
    put_table(con, "r", pa.table({"d": pa.array([126505], pa.int32()).cast(pa.date32())}))
    sql = "SELECT d FROM r WHERE d - DATE '1970-01-01' > INTERVAL '72 hours'"
    with pytest.raises(Exception, match="Overflowing"):
        run_sql(con, sql)
    code, out, err = run_checker((), substrait_json(con, sql))
    assert code != 0 and "date - date" in out + err


# --------------------------------------------------------------------------
# Times of day, formatting, timestamps from numbers

TOD_SQL = (
    "SELECT CAST(ts AS TIME) AS t, to_char(ts, '%Y-%m-%d %H:%M:%S') AS s, "
    "to_char(ts, '%F %T %j %%') AS f, date_part('hour', CAST(ts AS TIME)) AS h, "
    "date_part('microsecond', CAST(ts AS TIME)) AS us FROM r"
)


def tod_runs(sql: str, values: list[int | None]) -> dict[str, list[tuple]]:
    """As `date_runs`, over a timestamp column `ts`; times as microseconds."""

    def plain(out: pa.Table) -> list[tuple]:
        columns = []
        for c in out.columns:
            if pa.types.is_time(c.type):
                c = c.cast(pa.time64("us")).cast(pa.int64())
            columns.append(c)
        return [tuple(x.values()) for x in pa.table(columns, names=out.column_names).to_pylist()]

    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    plan = json.loads(substrait_json(con, sql))
    written = written_plan(json.dumps(plan))
    inline_tables(plan, {"r": [(v,) for v in values]})
    return {
        "datafusion": plain(run_sql(con, sql)),
        "lean": lean_values(json.dumps(plan)),
        "polars": plain(run_plan(con, written, "polars")),
        "duckdb": plain(run_plan(con, written, "duckdb")),
    }


#: Within chrono's years, and DuckDB's.
chrono = st.one_of(
    edges.filter(lambda v: PART_MIN <= v <= PART_MAX), st.integers(PART_MIN, PART_MAX)
)


@settings(max_examples=40, deadline=None)
@given(values=st.lists(st.one_of(st.none(), chrono), max_size=8))
def test_times_of_day_and_formats_match_datafusion(values):
    """`CAST(ts AS TIME)`, `to_char` (chrono's `%Y`: four digits, a sign
    outside 0 to 9999) and clock parts of a time agree with DataFusion."""
    runs = tod_runs(TOD_SQL, values)
    expected = canonical(runs.pop("datafusion"))
    for engine, rows in runs.items():
        assert canonical(rows) == expected, engine


@pytest.mark.parametrize(
    "sql", ["SELECT CAST(ts AS TIME) AS t FROM r", "SELECT to_char(ts, '%Y') AS t FROM r"]
)
def test_times_outside_chrono_fail(sql):
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array([PART_MIN - 1], pa.timestamp("us"))}))
    with pytest.raises(BaseException, match="(?i)convert|naive|datetime"):
        run_sql(con, sql)
    report = sv.verify(sql, tables={"r": ibis.schema({"ts": "timestamp"})})
    assert "overflow" in [i.kind for i in report.errors]
    with pytest.raises(polars_engine.Overflow):
        run_plan(con, written_plan(substrait_json(con, sql)), "polars")


def test_unsupported_formats_are_refused():
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array([0], pa.timestamp("us"))}))
    code, out, err = run_checker((), substrait_json(con, "SELECT to_char(ts, '%A %e') AS s FROM r"))
    assert code != 0 and "format" in out + err


def test_constructors_of_constants():
    """`ibis.date(2024, 2, 29)` and friends are constants; a bad date is
    refused (DataFusion's `make_date` fails), and so are columns."""
    expr = D.select(
        a=ibis.date(2024, 2, 29), b=ibis.timestamp(2024, 1, 2, 3, 4, 5), c=ibis.time(9, 30, 0)
    )
    plan = inline_tables(to_substrait(expr), {"t": [(None, None, None)]})
    got = lean_values(json.dumps(plan))
    assert got == [(19782, 1704164645000000, 34200000000)]
    with pytest.raises(Unsupported, match="day is out of range"):
        to_substrait(D.select(a=ibis.date(2024, 2, 30)))
    with pytest.raises(Unsupported, match="of columns"):
        to_substrait(D.select(a=ibis.date(D.n, 1, 1)))
