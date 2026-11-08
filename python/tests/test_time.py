"""`date_part` and `date_trunc`.

* Lean's semantics (`SubstraitLean/Time.lean`) agrees with DuckDB, also for
  timestamps before 1970 and at the ends of the reference's timestamps,
  0001-01-01 to 9999-12-31 (D32).
* `date_part` and truncating to a week, month, quarter or year outside that
  range are reported as errors, and DataFusion running the plan fails only
  where an error was reported.
* Polars and DuckDB, which run the plan Lean writes, agree with Lean, and
  raise outside the range.
* Contracts use that years and truncations grow with the timestamp.
* Dates: adding days and months (clamped to the end of a shorter month),
  parts and truncation give Lean's rows on Polars and DuckDB, and fail
  outside the reference's dates; Ibis's date operations that
  DataFusion's own SQL cannot run agree with Python's calendar.
* Times of day (`CAST(ts AS TIME)`, clock parts) and `strftime` (chrono's
  formats) give Lean's rows on Polars and DuckDB within the reference's
  timestamps, Lean's agree with Python's calendar, and they fail outside
  them.
* Time-based windows mean what Polars' `rolling_sum_by` and
  `group_by_dynamic` compute.
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
from sverify import duckdb_engine, polars_engine
from sverify.engine import (
    connect,
    put_table,
    run_checker,
    run_plan,
    substrait_json,
    written_plan,
)
from sverify.errors import UnsupportedError
from sverify.ibis_substrait import Unsupported, to_substrait, to_substrait_json
from sverify.testing import canonical, duckdb_sql, inline_tables, lean_values

MIN, MAX = -(2**63), 2**63 - 1
#: The reference's timestamps, 0001-01-01 to 9999-12-31 (`Time.tsMin`,
#: `Time.tsMax`, D32), and DataFusion's nanoseconds, which are inside them.
TS_MIN, TS_MAX = -62135596800000000, 253402300799999999
NS_MIN, NS_MAX = -9223372036854775, 9223372036854775
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
    plan = written_plan(substrait_json(con, sql, semantics="duckdb"))
    out = {"polars": micros(run_plan(con, plan, "polars"))}
    if all(v is None or DUCKDB_MIN <= v < MAX for v in values):
        out["duckdb"] = micros(run_plan(con, plan, "duckdb"))
    return out


def lean_and_duckdb(sql: str, values: list[int | None]) -> tuple[list, list]:
    """Rows from both; timestamps as microseconds."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    out = duckdb_sql(con, sql)
    columns = [c.cast(pa.int64()) if pa.types.is_timestamp(c.type) else c for c in out.columns]
    out = pa.table(columns, names=out.column_names)
    expected = [tuple(x.values()) for x in out.to_pylist()]
    plan = inline_tables(
        json.loads(substrait_json(con, sql, semantics="duckdb")), {"r": [(v,) for v in values]}
    )
    return lean_values(json.dumps(plan)), expected


edges = st.sampled_from(
    [
        0,
        -1,
        1,
        MIN,
        MAX,
        TS_MIN - 1,
        TS_MIN,
        TS_MAX,
        TS_MAX + 1,
        NS_MIN,
        NS_MAX,
        951782400000005,
        -62135596800000000,
        1700000000123456,
    ]
)
#: Timestamps a source can hold: the reference's 0001 to 9999 (D32); a read of
#: one outside fails (`test_timestamps_outside_the_range_fail_the_read`).
anywhere = st.one_of(
    edges.filter(lambda v: TS_MIN <= v <= TS_MAX),
    st.integers(TS_MIN, TS_MAX),
    st.integers(-400 * 365 * DAY, 400 * 365 * DAY),
)


@settings(max_examples=40, deadline=None)
@given(values=st.lists(st.one_of(st.none(), anywhere), max_size=8))
def test_date_part_matches_duckdb(values):
    # Outside the reference's timestamps, Lean reports an overflow
    # (`test_times_outside_the_range_fail`); DuckDB computes there.
    values = [v for v in values if v is None or TS_MIN <= v <= TS_MAX]
    sql = "SELECT " + ", ".join(f"date_part('{p}', ts) AS {p}" for p in PARTS) + " FROM r"
    got, expected = lean_and_duckdb(sql, values)
    assert canonical(got) == canonical(expected)
    for engine, rows in engines(sql, values).items():
        assert canonical(rows) == canonical(expected), engine


@pytest.mark.slow
@pytest.mark.parametrize("unit", UNITS)
@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(values=st.lists(st.one_of(st.none(), anywhere), max_size=8))
def test_date_trunc_matches_duckdb_where_no_issue(unit, values):
    sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
    # Only where there is no issue: DataFusion fails or wraps elsewhere.
    # DuckDB reads ±(2⁶³ - 1) as the timestamps ±infinity, which it does not
    # truncate (#240).
    calendar = unit in ("week", "month", "quarter", "year")
    lo, hi = (TS_MIN, TS_MAX) if calendar else (MIN + DAY, MAX - 1)
    values = [v for v in values if v is None or lo <= v <= hi]
    got, expected = lean_and_duckdb(sql, values)
    assert canonical(got) == canonical(expected)
    for engine, rows in engines(sql, values).items():
        assert canonical(rows) == canonical(expected), engine


#: D32's probe points, each at 23:59:59.999999: the ends of the reference's
#: timestamps, leap days (1900 is not a leap year), and both sides of the
#: Gregorian switch, which the proleptic calendar does not skip. The facts
#: `<engine>-calendar-range` record the same rows on DuckDB, Polars and Spark.
D32_POINTS: dict[str, int | None] = {
    "0001-01-01": -62135510400000001,
    "0004-02-29": -62035804800000001,
    "1582-10-04": -12220156800000001,
    "1582-10-15": -12219206400000001,
    "1600-02-29": -11670912000000001,
    "1900-02-28": -2203891200000001,
    "1900-03-01": -2203804800000001,
    "2000-02-29": 951868799999999,
    "9999-12-31": 253402300799999999,
}


def test_d32_probe_points():
    """At D32's probe points, Lean, DuckDB and Polars give the same calendar
    parts and truncations: 0001-01-01 is a Monday, its own week; the week of
    9999-12-31 starts 9999-12-27, in ISO week 52."""
    values = list(D32_POINTS.values())
    sql = (
        "SELECT "
        + ", ".join(f"date_trunc('{u}', ts) AS t_{u}" for u in ("week", "month", "quarter", "year"))
        + ", "
        + ", ".join(
            f"date_part('{p}', ts) AS {p}"
            for p in ("year", "quarter", "month", "week", "day", "dow", "doy")
        )
        + " FROM r"
    )
    got, expected = lean_and_duckdb(sql, values)
    assert canonical(got) == canonical(expected)
    for engine, rows in engines(sql, values).items():
        assert canonical(rows) == canonical(expected), engine
    days = 86_400_000_000
    first, last = got[0], got[-1]
    assert first[:4] == (TS_MIN,) * 4 and first[4:] == (1, 1, 1, 1, 1, 1, 1)
    assert last[0] == TS_MAX + 1 - 5 * days and last[4:] == (9999, 4, 12, 52, 31, 5, 365)


@pytest.mark.parametrize("ts", [TS_MAX + 1, TS_MIN - 1, MIN])
def test_timestamps_outside_the_range_fail_the_read(ts):
    """A TIMESTAMP of the reference lies in 0001 to 9999 by its type (D32):
    a source value outside it fails the read, naming the column."""
    con = connect()
    with pytest.raises(
        UnsupportedError, match=r"ts holds timestamps outside 0001–9999 \(1, e\.g\. "
    ):
        put_table(con, "r", pa.table({"ts": pa.array([ts, 0], pa.timestamp("us"))}))
    with pytest.raises(UnsupportedError, match=r"d holds dates outside 0001–9999 \(2, e\.g\. "):
        put_table(
            con,
            "r",
            pa.table({"d": pa.array([DAY_MAX + 1, DAY_MIN - 1, 0], pa.int32()).cast(pa.date32())}),
        )


def test_a_scan_outside_the_range_fails_the_read(tmp_path):
    """A table read where it lies (`Scan`): its Parquet statistics discharge
    the range where they cover it, and one range predicate decides it
    otherwise (D32)."""
    import pyarrow.parquet as pq

    from sverify._scan import Scan

    ok, bad = tmp_path / "ok.parquet", tmp_path / "bad.parquet"
    schema = pa.schema([("d", pa.date32())])
    pq.write_table(pa.table({"d": pa.array([0, DAY_MAX], pa.int32()).cast(pa.date32())}), ok)
    pq.write_table(pa.table({"d": pa.array([0, DAY_MAX + 1], pa.int32()).cast(pa.date32())}), bad)
    con = connect()
    con.put("ok", Scan(files=(str(ok),), schema=schema))
    assert con.rows("ok") == [(date(1970, 1, 1),), (date(9999, 12, 31),)]
    with pytest.raises(
        UnsupportedError, match=r"d holds dates outside 0001–9999 \(1, e\.g\. 10000-01-01\)"
    ):
        con.put("bad", Scan(files=(str(bad),), schema=schema))
    assert "bad" not in con._tables


def test_calendar_truncation_of_a_computed_timestamp_outside_the_range_fails():
    """`Issue.overflow`: a computed timestamp past 9999-12-31 raises when it
    is truncated (D32); a column read is in range by its type."""
    sql = "SELECT date_trunc('month', ts + INTERVAL 2 DAY) AS x FROM r"
    with pytest.raises(polars_engine.Overflow):
        engines(sql, [TS_MAX - DAY])


T = ibis.table({"ts": "timestamp", "n": "int64"}, name="t")


def kinds(expr) -> tuple[list[str], list[str]]:
    """What Lean reports, without the bounds `verify` would infer (#244)."""
    r = sv.verify(expr, on_inferred="off")
    return [i.kind for i in r.errors], [i.kind for i in r.warnings]


SINCE_2000 = T.ts.between(datetime(2000, 1, 1), datetime(2100, 1, 1))


@pytest.mark.parametrize(
    ("label", "expr", "errs", "warns"),
    [
        # A column read lies in 0001 to 9999 by its type (D32).
        ("year, column read", T.select(y=T.ts.year()), [], []),
        ("year, bounded", T.filter(SINCE_2000).select(y=T.ts.year()), [], []),
        ("hour, column read", T.select(h=T.ts.truncate("h")), [], []),
        ("hour, bounded", T.filter(SINCE_2000).select(h=T.ts.truncate("h")), [], []),
        ("month, column read", T.select(m=T.ts.truncate("M")), [], []),
        # A computed timestamp may leave it, so truncating it may raise.
        (
            "month, computed",
            T.select(m=(T.ts + ibis.interval(days=1)).truncate("M")),
            ["overflow"],
            [],
        ),
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


def test_parts_of_a_column_read_are_not_null():
    """A timestamp column lies in 0001 to 9999 by its type, where `date_part`
    is total (D32), so a part of a non-NULL column is not NULL."""
    report = sv.verify(
        T.select(y=T.ts.year()), requires={"t": [_.ts.notnull()]}, ensures=[_.y.notnull()]
    )
    assert report.proved, str(report)


#: Pipelines over `t(ts)`, on timestamps including the extremes.
PIPELINES = [
    T.select(m=T.ts.truncate("M")),
    T.select(y=T.ts.truncate("Y"), w=T.ts.truncate("W")),
    T.filter(T.ts >= datetime(1700, 1, 1)).select(m=T.ts.truncate("M")),
    T.filter(SINCE_2000).select(q=T.ts.truncate("Q")),
    T.select(d=T.ts.truncate("D"), y=T.ts.year()),
]


#: DataFusion refuses calendar truncation (upstream/bugs/DF-17.json): only the
#: last pipeline, a truncation to a day, runs there.
DF_PIPELINES = [
    pytest.param(i, marks=pytest.mark.skip(reason="DF-17: calendar truncation refused"))
    if i < len(PIPELINES) - 1
    else i
    for i in range(len(PIPELINES))
]


@pytest.mark.backend("datafusion")
@pytest.mark.parametrize("i", DF_PIPELINES)
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
        run_plan(con, written_plan(to_substrait_json(expr)), "datafusion")
    except BaseException as e:  # noqa: BLE001 - DataFusion also panics here
        assert reported, f"DataFusion failed ({e}) but no error was reported"


# --------------------------------------------------------------------------
# Dates: arithmetic with days and months, parts and truncation

#: The reference's dates, 0001-01-01 to 9999-12-31 (`Time.dayMin`, #251).
DAY_MIN, DAY_MAX = -719162, 2932896

#: Date arithmetic and parts, in Ibis: Lean gets the Ibis producer's plan
#: and DataFusion runs Ibis's SQL. (DuckDB's SQL types `DATE + INTERVAL` as
#: a TIMESTAMP, which the SQL lift cannot output yet, #240.)
R_DATES = ibis.table({"d": "date"}, name="r")
DATE_EXPR = R_DATES.select(
    a=R_DATES.d + ibis.interval(months=1),
    b=R_DATES.d - ibis.interval(months=13),
    c=R_DATES.d + ibis.interval(days=3),
    e=R_DATES.d + ibis.interval(months=1) + ibis.interval(days=2),
    f=R_DATES.d - ibis.interval(months=1) - ibis.interval(days=2),
    g=R_DATES.d + ibis.interval(years=2),
    y=R_DATES.d.year(),
    m=R_DATES.d.month(),
    dd=R_DATES.d.day(),
    w=R_DATES.d.day_of_week.index(),
    doy=R_DATES.d.day_of_year(),
    wk=R_DATES.d.week_of_year(),
)
TRUNC_EXPR = R_DATES.select(
    w=R_DATES.d.truncate("W"),
    m=R_DATES.d.truncate("M"),
    q=R_DATES.d.truncate("Q"),
    y=R_DATES.d.truncate("Y"),
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


def date_runs(expr: ibis.Table, values: list[int | None]) -> dict[str, list[tuple]]:
    """Rows from Lean's semantics of `expr`'s plan, and from Polars and
    DuckDB running the plan Lean writes."""
    con = connect()
    put_table(con, "r", pa.table({"d": pa.array(values, pa.int32()).cast(pa.date32())}))
    plan = to_substrait(expr)
    written = written_plan(json.dumps(plan))
    inline_tables(plan, {"r": [(v,) for v in values]})
    return {
        "lean": lean_values(json.dumps(plan)),
        "polars": days_of(run_plan(con, written, "polars")),
        "duckdb": days_of(run_plan(con, written, "duckdb")),
    }


day_edges = st.sampled_from(
    [0, -1, 19753, 19782, 19813, 11016, 10957, DAY_MIN + 800, DAY_MAX - 800]
)
dates = st.one_of(day_edges, st.integers(DAY_MIN + 800, DAY_MAX - 800))


@settings(max_examples=25, deadline=None)
@given(values=st.lists(st.one_of(st.none(), dates), max_size=8))
def test_date_arithmetic(values):
    """Months clamp to the end of a shorter month and come before days, as in
    DataFusion; Polars and DuckDB give Lean's rows."""
    runs = date_runs(DATE_EXPR, values)
    expected = canonical(runs.pop("lean"))
    for engine, rows in runs.items():
        assert canonical(rows) == expected, engine


@settings(max_examples=30, deadline=None)
@given(values=st.lists(st.one_of(st.none(), st.integers(DAY_MIN, DAY_MAX)), max_size=8))
def test_date_trunc_of_dates(values):
    """Within the reference's dates, Polars and DuckDB give Lean's rows."""
    runs = date_runs(TRUNC_EXPR, values)
    expected = canonical(runs.pop("lean"))
    for engine, rows in runs.items():
        assert canonical(rows) == expected, engine


@pytest.mark.parametrize(
    ("x", "d"),
    [
        (R_DATES.d + ibis.interval(days=1), DAY_MAX),
        (R_DATES.d - ibis.interval(days=1), DAY_MIN),
        (R_DATES.d + ibis.interval(months=1), DAY_MAX - 10),
    ],
)
def test_dates_outside_the_range_fail(x, d):
    """`rangeIssue`: date arithmetic that leaves the reference's dates (#251),
    and `date_trunc` outside them (D32): the checker reports an error and the
    engines raise."""
    con = connect()
    put_table(con, "r", pa.table({"d": pa.array([d], pa.int32()).cast(pa.date32())}))
    expr = R_DATES.select(x=x)
    report = sv.verify(expr, on_inferred="off")
    assert "overflow" in [i.kind for i in report.errors]
    written = written_plan(to_substrait_json(expr))
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
    """Ibis's temporal operations that DataFusion's own SQL does not run
    (`epoch_seconds`, `iso_year`, …), against Python's calendar."""
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


# --------------------------------------------------------------------------
# Times of day, formatting, timestamps from numbers

#: Times of day and formats, in Ibis (`to_char` is DataFusion's name).
R_TS = ibis.table({"ts": "timestamp"}, name="r")
TOD_EXPR = R_TS.select(
    t=R_TS.ts.time(),
    s=R_TS.ts.strftime("%Y-%m-%d %H:%M:%S"),
    f=R_TS.ts.strftime("%F %T %j %%"),
    h=R_TS.ts.time().hour(),
)


def tod_runs(
    expr: ibis.Table,
    values: list[int | None],
    engines: tuple[str, ...] = ("polars", "duckdb"),
) -> dict[str, list[tuple]]:
    """As `date_runs`, over a timestamp column `ts`; times as microseconds.
    Lean always runs; `engines` picks the others."""

    def plain(out: pa.Table) -> list[tuple]:
        columns = []
        for c in out.columns:
            if pa.types.is_time(c.type):
                c = c.cast(pa.time64("us")).cast(pa.int64())
            columns.append(c)
        return [tuple(x.values()) for x in pa.table(columns, names=out.column_names).to_pylist()]

    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    plan = to_substrait(expr)
    written = written_plan(json.dumps(plan))
    inline_tables(plan, {"r": [(v,) for v in values]})
    runs = {
        "polars": lambda: plain(run_plan(con, written, "polars")),
        "duckdb": lambda: plain(run_plan(con, written, "duckdb")),
    }
    return {"lean": lean_values(json.dumps(plan))} | {e: runs[e]() for e in engines}


#: Within the reference's timestamps (D32).
in_range = st.one_of(edges.filter(lambda v: TS_MIN <= v <= TS_MAX), st.integers(TS_MIN, TS_MAX))


def python_tod(v: int) -> tuple:
    """`TOD_EXPR` of a timestamp in years 1000 to 9999, by Python's calendar."""
    d = datetime(1970, 1, 1) + timedelta(microseconds=v)
    clock = d.strftime("%Y-%m-%d %H:%M:%S")
    return (v % US_PER_DAY, clock, f"{clock} {d.strftime('%j')} %", d.hour)


#: Years 1000 to 9999, where chrono's `%Y` is Python's.
FOUR_DIGITS = (
    int((datetime(1000, 1, 1) - datetime(1970, 1, 1)) / timedelta(microseconds=1)),
    int((datetime(9999, 12, 31, 23, 59, 59) - datetime(1970, 1, 1)) / timedelta(microseconds=1)),
)


@settings(max_examples=40, deadline=None)
@given(values=st.lists(st.one_of(st.none(), in_range), max_size=8))
def test_times_of_day_and_formats_match_the_reference(values):
    """`CAST(ts AS TIME)`, `to_char` (`%Y` in four digits) and clock parts of
    a time: Polars and DuckDB give Lean's rows, and Lean's are Python's in
    years 1000 to 9999."""
    runs = tod_runs(TOD_EXPR, values)
    expected = runs.pop("lean")
    for engine, rows in runs.items():
        assert canonical(rows) == canonical(expected), engine
    for v, row in zip(values, expected, strict=True):
        if v is not None and FOUR_DIGITS[0] <= v <= FOUR_DIGITS[1]:
            assert row == python_tod(v), v


US_PER_DAY = 86_400_000_000
#: A time of day plus intervals (#507), as (name, Ibis interval, microseconds).
TIME_SHIFTS = [
    ("p", ibis.interval(hours=1), 3_600_000_000),
    ("m", -ibis.interval(minutes=90), -5_400_000_000),
    ("d", ibis.interval(hours=25), 90_000_000_000),
    ("u", ibis.interval(microseconds=1), 1),
]
TIME_UNITS = {"h": 3_600_000_000, "m": 60_000_000, "s": 1_000_000, "ms": 1_000}


@pytest.mark.backend("duckdb")
@settings(max_examples=40, deadline=None)
@given(values=st.lists(st.one_of(st.none(), in_range), max_size=8))
def test_time_arithmetic_wraps_around_midnight(values):
    """#507: a time of day plus an interval wraps around midnight, both ways,
    and truncation floors it, in Lean as in DuckDB (`duckdb-time-plus-interval`)."""
    t = R_TS.ts.time()
    expr = R_TS.select(
        **{f"a{n}": t + iv for n, iv, _ in TIME_SHIFTS},
        s=t - ibis.interval(hours=1),
        **{f"t{u}": t.truncate(u) for u in TIME_UNITS},
    )
    runs = tod_runs(expr, values, engines=("duckdb",))

    def expected(v: int | None) -> tuple:
        if v is None:
            return (None,) * (len(TIME_SHIFTS) + 1 + len(TIME_UNITS))
        tod = v % US_PER_DAY
        shifted = [(tod + us) % US_PER_DAY for _, _, us in TIME_SHIFTS]
        return (*shifted, (tod - 3_600_000_000) % US_PER_DAY,
                *[tod // k * k for k in TIME_UNITS.values()])  # fmt: skip

    want = [expected(v) for v in values]
    for engine, rows in runs.items():
        assert rows == want, engine


def test_time_arithmetic_outside_the_model_is_refused():
    t = R_TS.ts.time()
    with pytest.raises(Unsupported, match="to a nanosecond"):
        to_substrait_json(R_TS.select(x=t.truncate("ns")))
    # Ibis has no months of a time; DuckDB drops them, and Lean refuses them.
    plan = to_substrait_json(R_TS.select(x=t + ibis.interval(hours=1)))
    day_to_second = '{"intervalDayToSecond": {"seconds": 3600, "subseconds": "0", "precision": 6}}'
    months = plan.replace(day_to_second, '{"intervalYearToMonth": {"months": 1}}')
    assert months != plan
    code, out, err = run_checker((), months)
    assert code != 0 and "months" in out + err


EARLIER = R_TS.ts - ibis.interval(days=1)


@pytest.mark.parametrize("t", [EARLIER.time(), EARLIER.strftime("%Y")])
def test_times_outside_the_range_fail(t):
    """A computed timestamp before 0001-01-01 raises in a calendar function."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array([TS_MIN], pa.timestamp("us"))}))
    expr = R_TS.select(t=t)
    report = sv.verify(expr, on_inferred="off")
    assert "overflow" in [i.kind for i in report.errors]
    with pytest.raises(polars_engine.Overflow):
        run_plan(con, written_plan(to_substrait_json(expr)), "polars")


def test_unsupported_formats_are_refused():
    expr = R_TS.select(s=R_TS.ts.strftime("%A %e"))
    code, out, err = run_checker((), to_substrait_json(expr))
    assert code != 0 and "format" in out + err


def test_constructors_of_constants():
    """`ibis.date(2024, 2, 29)` and friends are constants; a bad date is
    refused (DataFusion's `make_date` fails). A date of columns is computed
    (#809, `tests/test_sql_lift_temporal.py`); a timestamp of columns is
    refused."""
    expr = D.select(
        a=ibis.date(2024, 2, 29), b=ibis.timestamp(2024, 1, 2, 3, 4, 5), c=ibis.time(9, 30, 0)
    )
    plan = inline_tables(to_substrait(expr), {"t": [(None, None, None)]})
    got = lean_values(json.dumps(plan))
    assert got == [(19782, 1704164645000000, 34200000000)]
    # The reason after the colon is CPython's: "day is out of range for month"
    # up to 3.13, "day 30 must be in range 1..29 …" from 3.14.
    with pytest.raises(Unsupported, match=r"DateFromYMD of \[2024, 2, 30\]: day "):
        to_substrait(D.select(a=ibis.date(2024, 2, 30)))
    with pytest.raises(Unsupported, match="of columns"):
        to_substrait(D.select(a=ibis.timestamp(D.n, 1, 1, 0, 0, 0)))


# --------------------------------------------------------------------------
# Time-based windows, to Polars lazy's level (#95)

W = ibis.table({"g": "int64", "ts": "timestamp", "x": "int64"}, name="t")
#: Polars' `closed="right"`: the window (t - 7d, t], microsecond timestamps.
SEVEN_DAYS = ibis.interval(days=7) - ibis.interval(microseconds=1)
ROLLING = W.select(
    "g",
    "ts",
    "x",
    s=W.x.sum().over(
        ibis.range_window(group_by="g", order_by="ts", preceding=SEVEN_DAYS, following=0)
    ),
)
BUCKETED = W.mutate(b=W.ts.bucket(minutes=15))
DYNAMIC = BUCKETED.group_by(["g", "b"]).aggregate(s=BUCKETED.x.sum(), n=BUCKETED.x.count())

minutes = st.sampled_from([0, 7, 15, 600, 10080, 10081, 20000])


@st.composite
def w_rows(draw: st.DrawFn) -> list[tuple]:
    n = draw(st.integers(0, 8))
    start = datetime(2024, 1, 1)
    return [
        (
            draw(st.one_of(st.none(), st.integers(1, 2))),
            start + timedelta(minutes=draw(minutes), microseconds=draw(st.sampled_from([0, 1]))),
            draw(st.one_of(st.none(), st.integers(1, 2))),
        )
        for _ in range(n)
    ]


def as_micros(v: object) -> object:
    return (v - datetime(1970, 1, 1)) // timedelta(microseconds=1) if isinstance(v, datetime) else v


def polars_sums(rows: list[tuple]) -> list[tuple]:
    """Polars sums no values to 0; SQL (and Lean) to NULL."""
    return [(*r[:-2], None if r[-1] == 0 else r[-2], r[-1]) for r in rows]


@settings(max_examples=40, deadline=None)
@given(rows=w_rows())
def test_time_windows_match_polars(rows):
    """A rolling sum over the last seven days (`rolling_sum_by(ts, "7d",
    closed="right")`, peers with equal times included) and 15-minute buckets
    (`group_by_dynamic(ts, every="15m")`) mean what Polars' own operations
    compute, and Polars and DuckDB running Lean's plans agree."""
    import polars as pl

    table = pa.table(
        {
            "g": pa.array([r[0] for r in rows], pa.int64()),
            "ts": pa.array([r[1] for r in rows], pa.timestamp("us")),
            "x": pa.array([r[2] for r in rows], pa.int64()),
        }
    )
    df = pl.DataFrame(table).sort("ts")
    rolling = df.with_columns(
        s=pl.col("x").rolling_sum_by("ts", "7d", closed="right", min_samples=0).over("g")
    )
    # The rolling sum's emptiness, by counting the non-NULL values in the window.
    counts = df.with_columns(
        c=pl.col("x")
        .is_not_null()
        .cast(pl.Int64)
        .rolling_sum_by("ts", "7d", closed="right")
        .over("g")
    )["c"].to_list()
    native_rolling = [
        (g, as_micros(ts), x, s if c else None)
        for (g, ts, x, s), c in zip(rolling.select("g", "ts", "x", "s").rows(), counts, strict=True)
    ]
    native_dynamic = (
        polars_sums(
            [
                tuple(as_micros(v) for v in r)
                for r in df.group_by_dynamic("ts", every="15m", group_by="g")
                .agg(s=pl.col("x").sum(), n=pl.col("x").count())
                .select("g", "ts", "s", "n")
                .rows()
            ]
        )
        if rows
        else []
    )
    for expr, native in ((ROLLING, native_rolling), (DYNAMIC, native_dynamic)):
        lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"t": rows})))
        assert canonical(lean) == canonical(native)
        plan = written_plan(to_substrait_json(expr))
        for engine in (polars_engine, duckdb_engine):
            got = [
                tuple(as_micros(v) for v in r.values())
                for r in engine.run(plan, {"t": table}).to_pylist()
            ]
            assert canonical(got) == canonical(lean), engine.__name__


def test_calendar_offsets_and_truncation():
    """`dt.offset_by("1mo2d")`, `dt.truncate("1mo" / "1w" / "1q")` and
    `dt.month_end` as interval arithmetic and truncation (`Time.addMonths`
    clamps to the end of a shorter month)."""
    expr = D.select(
        o=D.ts + ibis.interval(months=1) + ibis.interval(days=2),
        m=D.ts.truncate("M"),
        w=D.ts.truncate("W"),
        q=D.ts.truncate("Q"),
        e=D.d.truncate("M") + ibis.interval(months=1) - ibis.interval(days=1),
    )
    rows = [(19753, 19753 * DAY + 3_600_000_000, 0)]  # 2024-01-31 01:00
    plan = inline_tables(to_substrait(expr), {"t": rows})
    assert lean_values(json.dumps(plan)) == [
        (19784 * DAY + 3_600_000_000, 19723 * DAY, 19751 * DAY, 19723 * DAY, 19753)
    ]


def test_overlapping_windows_are_refused():
    """`group_by_dynamic` with `period > every` puts a row into several
    windows: an array of window starts, then UNNEST (#94), which is refused."""
    starts = ibis.range(
        W.ts.bucket(minutes=15) - ibis.interval(minutes=15), W.ts, ibis.interval(minutes=15)
    )
    with pytest.raises(Unsupported):
        to_substrait(W.mutate(start=starts.unnest()))


def test_constant_date_arithmetic_has_no_guard():
    """`DATE '1994-01-01' + INTERVAL 1 YEAR` (TPC-H Q6) stays within the
    reference's dates, which is decided when the plan is written: the SQL
    has no range guard. A column's arithmetic keeps it (#251)."""
    from sverify.sql import to_sql as plan_sql
    from sverify.sql.duckdb import DUCKDB

    t = ibis.table({"d": "date"}, name="t")
    for expr, guarded in [
        (t.filter(t.d < ibis.date("1994-01-01") + ibis.interval(years=1)), False),
        (t.filter(t.d < ibis.date("1994-01-01") + ibis.interval(days=365)), False),
        (t.select(e=t.d + ibis.interval(years=1)), True),
    ]:
        sql = plan_sql(json.loads(written_plan(to_substrait_json(expr))), DUCKDB)
        assert ("outside the reference" in sql) == guarded, sql


def test_times_in_nanoseconds_are_refused():
    """DuckDB's `TIME_NS` is `time64[ns]` in Arrow; Ibis's time has no unit,
    so the plan read it as microseconds and the engine kept the nanoseconds,
    dropping a `::TIME` cast (#627)."""
    from sverify.engine import connect
    from sverify.plan_json import Unsupported

    rel = duckdb.sql("SELECT '13:00:00.12345678'::TIME_NS AS tns")
    assert rel is not None
    ns = rel.to_arrow_table()
    nested = pa.table({"l": pa.array([[1]], pa.list_(pa.time64("ns")))})
    con = connect()
    for table in (ns, nested):
        with pytest.raises(Unsupported, match="nanoseconds"):
            con.put("times", table)
    con.put("times", pa.table({"t": pa.array([1], pa.time64("us"))}))
