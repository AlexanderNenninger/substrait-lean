"""`date_part` and `date_trunc`.

* Lean's semantics (`SubstraitLean/Time.lean`) agrees with DataFusion, also
  for timestamps before 1970, at the ends of the years `chrono` represents
  (where `date_part` becomes NULL) and of DataFusion's nanosecond range.
* Truncating to a week, month, quarter or year outside that range is reported
  as an error, and DataFusion fails only where an error was reported.
* Polars and DuckDB, which run the plan Lean writes, agree with both, and
  fail where DataFusion does.
* Contracts use that years and truncations grow with the timestamp.
"""

import json
from datetime import datetime

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
    run_plan,
    run_sql,
    substrait_json,
    to_sql,
    written_plan,
)
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
