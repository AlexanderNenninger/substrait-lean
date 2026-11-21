"""Calendar functions of an instant at UTC (D69, #1725): the function of its UTC wall clock,
written by the Ibis producer as the cast to a naive timestamp, whatever the session's zone."""

import datetime as dt
import json
import os
import time
from collections.abc import Iterator

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify import _duckdb
from sverify.ibis_substrait import to_substrait_json

U = lambda *a: dt.datetime(*a, tzinfo=dt.UTC)  # noqa: E731
#: Rows within an hour of midnight UTC on both sides, where a zone east or west of UTC
#: gives another day.
TS = [U(2024, 1, 2, 0, 30), U(2024, 1, 1, 23, 30), U(2023, 12, 31, 23, 59, 59, 999999), None]
TABLE = pa.table({"id": [1, 2, 3, 4], "ts": pa.array(TS, pa.timestamp("us", tz="UTC"))})
T = ibis.table({"id": "int64", "ts": "timestamp('UTC', 6)"}, name="t")
N = ibis.table({"id": "int64", "ts": "timestamp"}, name="t")

OPENED = {
    "date()": lambda c: c.date(),
    "cast to date": lambda c: c.cast("date"),
    "time()": lambda c: c.time(),
    "cast to time": lambda c: c.cast("time"),
    "truncate day": lambda c: c.truncate("D"),
    "truncate hour": lambda c: c.truncate("h"),
    "bucket": lambda c: c.bucket(hours=6),
    "year": lambda c: c.year(),
    "month": lambda c: c.month(),
    "day": lambda c: c.day(),
    "hour": lambda c: c.hour(),
    "day of week": lambda c: c.day_of_week.index(),
    "day of week name": lambda c: c.day_of_week.full_name(),
    "week of year": lambda c: c.week_of_year(),
    "milliseconds": lambda c: c.millisecond(),
    "epoch seconds": lambda c: c.epoch_seconds(),
    "strftime": lambda c: c.strftime("%Y-%m-%d %H:%M:%S"),
}


def _plan(table, f) -> str:
    return json.dumps(
        json.loads(to_substrait_json(table.select(table.id, x=f(table.ts)))), sort_keys=True
    )


@pytest.mark.parametrize("name", OPENED)
def test_the_plan_is_that_of_the_cast_to_a_timestamp(name):
    f = OPENED[name]
    assert _plan(T, f) == _plan(T, lambda c: f(c.cast("timestamp"))), name


def _family(t: ibis.expr.datatypes.DataType) -> str:
    """The kind of a type: the widths and the scale are those sverify fixes."""
    for kind in ("timestamp", "date", "time", "string", "integer"):
        if getattr(t, f"is_{kind}")():
            return kind
    return str(t)


@pytest.mark.parametrize("name", OPENED)
def test_the_output_kind_is_the_expressions_type(name):
    """`truncate` and `bucket` of an instant are naive timestamps, as Ibis types them."""
    f = OPENED[name]
    report = sv.verify(T.select(T.id, x=f(T.ts)), counterexamples=0)
    assert _family(report.output["x"]) == _family(f(T.ts).type()), name
    if name in ("truncate day", "truncate hour", "bucket"):
        assert report.output["x"].timezone is None


@pytest.fixture
def duckdb_zone() -> Iterator:
    cursor = _duckdb.cursor()
    cursor.execute("SET GLOBAL TimeZone = 'UTC'").fetchall()

    def set_zone(zone: str) -> None:
        cursor.execute(f"SET GLOBAL TimeZone = '{zone}'").fetchall()

    yield set_zone
    cursor.execute("RESET GLOBAL TimeZone").fetchall()


@pytest.fixture
def host_zone() -> Iterator:
    old = os.environ.get("TZ")

    def set_zone(zone: str) -> None:
        os.environ["TZ"] = zone
        time.tzset()

    yield set_zone
    if old is None:
        os.environ.pop("TZ", None)
    else:
        os.environ["TZ"] = old
    time.tzset()


def _rows(table: pa.Table) -> list[tuple]:
    return sorted((tuple(r.values()) for r in table.to_pylist()), key=repr)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("name", OPENED)
def test_the_rows_are_the_utc_wall_clocks_under_any_session_zone(
    name, engine, duckdb_zone, host_zone
):
    """The writer reads no session zone: east and west of UTC give the rows of UTC, which are
    those of the naive timestamps of the same wall clocks."""
    f = OPENED[name]
    report = sv.verify(T.select(T.id, x=f(T.ts)), counterexamples=0)
    naive = pa.table({"id": TABLE["id"], "ts": TABLE["ts"].cast(pa.timestamp("us"))})
    want_report = sv.verify(N.select(N.id, x=f(N.ts)), counterexamples=0)
    con = sv.connect(engine)
    con.put("t", naive)
    want = _rows(want_report.run(con, engine, unverified=True))
    for session, host in [
        ("UTC", "UTC"),
        ("America/New_York", "Asia/Kolkata"),
        ("Asia/Tokyo", "America/Los_Angeles"),
    ]:
        duckdb_zone(session)
        host_zone(host)
        con = sv.connect(engine)
        con.put("t", TABLE)
        assert _rows(report.run(con, engine, unverified=True)) == want, (name, session)


REFUSED = {
    "an instant plus an interval": lambda t: t.select(x=t.ts + ibis.interval(hours=1)),
    "the difference of two instants": lambda t: t.select(x=t.ts - t.ts),
    "an instant cast to a string": lambda t: t.select(x=t.ts.cast("string")),
}


@pytest.mark.parametrize("what", REFUSED)
def test_arithmetic_and_strings_of_an_instant_stay_refused(what):
    with pytest.raises(Exception, match="1725"):
        sv.verify(REFUSED[what](T), counterexamples=0)
