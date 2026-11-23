"""Ibis's cast of a number to a timestamp reads seconds since the epoch. The
producer writes an integer as `as_timestamp("s")` (#860): the replay of Ibis's
`test_integer_cast_to_timestamp_column` found the plan read microseconds. A
double is its microseconds `x * 1e6` as a double, rounded half to even, as
DuckDB's `to_timestamp` gives (ruling 266, #1922)."""

from __future__ import annotations

import datetime as dt
import warnings

import ibis
import pandas as pd
import pyarrow as pa
import pytest

import sverify as sv
from sverify.errors import UnsupportedError


@pytest.fixture
def con():
    c = sv.connect()
    c.put("t", pa.table({"i": pa.array([0, 1, 86400, None], pa.int32())}))
    return c


@pytest.mark.parametrize("to", ["timestamp", "timestamp(0)", "timestamp(3)"])
def test_an_integer_cast_to_a_timestamp_is_seconds(con, to) -> None:
    """Also to a second or millisecond timestamp, which the producer floors
    after the microsecond cast (D61)."""
    t = con.table("t")
    expr = t.select(ts=t.i.cast(to))
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        report = sv.verify(expr, on_inferred="warn")
    assert report.verdict == sv.Verdict.PROVED
    ours = report.run(con, "duckdb").column("ts").to_pylist()
    epoch = dt.datetime(1970, 1, 1)
    assert ours == [epoch, epoch + dt.timedelta(seconds=1), dt.datetime(1970, 1, 2), None]
    # Ibis's own DuckDB backend, the meaning sverify proves.
    theirs = ibis.duckdb.connect().execute(ibis.memtable(con.get("t")).i.cast(to).name("ts"))
    assert [None if v is pd.NaT else v.to_pydatetime() for v in theirs] == ours


@pytest.mark.parametrize(
    "build",
    [
        lambda t: t.i.try_cast("timestamp"),
        lambda t: t.i.cast("timestamp('UTC')"),
    ],
    ids=["try_cast", "time zone"],
)
def test_the_other_integer_casts_to_a_timestamp_are_refused(con, build) -> None:
    t = con.table("t")
    with pytest.raises(UnsupportedError, match="as_timestamp"):
        sv.verify(t.select(ts=build(t)), on_inferred="warn")


#: Seconds as doubles: Ibis's `test_subsecond_cast_to_timestamp`, products of 1e6
#: that are ties (2.5e-6 * 1e6 is 2.5 as a double), a fraction to round, -0.0.
SECONDS = [1699109238.5, 2.5e-6, 1.5e-6, -1.5e-6, 0.1234567, -0.0, None]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("to", ["timestamp", "timestamp(3)", "timestamp(6)"])
def test_a_double_cast_to_a_timestamp_rounds_its_microseconds_half_to_even(engine, to) -> None:
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array(SECONDS, pa.float64())}))
    t = con.table("t")
    # A double past ±9.2e12 seconds leaves 64 bits of microseconds: bound it.
    report = sv.verify(
        t.select(ts=t.x.cast(to)), requires={"t": ['"x" IS NULL OR "x" BETWEEN -1e10 AND 1e10']}
    )
    assert report.verdict == sv.Verdict.PROVED
    ours = report.run(con, engine).column("ts").to_pylist()
    epoch = dt.datetime(1970, 1, 1)
    if to == "timestamp(3)":
        # Floored to the millisecond, as every cast to one (D61). Ibis's DuckDB backend
        # keeps the microseconds of `to_timestamp`, so it is not the oracle here.
        assert ours[0] == dt.datetime(2023, 11, 4, 14, 47, 18, 500000)
        assert ours[1:6] == [
            epoch,
            epoch,
            epoch - dt.timedelta(milliseconds=1),
            epoch.replace(microsecond=123000),
            epoch,
        ]
        return
    theirs = ibis.duckdb.connect().execute(ibis.memtable(con.get("t")).x.cast(to).name("ts"))
    assert ours == [None if v is pd.NaT else v.to_pydatetime() for v in theirs]
    micros = [2, 2, -2, 123457, 0]  # 2.5 and 1.5 round to 2, -1.5 to -2
    assert ours[1:6] == [epoch + dt.timedelta(microseconds=us) for us in micros]


@pytest.mark.parametrize(
    "build",
    [lambda t: t.x.try_cast("timestamp"), lambda t: t.x.cast("timestamp('UTC')")],
    ids=["try_cast", "time zone"],
)
def test_the_other_double_casts_to_a_timestamp_are_refused(build) -> None:
    t = ibis.table({"x": "float64"}, name="t")
    with pytest.raises(UnsupportedError, match="cast of a double"):
        sv.verify(t.select(ts=build(t)), on_inferred="ignore")
