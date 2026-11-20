"""Ibis's cast of an integer to a timestamp reads seconds since the epoch;
the producer writes it as `as_timestamp("s")` (#860). The replay of Ibis's
`test_integer_cast_to_timestamp_column` found the plan read microseconds."""

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
