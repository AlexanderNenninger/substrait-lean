"""Second and millisecond timestamps are read as microseconds, exactly (#323, D61):
the result is `timestamp(6)` and equals the same instants read at microseconds."""

import datetime as dt_

import ibis
import ibis.expr.datatypes as dt
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars"]
EPOCH = dt_.datetime(1970, 1, 1)
UNITS = {"s": 1_000_000, "ms": 1000}


def run(engine, unit, counts):
    ty = {"s": "timestamp(0)", "ms": "timestamp(3)"}[unit]
    t = ibis.table({"x": ty}, name="t")
    report = sv.verify(t.select(x=t.x, y=t.x.year()), on_inferred="ignore")
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array(counts, pa.timestamp(unit))}))
    return report, report.run(con, engine, unverified=True)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("unit", UNITS)
def test_a_coarser_timestamp_is_read_as_microseconds(engine, unit):
    counts = [0, 1500, -1, None]
    report, out = run(engine, unit, counts)
    assert report.output["x"] == dt.Timestamp(scale=6)
    assert out.schema.field("x").type == pa.timestamp("us")
    got = out.column("x").to_pylist()
    want = [
        None if c is None else EPOCH + dt_.timedelta(microseconds=c * UNITS[unit]) for c in counts
    ]
    assert got == want


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(("ty", "per"), [("timestamp(3)", 1000), ("timestamp(0)", 1_000_000)])
def test_a_narrowing_cast_floors_on_the_timeline(engine, ty, per):
    """DuckDB truncates toward zero below 1970 (`duckdb-ts-narrow-toward-zero`);
    the reference floors, as `date_trunc` does."""
    t = ibis.table({"x": "timestamp(6)"}, name="t")
    report = sv.verify(t.select(y=t.x.cast(ty)), on_inferred="ignore")
    counts = [1999, -1, -1_500_001, 0, None]
    con = sv.connect()
    con.put("t", pa.table({"x": pa.array(counts, pa.timestamp("us"))}))
    got = report.run(con, engine, unverified=True).column("y").to_pylist()
    want = [
        None if c is None else EPOCH + dt_.timedelta(microseconds=c // per * per) for c in counts
    ]
    assert report.output["y"] == dt.Timestamp(scale=6)
    assert got == want


def test_typeof_of_a_widened_column_is_refused():
    t = ibis.table({"x": "timestamp(3)"}, name="t")
    with pytest.raises(Exception, match="typeof of a"):
        sv.verify(t.select(y=t.x.typeof()), on_inferred="ignore")
