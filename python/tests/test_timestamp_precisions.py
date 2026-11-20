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
    return report, report.run(con, engine)


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
    got = report.run(con, engine).column("y").to_pylist()
    want = [
        None if c is None else EPOCH + dt_.timedelta(microseconds=c // per * per) for c in counts
    ]
    assert report.output["y"] == dt.Timestamp(scale=6)
    assert got == want


def test_typeof_of_a_widened_column_is_refused():
    t = ibis.table({"x": "timestamp(3)"}, name="t")
    with pytest.raises(Exception, match="typeof of a"):
        sv.verify(t.select(y=t.x.typeof()), on_inferred="ignore")


def test_a_scan_with_a_millisecond_column_is_refused(tmp_path):
    """Only an Arrow table is widened at the read; a table an engine reads where
    it is would meet two units in one comparison (`polars-ts-units-compare-coarse`)."""
    import pyarrow.parquet as pq

    from sverify._scan import Scan
    from sverify.plan_json import Unsupported

    f = tmp_path / "t.parquet"
    schema = pa.schema([("x", pa.timestamp("ms"))])
    pq.write_table(pa.table({"x": pa.array([0, 1500], pa.timestamp("ms"))}, schema=schema), f)
    with pytest.raises(Unsupported, match="timestamp in milliseconds"):
        sv.connect().put("t", Scan((str(f),), schema))


@pytest.mark.parametrize(("ty", "per"), [("timestamp(3)", 1000), ("timestamp(0)", 1_000_000)])
def test_a_cast_from_a_string_floors_too(ty, per):
    """Unverified: a string may not parse, so the plan is not proved; Polars has
    no string-to-timestamp parse yet."""
    engine = "duckdb"
    t = ibis.table({"s": "string"}, name="t")
    report = sv.verify(t.select(y=t.s.cast(ty)), on_inferred="ignore")
    con = sv.connect()
    con.put("t", pa.table({"s": ["1970-01-01 00:00:01.123456", "1969-12-31 23:59:59.999999"]}))
    got = report.run(con, engine, unverified=True).column("y").to_pylist()
    want = [EPOCH + dt_.timedelta(microseconds=c // per * per) for c in (1_123_456, -1)]
    assert got == want


def test_a_cast_to_a_zoned_millisecond_timestamp_is_refused_with_the_zone_cast():
    """The zone conversion is D53's and the checker refuses it (#1725); the
    precision does not lift that: the floor is not applied around a refused cast."""
    t = ibis.table({"x": "timestamp(6)"}, name="t")
    with pytest.raises(Exception, match="1725"):
        sv.verify(t.select(y=t.x.cast(dt.Timestamp(timezone="UTC", scale=3))), on_inferred="ignore")
