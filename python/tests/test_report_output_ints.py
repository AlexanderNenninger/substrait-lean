"""`Report.output` states the run's integer widths and timestamp type (#1484,
ruling 114): a computed integer is int64, a passed-through column keeps its
declared width, a timestamp has microseconds. Polars returns every integer
as int64 whatever its declared width, so the integer tests run on DuckDB."""

import ibis
import ibis.expr.datatypes as dt
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars"]

SCHEMA = {"a": "int8", "b": "int16", "c": "timestamp", "s": "string", "d": "timestamp"}


def table():
    return ibis.table(SCHEMA, name="t")


def data():
    ts = pa.array([0, 1_000_000], pa.timestamp("us"))
    return pa.table(
        {
            "a": pa.array([1, -5], pa.int8()),
            "b": pa.array([2, 3], pa.int16()),
            "c": ts,
            "s": ["x", "yz"],
            "d": ts,
        }
    )


def run_types(report, engine):
    con = sv.connect()
    con.put("t", data())
    out = report.run(con, engine, unverified=True)
    return {f.name: dt.dtype(ibis.formats.pyarrow.PyArrowType.to_ibis(f.type)) for f in out.schema}


COMPUTED = {
    "a + a": lambda t: t.a + t.a,
    "b * b": lambda t: t.b * t.b,
    "abs(a)": lambda t: t.a.abs(),
    "-b": lambda t: -t.b,
    "a % a": lambda t: t.a % t.a.nullif(0),
    "year(c)": lambda t: t.c.year(),
    "length(s)": lambda t: t.s.length(),
}


@pytest.mark.parametrize("name", COMPUTED)
def test_a_computed_integer_is_int64_in_the_report_and_the_run(name):
    t = table()
    report = sv.verify(t.select(a=t.a, b=t.b, x=COMPUTED[name](t)), on_inferred="ignore")
    assert report.output["x"] == dt.int64
    assert report.output["a"] == dt.int8 and report.output["b"] == dt.int16
    assert dict(report.output) == run_types(report, "duckdb")


@pytest.mark.parametrize("engine", ENGINES)
def test_timestamps_are_microseconds_in_the_report_and_the_run(engine):
    t = table()
    report = sv.verify(t.select(c=t.c, d=t.d))
    assert report.output["c"] == dt.Timestamp(scale=6)
    assert dict(report.output) == run_types(report, engine)


def test_an_explicit_integer_cast_has_todays_width():
    """Pins today's widths: the report and the run agree on what a cast gives.
    The cast to the width it names is #1772 (a writer change and a regen of the
    generated DuckDB lowering); this test changes with it."""
    t = table()
    report = sv.verify(t.select(n=t.a.cast("int32"), w=t.b.cast("int64")))
    assert dict(report.output) == run_types(report, "duckdb")


def test_a_timestamp_difference_does_not_run():
    """`ts - ts` is an interval, which the run cannot return (ruling 114)."""
    t = table()
    report = sv.verify(t.select(x=t.c - t.d), on_inferred="ignore")
    with pytest.raises(ValueError, match="Arrow interval type is not supported"):
        run_types(report, "duckdb")
