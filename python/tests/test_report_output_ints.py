"""`Report.output` states the run's integer widths and timestamp type (#1484,
ruling 114): a computed integer is int64, a passed-through column keeps its
declared width, a timestamp has microseconds, on every engine (ruling 121: a
Polars run casts a passed-through narrow column back to its declared width)."""

import ibis
import ibis.expr.datatypes as dt
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars", "spark"]

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
    if engine == "spark":
        from spark_session import session

        session()  # skips without pyspark or a JVM
    con = sv.connect()
    con.put("t", data())
    try:
        out = report.run(con, engine, unverified=True)
    except Exception as e:  # noqa: BLE001 - a plan an engine does not run (#271)
        if "Unsupported" in type(e).__name__:
            pytest.skip(str(e))
        raise
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


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", COMPUTED)
def test_a_computed_integer_is_int64_in_the_report_and_the_run(name, engine):
    t = table()
    report = sv.verify(t.select(a=t.a, b=t.b, x=COMPUTED[name](t)), on_inferred="ignore")
    assert report.output["x"] == dt.int64
    assert report.output["a"] == dt.int8 and report.output["b"] == dt.int16
    assert dict(report.output) == run_types(report, engine)


@pytest.mark.parametrize("engine", ENGINES)
def test_timestamps_are_microseconds_in_the_report_and_the_run(engine):
    t = table()
    report = sv.verify(t.select(c=t.c, d=t.d))
    assert report.output["c"] == dt.Timestamp(scale=6)
    assert dict(report.output) == run_types(report, engine)


@pytest.mark.parametrize("engine", ENGINES)
def test_an_explicit_integer_cast_has_the_width_it_names(engine):
    """Ruling 114 (#1772): a cast to an integer type gives that type, in the report
    and in the run, narrowing, widening below 64 bits or widening to 64."""
    t = table()
    report = sv.verify(
        t.select(n=t.a.cast("int32"), w=t.b.cast("int64"), m=t.b.cast("int8"), a=t.a),
        on_inferred="ignore",
    )
    assert report.output["n"] == dt.int32 and report.output["w"] == dt.int64
    assert report.output["m"] == dt.int8 and report.output["a"] == dt.int8
    assert dict(report.output) == run_types(report, engine)


def test_a_timestamp_difference_does_not_run():
    """`ts - ts` is an interval, which the run cannot return (ruling 114)."""
    t = table()
    report = sv.verify(t.select(x=t.c - t.d), on_inferred="ignore")
    with pytest.raises(ValueError, match="Arrow interval type is not supported"):
        run_types(report, "duckdb")
