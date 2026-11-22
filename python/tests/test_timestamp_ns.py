"""Nanosecond timestamps are a kind of their own (#323, D61): a column is read,
compared with others of its kind, used as a key, counted and its MIN and MAX
taken, keeping every digit on DuckDB and Polars. It meets microseconds only
through a cast, which is refused, as are the calendar functions; the message
states the range, 1677-09-21 to 2262-04-11."""

import ibis
import ibis.expr.datatypes as dt
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars"]
NS = pa.timestamp("ns")
# Two instants one nanosecond apart, one before 1970, and a NULL.
A, B, C = 1_700_000_000_123_456_789, 1_700_000_000_123_456_790, -1_000_000_000_000_000_001
RANGE = "1677-09-21 to 2262-04-11"

t = ibis.table({"k": "int64", "x": "timestamp(9)", "y": "timestamp(9)"}, name="t")


def con_with(rows):
    k, x, y = zip(*rows, strict=True)
    con = sv.connect()
    con.put(
        "t", pa.table({"k": pa.array(k, pa.int64()), "x": pa.array(x, NS), "y": pa.array(y, NS)})
    )
    return con


ROWS = [(1, A, B), (1, B, A), (2, C, C), (2, None, A)]


def ns(table: pa.Table, column: str) -> list:
    """A column's values as counts of nanoseconds, so no digit is lost to Python."""
    return table.column(column).cast(pa.int64()).to_pylist()


@pytest.mark.parametrize("engine", ENGINES)
def test_a_nanosecond_column_is_carried_with_every_digit(engine):
    report = sv.verify(t.select("k", "x"))
    assert report.verdict == sv.Verdict.PROVED
    assert report.output["x"] == dt.Timestamp(scale=9)
    out = report.run(con_with(ROWS), engine)
    assert out.schema.field("x").type == NS
    assert ns(out, "x") == [A, B, C, None]


@pytest.mark.parametrize("engine", ENGINES)
def test_two_nanosecond_columns_compare_by_the_nanosecond(engine):
    report = sv.verify(t.filter(t.x < t.y).select("k", "x"), ensures=['"x" IS NOT NULL'])
    assert report.verdict == sv.Verdict.PROVED
    assert ns(report.run(con_with(ROWS), engine), "x") == [A]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_nanosecond_column_orders_groups_and_takes_min_and_max(engine):
    expr = (
        t.group_by("x")
        .aggregate(n=t.k.count(), lo=t.y.min(), hi=t.y.max())
        .order_by(ibis.asc("x", nulls_first=True))
    )
    report = sv.verify(expr)
    assert report.verdict == sv.Verdict.PROVED
    rows = con_with([*ROWS, (3, A, C)])
    out = report.run(rows, engine)
    assert ns(out, "x") == [None, C, A, B]
    assert out.column("n").to_pylist() == [1, 1, 2, 1]
    assert ns(out, "lo") == [A, C, C, A]
    assert ns(out, "hi") == [A, C, B, A]


@pytest.mark.parametrize(
    "expr",
    [
        pytest.param(lambda: t.filter(t.x > ibis.timestamp("2020-01-01")), id="literal"),
        pytest.param(lambda: t.select(y=t.x.year()), id="calendar"),
        pytest.param(lambda: t.select(y=t.x.cast("timestamp(6)")), id="cast"),
        pytest.param(lambda: t.select(y=t.x + ibis.interval(days=1)), id="interval"),
    ],
)
def test_nanoseconds_meet_microseconds_only_through_a_cast(expr):
    with pytest.raises(Exception, match=RANGE):
        sv.verify(expr())


def test_spark_refuses_a_nanosecond_column():
    pytest.importorskip("pyspark")
    report = sv.verify(t.select("x"))
    with pytest.raises(Exception, match="spark-timestamp-precision"):
        report.run(con_with(ROWS), "spark")


@pytest.mark.parametrize("engine", ENGINES)
def test_duckdb_sql_over_a_nanosecond_table_lifts(engine):
    report = sv.verify("SELECT k, x FROM t WHERE x < y ORDER BY x", tables={"t": t.schema()})
    assert report.verdict == sv.Verdict.PROVED
    out = report.run(con_with(ROWS), engine)
    assert ns(out, "x") == [A]


def test_a_zoned_nanosecond_column_is_refused():
    """DuckDB's TIMESTAMPTZ holds microseconds only."""
    z = ibis.table({"x": "timestamp('UTC', 9)"}, name="z")
    with pytest.raises(Exception, match="time zone in nanoseconds"):
        sv.verify(z.select("x"))
