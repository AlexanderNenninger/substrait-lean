"""Casts to VARCHAR of booleans and dates (#346): `true`/`false` and `YYYY-MM-DD`, the text every
tier-1 engine gives, on every engine, from Ibis and from DuckDB SQL. Timestamps and decimals stay
refused until their text is decided."""

import datetime as dt

import ibis
import pyarrow as pa
import pytest

import sverify as sv

ROWS = pa.table(
    {
        "b": [True, False, None],
        "d": pa.array([dt.date(1, 1, 1), dt.date(1970, 1, 1), None], pa.date32()),
    }
)
T = ibis.table({"b": "boolean", "d": "date"}, name="t")
WANT = {"b": ["true", "false", None], "d": ["0001-01-01", "1970-01-01", None]}
ENGINES = ["duckdb", "polars"]


def _run(report, engine):
    con = sv.connect(engine)
    con.put("t", ROWS)
    return report.run(con, engine, unverified=True)


@pytest.mark.parametrize("engine", ENGINES)
def test_ibis_casts_of_booleans_and_dates_give_their_text(engine):
    report = sv.verify(T.select(b=T.b.cast("string"), d=T.d.cast("string")), counterexamples=0)
    out = _run(report, engine)
    assert out.column("b").to_pylist() == WANT["b"]
    assert out.column("d").to_pylist() == WANT["d"]


@pytest.mark.parametrize("engine", ENGINES)
def test_sql_casts_of_booleans_and_dates_give_their_text(engine):
    sql = "SELECT CAST(b AS VARCHAR) AS b, CAST(d AS VARCHAR) AS d FROM t"
    report = sv.verify(sv.sql(sql, dialect="duckdb", t=T), counterexamples=0)
    out = _run(report, engine)
    assert out.column("b").to_pylist() == WANT["b"]
    assert out.column("d").to_pylist() == WANT["d"]


def test_constant_casts_fold_to_their_text():
    sql = (
        "SELECT CAST(TRUE AS VARCHAR) AS a, CAST(FALSE AS VARCHAR) AS b,"
        " CAST(DATE '2024-01-05' AS VARCHAR) AS c FROM t"
    )
    report = sv.verify(sv.sql(sql, dialect="duckdb", t=T), counterexamples=0)
    out = _run(report, "duckdb")
    assert out.column("a")[0].as_py() == "true"
    assert out.column("b")[0].as_py() == "false"
    assert out.column("c")[0].as_py() == "2024-01-05"


@pytest.mark.parametrize(
    "expr",
    [
        lambda t: t.select(x=t.ts.cast("string")),
        lambda t: t.select(x=t.dec.cast("string")),
    ],
    ids=["timestamp", "decimal"],
)
def test_timestamps_and_decimals_stay_refused(expr):
    t = ibis.table({"ts": "timestamp", "dec": "decimal(10, 2)"}, name="t")
    with pytest.raises(Exception, match="cast"):
        sv.verify(expr(t), counterexamples=0)
