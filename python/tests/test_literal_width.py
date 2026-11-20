"""A column projected from an integer literal has the literal's declared width,
whatever its value (#1934): `ibis.literal(0, "int64")` starts a 64-bit column, so
later arithmetic on it is checked at 64 bits, and an `int8` literal still starts
an 8-bit one."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars", "spark"]

T = ibis.table({"x": "float64"}, name="t")


def lit(v, ty):
    return ibis.literal(v, ty)


def accumulated(ty, step, steps=3):
    """`e` starts at `0` of type `ty` and adds `step` where `x > 0`, `steps` times."""
    q = T.mutate(e=lit(0, ty))
    for _ in range(steps):
        q = q.mutate(e=q.e + ibis.cases((q.x > 0, lit(step, ty)), else_=lit(0, ty)))
    return q.select("e")


def run(report, engine):
    if engine == "spark":
        from spark_session import session

        session()  # skips without pyspark or a JVM
    con = sv.connect()
    con.put("t", pa.table({"x": [1.0, -1.0]}))
    return report.run(con, engine).column("e").to_pylist()


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("ty", ["int16", "int32", "int64"])
def test_a_literal_column_keeps_its_declared_width(engine, ty):
    report = sv.verify(accumulated(ty, 100))
    assert report.issues == [], report.issues
    assert run(report, engine) == [300, 0]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_case_of_literals_keeps_their_declared_width(engine):
    """A `CASE` of int64 literals is an int64 column: `e * e` cannot overflow."""
    q = T.mutate(e=ibis.cases((T.x > 0, lit(100, "int64")), else_=lit(0, "int64")))
    report = sv.verify(q.select(e=q.e * q.e))
    assert report.issues == [], report.issues
    assert run(report, engine) == [10_000, 0]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_case_of_literals_keeps_their_declared_width(engine):
    """A `CASE` of int64 literals is an int64 column: `e * e` cannot overflow (#1968)."""
    q = T.mutate(e=ibis.cases((T.x > 0, lit(100, "int64")), else_=lit(0, "int64")))
    report = sv.verify(q.select(e=q.e * q.e))
    assert report.issues == [], report.issues
    assert run(report, engine) == [10_000, 0]


@pytest.mark.parametrize("ty", ["TINYINT", "SMALLINT"])
def test_a_case_of_narrow_literals_keeps_its_narrow_width(ty):
    """A `CASE` of `TINYINT` constants stays 8 bits: `e * e` past 127 is an
    overflow, as DuckDB raises it."""
    big = {"TINYINT": 100, "SMALLINT": 1000}[ty]
    sql = (
        f"SELECT e * e AS y FROM (SELECT CASE WHEN x > 0 THEN CAST({big} AS {ty}) "
        f"ELSE CAST(0 AS {ty}) END AS e FROM t)"
    )
    assert "overflow" in [i.kind for i in sv.verify(sql, tables={"t": {"x": "float64"}}).issues]


@pytest.mark.parametrize(
    ("ty", "big", "small"),
    [("TINYINT", 100, 10), ("SMALLINT", 1000, 100), ("INTEGER", 100000, 1000)],
)
def test_a_narrow_literal_column_keeps_its_narrow_width(ty, big, small):
    """Ibis widens `int8 + int8` to int16, so the narrow case is SQL: DuckDB
    multiplies two TINYINTs as a TINYINT and raises past 127."""

    def sql(v):
        return f"SELECT e * e AS y FROM (SELECT CAST({v} AS {ty}) AS e FROM t)"

    with pytest.raises(duckdb.Error, match="Overflow|out of range"):
        con = duckdb.connect()
        con.execute("CREATE TABLE t AS SELECT 1.0::DOUBLE AS x")
        con.execute(sql(big)).fetchall()
    tables = {"t": {"x": "float64"}}
    assert "overflow" in [i.kind for i in sv.verify(sql(big), tables=tables).issues]
    assert sv.verify(sql(small), tables=tables).issues == []


@pytest.mark.parametrize("engine", ENGINES)
def test_an_int64_literal_column_passes_32_bits(engine):
    """`2**31 - 1` as an int64 column, then `+ 1`: a 32-bit reading would
    report an overflow, and a 32-bit run would raise."""
    q = T.mutate(e=lit(2**31 - 1, "int64"))
    q = q.select(e=q.e + lit(1, "int64"))
    report = sv.verify(q)
    assert report.issues == [], report.issues
    assert run(report, engine) == [2**31, 2**31]
