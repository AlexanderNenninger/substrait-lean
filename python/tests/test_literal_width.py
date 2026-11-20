"""A column projected from an integer literal has the literal's declared width,
whatever its value (#1934): `ibis.literal(0, "int64")` starts a 64-bit column, so
later arithmetic on it is checked at 64 bits, and an `int8` literal still starts
an 8-bit one."""

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


def test_a_narrow_literal_column_keeps_its_narrow_width():
    # 3 * 100 leaves 8 bits: an `int8` column overflows where the plan says it does.
    assert "overflow" in [i.kind for i in sv.verify(accumulated("int8", 100)).issues]
    assert sv.verify(accumulated("int8", 10)).issues == []
