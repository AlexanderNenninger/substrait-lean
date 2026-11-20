"""Casts of a boolean to a number (#1911) and of a list element by element
(#1919): `CAST(b AS INT)` is 1, 0 or NULL, and `CAST(l AS VARCHAR[])` casts
every element, on every engine."""

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv

ENGINES = ["duckdb", "polars", "spark"]

T = ibis.table({"b": "boolean", "l": "array<int64>"}, name="t")
DATA = pa.table({"b": [True, False, None], "l": [[0, 1], None, [2, None]]})


def run(report, engine):
    if engine == "spark":
        from spark_session import session

        session()  # skips without pyspark or a JVM
    con = sv.connect()
    con.put("t", DATA)
    return report.run(con, engine).column("x")


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize(
    ("to", "expected", "ty"),
    [
        ("int64", [1, 0, None], pa.int64()),
        # A computed integer is int64 in the report and the run (ruling 114).
        ("int8", [1, 0, None], pa.int64()),
        ("float64", [1.0, 0.0, None], pa.float64()),
    ],
)
def test_a_boolean_casts_to_one_or_zero(engine, to, expected, ty):
    report = sv.verify(T.select(x=T.b.cast(to)))
    assert report.issues == [], report.issues
    got = run(report, engine)
    assert got.to_pylist() == expected
    assert got.type == ty


@pytest.mark.parametrize("engine", ENGINES)
def test_a_sum_of_booleans_counts_the_trues(engine):
    """Ibis's `bool_sum` (`test_reduction_ops`): the sum of the cast."""
    report = sv.verify(T.aggregate(x=T.b.cast("int64").sum()))
    assert report.issues == [], report.issues
    assert run(report, engine).to_pylist() == [1]


def test_a_list_casts_element_by_element():
    """The cast is `transform(l, x -> CAST(x AS VARCHAR))`: Polars runs the
    lambda; the SQL engines refuse it, naming the construct (#348)."""
    report = sv.verify(T.select(x=T.l.cast("array<string>")))
    assert report.issues == [], report.issues
    assert run(report, "polars").to_pylist() == [["0", "1"], None, ["2", None]]
    for engine in ["duckdb", "spark"]:
        with pytest.raises(Exception, match="lambdas have no SQL form yet"):
            run(report, engine)


def test_a_list_constant_casts_element_by_element():
    """Ibis's own `test_cast[array]`."""
    expr = ibis.literal([0, 1, 2], type="array<int>").cast("array<string>")
    report = sv.verify(T.select(x=expr).limit(1))
    assert report.issues == [], report.issues
    assert run(report, "polars").to_pylist() == [["0", "1", "2"]]


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT CAST(b AS INTEGER) AS x FROM t",
        "SELECT CAST(b AS TINYINT) AS x FROM t",
        "SELECT CAST(b AS DOUBLE) AS x FROM t",
        "SELECT sum(b::INT) AS x FROM t",
    ],
)
def test_sql_casts_are_duckdbs(sql):
    report = sv.verify(sql, tables={"t": {"b": "boolean", "l": "array<int64>"}})
    assert report.issues == [], report.issues
    native = duckdb.connect()
    native.register("t", DATA)
    expected = [row[0] for row in native.execute(sql).fetchall()]
    assert run(report, "duckdb").to_pylist() == expected


def test_a_struct_cast_is_refused_by_design():
    """Ruling 186: the core cannot build a struct (D66 reserved), so Ibis's own
    `test_cast[struct]` is refused, naming why."""
    expr = ibis.literal({"a": 0, "b": "1"}, type="struct<a: int64, b: string>")
    with pytest.raises(Exception, match="casts of structs"):
        sv.verify(T.select(x=expr.cast("struct<a: string, b: int64>")).limit(1))
