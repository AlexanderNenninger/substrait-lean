"""Opaque columns (D67, #1958): a binary or map column is carried through a plan
unchanged, and `IS NULL` reads it; every other use is refused, naming the use.
Facts: `duckdb-opaque-carry`, `polars-opaque-carry`, `spark-opaque-carry`."""

import json

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify._lean_eval import inline_tables
from sverify._unsupported import Unsupported
from sverify.ibis_substrait import to_substrait_json

ENGINES = ["duckdb", "polars", "spark"]

T = ibis.table({"i": "!int64", "b": "binary", "m": "map<string, int64>"}, name="t")
BLOBS = [b"\x00", b"", None, b"x" * 100_000]
MAPS = [[("a", 1)], [], None, [("b", 2), ("c", None)]]
DATA = pa.table(
    {
        "i": pa.array([1, 2, 3, 4], pa.int64()),
        "b": pa.array(BLOBS, pa.binary()),
        "m": pa.array(MAPS, pa.map_(pa.string(), pa.int64())),
    }
)


def run(report, engine):
    if engine == "spark":
        from spark_session import session

        session()  # skips without pyspark or a JVM
    con = sv.connect()
    con.put("t", DATA)
    return report.run(con, engine)


def maps(column):
    """A map column's values as lists of pairs, whichever Arrow type it comes back as."""

    def pairs(v):
        if isinstance(v, dict):
            return list(v.items())
        return [(e["key"], e["value"]) if isinstance(e, dict) else tuple(e) for e in v]

    return [None if v is None else sorted(pairs(v)) for v in column.to_pylist()]


@pytest.mark.parametrize("engine", ENGINES)
def test_an_opaque_column_is_carried_unchanged(engine):
    q = T.filter(T.i > 0).mutate(j=T.i > 2).order_by("i").limit(10)
    report = sv.verify(q)
    assert report.issues == [], report.issues
    got = run(report, engine)
    assert got.column("b").to_pylist() == BLOBS
    assert maps(got.column("m")) == [None if v is None else sorted(v) for v in MAPS]


@pytest.mark.parametrize("engine", ENGINES)
def test_is_null_reads_an_opaque_column(engine):
    report = sv.verify(T.filter(T.b.notnull() & T.m.isnull()).select("i", "b"))
    assert report.issues == [], report.issues
    assert run(report, engine).column("i").to_pylist() == []
    report = sv.verify(T.filter(T.b.isnull()).select("i"))
    assert run(report, engine).column("i").to_pylist() == [3]


@pytest.mark.parametrize(
    ("build", "use"),
    [
        (lambda t: t.select(n=t.b.cast("string")), "a cast of it"),
        (lambda t: t.select(n=t.b == t.b), "a function, comparison, CASE or cast of it"),
        (lambda t: t.filter(t.b == t.b).select("i"), "a filter on it"),
        (lambda t: t.order_by("b"), "ORDER BY it"),
        (lambda t: t.group_by("b").agg(n=t.i.count()), "a grouping key or an aggregate of it"),
        (lambda t: t.select("i", "b").distinct(), "DISTINCT over it"),
    ],
    ids=["cast", "comparison", "filter", "order", "group", "distinct"],
)
def test_any_other_use_is_refused_naming_it(build, use):
    with pytest.raises(Unsupported, match=use) as e:
        sv.verify(build(T))
    assert "by design" in str(e.value) and "coverage issues" not in str(e.value)


def test_a_binary_constant_is_refused():
    with pytest.raises(Unsupported, match="binary constant is not modelled"):
        sv.verify(T.select(c=ibis.literal(b"x")))


def test_the_reference_evaluator_refuses_an_opaque_column():
    """The model holds no value of an opaque column, so the reference
    evaluates no plan over a table with one."""
    plan = json.loads(to_substrait_json(T.select("i", "b")))
    with pytest.raises(TypeError, match="opaque column"):
        inline_tables(plan, {"t": [(1, b"x", None)]})
