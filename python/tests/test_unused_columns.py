"""A column no query mentions blocks nothing (#1484, #1485 item 22): a struct
on the DuckDB writer, a `map` on a Delta source. A query that reads the column
still refuses, and the message names the column."""

import ibis
import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.ibis_substrait import Unsupported
from sverify.incremental import arrow_rows
from sverify.io import DeltaSource

pytestmark = pytest.mark.backend("duckdb")

TABLE = pa.table(
    {
        "d": pa.array([1, 2, 3], pa.int64()),
        "e": pa.array([10, 20, 30], pa.int64()),
        "s": pa.array([{"x": 1}, None, {"x": 3}], pa.struct([("x", pa.int64())])),
    }
)
T = ibis.table({"d": "!int64", "e": "!int64", "s": "struct<x: int64>"}, name="t")


@pytest.fixture(scope="module")
def con():
    c = connect()
    put_table(c, "t", TABLE)
    return c


def test_an_unused_struct_column_does_not_block_the_duckdb_writer(con):
    plan = plan_json(con, T.select(T.d, T.e, y=T.d + T.e))
    assert '"s"' not in plan
    rows = arrow_rows(run_plan(con, written_plan(plan), "duckdb"))
    assert sorted(rows) == [(1, 10, 11), (2, 20, 22), (3, 30, 33)]


def test_polars_reads_a_pruned_plan_from_the_whole_table(con):
    """The plan names the columns it reads; the table has one more."""
    plan = plan_json(con, T.select(T.d, y=T.e * 2))
    rows = arrow_rows(run_plan(con, written_plan(plan), "polars"))
    assert sorted(rows) == [(1, 20), (2, 40), (3, 60)]


def test_a_struct_column_the_query_reads_is_still_refused_on_duckdb(con):
    w = written_plan(plan_json(con, T.select(a=T.s.x)))
    with pytest.raises(Exception, match="struct columns have no SQL form yet"):
        run_plan(con, w, "duckdb")


def test_a_struct_column_the_output_carries_is_not_dropped(con):
    assert '"s"' in plan_json(con, T.filter(T.d > 1))


def test_an_unused_struct_column_does_not_block_verify():
    sql = sv.verify("SELECT d, e, d + e AS y FROM t", tables={"t": T.schema()}, ensures=["y > 0"])
    ibis_ = sv.verify(T.select(T.d, T.e, y=T.d + T.e), ensures=[_.y > 0])
    for report in (sql, ibis_):
        assert "struct columns have no SQL form" not in str(report)


@pytest.mark.parametrize("dtype", ["binary", "map<string, int64>"])
def test_an_unused_column_does_not_block_a_sql_condition_on_ibis(dtype):
    """A SQL `ensures` on an Ibis transformation reads it through a SQL model,
    which the producer's pruning did not see into (#1958)."""
    t = ibis.table({"id": "int64", "x": dtype}, name="t")
    report = sv.verify(t.select("id"), requires={"t": ['"id" > 0']}, ensures=['"id" > 0'])
    assert report.issues == []


def test_a_condition_on_the_column_keeps_it_in_every_plan():
    """`requires` mentions `s`, the transformation does not: one schema for `t`."""
    report = sv.verify(T.select(T.d), requires={"t": [_.s.isnull() | (_.d > 0)]}, ensures=[_.d > 0])
    assert report.verdict is not None


@pytest.fixture
def delta(tmp_path):
    table = pa.table(
        {
            "id": pa.array([1, 2], pa.int64()),
            "amt": pa.array([3, 4], pa.int64()),
            "m": pa.array([[("a", "b")], [("c", "d")]], pa.map_(pa.string(), pa.string())),
        }
    )
    write_deltalake(tmp_path / "t", table)
    return DeltaSource(str(tmp_path / "t"))


def test_an_unused_map_column_does_not_refuse_a_delta_table(delta):
    delta.pipe(lambda t: t.group_by("id").agg(total=t.amt.sum()))


def test_a_map_column_the_query_reads_is_refused_naming_it(delta):
    with pytest.raises(Unsupported, match=r"column 'm' of '.*': type map<!string, string>"):
        delta.pipe(lambda t: t.select("id", "m"))


@pytest.mark.parametrize(
    "build",
    [
        lambda t: t.select("x"),
        lambda t: t.select(y=ibis.literal(b"A")),
        lambda t: t.select(y=ibis.literal(None, type="binary")),
    ],
    ids=["column", "constant", "null"],
)
def test_binary_values_are_refused_by_design(build):
    """Ruling 186 (#1918): sverify reads no binary values, and says how to get
    around it without an engine's own text form of a BLOB."""
    t = ibis.table({"id": "int64", "x": "binary"}, name="t")
    with pytest.raises(Exception, match="encode them as text at the source"):
        sv.verify(build(t))
