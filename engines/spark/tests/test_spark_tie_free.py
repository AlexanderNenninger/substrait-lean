"""A proved, tie-free window reaches Spark's SQL writer as `deterministic`
(B5 of the 1.0 API review): `Report.run` and a stored node's refresh pass
the report's fact, so Spark takes a window it would refuse without it."""

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.io import StaticSource

pytestmark = pytest.mark.backend("spark")

ROWS = pa.table({"k": [1, 1, 2], "ts": [1, 2, 1], "v": [10, 20, 30]})


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def _prev(t):
    w = ibis.window(group_by="k", order_by="ts")
    return t.mutate(prev=t.v.lag(1).over(w))


def test_a_tie_free_window_runs_on_spark(spark):
    t = ibis.table({"k": "int64", "ts": "int64", "v": "int64"}, name="t")
    keyed = sv.verify(_prev(t), requires={"t": [sv.unique("k", "ts")]})
    assert keyed.verdict == sv.Verdict.PROVED and keyed.deterministic
    con = sv.connect()
    con.put("t", ROWS)
    out = keyed.run(con, spark)
    assert sorted(out.select(["k", "ts", "prev"]).to_pylist(), key=lambda r: (r["k"], r["ts"])) == [
        {"k": 1, "ts": 1, "prev": None},
        {"k": 1, "ts": 2, "prev": 10},
        {"k": 2, "ts": 1, "prev": None},
    ]
    # Without the key, rows may tie: Spark runs the window with them open.
    loose = sv.verify(_prev(t))
    assert not loose.deterministic
    assert len(loose.run(con, spark)) == len(ROWS)


def test_a_tie_free_window_refreshes_on_spark(spark):
    @sv.transform(requires={"t": [sv.unique("k", "ts")]})
    def prev(t):
        return _prev(t)

    node = StaticSource(ROWS, name="t").pipe(prev)
    assert node.report is not None and node.report.deterministic
    node.refresh(engine=spark)
    got = sorted(node.to_arrow().to_pylist(), key=lambda r: (r["k"], r["ts"]))
    assert [r["prev"] for r in got] == [None, 10, None]


def test_a_table_with_an_empty_chunk_loses_no_rows(spark):
    """`createDataFrame` of Arrow chunks of 3, 0 and 2 rows gave back 3 rows
    (#1608): the loader makes one chunk."""
    from sverify_spark.engine import put_tables

    def chunk(xs):
        return pa.record_batch({"x": pa.array(xs, pa.int64())})

    table = pa.Table.from_batches([chunk([1, 2, 3]), chunk([]), chunk([4, 5])])
    put_tables({"chunked": table}, spark)
    assert spark.sql("SELECT count(*) AS n FROM chunked").collect()[0]["n"] == 5
