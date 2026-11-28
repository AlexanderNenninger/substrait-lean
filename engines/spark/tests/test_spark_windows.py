"""Windows Spark runs without an ORDER BY, and the variance over a frame
(#2540), against DuckDB, the oracle."""

import math

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.errors import UnsupportedError

pytestmark = pytest.mark.backend("spark")

#: A frame of the row and its neighbours in `k`.
NEAR = ibis.window(group_by="k", order_by="i", preceding=1, following=1)
T = ibis.table({"k": "string", "q": "int64", "x": "float64", "i": "!int64"}, name="t")
ROWS = pa.table(
    {
        "k": ["a", "a", "b", "a", None, "b", "c"],
        "q": [1, None, 5, -3, 7, 2, None],
        "x": [1.5, 3.25, None, -2.0, 0.5, 8.0, 4.0],
        "i": [0, 1, 2, 3, 4, 5, 6],
    }
)


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def both(spark, expr) -> tuple[list[tuple], list[tuple]]:
    con = connect()
    put_table(con, "t", ROWS)
    plan = written_plan(plan_json(con, expr))

    def rows(engine) -> list[tuple]:
        out = run_plan(con, plan, engine, tie_free=False).to_pylist()
        return sorted((tuple(r.values()) for r in out), key=lambda r: r[3])

    return rows("duckdb"), rows(spark)


@pytest.mark.parametrize(
    "build",
    [lambda: T.q.sum().over(group_by="k"),
     lambda: (T.q * 2).sum().over(group_by="k"),
     lambda: T.q.count().over(group_by="k")],
)  # fmt: skip
def test_an_aggregate_over_the_whole_partition_needs_no_order(spark, build):
    duck, got = both(spark, T.mutate(o=build()))
    assert got == duck


@pytest.mark.parametrize(
    "build",
    [lambda: T.x.std().over(group_by="k"),
     lambda: T.x.var(how="pop").over(group_by="k"),
     lambda: T.x.var(how="pop").over(ibis.window(order_by="i", preceding=2, following=0)),
     lambda: T.x.std(how="pop").over(NEAR)],
)  # fmt: skip
def test_the_variance_over_a_frame_is_duckdbs(spark, build):
    """Spark's own `VAR_*` and `STDDEV_*` (spark-var-stddev), clamped as
    DuckDB's are: equal up to rounding, NULL for no values or a sample of one."""
    duck, got = both(spark, T.mutate(o=build()))
    assert [r[:4] for r in got] == [r[:4] for r in duck]
    for g, d in zip(got, duck, strict=True):
        assert (g[4] is None) == (d[4] is None)
        if d[4] is not None:
            assert math.isclose(g[4], d[4], rel_tol=1e-12, abs_tol=1e-12)


def test_row_number_without_an_order_stays_refused(spark):
    con = connect()
    put_table(con, "t", ROWS)
    plan = written_plan(plan_json(con, T.mutate(o=ibis.row_number().over(group_by="k"))))
    with pytest.raises(UnsupportedError, match="ORDER BY"):
        run_plan(con, plan, spark, tie_free=False)
