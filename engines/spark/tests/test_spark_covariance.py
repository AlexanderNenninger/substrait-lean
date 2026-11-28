"""Covariance and correlation on Spark (#2540): Spark's own Welford
co-moment (spark-covar, spark-corr), clamped and with the reference's NULL
cases, against DuckDB's, equal up to rounding."""

import math

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan

pytestmark = pytest.mark.backend("spark")

T = ibis.table({"k": "string", "x": "float64", "y": "int64"}, name="t")
BIG = 1e12
ROWS = pa.table(
    {
        "k": ["a", "a", "a", "a", "b", "c", "c", "d", "d", "e", "e", "e", "f", "f"],
        "x": [4.0, 7.0, 13.0, 16.0, 1.0, 2.0, 2.0, None, 3.0, BIG + 4, BIG + 7, BIG + 13,
              math.nan, 1.0],
        "y": [1, 3, None, 10, 5, 1, 2, 4, 4, 8, 14, 26, 1, 2],
    }
)  # fmt: skip


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def both(spark, table: pa.Table, expr) -> tuple[list[tuple], list[tuple]]:
    con = connect()
    put_table(con, "t", table)
    plan = written_plan(plan_json(con, expr))
    return tuple(
        sorted(
            (tuple(r.values()) for r in run_plan(con, plan, e, tie_free=False).to_pylist()),
            key=lambda r: r[0],
        )
        for e in ("duckdb", spark)
    )


def close(a, b) -> bool:
    if a is None or b is None:
        return a is b
    if math.isnan(a) or math.isnan(b):
        return math.isnan(a) and math.isnan(b)
    return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-9)


def test_covariance_and_correlation_are_duckdbs(spark):
    q = T.group_by("k").aggregate(
        cs=T.x.cov(T.y), cp=T.x.cov(T.y, how="pop"), r=T.x.corr(T.y), rp=T.x.corr(T.y, how="pop")
    )
    duck, got = both(spark, ROWS, q)
    assert [r[0] for r in got] == [r[0] for r in duck]
    for g, d in zip(got, duck, strict=True):
        assert all(close(a, b) for a, b in zip(g[1:], d[1:], strict=True)), (g, d)
    # One pair: NULL sample covariance, 0.0 population; a constant side: NULL correlation.
    by = {r[0]: r for r in got}
    assert by["b"][1] is None and by["b"][2] == 0.0 and by["c"][3] is None


def test_an_infinite_side_raises(spark):
    rows = pa.table({"k": ["a", "a"], "x": [1.0, math.inf], "y": [1, 2]})
    con = connect()
    put_table(con, "t", rows)
    plan = written_plan(plan_json(con, T.group_by("k").aggregate(c=T.x.cov(T.y))))
    with pytest.raises(Exception, match="domain error"):
        run_plan(con, plan, spark, tie_free=False)
