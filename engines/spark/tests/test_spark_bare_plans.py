"""Spark takes FETCH and windows over a named table with the ties open
(#1484, ruling 98): `to_sql` writes what the runner sends, and the runner's
result is one `Rel.Allowed` allows, with a total sort or with ties."""

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.engines import to_sql
from sverify.io import StaticSource
from sverify_spark.dialect import SPARK

pytestmark = pytest.mark.backend("spark")

T = ibis.table({"k": "!int64", "a": "!int64", "v": "!int64"}, name="t")
TOTAL = pa.table({"k": [1, 1, 2, 2, 3], "a": [5, 4, 3, 2, 1], "v": [10, 20, 30, 40, 50]})
TIES = pa.table({"k": [1, 1, 1, 2, 2], "a": [1, 1, 2, 7, 7], "v": [10, 20, 30, 40, 50]})


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def run(spark, table: pa.Table, expr) -> list[dict]:
    con = connect()
    put_table(con, "t", table)
    plan = written_plan(plan_json(con, expr))
    return run_plan(con, plan, spark, tie_free=False).to_pylist()


def window():
    return ibis.window(group_by="k", order_by="a")


def test_a_top_n_over_a_total_sort_is_the_reference_rows(spark):
    got = run(spark, TOTAL, T.order_by(["k", "a"]).limit(4))
    assert [(r["k"], r["a"]) for r in got] == [(1, 4), (1, 5), (2, 2), (2, 3)]


def test_windows_over_a_total_sort_are_the_reference_rows(spark):
    q = T.select("k", "a", rn=ibis.row_number().over(window()), prev=T.v.lag().over(window()))
    got = sorted(run(spark, TOTAL, q), key=lambda r: (r["k"], r["a"]))
    assert [(r["rn"], r["prev"]) for r in got] == [
        (0, None),
        (1, 20),
        (0, None),
        (1, 40),
        (0, None),
    ]


def test_a_top_n_over_ties_takes_rows_the_sort_allows(spark):
    got = run(spark, TIES, T.order_by(["k", "a"]).limit(2))
    # The two smallest by (k, a): both rows of (1, 1), whichever v they carry.
    assert sorted((r["k"], r["a"]) for r in got) == [(1, 1), (1, 1)]
    assert {r["v"] for r in got} == {10, 20}


def test_windows_over_ties_number_and_lag_along_one_arrangement(spark):
    """Two functions that read the order of tied rows share one arrangement:
    the row numbered n + 1 has the value of the row numbered n as its `lag`."""
    q = T.select("k", "a", "v", rn=ibis.row_number().over(window()), prev=T.v.lag().over(window()))
    for k in (1, 2):
        part = sorted((r for r in run(spark, TIES, q) if r["k"] == k), key=lambda r: r["rn"])
        assert [r["rn"] for r in part] == list(range(len(part)))
        assert part[0]["prev"] is None
        assert all(part[i + 1]["prev"] == part[i]["v"] for i in range(len(part) - 1))


def test_to_sql_for_spark_is_what_the_runner_sends():
    plan = written_plan(plan_json(None, T.select(rn=ibis.row_number().over(window()))))
    assert to_sql(plan, "spark") == to_sql(plan, SPARK, rows="multiset")
    with pytest.raises(Exception, match='rows="multiset"'):
        to_sql(plan, "spark", rows="sequence")


def test_a_node_without_a_report_writes_the_sql_a_refresh_runs():
    node = StaticSource(TIES, name="t").pipe(
        lambda t: t.select("k", rn=ibis.row_number().over(window()))
    )
    assert node.to_sql("spark") == to_sql(node.internal_plan, SPARK, finite=True)


def test_snowflake_and_spark_share_the_refusal_text():
    plan = written_plan(plan_json(None, T.select(rn=ibis.row_number().over(window()))))
    for engine in ("spark", "snowflake"):
        with pytest.raises(Exception, match='tables have no row order, so rows="sequence"'):
            to_sql(plan, engine, rows="sequence")
