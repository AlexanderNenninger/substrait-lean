"""Spark runs a pruned plan (#1484, #1485 item 22): a plan leaves out the
struct and map columns nothing mentions, and reads the others by name."""

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.incremental import arrow_rows

pytestmark = pytest.mark.backend("spark")

TABLE = pa.table(
    {
        "d": pa.array([1, 2, 3], pa.int64()),
        "e": pa.array([10, 20, 30], pa.int64()),
        "s": pa.array([{"x": 1}, None, {"x": 3}], pa.struct([("x", pa.int64())])),
        "m": pa.array([[("a", "b")], [], None], pa.map_(pa.string(), pa.string())),
    }
)
T = ibis.table(
    {"d": "!int64", "e": "!int64", "s": "struct<x: int64>", "m": "map<string, string>"},
    name="t",
)


def test_spark_runs_a_plan_that_leaves_out_an_unused_struct_and_map():
    con = connect()
    # Spark's test loader has no Spark type for a struct or map, so the table it
    # holds is the columns the plan reads: Spark reads them by name.
    put_table(con, "t", TABLE.select(["d", "e"]))
    plan = plan_json(con, T.select(T.d, y=T.d + T.e))
    assert '"s"' not in plan and '"m"' not in plan
    spark = arrow_rows(run_plan(con, written_plan(plan), "spark"))
    assert sorted(spark) == [(1, 11), (2, 22), (3, 33)]
    assert sorted(spark) == sorted(arrow_rows(run_plan(con, written_plan(plan), "duckdb")))
