"""Engines that order doubles as `Value.le` does, NaN equal to NaN and above
`+inf` (`duckdb-nan-order`, `spark-nan-order`), sort by the double itself:
the written SQL ranks no NaN apart (`Dialect.nan_orders`, #824). Snowflake's
writer still does.

The model is the checker on the plan with the rows inlined; the written SQL
runs on DuckDB."""

from __future__ import annotations

import json
import math

import duckdb
import ibis
import pytest

from sverify._lean_eval import inline_tables, lean_values
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import to_sql
from sverify.sql.snowflake import SNOWFLAKE
from sverify_duckdb.dialect import DUCKDB
from sverify_spark.dialect import SPARK

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table(ibis.schema({"k": "int64", "x": "float64"}), name="t")
ROWS = [
    (1, math.nan),
    (2, math.inf),
    (3, -math.inf),
    (4, -0.0),
    (5, 0.0),
    (6, None),
    (7, 1.5),
    (8, -math.nan),
    (9, -2.0),
]
QUERIES = {
    "sort": T.order_by(["x", "k"]),
    "sort descending": T.order_by([ibis.desc("x"), "k"]),
    "window": T.select(T.k, r=ibis.row_number().over(order_by=["x", "k"])),
}


def keys(rows) -> list:
    return [r[0] for r in rows]


@pytest.mark.parametrize("name", QUERIES)
def test_duckdb_sorts_doubles_as_the_model(name):
    plan = to_substrait(QUERIES[name])
    sql = to_sql(json.loads(written_plan(json.dumps(plan))), DUCKDB, rows="sequence")
    db = duckdb.connect()
    db.execute("CREATE TABLE t(k BIGINT, x DOUBLE)")
    db.executemany("INSERT INTO t VALUES (?, ?)", ROWS)
    got = db.execute(sql).fetchall()
    want = lean_values(json.dumps(inline_tables(plan, {"t": ROWS})))
    if name == "window":
        assert sorted(got) == sorted(tuple(r) for r in want)
    else:
        assert keys(got) == keys(want)


def test_only_snowflake_ranks_nan_apart():
    plan = json.loads(written_plan(json.dumps(to_substrait(QUERIES["sort"]))))
    for dialect in (DUCKDB, SPARK):
        assert "THEN 1 ELSE 0 END" not in to_sql(plan, dialect, rows="multiset")
    assert "THEN 1 ELSE 0 END" in to_sql(plan, SNOWFLAKE, rows="multiset")
