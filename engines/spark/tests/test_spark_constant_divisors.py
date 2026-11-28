"""Integer `/` and `%` by a constant other than 0 are written without the zero
guard (#2540): the guard repeated the dividend, and nested, as the lift's
calendar arithmetic nests them, Spark's SQL grew past its driver's heap."""

import json

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan
from sverify.sql import to_sql
from sverify_spark.dialect import SPARK

pytestmark = pytest.mark.backend("spark")

T = ibis.table({"i": "!int64", "a": "int64", "b": "int64"}, name="t")
MIN = -(2**63)
ROWS = pa.table(
    {"i": [0, 1, 2, 3, 4, 5], "a": [7, -7, None, 0, MIN + 1, 2**63 - 1], "b": [2, -3, 1, 5, 4, 0]}
)


def _plan(con, expr) -> str:
    return written_plan(plan_json(con, expr))


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


@pytest.mark.parametrize(
    "build",
    [lambda: T.a // 4, lambda: T.a // -1, lambda: T.a % 4, lambda: T.a % -3, lambda: T.a % -1],
)
def test_a_constant_divisor_is_duckdbs(spark, build):
    con = connect()
    put_table(con, "t", ROWS)
    plan = _plan(con, T.select("i", o=build()))
    assert "division by zero" not in to_sql(json.loads(plan), SPARK)
    duck, got = (
        sorted(tuple(r.values()) for r in run_plan(con, plan, e, tie_free=False).to_pylist())
        for e in ("duckdb", spark)
    )
    assert got == duck


def test_a_column_divisor_keeps_its_guard(spark):
    con = connect()
    put_table(con, "t", ROWS)
    plan = _plan(con, T.select("i", o=T.a // T.b))
    assert "division by zero" in to_sql(json.loads(plan), SPARK)
    with pytest.raises(Exception, match="division by zero"):
        run_plan(con, plan, spark, tie_free=False)


def test_a_date_from_columns_is_small(monkeypatch):
    """The lift's calendar check of `ibis.date(2024, m, 1)`: 175 KB of Spark
    SQL before, 43 KB now."""
    from sverify import _support

    con = connect()
    put_table(con, "t", ROWS)
    plan = _plan(con, T.select(x=ibis.date(2024, T.a.clip(1, 12), 1)))
    # Spark still refuses the date guard itself.
    monkeypatch.setattr(_support, "_runs", lambda name, engine, field: True)
    assert len(to_sql(json.loads(plan), SPARK)) < 50_000
