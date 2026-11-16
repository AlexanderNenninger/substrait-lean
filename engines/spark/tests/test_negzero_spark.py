"""Spark's writer prints raw doubles (D31, #1461), as `test_negzero_writer.py`
checks DuckDB's: the written SQL run on a local session against the model, read
by the sign of a zero. Only a zero class's pick (`MIN`, `MAX`) is the writer's
canonical `+0.0`, since Spark's depends on order and partitioning."""

from __future__ import annotations

import json
from typing import Any

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import Unsupported, to_sql
from sverify_spark.dialect import SPARK
from sverify_spark.engine import session
from test_negzero_writer import NEG_ZERO, T, X, model, signed

pytestmark = pytest.mark.backend("spark")


def on_spark(expr, rows: list[tuple[int, float]], parts: int = 1) -> list[tuple[int, Any]]:
    sql = to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)
    s = session()
    s.createDataFrame(rows, "k BIGINT, x DOUBLE").repartition(parts).createOrReplaceTempView("t")
    return sorted((r[0], signed(r[1])) for r in s.sql(sql).collect())


STORED = {
    "x": T.select(T.k, v=X),
    "-x": T.select(T.k, v=-X),
    "sqrt(x)": T.select(T.k, v=X.sqrt()),
    "x * -1.0": T.select(T.k, v=X * -1.0),
    "x = 0.0": T.select(T.k, v=(X == 0.0)),
    "x < 0.0": T.select(T.k, v=(X < 0.0)),
}


@pytest.mark.parametrize("label", STORED)
def test_a_stored_zero_is_the_models_on_spark(label: str) -> None:
    rows = [(0, NEG_ZERO), (1, 0.0), (2, 1.5)]
    assert on_spark(STORED[label], rows) == model(STORED[label], rows), label


def test_atan2_is_refused_where_spark_differs_from_the_reference() -> None:
    """Spark adds `0.0` to `atan2`'s arguments: `atan2(-0.0, -1)` is `π` where
    the reference gives `-π` (spark-zero-sign), so the writer refuses it."""
    expr = T.select(T.k, v=(X * -1.0).atan2(-1.0))
    with pytest.raises(Unsupported, match="atan2|power"):
        to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)


@pytest.mark.parametrize("parts", [1, 4])
@pytest.mark.parametrize("order", [[0, 1, 2, 3], [2, 3, 0, 1], [3, 2, 1, 0]])
def test_min_and_max_of_mixed_zeros_are_the_canonical_zero(order, parts) -> None:
    """Spark's `MIN` and `MAX` of equal zeros keep whichever it saw first, by
    order and partitioning (spark-zero-order): the writer prints `+0.0`."""
    base = [(0, NEG_ZERO), (1, 0.0), (2, NEG_ZERO), (3, 0.0)]
    rows = [base[i] for i in order]
    for agg in (X.min(), X.max()):
        expr = T.aggregate(v=agg).mutate(k=ibis.literal(0)).select("k", "v")
        assert on_spark(expr, rows, parts) == [(0, (0.0, 1.0))]


def test_group_keys_and_distinct_rows_are_canonical_on_spark() -> None:
    rows = [(0, NEG_ZERO), (1, 0.0), (2, NEG_ZERO)]
    keys = T.group_by("x").aggregate(n=T.k.count()).select(k=_.n, v=_.x)
    assert on_spark(keys, rows) == [(3, (0.0, 1.0))]
    assert on_spark(T.select(T.k * 0, v=X).distinct(), rows) == [(0, (0.0, 1.0))]


@pytest.mark.parametrize("which", ["sqrt", "atan2"])
def test_a_plan_with_sqrt_or_atan2_is_refused_on_spark(which: str) -> None:
    """The verdict today: `fp.elem` reads `pow_one_inf`, which Spark refuses
    (spark-math-domain, spark-elem-rounding), so a plan with `sqrt` or `atan2`
    does not run on Spark, and its `zero_sign` row is not what refuses it."""
    con = sv.connect()
    con.create("t", ibis.schema({"k": "int64", "x": "float64"}), [])
    t = con.table("t")
    expr = t.select(t.k, v=t.x.abs().sqrt() if which == "sqrt" else t.x.atan2(-1.0))
    report = sv.verify(expr, requires={"t": [_.x.between(-100, 100)]})
    route = routes.choose(report, "spark")
    assert route.refused and "pow_one_inf" in route.reason, route
