"""Spark's writer prints raw doubles (D31, #1461), as `test_negzero_writer.py`
checks DuckDB's: the written SQL run on a local session against the model, read
by the sign of a zero. Only a zero class's pick (`MIN`, `MAX`) is the writer's
canonical `+0.0`, since Spark's depends on order and partitioning."""

from __future__ import annotations

import json
import math
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
    with pytest.raises(Unsupported, match="StrictMath"):
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


@pytest.mark.parametrize("stored_right", [True, False])
@pytest.mark.parametrize("pair", [(NEG_ZERO, 0.0), (0.0, NEG_ZERO)])
def test_least_and_greatest_of_both_zeros_keep_the_first_argument_on_spark(pair, stored_right):
    """The reference keeps the first argument unless the second is strictly
    better (`Value.pick`); Spark's `greatest` and `least` do too
    (spark-zero-order, probe `double-compare`). The other argument is a second
    stored column, or a literal."""
    if stored_right:
        t = ibis.table(ibis.schema({"k": "int64", "x": "float64", "y": "float64"}), name="t")
        frame, cols, other = [(0, *pair)], "k BIGINT, x DOUBLE, y DOUBLE", t.y
    else:
        t = T
        frame, cols, other = [(0, pair[0])], "k BIGINT, x DOUBLE", ibis.literal(pair[1])
    s = session()
    s.createDataFrame(frame, cols).createOrReplaceTempView("t")
    for fn in (ibis.least, ibis.greatest):
        sql = to_sql(written_plan(json.dumps(to_substrait(t.select(t.k, v=fn(t.x, other))))), SPARK)
        got = [signed(r[1]) for r in s.sql(sql).collect()]
        assert got == [(pair[0], math.copysign(1.0, pair[0]))], sql


def test_group_keys_and_distinct_rows_are_canonical_on_spark() -> None:
    rows = [(0, NEG_ZERO), (1, 0.0), (2, NEG_ZERO)]
    keys = T.group_by("x").aggregate(n=T.k.count()).select(k=_.n, v=_.x)
    assert on_spark(keys, rows) == [(3, (0.0, 1.0))]
    assert on_spark(T.select(T.k * 0, v=X).distinct(), rows) == [(0, (0.0, 1.0))]


@pytest.mark.parametrize("fn", ["sqrt", "exp", "sin", "cos", "tan", "asin", "acos", "atan", "ln"])
def test_the_unary_functions_route_to_spark(fn: str) -> None:
    """`fp.elem` has no `pow_one_inf` (ruling 163): `sqrt`, `exp` and the trigonometric
    functions reach Spark, as the logarithms do."""
    con = sv.connect()
    con.create("t", ibis.schema({"k": "int64", "x": "float64"}), [])
    t = con.table("t")
    arg = t.x.abs() + 1.0 if fn in {"ln"} else t.x.abs() / 200.0
    route = routes.choose(
        sv.verify(t.select(t.k, v=getattr(arg, fn)()), requires={"t": [_.x.between(-100, 100)]}),
        "spark",
    )
    assert not route.refused, route


@pytest.mark.parametrize(
    ("which", "group", "option"),
    [("power", "fp.pow", "pow_one_inf"), ("atan2", "fp.atan2", "zero_sign")],
)
def test_power_and_atan2_are_refused_on_spark_by_their_own_group(
    which: str, group: str, option: str
) -> None:
    """Spark's `power` is `StrictMath.pow` (`pow(1, ±∞)` is NaN) and its `atan2` adds `0.0`
    to its arguments (`atan2(-0.0, -1)` is π): each is refused, naming its group."""
    con = sv.connect()
    con.create("t", ibis.schema({"k": "int64", "x": "float64"}), [])
    t = con.table("t")
    expr = t.select(t.k, v=t.x**2.5 if which == "power" else t.x.atan2(-1.0))
    report = sv.verify(expr, requires={"t": [_.x.between(1, 100)]})
    route = routes.choose(report, "spark")
    assert route.refused and group in route.why and option in route.why, route
