"""Spark runs the elementary functions of doubles (`exp`, the logarithms, the
trigonometric functions): `StrictMath`'s and `java.lang.Math`'s values, within
a few ulps of libm's (`fp.elem` and `fp.log` rows, spark-elem-rounding), and
the domain errors raise as the reference's do, where Spark would give NaN or NULL."""

from __future__ import annotations

import json
import math
from collections.abc import Callable

import pytest

from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import to_sql
from sverify_spark.dialect import SPARK
from sverify_spark.engine import session
from test_negzero_writer import T, X

pytestmark = pytest.mark.backend("spark")

#: S + R per function in ulps (`EngineProfile.elemUlps`, spark-ulp-libm): the plan's bound
#: from libm's value, which Python's `math` calls.
ULPS = {"ln": 2, "log10": 3, "log2": 5, "log(3)": 5.5, "sin": 2, "cos": 2, "tan": 4,
        "asin": 2, "acos": 2, "atan": 2, "exp": 2}  # fmt: skip

INPUTS = [
    1.0000000000000002,
    0.9999999999999999,
    0.1,
    0.5,
    0.9,
    1.0,
    1.5,
    2.0,
    3.7,
    10.0,
    123.456,
    1e-5,
    700.0,
]
UNIT = [-0.9, -0.5, -0.1, 0.0, 0.3, 0.75, 1.0]

#: label -> (expression, libm's value, inputs inside the domain).
FUNCS: dict[str, tuple[Callable, Callable[[float], float], list[float]]] = {
    "exp": (lambda: X.exp(), math.exp, [*INPUTS, -3.0, -700.0]),
    "ln": (lambda: X.ln(), math.log, INPUTS),
    "log10": (lambda: X.log10(), math.log10, INPUTS),
    "log2": (lambda: X.log2(), math.log2, INPUTS),
    "log(3)": (lambda: X.log(3.0), lambda x: math.log(x) / math.log(3.0), INPUTS),
    "sin": (lambda: X.sin(), math.sin, [*INPUTS, -2.5, math.pi, 1048576.0, 1.5707963267948966]),
    "cos": (lambda: X.cos(), math.cos, [*INPUTS, -2.5, math.pi / 2, 1048576.0]),
    "tan": (lambda: X.tan(), math.tan, [*INPUTS, -2.5]),
    "asin": (lambda: X.asin(), math.asin, UNIT),
    "acos": (lambda: X.acos(), math.acos, UNIT),
    "atan": (lambda: X.atan(), math.atan, [*INPUTS, -2.5]),
}


def on_spark(expr, xs: list[float]) -> list[float | None]:
    sql = to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)
    s = session()
    s.createDataFrame(list(enumerate(xs)), "k BIGINT, x DOUBLE").createOrReplaceTempView("t")
    return [r[1] for r in sorted(s.sql(sql).collect(), key=lambda r: r[0])]


@pytest.mark.parametrize("label", FUNCS)
def test_spark_is_within_ulps_of_libm(label: str) -> None:
    make, libm, xs = FUNCS[label]
    got = on_spark(T.select(T.k, v=make()), xs)
    for x, g in zip(xs, got, strict=True):
        want = libm(x)
        assert g is not None and abs(g - want) <= ULPS[label] * math.ulp(want) + 1e-300, (
            label,
            x,
            g,
            want,
        )


@pytest.mark.parametrize(
    ("label", "x"),
    [("ln", 0.0), ("ln", -1.0), ("log10", -2.0), ("log2", 0.0), ("asin", 1.5), ("acos", 2.0)],
)
def test_a_domain_error_raises_where_spark_gives_null_or_nan(label: str, x: float) -> None:
    make = FUNCS[label.split("(")[0]][0]
    with pytest.raises(Exception, match="domain"):
        on_spark(T.select(T.k, v=make()), [x])
