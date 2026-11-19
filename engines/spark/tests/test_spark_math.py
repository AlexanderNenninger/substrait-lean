"""Spark runs the elementary functions of doubles (`exp`, the logarithms, the
trigonometric functions): `StrictMath`'s and `java.lang.Math`'s values, within
a few ulps of libm's (`fp.elem` and `fp.log` rows, spark-elem-rounding), and
the domain errors raise as the reference's do, where Spark would give NaN or NULL."""

from __future__ import annotations

import json
import math
import random
from collections.abc import Callable
from typing import Any

import ibis
import pytest

from sverify._lean_eval import inline_tables, lean_values
from sverify.contracts import decode_double
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import to_sql
from sverify_spark.dialect import SPARK
from sverify_spark.engine import session
from test_negzero_writer import T, X

pytestmark = pytest.mark.backend("spark")

#: S + R per function in ulps (`EngineProfile.elemUlps`, spark-ulp-libm), and the bound on
#: the result's magnitude `Epsilon.resultMag` uses (`None`: the largest result in the rows).
#: The plan's bound is `2 · (S + R) · 2⁻⁵³ · mag` in absolute terms.
BOUNDS: dict[str, tuple[float, float | None]] = {
    "exp": (2, 1.0),
    "ln": (2, 745.0), "log10": (3, 324.0), "log2": (5, 1075.0), "log(b)": (5.5, None),
    "sin": (2, 1.0), "cos": (2, 1.0), "tan": (4, None),
    "asin": (2, math.pi / 2), "acos": (2, math.pi), "atan": (2, math.pi / 2),
}  # fmt: skip
GUARD = 2.0**20


def kpi(n: int) -> list[float]:
    """The doubles nearest `k·π/2` for the convergents of `π/2` and other `k`, below 2²⁰."""
    ks = [1, 2, 3, 7, 11, 22, 333, 355, 103993, 104348, 208341, 312689, 833719, 1146408, 4272943]
    ks = [k for k in ks if k * math.pi / 2 < GUARD]
    ks += random.Random(n).sample(range(1, 600000), 12)
    return [s * k * math.pi / 2 for k in ks for s in (1.0, -1.0)]


def draws(rng: random.Random, lo: float, hi: float, n: int = 40) -> list[float]:
    return [rng.uniform(lo, hi) for _ in range(n)]


def logs(rng: random.Random) -> list[float]:
    near1 = [1.0, math.nextafter(1.0, 2.0), math.nextafter(1.0, 0.0), 1.0 + 1e-9, 1.0 - 1e-9]
    return [*near1, 5e-324, 1e-310, 2.2250738585072014e-308, 0.5, 2.0, 10.0, 1e300,
            *[math.exp(rng.uniform(-700, 700)) for _ in range(30)]]  # fmt: skip


def inputs(label: str) -> list[float]:
    rng = random.Random(label)
    match label:
        case "ln" | "log10" | "log2":
            return logs(rng)
        case "exp":
            return [
                *draws(rng, -300, 700),
                0.0,
                1.0,
                -1.0,
                1e-10,
                709.0,
                -300.0,
            ]  # the scale reads from e^-310
        case "sin" | "cos":
            return [*draws(rng, -GUARD, GUARD), *kpi(1), 0.0, 5e-324, 1e-310, GUARD, -GUARD]
        case "tan":
            return [*draws(rng, -GUARD, GUARD), *kpi(2), 0.0, 5e-324, 1e-310, GUARD, -GUARD]
        case "asin" | "acos":
            return [*draws(rng, -1, 1), 0.0, 1.0, -1.0, 5e-324, math.nextafter(1.0, 0.0)]
        case _:
            return [*draws(rng, -1e6, 1e6), 0.0, 5e-324, 1e300, -1e300]


FUNCS: dict[str, Callable[[], Any]] = {
    "exp": lambda: X.exp(),
    "ln": lambda: X.ln(), "log10": lambda: X.log10(), "log2": lambda: X.log2(),
    "sin": lambda: X.sin(), "cos": lambda: X.cos(), "tan": lambda: X.tan(),
    "asin": lambda: X.asin(), "acos": lambda: X.acos(), "atan": lambda: X.atan(),
}  # fmt: skip


def on_spark(expr, xs: list[float]) -> list[float | None]:
    sql = to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)
    s = session()
    s.createDataFrame(list(enumerate(xs)), "k BIGINT, x DOUBLE").createOrReplaceTempView("t")
    return [r[1] for r in sorted(s.sql(sql).collect(), key=lambda r: r[0])]


#: The checker prints doubles with six decimals, so its values are read through a product
#: with a power of two, which is exact: a result of 1e-9 prints as 1e-9 · 2⁵⁰⁰, to the digit.
SCALE = 2.0**500


def reference_values(expr, rows: list[tuple]) -> dict[int, float | None]:
    """The checker's values of `expr` over `rows`, the reference binary's `libm`, as doubles
    (`None`: below what the scale prints, a subnormal result)."""
    scaled = expr.select(expr.k, v=expr.v * SCALE)
    plan = inline_tables(to_substrait(scaled), {"t": rows})
    out: dict[int, float | None] = {}
    for k, v in lean_values(json.dumps(plan)):
        f = decode_double(v) if isinstance(v, int) else float(v)
        out[k] = f / SCALE if f != 0.0 else None
    return out


def reference(expr, xs: list[float]) -> list[float | None]:
    got = reference_values(expr, list(enumerate(xs)))
    return [got[k] for k in range(len(xs))]


def check(label: str, expr, xs: list[float]) -> None:
    s_plus_r, mag = BOUNDS[label]
    got, want = on_spark(expr, xs), reference(expr, xs)
    if mag is None:
        mag = max(abs(w) for w in want if w is not None)
    eps = 2 * s_plus_r * 2.0**-53 * mag
    for x, g, w in zip(xs, got, want, strict=True):
        w = 0.0 if w is None else w  # a subnormal or zero result, within eps of 0 anyway
        if label == "exp":  # `rule_exp`: 4u · exp x, one ulp on each side
            eps = 4 * 2.0**-53 * abs(w) + 1e-300
        assert g is not None and abs(g - w) <= eps, (label, x, g, w, eps)


@pytest.mark.parametrize("label", FUNCS)
def test_spark_is_within_the_plans_bound_of_the_reference(label: str) -> None:
    xs = inputs(label)
    check(label, T.select(T.k, v=FUNCS[label]()), xs)


@pytest.mark.parametrize("order", ["x first", "base first"])
def test_log_with_a_base_is_within_the_plans_bound(order: str) -> None:
    """`log(b, x)` for `b` and `x` near 1 and far from it, in both argument orders."""
    rng = random.Random(order)
    others = [x for x in logs(rng)[:20] if x != 1.0]
    pairs = [(b, x) for b in (1.0000000001, 1.5, 3.0, 1e-5, 2.0, 1e10, 0.999999999) for x in others]
    t = ibis.table({"k": "int64", "x": "float64", "b": "float64"}, name="t")
    expr = t.select(t.k, v=t.x.log(t.b) if order == "x first" else t.b.log(t.x))
    cols = [(i, x, b) for i, (b, x) in enumerate(pairs)]
    sql = to_sql(written_plan(json.dumps(to_substrait(expr))), SPARK)
    s = session()
    s.createDataFrame(cols, "k BIGINT, x DOUBLE, b DOUBLE").createOrReplaceTempView("t")
    got = {r[0]: r[1] for r in s.sql(sql).collect()}
    want = reference_values(expr, cols)
    bound = 2 * 5.5 * 2.0**-53 * max(abs(w) for w in want.values() if w is not None)
    for k, w in want.items():
        assert abs(got[k] - (w or 0.0)) <= bound, (pairs[k], got[k], w, bound)


def test_a_base_of_one_raises() -> None:
    t = ibis.table({"k": "int64", "x": "float64", "b": "float64"}, name="t")
    sql = to_sql(written_plan(json.dumps(to_substrait(t.select(t.k, v=t.x.log(t.b))))), SPARK)
    s = session()
    s.createDataFrame([(0, 5.0, 1.0)], "k BIGINT, x DOUBLE, b DOUBLE").createOrReplaceTempView("t")
    with pytest.raises(Exception, match="domain"):
        s.sql(sql).collect()


@pytest.mark.parametrize(
    ("label", "x"),
    [("ln", 0.0), ("ln", -1.0), ("log10", -2.0), ("log2", 0.0), ("asin", 1.5), ("acos", 2.0)],
)
def test_a_domain_error_raises_where_spark_gives_null_or_nan(label: str, x: float) -> None:
    with pytest.raises(Exception, match="domain"):
        on_spark(T.select(T.k, v=FUNCS[label]()), [x])
