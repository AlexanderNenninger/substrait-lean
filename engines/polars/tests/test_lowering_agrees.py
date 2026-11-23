"""The generated lowering to Polars, as the translation writes it, gives the
reference's values (#271).

The Lean build generates Polars's lowering and proves each template gives the
reference's outcome under `Profile.polars` (`Lowering.polars_exact`,
`engines/polars/Sverify/Polars/Lowering.lean`). The translation writes those
templates through `sverify_polars.lowering`. This test runs each template
through Polars on the edge cases of each function's facts and compares with
the reference's value computed here: what is trusted is that the interpreter
writes each call as Polars computes it, which these cases pin.
"""

import math

import polars as pl
import pytest

from sverify.sql import lowering as table_export
from sverify_polars import lowering

pytestmark = pytest.mark.backend("polars")

MIN, MAX = -(2**63), 2**63 - 1


def lowered(fn: str, *xs: pl.Expr) -> pl.Expr:
    """`fn` as the interpreter writes its template."""
    e = lowering.render(fn, xs)
    assert e is not None, fn
    return e


def run(exprs: dict[str, pl.Expr], cols: dict[str, pl.Series]) -> dict[str, list]:
    out = pl.LazyFrame(cols).select(**exprs).collect(engine="streaming")
    return {k: out[k].to_list() for k in exprs}


def test_the_table_covers_what_polars_computes_its_own_way():
    """`round`, `round_even`, `ceil`, integer `//` and `%` have templates; `%` of doubles has
    no entry (refused); everything else is native, and `render` gives None."""
    assert set(table_export.table("polars")) == {
        "Substrait.UnFn.fround", "Substrait.UnFn.froundEven", "Substrait.UnFn.fceil",
        "idiv", "imod",
    }  # fmt: skip
    assert lowering.render("fadd", [pl.col("a"), pl.col("b")]) is None


def _tdiv(a: int, b: int) -> int:
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def test_division_truncates():
    """`//` and `%` truncate (`Int.tdiv`, `Int.tmod`) on every sign
    combination and at the bounds. `MIN // -1` and a zero divisor are left
    out: the reference raises there, and the translation guards them
    (`div_overflows`, `zero_divisor`)."""
    edge = [MIN, MIN + 1, -7, -6, -2, -1, 0, 1, 2, 6, 7, MAX - 1, MAX]
    pairs = [(a, b) for a in edge for b in edge if b != 0 and (a, b) != (MIN, -1)]
    cols = {
        "a": pl.Series([a for a, _ in pairs] + [None, 1], dtype=pl.Int64),
        "b": pl.Series([b for _, b in pairs] + [1, None], dtype=pl.Int64),
    }
    a, b = pl.col("a"), pl.col("b")
    got = run(
        {
            "div": lowered("idiv", a, b).cast(pl.Int64),
            "mod": lowered("imod", a, b).cast(pl.Int64),
        },
        cols,
    )
    assert got["div"] == [_tdiv(x, y) for x, y in pairs] + [None, None]
    assert got["mod"] == [x - y * _tdiv(x, y) for x, y in pairs] + [None, None]


def _round(x: float) -> float:
    """`roundMag`: halves away from zero; `+0.0` for a value that rounds to
    zero (the reference's `eval`)."""
    if not math.isfinite(x):
        return x
    r = math.copysign(math.floor(abs(x) + 0.5), x)
    return r + 0.0


def test_rounding_gives_the_reference_value():
    """`round` and `ceil` on halves, on negative values that round to zero, on
    the zeros, NaN and the infinities: exactly the reference's values, a zero
    sign included (`round_zero_sign`)."""
    xs = [-2.5, -1.5, -0.5, -0.4, 0.0, 0.4, 0.5, 1.5, 2.5, 1e300, -1e-300]
    xs += [math.nan, math.inf, -math.inf]
    x = pl.col("x")
    got = run(
        {
            "round": lowered("Substrait.UnFn.fround", x),
            "ceil": lowered("Substrait.UnFn.fceil", x),
        },
        {"x": pl.Series([*xs, None], dtype=pl.Float64)},
    )

    def same(p: float | None, q: float | None) -> bool:
        if p is None or q is None:
            return p is q
        if math.isnan(p) or math.isnan(q):
            return math.isnan(p) and math.isnan(q)
        return p == q and math.copysign(1.0, p) == math.copysign(1.0, q)

    want_round = [_round(v) for v in xs] + [None]
    want_ceil = [v if not math.isfinite(v) else math.ceil(v) + 0.0 for v in xs] + [None]
    assert all(same(p, q) for p, q in zip(got["round"], want_round, strict=True)), got["round"]
    assert all(same(p, q) for p, q in zip(got["ceil"], want_ceil, strict=True)), got["ceil"]
