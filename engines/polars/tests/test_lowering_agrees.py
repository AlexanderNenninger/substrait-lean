"""The generated lowering to Polars and the hand-written hooks agree (#271,
ruling 235 C3).

The Lean build generates Polars's lowering and proves each template gives the
reference's outcome under `Profile.polars` (`Lowering.polars_exact`,
`engines/polars/Sverify/Polars/Lowering.lean`). Until its interpreter writes
the plan (#271, step 2), the translation still writes these functions by hand
(`sverify_polars.shims`). This test runs each template of the exported table
through Polars beside the hook it will replace, on the edge cases of each
function's facts, so the proved table and the running code cannot drift apart.

The templates are written by the translation's own interpreter
(`sverify_polars.lowering`), the one that replaces the hooks.
"""

import math
from typing import Any

import polars as pl
import pytest

from sverify.sql import lowering as table_export
from sverify_polars import lowering, shims

pytestmark = pytest.mark.backend("polars")

MIN, MAX = -(2**63), 2**63 - 1


def lowered(fn: str, *xs: pl.Expr) -> pl.Expr:
    """`fn` as the interpreter writes its template."""
    e = lowering.render(fn, xs)
    assert e is not None, fn
    return e


def run(exprs: dict[str, pl.Expr], cols: dict[str, Any]) -> dict[str, list]:
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


def test_division_agrees_with_the_shims():
    """`//` and `%` truncate, as `int_div_trunc` and `int_mod_trunc` do, on
    every sign combination and at the bounds. `MIN // -1` and a zero divisor
    are left out: the reference raises there, and both translations guard
    them (`div_overflows`, `zero_divisor`)."""
    edge = [MIN, MIN + 1, -7, -6, -2, -1, 0, 1, 2, 6, 7, MAX - 1, MAX, None]
    pairs = [(a, b) for a in edge for b in edge if b != 0 and (a, b) != (MIN, -1)]
    cols = {
        "a": pl.Series([a for a, _ in pairs], dtype=pl.Int64),
        "b": pl.Series([b for _, b in pairs], dtype=pl.Int64),
    }
    a, b = pl.col("a"), pl.col("b")
    got = run(
        {
            "div": lowered("idiv", a, b).cast(pl.Int64),
            "mod": lowered("imod", a, b).cast(pl.Int64),
            "div_hook": shims.int_div_trunc(a, b),
            "mod_hook": shims.int_mod_trunc(a, b),
        },
        cols,
    )
    assert got["div"] == got["div_hook"]
    assert got["mod"] == got["mod_hook"]


def same(x: float | None, y: float | None) -> bool:
    """Equal as the reference compares doubles: NaN is one value and the zeros
    are one (`round_zero_sign`: the template gives `0.0` where the hook keeps
    IEEE's `-0.0`, one class, D31)."""
    if x is None or y is None:
        return x is y
    return (math.isnan(x) and math.isnan(y)) or x == y


def test_rounding_agrees_with_the_hooks():
    """`round` and `ceil` on halves, on negative values that round to zero, on
    the zeros, NaN and the infinities."""
    xs = [-2.5, -1.5, -0.5, -0.4, -0.0, 0.0, 0.4, 0.5, 1.5, 2.5, 1e300, -1e-300]
    xs += [math.nan, math.inf, -math.inf, None]
    x = pl.col("x")
    got = run(
        {
            "round": lowered("Substrait.UnFn.fround", x),
            "ceil": lowered("Substrait.UnFn.fceil", x),
            "round_hook": shims.round_half_away(x),
            "ceil_hook": x.ceil(),
        },
        {"x": pl.Series(xs, dtype=pl.Float64)},
    )
    for f in ("round", "ceil"):
        assert all(same(p, q) for p, q in zip(got[f], got[f + "_hook"], strict=True)), f
    # The template is exact: a negative value that rounds to zero gives 0.0.
    assert math.copysign(1.0, got["round"][xs.index(-0.4)]) == 1.0
