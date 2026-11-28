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
    """`round`, `round_even`, `ceil`, integer `//` and `%`, decimal `%`, `<<`, `>>`,
    `strpos` and the split have templates; `%` of doubles has no entry (refused);
    everything else is native, and `render` gives None."""
    assert set(table_export.table("polars")) == {
        "Substrait.UnFn.fround", "Substrait.UnFn.froundEven", "Substrait.UnFn.fceil",
        "idiv", "imod", "dmod", "bit:bitwise_shift_left", "bit:bitwise_shift_right",
        "Substrait.BinFn.strpos", "Substrait.BinFn.splitFirst",
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


def _shl(a: int, k: int) -> int:
    """`BitOp.shl`: `a · 2ᵏ` wrapped at 64 bits."""
    return ((a << k) + 2**63) % 2**64 - 2**63


@pytest.mark.parametrize(
    ("fn", "op"),
    [("bit:bitwise_shift_left", _shl), ("bit:bitwise_shift_right", lambda a, k: a >> k)],
    ids=["shl", "shr"],
)
def test_shifts_agree_and_raise_outside_0_to_63(fn, op):
    """`<<` and `>>` are the reference's for every count 0–63 at the edges of 64
    bits (`BitOp.apply`), raise on an integer shifted by a count outside them,
    and are NULL where either argument is. Polars computes every branch on
    every row: the counts outside `0`–`63` must not fail the query
    (polars-int-pow-exponent)."""
    values = [MIN, MIN + 1, -(2**62), -5, -1, 0, 1, 3, 2**62, 2**62 + 1, MAX - 1, MAX]
    counts = [*range(64), -1, -64, 64, 65, MIN, MAX]
    pairs: list[tuple[int | None, int | None]] = [(a, k) for a in values for k in counts]
    pairs += [(None, -1), (None, 3), (None, 64), (None, MIN), (5, None), (None, None)]
    cols = {
        "a": pl.Series([a for a, _ in pairs], dtype=pl.Int64),
        "k": pl.Series([k for _, k in pairs], dtype=pl.Int64),
    }
    raised: list[tuple[str, pl.Expr]] = []
    out = lowering.render(fn, [pl.col("a"), pl.col("k")], lambda m, rows: raised.append((m, rows)))
    assert out is not None and [m for m, _ in raised] == ["domain error"]
    got = run({"v": out.cast(pl.Int64), "raises": raised[0][1]}, cols)

    def want(a: int | None, k: int | None) -> int | None:
        return None if a is None or k is None or not 0 <= k < 64 else op(a, k)

    assert got["v"] == [want(a, k) for a, k in pairs]
    assert got["raises"] == [a is not None and k is not None and not 0 <= k < 64 for a, k in pairs]


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


def test_round_asks_half_away_from_zero_once():
    """Ruling 282's C8 (M3): the mode of Polars's `round` is written once, in
    `Polars.asks`, and the rendering carries it; Polars rounds half to even unless
    asked (polars-round)."""
    assert table_export.asks("polars") == {
        ("Substrait.UnFn.fround", "rounding"): "TIE_AWAY_FROM_ZERO"
    }
    assert lowering._asked_mode("Substrait.UnFn.fround") == "half_away_from_zero"
    # The ties tell the modes apart: half to even would give 0.0, 2.0 and -2.0.
    got = run(
        {"r": lowered("Substrait.UnFn.fround", pl.col("x"))},
        {"x": pl.Series([0.5, 2.5, -2.5] * 400)},
    )
    assert got["r"][:3] == [1.0, 3.0, -3.0]


def _split_first(s: str | None, t: str | None) -> str | None:
    """`Text.splitFirst`: the prefix before the leftmost `t`, `s` where it does
    not occur or `t` is empty."""
    if s is None or t is None:
        return None
    i = s.find(t) if t else -1
    return s if i < 0 else s[:i]


SPLIT_CASES = [
    ("héllo wörld", "ö"), ("日本語日本", "本"), ("aaa", "aa"), ("abc", "d"), ("ab", "abc"),
    ("abc", ""), ("", ""), ("éx", ""), ("a.b", "."), (None, "a"), ("abc", None), ("", "a"),
]  # fmt: skip


def test_the_split_and_strpos_agree_with_the_reference():
    """Ruling 286: the split's entry passes `s` through for an empty `t`, where
    Polars's own split gives the first code point; `strpos` is the template
    over it, one-based in characters, 0 when absent, 1 for an empty `t`."""
    cols = {
        "s": pl.Series([s for s, _ in SPLIT_CASES], dtype=pl.String),
        "t": pl.Series([t for _, t in SPLIT_CASES], dtype=pl.String),
    }
    split = lowering.render("Substrait.BinFn.splitFirst", [pl.col("s"), pl.col("t")])
    pos = lowering.render("Substrait.BinFn.strpos", [pl.col("s"), pl.col("t")])
    assert split is not None and pos is not None
    got = run({"split": split, "pos": pos}, cols)
    assert got["split"] == [_split_first(s, t) for s, t in SPLIT_CASES]
    assert got["pos"] == [None if s is None or t is None else s.find(t) + 1 for s, t in SPLIT_CASES]
