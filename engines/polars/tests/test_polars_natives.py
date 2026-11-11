"""#1270: operations the Polars translation computes natively, against the
Python and numpy code they replace, on the streaming engine."""

import math
import random
import re

import ibis
import polars as pl
import pytest

from sverify.engine import connect, run_plan, substrait_json, written_plan
from sverify.ibis_substrait import to_substrait_json
from sverify_polars import engine as E

I64_MIN, I64_MAX = -(2**63), 2**63 - 1


def _run(df: pl.DataFrame, expr: pl.Expr) -> list:
    return df.lazy().select(expr.alias("o")).collect(engine="streaming")["o"].to_list()


def test_shifts_are_pythons():
    """`BitOp.shl` and `BitOp.shr` for every count 0–63 (polars-int-arith,
    polars-int-divide), at the edges of 64 bits."""
    values = [0, 1, -1, 3, -5, 2**62, -(2**62), I64_MIN, I64_MAX, 123456789, -987654321]
    rows = [(a, k) for a in values for k in range(64)]
    df = pl.DataFrame({"a": [a for a, _ in rows], "k": [k for _, k in rows]},
                      schema={"a": pl.Int64, "k": pl.Int64})  # fmt: skip
    left = _run(df, E.shift_left(pl.col("a"), pl.col("k")))
    right = _run(df, E.shift_right(pl.col("a"), pl.col("k")))
    assert left == [((a << k) + 2**63) % 2**64 - 2**63 for a, k in rows]
    assert right == [a >> k for a, k in rows]


def _doubles() -> list[float]:
    rng = random.Random(1270)
    edges = [0.0, -0.0, 0.5, -0.5, 1.5, 2.5, -2.5, 2.675, 1.005, 0.125, 1e-300, 5e-324]
    edges += [1e300, -1e300, 1.7976931348623157e308, 4503599627370495.5, 0.49999999999999994]
    return (
        edges
        + [rng.uniform(-1e6, 1e6) for _ in range(2000)]
        + [math.ldexp(rng.uniform(0.5, 1.0), rng.randint(-1074, 1023)) for _ in range(2000)]
    )


def _round_to(x: float, d: int) -> float:
    """`FloatCode.roundTo`, transcribed: `round(x · 10^d) / 10^d`, halves away
    from zero, `x` where that is not finite."""
    m = math.pow(10.0, d)
    y = x * m
    if not math.isfinite(y):
        return x
    a = math.floor(abs(y))
    r = math.copysign(a + (1.0 if abs(y) - a >= 0.5 else 0.0), y) / m
    return r if math.isfinite(r) else x


@pytest.mark.parametrize("d", [0, 1, 2, 7, 15, 22])
def test_round_digits_is_round_to(d):
    """Polars's own `round(d)` (half away from zero) for `0 ≤ d ≤ 22` is
    `FloatCode.roundTo` (polars-round-digits)."""
    xs = _doubles()
    df = pl.DataFrame({"x": xs}, schema={"x": pl.Float64})
    after = E.Exprs.round_to(E.Val(pl.col("x"), pl.Float64), {"literal": {"i64": d}}).expr
    assert _run(df, after) == [_round_to(x, d) for x in xs]


_ALPHABET = ["a", "b", "é", "日", "é", "🇩🇪", "%", "_", "\\", ".", "(", " ", "\n", "A", "É"]


def _strings(n: int = 4000) -> list[str | None]:
    rng = random.Random(1270)
    words = ["".join(rng.choice(_ALPHABET) for _ in range(rng.randint(0, 6))) for _ in range(n)]
    return [None if rng.random() < 0.02 else w for w in words]


def _frame(**cols) -> pl.DataFrame:
    return pl.DataFrame(cols, schema={k: (pl.Int64 if k == "n" else pl.String) for k in cols})


@pytest.mark.parametrize("pat, val", [("", "-"), ("a", "zz"), ("é", ""), ("%", "\\1"), ("é", "E")])
def test_replace_of_a_literal_pattern_is_pythons(pat, val):
    """`replace(s, p, r)` with a literal `p`: Polars's literal `replace_all`
    (polars-string-natives), the empty pattern at every character boundary."""
    s = _strings()
    got = _run(_frame(s=s), pl.col("s").str.replace_all(pl.lit(pat), pl.lit(val), literal=True))
    assert got == [None if v is None else v.replace(pat, val) for v in s]


def test_reverse_and_ascii_are_by_code_point():
    """`Text.reverse` and `Text.ascii` (polars-string-natives)."""
    s = _strings()
    df = _frame(s=s)
    assert _run(df, E.reverse_chars(pl.col("s"))) == [None if v is None else v[::-1] for v in s]
    assert _run(df, E.first_code_point(pl.col("s"))) == [
        None if v is None else (ord(v[0]) if v else 0) for v in s
    ]


def test_repeat_is_pythons():
    """`Text.repeatStr` for counts below 1 and above (polars-string-natives)."""
    rng = random.Random(1270)
    s = _strings()
    n = [None if rng.random() < 0.02 else rng.randint(-2, 4) for _ in s]
    k, x = pl.col("n").clip(lower_bound=0), pl.col("s")
    got = _run(_frame(s=s, n=n), pl.when(x.is_null() | pl.col("n").is_null()).then(None)
               .otherwise(x.repeat_by(k).list.join("")))  # fmt: skip
    assert got == [
        None if v is None or m is None else v * max(m, 0) for v, m in zip(s, n, strict=True)
    ]


def _like(s: str, p: str) -> bool:
    """`Text.like`, transcribed: `%` any characters, `_` one, a backslash
    makes the next character literal (a trailing one is itself)."""
    out, k = [], 0
    while k < len(p):
        c = p[k]
        if c == "\\" and k + 1 < len(p):
            out.append(re.escape(p[k + 1]))
            k += 2
            continue
        out.append(".*" if c == "%" else "." if c == "_" else re.escape(c))
        k += 1
    return re.fullmatch("".join(out), s, re.DOTALL) is not None


@pytest.mark.parametrize(
    "pattern", ["a%", "%é_", "\\%%", "%\\_b", "_", "", "%", "a\\", "日%本", "%.%", "(%"]
)
def test_like_of_a_literal_pattern_is_text_like(pattern):
    """`LIKE` with a literal pattern, as one regular expression Polars matches
    (`like_regex`), against `Text.like`'s Python transcription (`_like`)."""
    s = _strings()
    got = _run(_frame(s=s), pl.col("s").str.contains(E.like_regex(pattern)))
    assert got == [None if v is None else _like(v, pattern) for v in s]


_TEXTS = ibis.schema({"s": "string", "t": "string"})
_FLOATS = ibis.schema({"x": "float64"})


def _refused(schema, rows, plan: str, message: str) -> None:
    con = connect()
    con.create("r", schema, rows)
    with pytest.raises(E.Unsupported, match=message):
        run_plan(con, written_plan(plan), "polars")


@pytest.mark.parametrize(
    "sql, message",
    [("SELECT ROUND(x, -1) AS r FROM r", "polars-round-digits"),
     ("SELECT ROUND(x, 23) AS r FROM r", "polars-round-digits"),
     ("SELECT x % 3.0 AS m FROM r", "% of doubles")],
)  # fmt: skip
def test_rounding_and_remainders_polars_cannot_match_are_refused(sql, message):
    """#1270, Fable's decisions: `ROUND` to digits outside 0 to 22 and `%` of doubles
    have no exact native form; the run is refused, never computed by Python."""
    con = connect()
    con.create("r", _FLOATS, [(1.5,), (-2.25,)])
    _refused(_FLOATS, [(1.5,), (-2.25,)], substrait_json(con, sql, "reference"), message)


@pytest.mark.parametrize(
    "build, message",
    [(lambda t: t.s.like(t.t), "LIKE with a pattern"),
     (lambda t: t.s.ilike(t.t), "ILIKE with a pattern"),
     (lambda t: t.s.levenshtein(t.t), "no levenshtein")],
)  # fmt: skip
def test_string_functions_polars_cannot_match_are_refused(build, message):
    """A pattern per row and `levenshtein` (#1270), from Ibis: refused on
    Polars with the reason. (`replace` with a pattern per row is refused
    before Polars by both front ends; its Polars refusal guards raw plans.)"""
    t = ibis.table(_TEXTS, name="r")
    _refused(_TEXTS, [("ab", "a%")], to_substrait_json(t.select(o=build(t))), message)
