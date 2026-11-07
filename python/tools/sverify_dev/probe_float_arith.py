"""Probe each engine's double `+ - * /` against D31 (#929).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The facts `<engine>-ieee-arith-<platform>` cite it.

D31 defines a double `+ - * /` as the exact result rounded once to binary64,
to nearest with ties to even. This computes that result with exact rationals
(`fractions.Fraction`, rounded by `int / int`, which CPython rounds
correctly), runs the same operations natively on each engine, and compares
the bits. The operands:

* every pair of a table of edge values: zeros, the smallest and largest
  subnormals, the smallest normal, one and its neighbour, `2⁻⁵³`, `2⁵³`, the
  largest double, the infinities, NaN, and their negatives;
* pseudo-random operands at every exponent from `0` to `2046`, each paired
  with one at a random exponent, both ways round, so the results cross each
  binade, the subnormal range and the overflow threshold;
* ties: `1 + 2⁻⁵³`, `1 + 3 · 2⁻⁵³`, and subnormals times `0.5`;
* contraction: `a * b - c` with `c` the rounded product, which is `0` unless
  the engine fuses the multiply and the subtraction into one rounding (an
  FMA), for random `a` and `b` whose product is inexact.

A result is classified: `rounding` (a finite non-zero result off by any bit),
`flush_to_zero` (a subnormal result given as zero), `contraction` (`a * b - c`
not zero), `zero_sign` (the other zero), `nan` (NaN where none is due, or
none where one is), and `special` (another infinity). The sign of a NaN is
open (D31) and not compared. Division by zero is left out: it is the option
`on_division_by_zero`, which each engine's `fp.div` facts cover.

    python -m sverify_dev.probe_float_arith [--spark] [--seed N]

prints one JSON object: the platform, and per engine and path the number of
operations compared and the mismatches by class, with up to five examples
each.
"""

from __future__ import annotations

import argparse
import json
import math
import platform
import random
import struct
import sys
from fractions import Fraction

EDGE_BITS = [
    0x0000000000000000,
    0x0000000000000001,
    0x0000000000000003,
    0x0008000000000000,
    0x000FFFFFFFFFFFFF,
    0x0010000000000000,
    0x0010000000000001,
    0x3C90000000000000,
    0x3CA0000000000000,
    0x3FF0000000000000,
    0x3FF0000000000001,
    0x4340000000000000,
    0x7FE0000000000000,
    0x7FEFFFFFFFFFFFFF,
    0x7FF0000000000000,
    0x7FF8000000000000,
]


def of_bits(n: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", n))[0]


def bits(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def edges() -> list[float]:
    return [of_bits(n) for n in EDGE_BITS] + [of_bits(n | 1 << 63) for n in EDGE_BITS]


def random_pairs(rng: random.Random) -> list[tuple[float, float]]:
    out = []
    for e in range(2047):
        x = of_bits(rng.getrandbits(1) << 63 | e << 52 | rng.getrandbits(52))
        y = of_bits(rng.getrandbits(1) << 63 | rng.randrange(2047) << 52 | rng.getrandbits(52))
        out += [(x, y), (y, x)]
    return out


def tie_pairs() -> list[tuple[float, float]]:
    return [
        (1.0, of_bits(0x3CA0000000000000)),
        (1.0, of_bits(0x3CB8000000000000)),
        (of_bits(3), 0.5),
        (of_bits(1), 0.5),
        (of_bits(5), 0.5),
        (-of_bits(3), 0.5),
    ]


def round_once(q: Fraction) -> float:
    """`q` rounded to the nearest double, ties to even, `±∞` past the largest."""
    if q == 0:
        return 0.0
    try:
        return q.numerator / q.denominator
    except OverflowError:
        return math.inf if q > 0 else -math.inf


def exact(op: str, a: float, b: float) -> float:
    """D31's result of `a op b`, `b` non-zero for `/`."""
    if not (math.isfinite(a) and math.isfinite(b)) or a == 0 or b == 0:
        # No rounding: IEEE 754's table of special cases, which every
        # platform's native operations agree on.
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        return a * b if op == "*" else a / b
    fa, fb = Fraction(a), Fraction(b)
    if op == "+":
        return round_once(fa + fb)
    if op == "-":
        return round_once(fa - fb)
    return round_once(fa * fb if op == "*" else fa / fb)


def classify(expected: float, got: float | None) -> str | None:
    if got is None:
        return "nan" if not math.isnan(expected) else None
    if math.isnan(expected) or math.isnan(got):
        return None if math.isnan(expected) and math.isnan(got) else "nan"
    if bits(expected) == bits(got):
        return None
    if expected == 0 and got == 0:
        return "zero_sign"
    if math.isinf(expected) or math.isinf(got):
        return "special"
    if got == 0 and abs(expected) < 2.2250738585072014e-308:
        return "flush_to_zero"
    return "rounding"


def cases(seed: int) -> tuple[list[tuple[float, float, float]], list[tuple[float, float, float]]]:
    """Rows `(a, b, c)`: the pairs, with `c = 0`, and the contraction rows."""
    rng = random.Random(seed)
    es = edges()
    pairs = [(x, y) for x in es for y in es] + random_pairs(rng) + tie_pairs()
    fma = []
    while len(fma) < 2000:
        a = of_bits(rng.getrandbits(1) << 63 | rng.randrange(900, 1150) << 52 | rng.getrandbits(52))
        b = of_bits(rng.randrange(900, 1150) << 52 | rng.getrandbits(52))
        p = Fraction(a) * Fraction(b)
        c = round_once(p)
        if Fraction(c) != p:
            fma.append((a, b, c))
    return [(a, b, 0.0) for a, b in pairs], fma


OPS = ["+", "-", "*", "/"]
SQL = (
    "SELECT a + b AS s, a - b AS d, a * b AS p, "
    "CASE WHEN b <> 0 THEN a / b END AS q, a * b - c AS f FROM t"
)


def compare(rows: list[tuple[float, float, float]], fma: set[int], out: list[tuple]) -> dict:
    """Mismatches of the results `out` (`s, d, p, q, f` per row)."""
    found: dict[str, list] = {}
    n = 0

    def note(cls: str | None, what: str) -> None:
        if cls:
            found.setdefault(cls, [])
            if len(found[cls]) < 5:
                found[cls].append(what)
            found.setdefault(f"{cls}_count", [0])[0] += 1

    for i, ((a, b, c), res) in enumerate(zip(rows, out, strict=True)):
        if i in fma:
            n += 1
            f = res[4]
            if f is None or f != 0:
                note("contraction", f"{a!r} * {b!r} - {c!r} = {f!r}")
            continue
        for op, got in zip(OPS, res[:4], strict=False):
            if op == "/" and b == 0:
                continue
            n += 1
            want = exact(op, a, b)
            note(classify(want, got), f"{a!r} {op} {b!r}: {got!r}, D31 {want!r}")
    return {"compared": n, "mismatches": {k: v for k, v in found.items()}}


def run_duckdb(rows: list) -> list[tuple]:
    import duckdb
    import pyarrow as pa

    t = pa.table({k: [r[i] for r in rows] for i, k in enumerate("abc")})
    con = duckdb.connect()
    con.register("t", t)
    return con.execute(SQL).fetchall()


def run_polars(rows: list, streaming: bool) -> list[tuple]:
    import polars as pl

    df = pl.DataFrame(
        {k: [r[i] for r in rows] for i, k in enumerate("abc")},
        schema=dict.fromkeys("abc", pl.Float64),
    )
    a, b, c = pl.col("a"), pl.col("b"), pl.col("c")
    q = df.lazy().select(s=a + b, d=a - b, p=a * b, q=pl.when(b != 0).then(a / b), f=a * b - c)
    out = q.collect(engine="streaming" if streaming else "in-memory")
    return out.rows()


def run_spark(rows: list) -> list[tuple]:
    from pyspark.sql import SparkSession
    from pyspark.sql.types import DoubleType, StructField, StructType

    spark = SparkSession.builder.master("local[1]").getOrCreate()
    schema = StructType([StructField(k, DoubleType()) for k in "abc"])
    spark.createDataFrame(rows, schema).createOrReplaceTempView("t")
    out = [tuple(r) for r in spark.sql(SQL).collect()]
    spark.stop()
    return out


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--spark", action="store_true", help="also probe a local Spark session")
    parser.add_argument("--seed", type=int, default=929)
    args = parser.parse_args(argv)
    pairs, fma = cases(args.seed)
    rows = pairs + fma
    fma_rows = set(range(len(pairs), len(rows)))
    import duckdb
    import polars

    found: dict = {
        "platform": f"{platform.system()} {platform.machine()}",
        "python": platform.python_version(),
        "seed": args.seed,
        "versions": {"duckdb": duckdb.__version__, "polars": polars.__version__},
        "duckdb": compare(rows, fma_rows, run_duckdb(rows)),
        "polars": {
            "in-memory": compare(rows, fma_rows, run_polars(rows, False)),
            "streaming": compare(rows, fma_rows, run_polars(rows, True)),
        },
    }
    if args.spark:
        import pyspark

        found["versions"]["spark"] = pyspark.__version__
        found["spark"] = compare(rows, fma_rows, run_spark(rows))
    json.dump(found, sys.stdout, indent=2)
    print()


if __name__ == "__main__":
    main()
