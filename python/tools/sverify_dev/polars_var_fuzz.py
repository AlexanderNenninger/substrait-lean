"""Fuzz Polars's `var` against the exact moments (#918, polars-var-bound).

For random columns (sizes 2 to 20 000, shifts up to 1e12, spreads 1e-8 to
1e3), each run of `var(ddof=0)` and `var(ddof=1)`, ungrouped and grouped,
on the streaming engine, is compared with the exact `S / d`. The printed
constant is the largest `|v − S/d| · d / (n u √(Q' S))`, the shape of the
leading term of `Stat.varTol` (160 there), with `Q' = Σ (|x| + 2⁻¹⁰²²)²`.

    python -m sverify_dev.polars_var_fuzz [seed ...]

In-process Polars only, a few seconds per seed.
"""

from __future__ import annotations

import math
import random
import sys
from fractions import Fraction

import polars as pl

U = 2.0**-53
TINY = Fraction(2) ** -1022


def run(seed: int, cases: int = 300) -> dict[str, float | int]:
    """The largest constant per path over `cases` random columns."""
    rnd = random.Random(seed)
    worst = {"ungrouped": 0.0, "grouped": 0.0}
    rows = 0
    for _ in range(cases):
        n = rnd.choice([2, 3, 5, 17, 128, 129, 300, 1000, 5000, 20000])
        shift = rnd.choice([0.0, 1e3, 1e6, 1e8, 1e9, 1e12, -1e10])
        scale = rnd.choice([1e-8, 1e-3, 1.0, 1e3])
        xs = [shift + scale * rnd.gauss(0, 1) for _ in range(n)]
        rows += n
        fx = [Fraction(x) for x in xs]
        sx = sum(fx)
        s = sum(x * x for x in fx) - sx * sx / n
        q = sum((abs(x) + TINY) ** 2 for x in fx)
        if s <= 0:
            continue
        denom = n * U * math.sqrt(float(q * s))
        df = pl.DataFrame({"x": xs, "k": [0] * n}).lazy()
        for ddof in (0, 1):
            d = n - ddof
            got = {
                "ungrouped": df.select(pl.col("x").var(ddof=ddof))
                .collect(engine="streaming")
                .item(),
                "grouped": df.group_by("k")
                .agg(pl.col("x").var(ddof=ddof))
                .collect(engine="streaming")["x"][0],
            }
            for path, v in got.items():
                worst[path] = max(worst[path], float(abs(Fraction(v) - s / d) * d) / denom)
    return {"seed": seed, "cases": cases, "rows": rows, **worst}


def main(argv: list[str] | None = None) -> None:
    seeds = [int(a) for a in (sys.argv[1:] if argv is None else argv)] or [918]
    print(f"polars {pl.__version__}")
    for seed in seeds:
        print(run(seed))


if __name__ == "__main__":
    main()
