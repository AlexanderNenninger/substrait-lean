"""Polars's `round(d, mode="half_away_from_zero")` against the reference's `round(x, d)`
(`FloatCode.roundTo`) at ties and edges, on the streaming engine (ruling 282, C8 M1, #2572).

Run with the pinned Polars (2.1.0); prints the mismatches, none expected."""

import math

import polars as pl


def ref(x, d):  # FloatCode.roundTo for d >= 0 (C round = half away)
    if math.isnan(x) or math.isinf(x):
        return x
    m = 10.0**d
    y = x * m
    if abs(y) < 2**52:
        t = math.floor(abs(y))
        t = t + 1 if abs(y) - t >= 0.5 else t
        r = math.copysign(t, y)
    else:
        r = y
    r = r / m
    return x if (math.isnan(r) or math.isinf(r)) else r


xs = [
    0.5,
    -0.5,
    1.5,
    -1.5,
    2.5,
    -2.5,
    -0.0,
    0.49999999999999994,
    -0.49999999999999994,
    2.0**52 - 0.5,
    2.0**52 + 1,
    -(2.0**52) + 0.5,
    4503599627370495.5,
    float("nan"),
    float("inf"),
    float("-inf"),
    1.005,
    2.675,
    0.125,
    -0.125,
    1234.5678,
    1e300,
    -1e-300,
    5e-324,
]
lf = pl.LazyFrame({"x": xs * 100})
bad = []
for d in (0, 1, 2, 3, 10, 22):
    out = (
        lf.select(r=pl.col.x.round(d, mode="half_away_from_zero"))
        .collect(engine="streaming")["r"]
        .to_list()[: len(xs)]
    )
    for x, got in zip(xs, out, strict=True):
        want = ref(x, d)
        same = (math.isnan(got) and math.isnan(want)) or (
            got == want and math.copysign(1, got) == math.copysign(1, want)
        )
        if not same:
            bad.append((d, x, got, want))
print("mismatches:", len(bad))
[print(b) for b in bad[:20]]
