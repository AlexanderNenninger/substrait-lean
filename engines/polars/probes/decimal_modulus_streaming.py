"""Polars's decimal `%` on the streaming engine (#1941, ruling 188 X5)."""

from decimal import Decimal as D

import polars as pl

CASES = [  # (a, (p, s)), (b, (p, s))
    ("7.50", (10, 2), "2.0", (5, 1)),
    ("-7.50", (10, 2), "2.0", (5, 1)),
    ("7.50", (10, 2), "-2.0", (5, 1)),
    ("-7.5", (10, 1), "-2", (5, 0)),
    ("-6", (10, 0), "3", (5, 0)),
    ("6", (10, 0), "-3", (5, 0)),
    ("1234567.123", (10, 3), "3.7", (3, 1)),
    ("12345.678901", (28, 6), "7.5", (28, 6)),
    ("99999999999999999999999999999999999999", (38, 0), "7.0000000001", (38, 10)),
    ("1", (37, 9), "0.5", (10, 10)),
    ("-1", (38, 9), "0.3", (10, 10)),
    (None, (10, 2), "2.0", (5, 1)),
    ("7.50", (10, 2), None, (5, 1)),
]
print("polars", pl.__version__)
for a, ta, b, tb in CASES:
    lf = pl.LazyFrame(
        {"a": [None if a is None else D(a)], "b": [None if b is None else D(b)]},
        schema={"a": pl.Decimal(*ta), "b": pl.Decimal(*tb)},
    )
    out = lf.select(r=pl.col("a") % pl.col("b")).collect(engine="streaming")
    print(f"{a} {ta} % {b} {tb} => {out.schema['r']}: {out['r'][0]}")
for zero in ("0.0",):
    lf = pl.LazyFrame(
        {"a": [D("7.50")], "b": [D(zero)]}, schema={"a": pl.Decimal(10, 2), "b": pl.Decimal(5, 1)}
    )
    try:
        print(
            "7.50 % 0.0 =>",
            lf.select(r=pl.col("a") % pl.col("b")).collect(engine="streaming")["r"][0],
        )
    except Exception as e:
        print("7.50 % 0.0 =>", type(e).__name__, str(e)[:80])
