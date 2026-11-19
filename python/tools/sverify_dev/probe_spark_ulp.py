"""Measure Spark's elementary functions against the correctly rounded value.

Maintainer tooling (`sverify_dev`), the Spark counterpart of the ulp probes
behind `duckdb-ulp-libm`: it records the facts of `spark-ulp-libm`
(#271, math functions on Spark). Each function runs on fixed random inputs through
Spark SQL (the codegen path, over a Parquet-free `createDataFrame`); the result
is compared with `mpmath` at 300 bits rounded to a double, and the largest
distance in ulps of the correct value is printed per function, for `DOUBLE`
inputs.

Needs `pyspark`, `mpmath` and a JVM (Java 17 or 21). Run it on homelab through
`homelab-run`; the laptop gives the macOS column.

    python -m sverify_dev.probe_spark_ulp [--n 3000]
"""

from __future__ import annotations

import argparse
import json
import math
import platform
import random

import mpmath
from pyspark.sql import SparkSession

mpmath.mp.prec = 300

#: name -> (SQL template over `x` and `y`, reference, sampler of (x, y)).
Sampler = "Callable[[random.Random], tuple[float, float]]"


def _logu(rng: random.Random, lo: float, hi: float) -> float:
    return math.exp(rng.uniform(math.log(lo), math.log(hi)))


def _signed(rng: random.Random, f: float) -> float:
    return f if rng.random() < 0.5 else -f


FUNCS: dict[str, tuple[str, object, object]] = {
    "exp": ("exp(x)", lambda x, y: mpmath.exp(x), lambda r: (r.uniform(-700, 700), 0.0)),
    "ln": ("ln(x)", lambda x, y: mpmath.log(x), lambda r: (_logu(r, 1e-300, 1e300), 0.0)),
    "log10": ("log10(x)", lambda x, y: mpmath.log10(x), lambda r: (_logu(r, 1e-300, 1e300), 0.0)),
    "log2": ("log2(x)", lambda x, y: mpmath.log(x, 2), lambda r: (_logu(r, 1e-300, 1e300), 0.0)),
    "log(b, x)": (
        "log(y, x)",
        lambda x, y: mpmath.log(x) / mpmath.log(y),
        lambda r: (_logu(r, 1e-100, 1e100), _logu(r, 1.01, 1e6)),
    ),
    "sin": ("sin(x)", lambda x, y: mpmath.sin(x), lambda r: (r.uniform(-1000, 1000), 0.0)),
    "cos": ("cos(x)", lambda x, y: mpmath.cos(x), lambda r: (r.uniform(-1000, 1000), 0.0)),
    "tan": ("tan(x)", lambda x, y: mpmath.tan(x), lambda r: (r.uniform(-1000, 1000), 0.0)),
    "asin": ("asin(x)", lambda x, y: mpmath.asin(x), lambda r: (r.uniform(-1, 1), 0.0)),
    "acos": ("acos(x)", lambda x, y: mpmath.acos(x), lambda r: (r.uniform(-1, 1), 0.0)),
    "atan": ("atan(x)", lambda x, y: mpmath.atan(x), lambda r: (_signed(r, _logu(r, 1e-10, 1e10)), 0.0)),
    # Arguments near a zero of cos or sin, where an intrinsic could lose bits.
    "sin (huge)": ("sin(x)", lambda x, y: mpmath.sin(x), lambda r: (_signed(r, _logu(r, 1e10, 1e300)), 0.0)),
    "cos (huge)": ("cos(x)", lambda x, y: mpmath.cos(x), lambda r: (_signed(r, _logu(r, 1e10, 1e300)), 0.0)),
    "tan (huge)": ("tan(x)", lambda x, y: mpmath.tan(x), lambda r: (_signed(r, _logu(r, 1e10, 1e300)), 0.0)),
}  # fmt: skip


def ulps(got: float, want: mpmath.mpf) -> float:
    """The distance of `got` from the exact value `want`, in ulps of the
    double nearest to `want`."""
    w = float(want)
    if math.isinf(w) or w == 0.0:
        return 0.0 if got == w else math.inf
    return float(abs(mpmath.mpf(got) - want) / math.ulp(w))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=3000)
    args = ap.parse_args()
    spark = (
        SparkSession.builder.master("local[2]")
        .config("spark.ui.enabled", "false")
        .config("spark.sql.ansi.enabled", "true")
        .getOrCreate()
    )
    spark.sparkContext.setLogLevel("ERROR")
    out: dict[str, float] = {}
    for name, (sql, ref, sampler) in FUNCS.items():
        rng = random.Random(name)
        pts = [sampler(rng) for _ in range(args.n)]
        df = spark.createDataFrame([(i, x, y) for i, (x, y) in enumerate(pts)], "i INT, x DOUBLE, y DOUBLE")
        df.createOrReplaceTempView("t")
        got = {r.i: r.v for r in spark.sql(f"SELECT i, {sql} AS v FROM t").collect()}
        worst = 0.0
        for i, (x, y) in enumerate(pts):
            want = ref(mpmath.mpf(x), mpmath.mpf(y))
            worst = max(worst, ulps(got[i], want))
        out[name] = round(worst, 3)
    print(json.dumps({"platform": platform.platform(), "n": args.n, "max_ulps": out}, indent=1))


if __name__ == "__main__":
    main()
