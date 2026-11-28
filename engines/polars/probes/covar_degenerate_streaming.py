"""Ruling 291 Q3 (#2628): Polars's COVAR at its degenerate inputs on the
streaming engine: no pairs and one pair, ungrouped and grouped, across
POLARS_IDEAL_MORSEL_SIZE x POLARS_MAX_THREADS, 50 runs each. Every distinct
outcome is recorded bit for bit (float.hex), with its kind.

No pairs: an empty frame, and n rows whose x is NULL in every row (no row has
both sides). One pair: one row, and n rows of which only the last has both
sides. Grouped: the same within each group.

Run: python covar_degenerate_streaming.py driver OUT.json"""

import collections
import json
import math
import os
import subprocess
import sys

RUNS = 50
MORSELS = ["default", "64", "1000"]
THREADS = ["default", "1", "4"]
COUNTS = [0, 1, 2, 64, 65, 129, 1000, 100_000]
GROUPS = [None, 1, 4]


def kind(v):
    if v is None:
        return "NULL"
    if math.isnan(v):
        return "NaN"
    return "0" if v == 0.0 else "number"


def enc(v):
    return None if v is None else float(v).hex()


def frames(pl, n):
    """(name, frame) of the degenerate inputs with n rows."""
    k = list(range(n))
    yield (
        "no pairs: x NULL",
        pl.LazyFrame(
            {"i": k, "x": [None] * n, "y": [float(i) for i in k]},
            schema={"i": pl.Int64, "x": pl.Float64, "y": pl.Float64},
        ),
    )
    if n >= 1:
        yield (
            "one pair: last row",
            pl.LazyFrame(
                {"i": k, "x": [None] * (n - 1) + [2.5], "y": [float(i) for i in k]},
                schema={"i": pl.Int64, "x": pl.Float64, "y": pl.Float64},
            ),
        )


def worker(morsel: str, threads: str) -> dict:
    if morsel != "default":
        os.environ["POLARS_IDEAL_MORSEL_SIZE"] = morsel
    if threads != "default":
        os.environ["POLARS_MAX_THREADS"] = threads
    import polars as pl

    aggs = [
        pl.cov(pl.col("x"), pl.col("y"), ddof=1).alias("covar_samp"),
        pl.cov(pl.col("x"), pl.col("y"), ddof=0).alias("covar_pop"),
    ]
    out = {"polars": pl.__version__, "morsel": morsel, "threads": threads, "cases": []}
    for n in COUNTS:
        for name, frame in frames(pl, n):
            for g in GROUPS:
                if g is not None and n == 0:
                    continue
                if g is None:
                    q = frame.select(aggs)
                else:
                    # every group holds the input's shape: the pair, if any, in group 0
                    q = frame.with_columns(k=(pl.col("i") % g)).group_by("k").agg(aggs).sort("k")
                seen = collections.defaultdict(collections.Counter)
                for _ in range(RUNS):
                    df = q.collect(engine="streaming")
                    for col in ("covar_samp", "covar_pop"):
                        seen[col][json.dumps([enc(v) for v in df[col].to_list()])] += 1
                out["cases"].append(
                    {
                        "input": name,
                        "n": n,
                        "groups": g,
                        "outcomes": {col: dict(c) for col, c in seen.items()},
                        "kinds": {
                            col: sorted(
                                {
                                    "/".join(
                                        kind(None if h is None else float.fromhex(h))
                                        for h in json.loads(o)
                                    )
                                    for o in c
                                }
                            )
                            for col, c in seen.items()
                        },
                    }
                )
    return out


if __name__ == "__main__":
    if sys.argv[1] == "worker":
        json.dump(worker(sys.argv[2], sys.argv[3]), sys.stdout)
    else:
        results = []
        for m in MORSELS:
            for t in THREADS:
                done = subprocess.run(
                    [sys.executable, __file__, "worker", m, t],
                    capture_output=True,
                    text=True,
                    check=True,
                )
                results.append(json.loads(done.stdout))
        with open(sys.argv[2], "w") as f:
            json.dump(results, f, indent=1)
        print("wrote", sys.argv[2])
