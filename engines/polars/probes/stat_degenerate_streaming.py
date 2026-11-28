"""Polars's degenerate VAR, STDDEV and CORR on the streaming engine, run to
run (#2628, ruling 291; fact polars-corr-degenerate-ungrouped).

Each case runs RUNS times, and every distinct outcome is recorded bit for bit
(`float.hex`), with its kind (NULL, NaN, 0 or a number) and how often it came
up. The driver starts one worker per morsel size and thread count, since Polars
reads POLARS_IDEAL_MORSEL_SIZE and POLARS_MAX_THREADS at import.

Run: python stat_degenerate_streaming.py driver OUT.json
(on homelab: uv run --no-project --python 3.12 --with polars==2.1.0 python ...)"""

import collections
import json
import math
import os
import subprocess
import sys

RUNS = 50
MORSELS = ["default", "64", "1000"]
THREADS = ["default", "1", "4"]
COUNTS = [1, 2, 63, 64, 65, 127, 128, 129, 1000, 100_000, 300_001]
VALUES = [0.1, 1 / 3, 1e8 + 0.3]  # equal values: 0.1 and 1/3 are inexact, 1e8+0.3 large
GROUPS = [None, 1, 4, 1000]  # None: ungrouped; else group_by(i % G)
COLUMNS = ("var_samp", "var_pop", "std_samp", "std_pop", "corr_y_x", "corr_x_x")


def kind(v):
    if v is None:
        return "null"
    if math.isnan(v):
        return "nan"
    if v == 0.0:
        return "zero"
    return "number"


def _dec(h):
    return None if h is None else float.fromhex(h)


def _kinds(k):
    """One run's kinds over its groups, short for many groups."""
    return "/".join(k) if len(k) < 6 else f"{len(k)} groups: " + ",".join(sorted(set(k)))


def enc(v):
    return None if v is None else float(v).hex()


def worker(morsel: str, threads: str) -> dict:
    if morsel != "default":
        os.environ["POLARS_IDEAL_MORSEL_SIZE"] = morsel
    if threads != "default":
        os.environ["POLARS_MAX_THREADS"] = threads
    import polars as pl

    out = {"polars": pl.__version__, "morsel": morsel, "threads": threads, "cases": []}
    aggs = lambda x, y: [  # noqa: E731
        pl.col(x).var(ddof=1).alias("var_samp"),
        pl.col(x).var(ddof=0).alias("var_pop"),
        pl.col(x).std(ddof=1).alias("std_samp"),
        pl.col(x).std(ddof=0).alias("std_pop"),
        pl.corr(pl.col(y), pl.col(x)).alias("corr_y_x"),  # x all equal, y varies
        pl.corr(pl.col(x), pl.col(x)).alias("corr_x_x"),  # both sides all equal
    ]
    for value in VALUES:
        for n in COUNTS:
            frame = pl.LazyFrame(
                {"i": range(n), "x": [value] * n, "y": [float(i) for i in range(n)]}
            )
            for g in GROUPS:
                if g is not None and g > n:
                    continue
                if g is None:
                    q = frame.select(aggs("x", "y"))
                else:
                    q = (
                        frame.with_columns(k=pl.col("i") % g)
                        .group_by("k")
                        .agg(aggs("x", "y"))
                        .sort("k")
                    )
                seen: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
                for _ in range(RUNS):
                    df = q.collect(engine="streaming")
                    for col in (
                        "var_samp",
                        "var_pop",
                        "std_samp",
                        "std_pop",
                        "corr_y_x",
                        "corr_x_x",
                    ):
                        vals = df[col].to_list()
                        # a run's outcome: the tuple over groups
                        seen[col][json.dumps([enc(v) for v in vals])] += 1
                kinds = {}
                for col, c in seen.items():
                    ks = set()
                    for outcome in c:
                        ks.add(
                            tuple(
                                kind(None if h is None else float.fromhex(h))
                                for h in json.loads(outcome)
                            )
                        )
                    kinds[col] = sorted(
                        "/".join(k)
                        if len(k) < 6
                        else f"{len(k)} groups: " + ",".join(sorted(set(k)))
                        for k in ks
                    )
                out["cases"].append(
                    {
                        "value": value,
                        "n": n,
                        "groups": g,
                        "distinct": {col: len(c) for col, c in seen.items()},
                        "kinds": kinds,
                        "outcomes": {
                            col: (
                                dict(c)
                                if len(json.loads(next(iter(c)))) <= 4
                                else {"(per-group tuples)": len(c)}
                            )
                            for col, c in seen.items()
                        },
                    }
                )
                print(
                    morsel,
                    threads,
                    value,
                    n,
                    g,
                    {c: len(v) for c, v in seen.items()},
                    flush=True,
                    file=sys.stderr,
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
