"""Touched-group recompute against recompute-and-diff, on the metrics shape.

    uv run python scripts/bench_touched.py [--hosts n] [--days d] [--refreshes r]
        [--engines duckdb] [--timeout seconds]

A view of per-minute groups (count, mean and max of a sample) over samples
taken every 5 seconds per host for `--days` days (default 14, 10 hosts:
2.4 million rows, 201,600 groups). Then `--refreshes` refreshes (default
5), each inserting the next minute of samples of every host. Per engine and
strategy: the build time and the median refresh time. Each case runs in a
process of its own, so the peak memory (`ru_maxrss`) is that case's.

* `touched`: the groups each batch touches, recomputed (`sverify._touched`).
* `diff`: the whole view recomputed and diffed, as before.
"""

import multiprocessing as mp
import resource
import statistics
import sys
import time
from datetime import datetime

import numpy as np
import pyarrow as pa

import sverify as sv
from sverify.engine import put_table
from sverify.incremental import Pipeline

T0 = datetime(2026, 11, 1)
STEP = 5  # seconds between samples


def samples(hosts: int, start: int, n: int, seed: int) -> pa.Table:
    """`n` samples per host, from sample number `start`."""
    rng = np.random.default_rng(seed)
    secs = np.repeat(np.arange(start, start + n, dtype=np.int64) * STEP, hosts)
    return pa.table(
        {
            "host": pa.array([f"host-{i}" for i in range(hosts)] * n),
            "ts": pa.array(np.datetime64(T0, "us") + secs * 1_000_000, pa.timestamp("us")),
            "value": rng.random(n * hosts),
        }
    )


def rows(table: pa.Table) -> list[tuple]:
    return list(zip(*table.to_pydict().values(), strict=True))


def case(strategy: str, engine: str, hosts: int, days: int, refreshes: int, out: mp.Queue):
    n = days * 24 * 3600 // STEP
    con = sv.connect()
    put_table(con, "samples", samples(hosts, 0, n, seed=0))
    pipe = Pipeline(con, engine)  # type: ignore[arg-type]
    s = con.table("samples")
    query = s.group_by(["host", s.ts.truncate("m").name("minute")]).aggregate(
        n=s.count(), mean=s.value.mean(), peak=s.value.max()
    )
    t = time.perf_counter()
    view = pipe.view("per_minute", query)
    build = time.perf_counter() - t
    if strategy == "diff":
        view.touched = None
    times = []
    per_minute = 60 // STEP
    for k in range(refreshes):
        batch = samples(hosts, n + k * per_minute, per_minute, seed=k + 1)
        t = time.perf_counter()
        pipe.apply({"samples": sv.Changes(inserts=rows(batch))})
        times.append(time.perf_counter() - t)
    out.put((build, statistics.median(times), resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))


def option(argv: list[str], name: str, default: str) -> tuple[str, list[str]]:
    if name not in argv:
        return default, argv
    i = argv.index(name)
    return argv[i + 1], argv[:i] + argv[i + 2 :]


def main(argv: list[str]) -> None:
    engines, argv = option(argv, "--engines", "duckdb")
    hosts, argv = option(argv, "--hosts", "10")
    days, argv = option(argv, "--days", "14")
    refreshes, argv = option(argv, "--refreshes", "5")
    timeout, argv = option(argv, "--timeout", "900")
    ctx = mp.get_context("spawn")
    print(f"{hosts} hosts, {days} days of 5 s samples, one minute per refresh", flush=True)
    for engine in engines.split(","):
        for strategy in ("touched", "diff"):
            q = ctx.Queue()
            args = (strategy, engine, int(hosts), int(days), int(refreshes), q)
            p = ctx.Process(target=case, args=args)
            p.start()
            p.join(float(timeout))
            if p.is_alive():
                p.kill()
                p.join()
                print(f"{strategy:8} {engine:7}: over {timeout} s", flush=True)
                continue
            if p.exitcode != 0:
                print(f"{strategy:8} {engine:7}: failed (exit {p.exitcode})", flush=True)
                continue
            build, refresh, rss = q.get()
            print(
                f"{strategy:8} {engine:7}: build {build * 1000:8.0f} ms,"
                f" refresh {refresh * 1000:8.0f} ms (median), peak {rss / 1024:6.0f} MB",
                flush=True,
            )


if __name__ == "__main__":
    main(sys.argv[1:])
