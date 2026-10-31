"""Benchmarks for the proved optimizations of `docs/optimizations.md`.

    uv run python scripts/bench_optimizations.py [rows]

* Guard elimination: a contract-verified transformation on Polars and on
  DuckDB, with the per-row checks and without them (`guards=False`, allowed
  because the contract report is `guard_free`).
* Sharded evaluation: a grouped aggregate on Polars over all the rows, and
  in two phases over 8 shards run in parallel threads.

Prints the median of 5 runs of each.
"""

import json
import statistics
import sys
import time
from collections.abc import Callable

import ibis
import numpy as np
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify import duckdb_engine, polars_engine
from sverify.engine import connect, create_table, plan_json, substrait_json, written_plan
from sverify.partition import run_sharded


def median_ms(f: Callable[[], object], runs: int = 5) -> float:
    f()  # warm up
    times = []
    for _run in range(runs):
        t = time.perf_counter()
        f()
        times.append((time.perf_counter() - t) * 1000)
    return statistics.median(times)


def guards(n: int) -> None:
    t = ibis.table({"a": "int64", "b": "int64"}, name="t")
    expr = t.filter(t.a % t.b != 0).select(q=t.a // t.b, m=t.a % t.b, s=t.a * 3 + t.b)
    report = sv.verify(expr, requires={"t": [_.a >= 0, _.a <= 10**6, _.b >= 1, _.b <= 1000]})
    assert report.guard_free, str(report)
    rng = np.random.default_rng(0)
    data = {"t": pa.table({"a": rng.integers(0, 10**6, n), "b": rng.integers(1, 1000, n)})}
    p = plan_json(connect(), expr)
    w = written_plan(p)
    for name, run in [
        ("polars", lambda g: polars_engine.run(w, data, guards=g)),
        ("duckdb", lambda g: duckdb_engine.run(json.loads(p), data, guards=g)),
    ]:
        with_ = median_ms(lambda run=run: run(True))
        without = median_ms(lambda run=run: run(False))
        print(
            f"guards   {name:7} {n:>9} rows: {with_:8.1f} ms checked, {without:8.1f} ms unchecked"
            f" ({with_ / without:.1f}x)"
        )


def sharded(n: int, k: int = 8) -> None:
    con = connect()
    create_table(con, "r", ibis.schema({"a": "int64", "b": "int64"}))
    sql = "SELECT b, COUNT(*) AS n, SUM(a) AS s, MAX(a) AS hi FROM r GROUP BY b"
    plan = substrait_json(con, sql)
    rng = np.random.default_rng(0)
    whole = pa.table({"a": rng.integers(0, 1000, n), "b": rng.integers(0, 50, n)})
    shards = [{"r": whole.slice(i * n // k, (i + 1) * n // k - i * n // k)} for i in range(k)]
    w = written_plan(plan)
    one = median_ms(lambda: polars_engine.run(w, {"r": whole}))
    many = median_ms(lambda: run_sharded(plan, shards, sharded=["r"]))
    print(
        f"sharded  polars  {n:>9} rows: {one:8.1f} ms whole,   {many:8.1f} ms in {k} shards"
        f" ({one / many:.1f}x)"
    )


if __name__ == "__main__":
    rows = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    guards(rows)
    sharded(rows)
