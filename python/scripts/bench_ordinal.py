"""What a checked run saves by leaving out the ordinal that keeps Lean's row
order, where the checker proved the observation cannot see it (#1787 item 2,
ruling 223).

    python scripts/bench_ordinal.py [ROWS] [THREADS]

Three proved plans over a table keyed on `id`, with the multiset lens: a top-N
by the key, a window ordered by the key, and a grouped sum. Each runs on
DuckDB, from Arrow and from Parquet, and on Polars, as a run writes it with
the ordinal (`rows="sequence"`) and without (`rows="multiset"`). Median of
5, seconds.
"""

import statistics
import sys
import tempfile
import time
from functools import partial
from pathlib import Path
from typing import Literal

import ibis
import numpy as np
import pyarrow as pa
import pyarrow.parquet as pq
from ibis import _

import sverify as sv
from sverify._scan import Scan
from sverify.engine import written_plan
from sverify_duckdb import engine as duckdb_engine
from sverify_polars import engine as polars_engine

BOTH: tuple[Literal["sequence", "multiset"], ...] = ("sequence", "multiset")

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
THREADS = int(sys.argv[2]) if len(sys.argv) > 2 else 4

T = ibis.table({"id": "int64", "g": "int64", "v": "int64"}, name="t")
REQUIRES = {"t": [_.id.notnull(), sv.unique("id")]}
PLANS = {
    "top-N by the key": T.order_by("id").limit(10),
    "window ordered by the key": T.mutate(n=ibis.row_number().over(group_by="g", order_by="id")),
    "grouped sum": T.group_by("g").agg(s=T.v.sum()),
}


def seconds(run) -> float:
    run()
    times = []
    for _i in range(5):
        start = time.perf_counter()
        run()
        times.append(time.perf_counter() - start)
    return statistics.median(times)


def main() -> None:
    import duckdb

    from sverify import _duckdb

    _duckdb.cursor().execute(f"SET threads = {THREADS}")
    t = pa.table(
        {
            # A shuffled key: the input is not in key order.
            "id": pa.array(np.random.default_rng(0).permutation(ROWS), pa.int64()),
            "g": pa.array([i % 1000 for i in range(ROWS)], pa.int64()),
            "v": pa.array([i % 97 for i in range(ROWS)], pa.int64()),
        }
    )
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "t.parquet"
        pq.write_table(t, path)
        sources = {"Arrow": {"t": t}, "Parquet": {"t": Scan((str(path),), t.schema)}}
        print(f"DuckDB {duckdb.__version__}, {ROWS:,} rows, {THREADS} threads; median of 5, s")
        print("| plan | engine, input | with the ordinal | without | ratio |")
        print("|---|---|---|---|---|")
        for name, expr in PLANS.items():
            report = sv.verify(expr, requires=REQUIRES)
            assert report._ordinal_free and report.internal_plan is not None
            plan = written_plan(report.internal_plan)
            for src, tables in sources.items():
                runs = [
                    partial(
                        duckdb_engine.run, plan, tables, rows=rows, deterministic=rows == "multiset"
                    )
                    for rows in BOTH
                ]
                a, b = seconds(runs[0]), seconds(runs[1])
                print(f"| {name} | DuckDB, {src} | {a:.3f} | {b:.3f} | {a / b:.1f}× |")
            runs = [partial(polars_engine.run, plan, {"t": t}, rows=rows) for rows in BOTH]
            a, b = seconds(runs[0]), seconds(runs[1])
            print(f"| {name} | Polars, Arrow | {a:.3f} | {b:.3f} | {a / b:.1f}× |")


if __name__ == "__main__":
    main()
