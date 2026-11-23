"""#1329's bar for the incremental store, measured: the state each of four
representative pipelines keeps, against the data it has read.

    python scripts/bench_store_bar.py [ROWS ...] [--engines duckdb,polars,spark]
        [--pipelines aggregate,join,windowed,distinct]

Per pipeline, engine and size N: four inserts of N/4 rows through a node
(`StaticSource.pipe`), each followed by a refresh. Each case runs in a
process of its own, twice:

* timed: the refresh of each insert, and the driver's peak memory
  (`ru_maxrss`) over the four, with no read of the state. After the last
  refresh it also splits the driver's memory: the sources' tables (every
  source keeps its whole table in the Python process, outside the bar,
  #1945), the Arrow memory pool's allocation (Arrow tables the driver
  built, such as a state held as Arrow; a source built from NumPy is
  outside it), the state location's files (`_parts.state_dir`, where
  Polars and Spark keep their parts), DuckDB's own memory
  (`duckdb_memory()`), the resident set's growth since before the sources
  were built (after a garbage collection, Arrow's `release_unused` and
  `malloc_trim`, so freed memory is not counted), and the residual of
  that growth the parts above leave unexplained. The timed run builds no Parquet of its own, and drops each
  batch once the source has it. The residual includes the engines' own
  libraries, loaded at the first refresh, a constant: compare it across N;
* sized: after each refresh, the view's state (`arrow_of(view.state)`): its
  rows, and its size as Parquet, against the Parquet size of the rows read
  so far. The worst of the four ratios and the last one are printed.

The pipelines (#1329, "The bar for 1.0"):

* `aggregate`: a double `SUM`, `VAR` and `COUNT` per group of 1,000; the
  bar is O(groups), flat in N;
* `join`: orders to their customer (one match each); its state is the
  join's output, O(output);
* `windowed`: hourly sums under a watermark of two hours over a stream in
  time order; O(open window), flat in N;
* `distinct`: the distinct values of a column with 50,000 of them;
  O(distinct output).
"""

import contextlib
import ctypes
import gc
import io
import multiprocessing as mp
import os
import resource
import sys
import time
from datetime import datetime, timedelta

import numpy as np
import pyarrow as pa
import pyarrow.parquet as pq
from ibis import _

import sverify as sv
from sverify import _duckdb, _parts
from sverify._state import arrow_of
from sverify.io import Changes, StaticSource

GROUPS = 1_000
CUSTOMERS = 10_000
DISTINCT = 50_000
T0 = datetime(2026, 1, 1)
#: One sample per second: an insert of N/4 rows spans N/4 seconds.
STEP = timedelta(seconds=1)


def orders(n: int, start: int) -> pa.Table:
    rng = np.random.default_rng(start)
    ids = np.arange(start, start + n, dtype=np.int64)
    return pa.table(
        {
            "id": ids,
            "g": ids % GROUPS,
            "customer": rng.integers(0, CUSTOMERS, n),
            "v": ids % DISTINCT,
            "amount": rng.random(n) * 1000.0,
            "ts": pa.array(
                (np.datetime64(T0) + ids * np.timedelta64(STEP)).astype("datetime64[us]")
            ),
        }
    )


def customers() -> pa.Table:
    return pa.table(
        {
            "customer": np.arange(CUSTOMERS, dtype=np.int64),
            "city": pa.array([f"city-{i % 1000}" for i in range(CUSTOMERS)]),
        }
    )


BOUNDS = [_.amount.between(0, 1000), _.ts >= datetime(2000, 1, 1), _.ts < datetime(2100, 1, 1)]


@sv.transform(requires={"orders": BOUNDS})
def aggregate(orders):
    return orders.group_by("g").aggregate(
        s=orders.amount.sum(), var=orders.amount.var(), n=orders.count()
    )


@sv.transform(requires={"customers": [sv.unique("customer")]})
def join(orders, customers):
    return orders.join(customers, "customer").select("id", "city", "amount")


@sv.transform(requires={"orders": [sv.arrives_within("ts", timedelta(hours=2)), *BOUNDS]})
def windowed(orders):
    return orders.group_by(orders.ts.truncate("h").name("hour")).aggregate(
        s=orders.amount.sum(), n=orders.count()
    )


@sv.transform()
def distinct(orders):
    return orders.select("v").distinct()


PIPELINES = {"aggregate": aggregate, "join": join, "windowed": windowed, "distinct": distinct}


def parquet_bytes(t: pa.Table) -> int:
    buf = io.BytesIO()
    pq.write_table(t, buf)
    return buf.tell()


def case(name: str, engine: str, n: int, sized: bool, out: mp.Queue) -> None:
    k = n // 4
    base = rss_trimmed()
    src = StaticSource(orders(k, 0), name="orders")
    sources = [src]
    transform = PIPELINES[name]
    if name == "join":
        sources.append(StaticSource(customers(), name="customers"))
        node = transform(src, sources[1])
    else:
        node = src.pipe(transform)
    # The sized run alone measures the data, so the timed run builds no
    # buffers of its own beyond the batches the source keeps.
    data = parquet_bytes(orders(k, 0)) if sized else 0
    times: list[float] = []
    sizes: list[tuple[int, int, int]] = []
    for i in range(4):
        if i:
            batch = orders(k, i * k)
            if sized:
                data += parquet_bytes(batch)
            src.apply(Changes(inserts=batch))
            del batch
        t = time.perf_counter()
        node.refresh(engine=engine)
        times.append(time.perf_counter() - t)
        if sized:
            assert node._stage is not None
            state = arrow_of(node._stage.view.state)
            sizes.append((state.num_rows, parquet_bytes(state), data))
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    out.put((times, peak, sizes, memory(sources, base)))


def dir_bytes(path: str) -> int:
    total = 0
    for root, _dirs, files in os.walk(path):
        for f in files:
            with contextlib.suppress(OSError):
                total += os.path.getsize(os.path.join(root, f))
    return total


def rss_trimmed() -> int:
    """The resident set after a garbage collection and after both allocators
    hand freed memory back to the system: Arrow's pool (`release_unused`;
    jemalloc on Linux keeps freed pages otherwise) and, on glibc, the C heap
    (`malloc_trim`). What the process still holds, not an allocator's
    high-water mark."""
    gc.collect()
    pa.default_memory_pool().release_unused()
    with contextlib.suppress(OSError, AttributeError):
        ctypes.CDLL("libc.so.6").malloc_trim(0)
    return rss_now()


def rss_now() -> int:
    """The resident set now, in bytes (Linux; 0 elsewhere)."""
    try:
        with open("/proc/self/statm", encoding="utf-8") as f:
            return int(f.read().split()[1]) * os.sysconf("SC_PAGE_SIZE")
    except OSError:
        return 0


def memory(sources: list, base: int) -> dict[str, int | None]:
    """Where the driver's memory is after the last refresh, against `base`,
    the resident set before the case built its sources: the growth, and the
    residual that the sources, the Arrow pool and DuckDB leave unexplained."""
    source = sum(s.table.nbytes for s in sources)
    rss = rss_trimmed()
    try:
        row = (
            _duckdb.cursor()
            .execute("SELECT coalesce(sum(memory_usage_bytes), 0) FROM duckdb_memory()")
            .fetchone()
        )
        duck = row[0] if row else 0
    except Exception:
        duck = 0
    arrow = pa.total_allocated_bytes()
    duck = int(duck)
    growth = rss - base if rss and base else None
    return {
        "source": source,
        "arrow": arrow,
        "files": dir_bytes(_parts.state_dir()) if "://" not in _parts.state_dir() else None,
        "duckdb": duck,
        "growth": growth,
        "residual": None if growth is None else growth - source - arrow - duck,
    }


def run(name: str, engine: str, n: int, sized: bool) -> tuple | str:
    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=case, args=(name, engine, n, sized, q))
    p.start()
    p.join(3600)
    if p.is_alive():
        p.kill()
        p.join()
        return "over an hour"
    if p.exitcode != 0:
        return f"failed (exit {p.exitcode})"
    return q.get()


def main(argv: list[str]) -> None:
    engines = ["duckdb", "polars", "spark"]
    if "--engines" in argv:
        i = argv.index("--engines")
        engines = argv[i + 1].split(",")
        argv = argv[:i] + argv[i + 2 :]
    pipelines = list(PIPELINES)
    if "--pipelines" in argv:
        i = argv.index("--pipelines")
        pipelines = argv[i + 1].split(",")
        argv = argv[:i] + argv[i + 2 :]
    sizes = [int(float(a)) for a in argv] or [10**6, 4 * 10**6]
    print(
        "| pipeline | engine | N | state rows (last) | state / data: worst, last "
        "| refresh s (each of 4) | driver peak MB | source MB | Arrow pool MB "
        "| state files MB | DuckDB MB | RSS growth MB | residual MB |"
    )
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for n in sizes:
        for name in pipelines:
            for engine in engines:
                timed = run(name, engine, n, False)
                sized = run(name, engine, n, True)
                if isinstance(timed, str) or isinstance(sized, str):
                    why = timed if isinstance(timed, str) else sized
                    print(f"| {name} | {engine} | {n:,} | {why} |")
                    continue
                times, rss, _, mem = timed
                m = {k: ("n/a" if v is None else f"{v / 2**20:.0f}") for k, v in mem.items()}
                mb = rss / (1024**2 if sys.platform == "darwin" else 1024)  # bytes, or KB
                ratios = [b / d for _, b, d in sized[2]]
                rows = sized[2][-1][0]
                print(
                    f"| {name} | {engine} | {n:,} | {rows:,} | {max(ratios):.4f}, {ratios[-1]:.4f} "
                    f"| {', '.join(f'{t:.2f}' for t in times)} | {mb:.0f} | {m['source']} "
                    f"| {m['arrow']} | {m['files']} | {m['duckdb']} | {m['growth']} "
                    f"| {m['residual']} |",
                    flush=True,
                )


if __name__ == "__main__":
    main(sys.argv[1:])
