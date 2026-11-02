"""Benchmarks for reading and writing table formats at scale (#173).

    uv run python scripts/bench_io.py [rows ...] [--formats delta,iceberg]
        [--dir path] [--timeout seconds]

Per format and size: a table of `rows` orders, written in files of at most
5·10⁶ rows by a setup process. A fresh process per view then times, on DuckDB:

* `read`: the source loaded into a pipeline (`Pipeline.source`);
* `full`: the view computed from scratch;
* `sink`: the view written to a new Delta table (`DeltaSink`);
* `incremental`: a refresh after 1% of the rows were appended and 1% deleted
  (a contiguous range of ids, so one file is rewritten);
* `merge`: the sink written again, as a MERGE of the change.

The views are `filter` (orders with an amount, projected: as large as its
input) and `by_customer` (amounts summed per customer: 10⁴ rows). Prints
each phase's time and the process's peak memory (`ru_maxrss`) after it.
The tables are left in `--dir` (default: a temporary directory, deleted at
the end).
"""

import multiprocessing as mp
import resource
import shutil
import sys
import tempfile
import time
from pathlib import Path

import numpy as np
import pyarrow as pa

FILE_ROWS = 5_000_000
VIEWS = ("filter", "by_customer")
CUSTOMERS = 10_000


def orders_table(n: int, start: int = 0, seed: int = 0) -> pa.Table:
    rng = np.random.default_rng(seed + start)
    return pa.table(
        {
            "id": np.arange(start, start + n, dtype=np.int64),
            "customer": rng.integers(0, CUSTOMERS, n),
            "amount": pa.array(rng.integers(0, 1000, n), mask=rng.random(n) < 0.05),
        }
    )


def chunks(n: int, start: int = 0):
    for lo in range(0, n, FILE_ROWS):
        yield orders_table(min(FILE_ROWS, n - lo), start + lo)


def catalog(root: Path):
    from pyiceberg.catalog.sql import SqlCatalog

    return SqlCatalog(
        "bench", uri=f"sqlite:///{root / 'catalog.db'}", warehouse=f"file://{root / 'warehouse'}"
    )


def setup(fmt: str, root: Path, n: int) -> None:
    if fmt == "delta":
        from deltalake import write_deltalake

        for i, part in enumerate(chunks(n)):
            write_deltalake(
                root / "orders",
                part,
                mode="overwrite" if i == 0 else "append",
                configuration={"delta.enableChangeDataFeed": "true"},
            )
    else:
        cat = catalog(root)
        cat.create_namespace("db")
        parts = chunks(n)
        first = next(parts)
        t = cat.create_table("db.orders", first.schema)
        t.append(first)
        for part in parts:
            t.append(part)


def mutate(fmt: str, root: Path, n: int) -> None:
    """Append 1% new rows, then delete 1% (a contiguous range of ids)."""
    k = max(1, n // 100)
    new = orders_table(k, start=n, seed=1)
    lo = n // 2
    where = f"id >= {lo} AND id < {lo + k}"
    if fmt == "delta":
        from deltalake import DeltaTable, write_deltalake

        write_deltalake(root / "orders", new, mode="append")
        DeltaTable(str(root / "orders")).delete(where)
    else:
        t = catalog(root).load_table("db.orders")
        t.append(new)
        t.delete(where)


def peak_mb() -> float:
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return rss / 1024 / (1024 if sys.platform == "darwin" else 1)


def measure(fmt: str, view_kind: str, root: Path, n: int, out: mp.Queue) -> None:
    import sverify as sv
    from sverify.incremental import Pipeline
    from sverify.io import DeltaSink, DeltaSource, IcebergSource

    phases: list[tuple[str, float, float]] = []

    def timed(name, f):
        t = time.perf_counter()
        r = f()
        phases.append((name, time.perf_counter() - t, peak_mb()))
        return r

    phases.append(("start", 0.0, peak_mb()))
    if fmt == "delta":
        src = DeltaSource(str(root / "orders"))
    else:
        src = IcebergSource(catalog(root), "db.orders")
    pipe = Pipeline(sv.connect())
    o = timed("read", lambda: pipe.source("orders", src))
    if view_kind == "filter":
        query = o.filter(o.amount.notnull()).select(o.id, o.customer, double=o.amount * 2)
    else:
        query = o.group_by("customer").aggregate(total=o.amount.sum(), n=o.id.count())
    view = timed("full", lambda: pipe.view("v", query))
    sink = DeltaSink(str(root / f"sink-{view_kind}"))
    sink._attach(view)
    timed("sink", sink._commit)
    mutate(fmt, root, n)
    timed("incremental", pipe.refresh)
    timed("merge", sink._commit)
    out.put(phases)


def option(argv: list[str], name: str, default: str) -> tuple[str, list[str]]:
    if name not in argv:
        return default, argv
    i = argv.index(name)
    return argv[i + 1], argv[:i] + argv[i + 2 :]


def run(ctx, target, args, timeout: float):
    q = ctx.Queue()
    p = ctx.Process(target=target, args=(*args, q) if target is measure else args)
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.kill()
        p.join()
        return f"over {timeout:.0f} s"
    if p.exitcode != 0:
        return f"failed (exit {p.exitcode})"
    return q.get() if target is measure else None


def main(argv: list[str]) -> None:
    formats, argv = option(argv, "--formats", "delta,iceberg")
    timeout, argv = option(argv, "--timeout", "1800")
    base, argv = option(argv, "--dir", "")
    sizes = [int(float(a)) for a in argv] or [10**6, 10**7]
    ctx = mp.get_context("spawn")
    top = Path(base) if base else Path(tempfile.mkdtemp(prefix="sverify-bench-io-"))
    try:
        for n in sizes:
            for fmt in formats.split(","):
                for view in VIEWS:
                    # A table per view: `mutate` changes it.
                    label = f"{fmt:8} {view:11} {n:>11} rows:"
                    root = top / f"{fmt}-{n}-{view}"
                    shutil.rmtree(root, ignore_errors=True)
                    root.mkdir(parents=True)
                    t = time.perf_counter()
                    err = run(ctx, setup, (fmt, root, n), float(timeout))
                    if err is not None:
                        print(f"{label} setup {err}", flush=True)
                        continue
                    print(f"{label} setup {time.perf_counter() - t:9.1f} s", flush=True)
                    result = run(ctx, measure, (fmt, view, root, n), float(timeout))
                    if result is None or isinstance(result, str):
                        print(f"{label} {result}", flush=True)
                    else:
                        for name, secs, mb in result:
                            print(f"{label} {name:12} {secs * 1000:9.0f} ms, peak {mb:7.0f} MB")
                        sys.stdout.flush()
                    if not base:
                        shutil.rmtree(root, ignore_errors=True)
    finally:
        if not base:
            shutil.rmtree(top, ignore_errors=True)


if __name__ == "__main__":
    main(sys.argv[1:])
