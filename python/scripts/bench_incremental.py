"""Benchmarks for incremental views at scale (#173).

    uv run python scripts/bench_incremental.py [rows ...] [--engines duckdb,polars]
        [--timeout seconds]

Per view, engine and size: building the view over `rows` orders, then one
refresh with 1% of the rows inserted and 1% deleted. Each case runs in a
process of its own, so the peak memory (`ru_maxrss`) is that case's, and is
stopped after `--timeout` seconds (default 600).

* `filter`: orders with an amount, projected (linear: the view is as large
  as its input).
* `join`: orders joined with their customer's city (linear).
* `by_city`: amounts summed per city after the join (no delta rules: the
  pipeline recomputes it and diffs the result).

Prints the build and refresh time, and the peak memory, of each.
"""

import multiprocessing as mp
import resource
import sys
import time

import ibis
import numpy as np
import pyarrow as pa

import sverify as sv
from sverify.engine import put_table
from sverify.incremental import Pipeline

CUSTOMERS = 10_000


def orders_table(n: int, start: int = 0, seed: int = 0) -> pa.Table:
    rng = np.random.default_rng(seed)
    return pa.table(
        {
            "id": np.arange(start, start + n, dtype=np.int64),
            "customer": rng.integers(0, CUSTOMERS, n),
            "amount": pa.array(rng.integers(0, 1000, n), mask=rng.random(n) < 0.05),
        }
    )


def customers_table() -> pa.Table:
    return pa.table(
        {
            "customer": np.arange(CUSTOMERS, dtype=np.int64),
            "city": pa.array([f"city-{i % 1000}" for i in range(CUSTOMERS)]),
        }
    )


def query(con, view: str) -> ibis.Table:
    o, c = con.table("orders"), con.table("customers")
    if view == "filter":
        return o.filter(o.amount.notnull()).select(o.id, o.customer, double=o.amount * 2)
    joined = o.join(c, o.customer == c.customer).select(o.id, c.city, o.amount)
    if view == "join":
        return joined
    return joined.group_by("city").agg(total=joined.amount.sum(), n=joined.id.count())


def rows(table: pa.Table) -> list[tuple]:
    return list(zip(*table.to_pydict().values(), strict=True))


def case(view: str, engine: str, n: int, out: mp.Queue) -> None:
    orders = orders_table(n)
    con = sv.connect()
    put_table(con, "orders", orders)
    put_table(con, "customers", customers_table())
    pipe = Pipeline(con, engine)  # type: ignore[arg-type]
    t = time.perf_counter()
    pipe.view("v", query(con, view))
    build = time.perf_counter() - t
    k = max(1, n // 100)
    gone = np.random.default_rng(1).choice(n, k, replace=False)
    changes = sv.Changes(
        inserts=rows(orders_table(k, start=n, seed=2)), deletes=rows(orders.take(gone))
    )
    t = time.perf_counter()
    pipe.apply({"orders": changes})
    refresh = time.perf_counter() - t
    out.put((build, refresh, resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))


def option(argv: list[str], name: str, default: str) -> tuple[str, list[str]]:
    if name not in argv:
        return default, argv
    i = argv.index(name)
    return argv[i + 1], argv[:i] + argv[i + 2 :]


def main(argv: list[str]) -> None:
    engines, argv = option(argv, "--engines", "duckdb,polars")
    timeout, argv = option(argv, "--timeout", "600")
    sizes = [int(float(a)) for a in argv] or [10**5, 10**6]
    ctx = mp.get_context("spawn")
    for n in sizes:
        for view in ("filter", "join", "by_city"):
            for engine in engines.split(","):
                q = ctx.Queue()
                p = ctx.Process(target=case, args=(view, engine, n, q))
                p.start()
                p.join(float(timeout))
                if p.is_alive():
                    p.kill()
                    p.join()
                    print(f"{view:8} {engine:7} {n:>10} rows: over {timeout} s", flush=True)
                    continue
                if p.exitcode != 0:
                    print(f"{view:8} {engine:7} {n:>10} rows: failed (exit {p.exitcode})")
                    continue
                build, refresh, rss = q.get()
                print(
                    f"{view:8} {engine:7} {n:>10} rows: build {build * 1000:9.0f} ms,"
                    f" refresh {refresh * 1000:9.0f} ms, peak {rss / 1024:7.0f} MB",
                    flush=True,
                )


if __name__ == "__main__":
    main(sys.argv[1:])
