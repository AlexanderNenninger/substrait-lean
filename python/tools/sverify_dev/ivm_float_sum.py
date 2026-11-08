"""Prototype of #918 Part B: a `SUM` of doubles maintained exactly.

A table `t(g, x)` of doubles in a few groups takes 1,000 batches of inserts
and deletes on in-process DuckDB. After each batch, per group:

* `exact`: the maintained state of `LinearAgg.floatState`, the exact sum as
  a Python `int` in units of `2⁻¹⁰⁷⁴`, each changed row's value times its
  weight added to it, rounded once at the end (`int / int` is correctly
  rounded in CPython, ties to even);
* `naive`: a running double sum, `+ x` on insert and `- x` on delete;
* `recompute`: DuckDB's `SUM(x)` over the group's current rows;

each against `math.fsum` of the current rows, the reference's correctly
rounded sum (`floatSumCR`, D25). It prints the distance of each in ulps of
the reference's value, and the rows each reads per batch.

    python -m sverify_dev.ivm_float_sum [--batches 1000] [--seed 918]
    python -m sverify_dev.ivm_float_sum --init 10000000

In-process DuckDB only, seconds per run; no checker runs.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import sys
from collections import Counter, defaultdict
from fractions import Fraction

import duckdb

SCALE = 2**1074
"""Every finite double is an integer multiple of `2⁻¹⁰⁷⁴` (`FloatCode.exact`)."""


def exact(x: float) -> int:
    """`x` in units of `2⁻¹⁰⁷⁴`, exactly."""
    q = Fraction(x) * SCALE
    assert q.denominator == 1
    return q.numerator


def rounded(s: int) -> float:
    """The exact sum `s · 2⁻¹⁰⁷⁴` rounded once (`ofExact`)."""
    return s / SCALE


def ulps(got: float, want: float) -> float:
    """`|got - want|` in ulps of `want`."""
    return 0.0 if got == want else abs(got - want) / math.ulp(want)


def value(rnd: random.Random) -> float:
    """A double from a mix that makes sums cancel: large and small, both signs."""
    kind = rnd.random()
    if kind < 0.1:
        return rnd.choice([-1.0, 1.0]) * rnd.uniform(1e15, 1e17)
    if kind < 0.2:
        return rnd.uniform(-1e-3, 1e-3)
    return rnd.uniform(-1e3, 1e3) + 0.1


def run(batches: int, seed: int, groups: int = 20, size: int = 50) -> dict[str, object]:
    rnd = random.Random(seed)
    con = duckdb.connect()
    con.execute("CREATE TABLE t (id BIGINT, g INTEGER, x DOUBLE)")
    rows: dict[int, tuple[int, float]] = {}
    state: dict[int, int] = defaultdict(int)
    naive: dict[int, float] = defaultdict(float)
    worst: dict[str, float] = defaultdict(float)
    off: Counter[str] = Counter()
    seen: dict[str, list[float]] = defaultdict(list)
    read = Counter[str]()
    next_id = 0
    for _ in range(batches):
        # A batch: about `size` changes, a third of them deletes once rows exist.
        ins, dels = [], []
        for _ in range(size):
            if rows and rnd.random() < 0.35:
                rid = rnd.choice(list(rows))
                if rid not in dels:
                    dels.append(rid)
            else:
                ins.append((next_id, rnd.randrange(groups), value(rnd)))
                next_id += 1
        change = [(g, x, 1) for _, g, x in ins] + [(*rows[r], -1) for r in dels]
        if ins:
            con.executemany("INSERT INTO t VALUES (?, ?, ?)", ins)
        if dels:
            con.execute(f"DELETE FROM t WHERE id IN ({', '.join(map(str, dels))})")
        for rid, g, x in ins:
            rows[rid] = (g, x)
        for rid in dels:
            del rows[rid]
        # The contributions, as `contrib` gives them: each changed row's
        # group, value and weight. The state adds them up.
        read["maintained"] += len(change)
        touched = {g for g, _, _ in change}
        for g, x, w in change:
            state[g] += w * exact(x)
            naive[g] += w * x
        current: dict[int, list[float]] = defaultdict(list)
        for g, x in rows.values():
            current[g].append(x)
        recomputed = dict(con.execute("SELECT g, SUM(x) FROM t GROUP BY g").fetchall())
        read["recompute touched"] += sum(len(current[g]) for g in touched)
        for g in touched:
            if not current[g]:
                continue
            want = math.fsum(current[g])
            off["checked"] += 1
            for name, got in (
                ("exact", rounded(state[g])),
                ("naive", naive[g]),
                ("recompute", recomputed[g]),
            ):
                d = ulps(got, want)
                worst[name] = max(worst[name], d)
                seen[name].append(d)
                off[name] += got != want
    return {
        "batches": batches,
        "seed": seed,
        "rows_now": len(rows),
        "changes": read["maintained"],
        "worst_ulps": dict(worst),
        "median_ulps": {k: statistics.median(v) for k, v in seen.items()},
        "group_results_off": dict(off),
        "rows_read": dict(read),
    }


def init_cost(n: int, groups: int = 1000) -> dict[str, object]:
    """The initial state's cost on `n` rows: DuckDB gives each row's
    contribution as Arrow (the `values` plan's shape), and
    `sverify._exact_sum.fold` adds them up. Rows per second, and the peak
    RSS of this process (run it alone: the peak counts the whole process)."""
    import resource
    import time

    from sverify import _exact_sum

    con = duckdb.connect()
    con.execute(
        f"CREATE TABLE t AS SELECT (i % {groups})::BIGINT AS k0, "
        "(random() - 0.5) * pow(10, (random() * 40)::INT - 20) AS x FROM range({n}) r(i)".replace(
            "{n}", str(n)
        )
    )
    start = time.perf_counter()
    rows = con.sql("SELECT k0, 1::BIGINT AS w, x FROM t").to_arrow_table()
    fetched = time.perf_counter()
    out = _exact_sum.fold(
        "fsum",
        rows.select(["k0"]),
        [rows.column("x").combine_chunks()],
        rows.column("w").combine_chunks(),
    )
    done = time.perf_counter()
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    peak_mb = peak / 2**20 if sys.platform == "darwin" else peak / 2**10
    return {
        "rows": n,
        "groups": len(out),
        "fetch_s": round(fetched - start, 2),
        "fold_s": round(done - fetched, 2),
        "fold_rows_per_s": round(n / (done - fetched)),
        "peak_rss_mb": round(peak_mb),
    }


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--batches", type=int, default=1000)
    p.add_argument("--seed", type=int, default=918)
    p.add_argument("--init", type=int, metavar="ROWS", help="measure the initial state instead")
    a = p.parse_args(argv)
    print(f"duckdb {duckdb.__version__}")
    print(init_cost(a.init) if a.init else run(a.batches, a.seed))


if __name__ == "__main__":
    main()
