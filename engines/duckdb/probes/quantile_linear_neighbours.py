"""DuckDB 2.0.0, raw quantile_cont of doubles against the restated LINEAR set:
between the neighbours of the double position, or an ulp past them.
Counts escapes by whether the lower neighbour is the first value (floor(RN) = 0)."""

import math
import random
from collections import Counter

import duckdb
import pyarrow as pa

con = duckdb.connect()
con.execute("SET threads=1")
random.seed(900)


def ulps(a: float, b: float) -> int:
    """How many doubles b lies above a (negative if below); small distances only."""
    n = 0
    x = a
    while x != b and abs(n) < 8:
        x = math.nextafter(x, b)
        n += 1 if b > a else -1
    return n if x == b else (99 if b > a else -99)


def group(n: int, m: int, k: int) -> list[float]:
    e = random.choice([-300, -20, -1, 0, 1, 7, 60, 300])
    c = random.uniform(1.0, 2.0) * 2.0**e
    if random.random() < 0.4:
        c = -c
    hi = c
    for _ in range(k):
        hi = math.nextafter(hi, math.inf)
    lows = sorted(c - abs(c) * random.uniform(0.25, 3.0) for _ in range(m))
    highs = sorted(hi + abs(c) * random.uniform(0.25, 3.0) for _ in range(n - m - 2))
    return lows + [c, hi] + highs


tally: Counter = Counter()
worst: dict = {}
qs = [f"0.{i:02d}" for i in range(1, 100)] + [
    f"0.{random.randrange(1, 1000):03d}" for _ in range(60)
]
for q in qs:
    qd = float(q)
    gid, xs, meta = [], [], {}
    g = 0
    for n in (2, 3, 4, 5, 7, 12, 26, 51):
        p = (n - 1) * qd
        m = math.floor(p)
        if math.ceil(p) == m or m + 1 > n - 1:
            continue
        for k in (0, 1, 2, 5):
            for _ in range(40):
                s = group(n, m, k)
                assert s == sorted(s) and len(s) == n, (s, n, m)
                meta[g] = (s[m], s[m + 1], m == 0, k, n)
                gid += [g] * n
                xs += random.sample(s, n)
                g += 1
    if not g:
        continue
    con.register("t", pa.table({"g": gid, "x": xs}))
    for gi, got in con.execute(f"SELECT g, quantile_cont(x, {q}) FROM t GROUP BY g").fetchall():
        lo, hi, first, k, n = meta[gi]
        where = "first" if first else "later"
        tally[(where, "groups")] += 1
        if lo <= got <= hi:
            continue
        d = ulps(hi, got) if got > hi else ulps(lo, got)
        tally[(where, f"{'above hi' if got > hi else 'below lo'} by {abs(d)} ulp")] += 1
        worst.setdefault((where, d), (q, n, k, lo, hi, got))
    con.unregister("t")

for key in sorted(tally):
    print(key, tally[key])
for key, w in sorted(worst.items(), key=str):
    print("example", key, w)
