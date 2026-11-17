"""DuckDB 2.0.0: which double does quantile_cont take for a decimal q?
On the group [0.0, 1.0], RN = 1·q_dbl and the result is q_dbl (or 1.0 where q_dbl is 1.0)."""

import random

import duckdb

con = duckdb.connect()
con.execute("SET threads=1")
con.execute("CREATE TABLE t(x DOUBLE)")
con.execute("INSERT INTO t VALUES (0.0), (1.0)")


def got(q: str) -> float:
    return con.execute(f"SELECT quantile_cont(x, {q}) FROM t").fetchall()[0][0]


print("version", duckdb.__version__)
for q in [
    "0.9999999999999999",
    "0.3333333333333333",
    "0.9007199254740993",
    "0.28",
    "0.2800000000000000",
]:
    print(q, "duckdb", repr(got(q)), "nearest", repr(float(q)), "same", got(q) == float(q))

random.seed(1530)
for scale in (2, 8, 15, 16, 17, 18):
    off = big = bigoff = 0
    worst = None
    for _ in range(4000):
        num = random.randrange(1, 10**scale)
        q = f"0.{num:0{scale}d}"
        g = got(q)
        if num >= 2**53:
            big += 1
        if g != float(q):
            off += 1
            if num >= 2**53:
                bigoff += 1
            worst = worst or (q, repr(g), repr(float(q)))
    print(
        "scale",
        scale,
        "of 4000: differ from nearest",
        off,
        "| num>=2^53:",
        big,
        "of which differ",
        bigoff,
        "| first",
        worst,
    )
