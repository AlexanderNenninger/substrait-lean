"""What the two-stage double `SUM` saves on DuckDB (ruling 212 C6, #1608 item 7).

    python scripts/bench_two_stage_sums.py [ROWS] [THREADS]

The written SQL of a grouped double `SUM` (with an `AVG` beside it), one stage
against two (`Dialect.two_stage_sums`), and a plain `SUM` for reference, on
four inputs: (a) a table whose every group's sum is finite; (b) the same
behind a join, so the input is read twice; (c) a table whose every group
holds `+inf`, so every group reaches the second stage; (d) a table with a
group per ten rows. Each query's result is hashed in DuckDB; median of 5,
seconds.
"""

import statistics
import sys
import time

import duckdb
import ibis

from sverify.ibis_substrait import to_substrait_json
from sverify.sql import dialect_of, to_sql

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
THREADS = int(sys.argv[2]) if len(sys.argv) > 2 else 4

T = ibis.table({"k": "int64", "x": "float64"}, name="t")
U = ibis.table({"k": "int64", "w": "float64"}, name="u")
FLAT = T.group_by("k").aggregate(s=T.x.sum(), a=T.x.mean())
JOINED = T.join(U, "k").group_by("k").aggregate(s=(T.x + U.w).sum(), a=T.x.mean())

CASES = {
    "(a) finite, table": (FLAT, "i % 100000", "(i % 997) * 0.5"),
    "(b) finite, join": (JOINED, "i % 100000", "(i % 997) * 0.5"),
    "(c) every group +inf": (
        FLAT,
        "i % 100000",
        "CASE WHEN i < 100000 THEN 'inf'::DOUBLE ELSE 1.0 END",
    ),
    "(d) many groups": (FLAT, "i // 10", "(i % 997) * 0.5"),
}


def seconds(con: duckdb.DuckDBPyConnection, sql: str) -> float:
    q = f"SELECT SUM(hash(COLUMNS(*))) FROM ({sql})"
    con.execute(q).fetchall()
    times = []
    for _ in range(5):
        start = time.perf_counter()
        con.execute(q).fetchall()
        times.append(time.perf_counter() - start)
    return statistics.median(times)


def main() -> None:
    con = duckdb.connect()
    con.execute(f"SET threads = {THREADS}")
    duck = type(dialect_of("duckdb"))
    print(f"DuckDB {duckdb.__version__}, {ROWS:,} rows, {THREADS} threads; median of 5, s")
    print("| input | one stage | two stages | plain SUM | one/two |")
    print("|---|---|---|---|---|")
    for name, (q, key, x) in CASES.items():
        con.execute(
            f"CREATE OR REPLACE TABLE t AS SELECT {key} AS k, {x} AS x FROM range({ROWS}) r(i)"
        )
        con.execute("CREATE OR REPLACE TABLE u AS SELECT i AS k, 1.0 AS w FROM range(1000000) r(i)")
        plan = to_substrait_json(q)
        found = {}
        for two in (False, True):
            duck.two_stage_sums = two
            found[two] = seconds(con, to_sql(plan, "duckdb"))
        src = "t JOIN u USING (k)" if q is JOINED else "t"
        plain = seconds(con, f"SELECT k, SUM(x), AVG(x) FROM {src} GROUP BY k")
        print(f"| {name} | {found[False]:.3f} | {found[True]:.3f} | {plain:.3f} "
              f"| {found[False] / found[True]:.2f}× |")  # fmt: skip


if __name__ == "__main__":
    main()
