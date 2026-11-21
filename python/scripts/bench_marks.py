"""What a checked run saves on DuckDB by writing the marked expressions without
their checks (ruling 223, #1787 item 1a).

    python scripts/bench_marks.py [ROWS] [THREADS]

The double arithmetic of `bench_added_costs.py` (`x * y + x / (y + 1)`),
verified with and without bounds on `x` and `y`: the SQL a checked run writes
(with the report's marks) against the SQL with every check, and the
hand-written query. With bounds the checker rules the overflow out and marks
the expression; without, the overflow is an assumed issue and keeps its check.
Each result is hashed in DuckDB; median of 5, seconds (characters).
"""

import statistics
import sys
import time

import duckdb
import ibis

import sverify as sv
from sverify.engines import to_sql

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
THREADS = int(sys.argv[2]) if len(sys.argv) > 2 else 4

T = ibis.table({"k": "int64", "x": "float64", "y": "float64"}, name="t")
Q = T.select(T.k, v=T.x * T.y + T.x / (T.y + 1.0))
HAND = "SELECT k, x * y + x / (y + 1.0) FROM t"
CONTRACTS = {
    "bounded": {"t": [ibis._.x.between(0, 1e6), ibis._.y.between(0, 1e6)]},
    "unbounded (finite)": {"t": [ibis._.x.between(-1e300, 1e300), ibis._.y.between(0, 1e300)]},
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
    con.execute(
        f"CREATE TABLE t AS SELECT i % 100000 AS k, (i % 997) * 0.5 AS x,"
        f" (i % 13) * 0.25 AS y FROM range({ROWS}) r(i)"
    )
    print(f"DuckDB {duckdb.__version__}, {ROWS:,} rows, {THREADS} threads; median of 5, s (chars)")
    print("| contract | every check | as a checked run writes it | hand-written |")
    print("|---|---|---|---|")
    for name, requires in CONTRACTS.items():
        report = sv.verify(Q, requires=requires, ensures=[sv.equivalent(floats="exact")])
        plan = report._plan_to_run("translated", checked=True, engine="duckdb")
        full = to_sql(plan, "duckdb")
        run = to_sql(plan, "duckdb", unchecked=report._marks_of(plan))
        print(
            f"| {name} | {seconds(con, full):.3f} ({len(full)}) | {seconds(con, run):.3f} "
            f"({len(run)}) | {seconds(con, HAND):.3f} ({len(HAND)}) |"
        )


if __name__ == "__main__":
    main()
