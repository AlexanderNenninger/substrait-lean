"""What a checked run saves on DuckDB by writing a double `SUM` and `AVG` that
no summation order overflows as plain sums (#1787 item 4, rulings 238 and 242).

    python scripts/bench_finite_sum.py [ROWS] [THREADS]

A grouped `SUM` and `AVG` of a bounded double, under a contract with a
`max_rows` cap: the SQL a checked run writes with the report's marks (one
stage) against the SQL without them (two stages, ruling 212), on a table and
behind a join. Each result is hashed in DuckDB; median of 5, seconds.
"""

import statistics
import sys
import time

import duckdb
import ibis
from ibis import _

import sverify as sv
from sverify.sql import to_sql
from sverify_duckdb.dialect import DUCKDB

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
THREADS = int(sys.argv[2]) if len(sys.argv) > 2 else 4

T = ibis.table({"k": "int64", "x": "float64"}, name="t")
U = ibis.table({"k": "int64", "w": "float64"}, name="u")
QUERIES = {
    "table": T.group_by("k").agg(s=T.x.sum(), a=T.x.mean()),
    "join": T.join(U, "k").group_by("k").agg(s=(T.x + U.w).sum(), a=T.x.mean()),
}
REQUIRES = {
    "t": [_.x.between(0, 1e6), sv.max_rows(10**9)],
    "u": [_.w.between(0, 1e6), sv.unique("k"), sv.max_rows(10**9)],
}


def without_measures(marks: dict) -> dict:
    """`marks` without an aggregate's measure slots (`1 + i`): the run as it
    was before item 4, every other mark kept."""
    slots = marks.get("slots", [])
    if marks.get("node") == "Aggregate":
        slots = [k for k in slots if k == 0]
    return {**marks, "slots": slots, "inputs": [without_measures(m) for m in marks["inputs"]]}


def seconds(con: duckdb.DuckDBPyConnection, sql: str) -> float:
    q = f"SELECT SUM(hash(COLUMNS(*))) FROM ({sql})"
    con.execute(q).fetchall()
    times = []
    for _i in range(5):
        start = time.perf_counter()
        con.execute(q).fetchall()
        times.append(time.perf_counter() - start)
    return statistics.median(times)


def main() -> None:
    con = duckdb.connect()
    con.execute(f"SET threads = {THREADS}")
    con.execute(
        f"CREATE TABLE t AS SELECT i % 100000 AS k, (i % 997) * 0.5 AS x FROM range({ROWS}) r(i)"
    )
    con.execute("CREATE TABLE u AS SELECT i AS k, (i % 13) * 0.25 AS w FROM range(100000) r(i)")
    print(f"DuckDB {duckdb.__version__}, {ROWS:,} rows, {THREADS} threads; median of 5, s (chars)")
    print("| input | two stages | as a checked run writes it | speed-up |")
    print("|---|---|---|---|")
    for name, q in QUERIES.items():
        report = sv.verify(q, requires={t: REQUIRES[t] for t in ("t", "u")[: 1 + (name == "join")]})
        plan = report._plan_to_run("translated", checked=True, engine="duckdb")
        marks = report._marks_of(plan)
        assert marks is not None, name
        two = to_sql(plan, DUCKDB, unchecked=without_measures(marks))
        one = to_sql(plan, DUCKDB, unchecked=marks)
        a, b = seconds(con, two), seconds(con, one)
        print(f"| {name} | {a:.3f} ({len(two)}) | {b:.3f} ({len(one)}) | {a / b:.2f}× |")


if __name__ == "__main__":
    main()
