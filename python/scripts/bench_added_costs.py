"""What sverify's own additions cost on DuckDB (#1787 research, 2026-11-21).

    python scripts/bench_added_costs.py [ROWS] [THREADS]

For a few everyday plans, the written SQL as `Report.run` writes it against
the same SQL without one of sverify's additions: per-row guards
(`guards=False`), the check of double operations against `±∞`
(`finite=False`), the row ordinal of sequence mode (`rows="multiset"`), and
the hand-written query. Each result is hashed in DuckDB; median of 5,
seconds. The input is a table (no `rowid` copy), so the ordinal's cost is the
numbering alone.
"""

import statistics
import sys
import time

import duckdb
import ibis

from sverify.ibis_substrait import to_substrait_json
from sverify.sql import to_sql

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
THREADS = int(sys.argv[2]) if len(sys.argv) > 2 else 4

T = ibis.table({"k": "int64", "a": "int64", "b": "int64", "x": "float64", "y": "float64"}, name="t")
U = ibis.table({"k": "int64", "w": "int64"}, name="u")

PLANS = {
    "integer arithmetic": (
        T.select(T.k, v=(T.a * T.b + T.a) // (T.b + 1)),
        "SELECT k, (a * b + a) // (b + 1) FROM t",
    ),
    "double arithmetic": (
        T.select(T.k, v=T.x * T.y + T.x / (T.y + 1.0)),
        "SELECT k, x * y + x / (y + 1.0) FROM t",
    ),
    "integer SUM": (
        T.group_by("k").aggregate(s=T.a.sum()),
        "SELECT k, SUM(a) FROM t GROUP BY k",
    ),
    "join, filter": (
        T.join(U, "k").filter(T.a > 5).select(T.k, T.a, U.w),
        "SELECT t.k, a, w FROM t JOIN u USING (k) WHERE a > 5",
    ),
    "order by, limit": (
        T.order_by(T.a).limit(100).select(T.k, T.a),
        "SELECT k, a FROM t ORDER BY a LIMIT 100",
    ),
}

VARIANTS = {
    "as run": {},
    "guards=False": {"guards": False},
    "finite=False": {"guards": False, "finite": False},
    'rows="multiset"': {"rows": "multiset"},
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
        f"CREATE TABLE t AS SELECT i % 100000 AS k, i % 1000 AS a, i % 77 AS b,"
        f" (i % 997) * 0.5 AS x, (i % 13) * 0.25 AS y FROM range({ROWS}) r(i)"
    )
    con.execute("CREATE TABLE u AS SELECT i AS k, i % 10 AS w FROM range(100000) r(i)")
    print(f"DuckDB {duckdb.__version__}, {ROWS:,} rows, {THREADS} threads; median of 5, s (chars)")
    print("| plan | " + " | ".join(VARIANTS) + " | hand-written |")
    print("|---|" + "---|" * (len(VARIANTS) + 1))
    for name, (q, hand) in PLANS.items():
        plan = to_substrait_json(q)
        cells = []
        for kw in VARIANTS.values():
            sql = to_sql(plan, "duckdb", **kw)
            cells.append(f"{seconds(con, sql):.3f} ({len(sql)})")
        cells.append(f"{seconds(con, hand):.3f} ({len(hand)})")
        print(f"| {name} | " + " | ".join(cells) + " |")


if __name__ == "__main__":
    main()
