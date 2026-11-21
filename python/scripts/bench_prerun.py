"""Where a checked run's time goes before its plan (#1787 item 3, ruling 223).

    python scripts/bench_prerun.py [ROWS]

fin-vwap, the first catalogue query with assumed issues, on DuckDB: the run as
`Report.run` makes it, the plan alone (`check_requires=False`), and each check
before it alone (the schema, the preconditions, the assumed issues). Median
of 7, ms.
"""

import statistics
import sys
import time

import sverify as sv
from sverify.engine import connect, put_table
from sverify.report import violation_counts
from sverify_dev import catalogue

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000


def ms(f, *args, **kwargs) -> float:
    f(*args, **kwargs)
    times = []
    for _i in range(7):
        start = time.perf_counter()
        f(*args, **kwargs)
        times.append(time.perf_counter() - start)
    return 1000 * statistics.median(times)


schemas = catalogue.load_schemas()
(q,) = [q for q in catalogue.load_queries() if q.id == "fin-vwap"]
requires, ensures = catalogue.contract(q, schemas, "native")
report = sv.verify(catalogue.build(q, schemas, "native"), requires=requires, ensures=ensures)
data = catalogue.synthetic(schemas, q.dataset, "native", rows=ROWS)
con = connect()
for t, table in data.items():
    put_table(con, t, table)
print(
    f"fin-vwap, {ROWS:,} rows, DuckDB; median of 7, ms; assumed: {[i.kind for i in report.assumed]}"
)


def conditions():
    for t, conds in report._conditions.items():
        if con.has(t):
            list(violation_counts(con.table(t), conds, "duckdb"))


parts = {
    "run": lambda: report.run(con, "duckdb"),
    "plan alone (check_requires=False)": lambda: report.run(con, "duckdb", check_requires=False),
    "check_inputs": lambda: report.check_inputs(con, "duckdb"),
    "schema": lambda: report._check_schema(con, "duckdb"),
    "conditions": conditions,
    "assumed check": lambda: report._check_assumed(con, "duckdb"),
}
for name, f in parts.items():
    print(f"| {name} | {ms(f):.0f} |")
print("conditions per table:", {t: len(c) for t, c in report._conditions.items()})
