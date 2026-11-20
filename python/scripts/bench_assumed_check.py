"""What the assumed check costs a run (#2018, ruling 195, G10).

    python scripts/bench_assumed_check.py [ROWS]

For #2018's repro (a left join to a grouped SUM no column of which is used)
and the first catalogue query whose report has assumed issues, on DuckDB and
Polars: the median of 5 of the run as `Report.run` makes it, of the plan
alone (`check_requires=False`: no precondition and no assumed check), and of
the check plan alone (`Report._check_assumed`). Main ran the plan alone on a
translated route, and the plan once more on DuckDB before it where its
engine did not check the assumptions as it ran (`checks_assumed`).
"""

import statistics
import sys
import time
from collections.abc import Callable

import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.engine import connect, put_table
from sverify_dev import catalogue

ROWS = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
ENGINES = ("duckdb", "polars")


def ms(f: Callable[..., object], *args: object, n: int = 5, **kwargs: object) -> float:
    f(*args, **kwargs)
    times = []
    for _i in range(n):
        start = time.perf_counter()
        f(*args, **kwargs)
        times.append(time.perf_counter() - start)
    return 1000 * statistics.median(times)


def repro() -> tuple[str, sv.Report, dict[str, pa.Table]]:
    t = ibis.table({"a": "int64", "x": "int64"}, name="t")
    s = t.group_by("a").aggregate(s=t.x.sum())
    expr = t.select("a").left_join(s, _.a == s.a).select(t.a)
    report = sv.verify(expr, ensures=[sv.equivalent(floats="exact")])
    data = pa.table({"a": [i % 1000 for i in range(ROWS)], "x": list(range(ROWS))})
    return "#2018 repro", report, {"t": data}


def from_catalogue() -> tuple[str, sv.Report, dict[str, pa.Table]]:
    schemas = catalogue.load_schemas()
    for q in catalogue.load_queries():
        if q.not_expressible is not None or q.requires is None:
            continue
        try:
            requires, ensures = catalogue.contract(q, schemas, "native")
            report = sv.verify(
                catalogue.build(q, schemas, "native"), requires=requires, ensures=ensures
            )
        except Exception:  # noqa: BLE001 - a query this bench cannot use
            continue
        if report.assumed and report.verdict != sv.Verdict.UNPROVED:
            data = catalogue.synthetic(schemas, q.dataset, "native", rows=ROWS)
            return f"catalogue {q.id}", report, data
    raise SystemExit("no catalogue query with assumed issues")


def main() -> None:
    print(f"{ROWS:,} rows; median of 5, ms")
    print("| plan | engine | run | plan alone | check alone |")
    print("|---|---|---|---|---|")
    for name, report, data in (repro(), from_catalogue()):
        con = connect()
        for t, table in data.items():
            put_table(con, t, table)
        for engine in ENGINES:
            run = ms(report.run, con, engine)
            alone = ms(report.run, con, engine, check_requires=False)
            check = ms(report._check_assumed, con, engine)
            print(f"| {name} | {engine} | {run:.0f} | {alone:.0f} | {check:.0f} |")


if __name__ == "__main__":
    main()
