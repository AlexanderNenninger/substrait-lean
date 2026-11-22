"""Probe Spark's parser on a deeply nested statement (`spark-exec-parser-depth`).

Maintainer tooling (`sverify_dev`): not in the wheel. A plan whose `AND`/`OR`
nest alternates `levels` deep around a raising operand (`x != 0 AND 10 // x > 1`
under `z > 0 OR` / `z > 0 AND`, #1719) is verified, written as Spark SQL, and
run on a local Spark session phase by phase: sverify's translation to SQL,
`spark.sql` (Spark's parser and analyzer), the optimizer, physical planning and
execution. A statement the parser refuses (`FAILED_TO_PARSE_TOO_COMPLEX`) ends
the row there, through `sverify_spark.engine.parse_sql`.

`python -m sverify_dev.spark_parser_depth --write` writes
`engines/spark/probes/parser-depth.json`, the fact's evidence. It needs
`pyspark` and a JVM, and the checker; run it on homelab (CLAUDE.md), where it
takes about a minute. No test checks it is current: a JVM is too heavy for the
test suite.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

OUT = Path(__file__).resolve().parents[3] / "engines" / "spark" / "probes" / "parser-depth.json"
LEVELS = (10, 20, 70, 80)
ROWS = 3000


def _nest(levels: int):
    import ibis

    t = ibis.table({"x": "int64", "z": "int64"}, name="t")
    e = (t.x != 0) & ((10 // t.x) > 1)
    for i in range(levels):
        e = ((t.z > 0) | e) if i % 2 == 0 else ((t.z > 0) & e)
    return t.filter(e)


def row(levels: int) -> dict[str, Any]:
    import pyarrow as pa

    import sverify as sv
    from sverify._unsupported import Unsupported
    from sverify.sql import to_sql
    from sverify_spark.dialect import SPARK
    from sverify_spark.engine import _condition, parse_sql, put_tables, session

    out: dict[str, Any] = {"levels": levels}
    report = sv.verify(_nest(levels), on_inferred="off")
    plan = report._plan_to_run(None, checked=False, engine="spark")
    t0 = time.perf_counter()
    sql = to_sql(plan, SPARK, deterministic=False, finite=True)
    out["to_sql_s"] = round(time.perf_counter() - t0, 2)
    out["sql_bytes"] = len(sql)
    spark = session()
    # x = 0 on every 11th row; z alternates
    table = pa.table({"x": [i % 11 for i in range(ROWS)], "z": [i % 2 for i in range(ROWS)]})
    put_tables({"t": table}, spark)
    t0 = time.perf_counter()
    try:
        df = parse_sql(spark, sql)
    except Unsupported as e:
        out["parse_and_analysis_s"] = round(time.perf_counter() - t0, 2)
        cause = e.__cause__
        assert cause is not None
        out["refused"] = f"{type(cause).__name__}: {_condition(cause) or ''}"
        out["message"] = str(e)
        return out
    out["parse_and_analysis_s"] = round(time.perf_counter() - t0, 2)
    qe = df._jdf.queryExecution()  # pyrefly: ignore
    for name, step in (
        ("optimizer_s", qe.optimizedPlan),
        ("physical_planning_s", qe.sparkPlan),
        ("prepare_s", qe.executedPlan),
    ):
        t0 = time.perf_counter()
        step()
        out[name] = round(time.perf_counter() - t0, 2)
    t0 = time.perf_counter()
    out["rows"] = df.toArrow().num_rows
    out["execution_s"] = round(time.perf_counter() - t0, 2)
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--levels", type=int, nargs="+", default=list(LEVELS))
    ap.add_argument("--write", action="store_true", help=f"write {OUT}")
    args = ap.parse_args()
    import pyspark

    rows = []
    for n in args.levels:
        rows.append(row(n))
        print(json.dumps(rows[-1]), file=sys.stderr, flush=True)
    got = {
        "probe": "spark_parser_depth",
        "engine": "spark",
        "version": pyspark.__version__,
        "shape": "filter",
        "rows": rows,
    }
    if args.write:
        OUT.write_text(json.dumps(got, indent=2) + "\n")
    else:
        print(json.dumps(got, indent=2))


if __name__ == "__main__":
    main()
