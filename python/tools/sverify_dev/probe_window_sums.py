"""Probe how each engine sums a window's frame of doubles (#1032).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. The facts `duckdb-window-sum-order`, `polars-window-agg` and
`spark-window-agg` cite it for `window_sum_algo`.

The probe sums `[1e16, 1, 1, 1, 1]` (in row order `i`) over the frame `ROWS
BETWEEN 1 PRECEDING AND CURRENT ROW`. Summed anew, by a tree or by a running
sum that only grows, each frame is a sum of its own values: the frames `[1,
1]` give `2.0`. An accumulator that adds the entering row and subtracts the
leaving one (`SLIDING`) has carried `1e16` and gives `0.0` there, since
`1e16 + 1` rounds back to `1e16`.

    python -m sverify_dev.probe_window_sums [--spark]

prints one JSON object: per engine and path, the window sums. `--spark` adds
Spark's local session (a JVM, Java 17 or 21; about half a minute).
"""

from __future__ import annotations

import argparse
import json
import sys

VALUES = [1e16, 1.0, 1.0, 1.0, 1.0]
#: Each frame summed on its own: what `RECOMPUTE`, `TREE` and `RUNNING_ADD` give.
OWN_VALUES = [1e16, 1e16, 2.0, 2.0, 2.0]
FRAME = "ROWS BETWEEN 1 PRECEDING AND CURRENT ROW"
ROWS = ", ".join(f"({i}, CAST({v!r} AS DOUBLE))" for i, v in enumerate(VALUES))
SQL = f"SELECT i, sum(v) OVER (ORDER BY i {FRAME}) AS s FROM (VALUES {ROWS}) AS t(i, v) ORDER BY i"


def duckdb_sums() -> dict[str, list[float]]:
    import duckdb

    con = duckdb.connect()
    return {"sql": [r[1] for r in con.execute(SQL).fetchall()]}


def polars_sums() -> dict[str, list[float]]:
    import ibis
    import polars as pl
    import pyarrow as pa
    from ibis import _

    import sverify as sv

    # sverify's translation (`polars_engine.Windows`), as a verified plan runs.
    con = sv.connect()
    con.put("t", pa.table({"i": list(range(len(VALUES))), "v": VALUES}))
    t = con.table("t")
    w = ibis.window(order_by=t.i, preceding=1, following=0)
    finite = {"t": [_.v.between(-1e17, 1e17), _.i.notnull()]}
    report = sv.verify(t.mutate(s=t.v.sum().over(w)).order_by("i"), requires=finite)
    ran = report.run(con, "polars")
    # Polars' own rolling kernel (a sliding Kahan sum), which the translation does not use.
    native = pl.Series(VALUES).rolling_sum(window_size=2, min_samples=1)
    return {"sverify": ran.column("s").to_pylist(), "rolling_sum": native.to_list()}


def spark_sums() -> dict[str, list[float]]:
    from pyspark.sql import SparkSession

    spark = SparkSession.builder.master("local[1]").getOrCreate()
    out = {"default": [r["s"] for r in spark.sql(SQL).collect()]}
    spark.conf.set("spark.sql.window.segmentTree.enabled", "true")
    out["segment_tree"] = [r["s"] for r in spark.sql(SQL).collect()]
    spark.stop()
    return out


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--spark", action="store_true", help="also probe a local Spark session")
    args = parser.parse_args(argv)
    found = {"sql": SQL, "own_values": OWN_VALUES, "duckdb": duckdb_sums(), "polars": polars_sums()}
    if args.spark:
        found["spark"] = spark_sums()
    json.dump(found, sys.stdout, indent=2)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
