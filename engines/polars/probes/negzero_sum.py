"""The sign of a double SUM and AVG over only -0.0 (#2587, ruling 285, F2).

Run: python negzero_sum_probe.py [duckdb|polars|spark ...]

The reference's sum is correctly rounded from the exact sum, which is the exact
zero, so +0.0 (`floatSumCR`). An engine that adds -0.0 + -0.0 in IEEE gets -0.0.
Each case prints the result and its sign bit.
"""

import math
import sys

CASES = {"one": [-0.0], "two": [-0.0, -0.0]}


def sign(x):
    if x is None:
        return "NULL"
    return f"{x!r} ({'-' if math.copysign(1.0, x) < 0 else '+'})"


def duckdb_rows():
    import duckdb

    con = duckdb.connect()
    print("duckdb", duckdb.__version__)
    for name, xs in CASES.items():
        con.execute("DROP TABLE IF EXISTS t")
        con.execute("CREATE TABLE t (g INTEGER, x DOUBLE)")
        con.executemany("INSERT INTO t VALUES (1, ?)", [[x] for x in xs])
        for what, q in [
            ("sum", "SELECT SUM(x) FROM t"),
            ("avg", "SELECT AVG(x) FROM t"),
            ("sum grouped", "SELECT SUM(x) FROM t GROUP BY g"),
            ("avg grouped", "SELECT AVG(x) FROM t GROUP BY g"),
            ("sum window", "SELECT SUM(x) OVER (PARTITION BY g) FROM t LIMIT 1"),
            ("avg window", "SELECT AVG(x) OVER (PARTITION BY g) FROM t LIMIT 1"),
            ("sum running", "SELECT SUM(x) OVER (ORDER BY g ROWS UNBOUNDED PRECEDING) FROM t"),
        ]:
            rows = [r[0] for r in con.execute(q).fetchall()]
            yield name, what, ", ".join(sign(v) for v in rows)


def polars_rows():
    import polars as pl

    print("polars", pl.__version__)
    for name, xs in CASES.items():
        lf = pl.LazyFrame({"g": [1] * len(xs), "x": xs}, schema={"g": pl.Int64, "x": pl.Float64})
        for engine in ("in-memory", "streaming"):

            def run(q, engine=engine):
                return q.collect(engine="streaming" if engine == "streaming" else "in-memory")

            for what, q in [
                ("sum", lf.select(pl.col("x").sum())),
                ("avg", lf.select(pl.col("x").mean())),
                ("sum grouped", lf.group_by("g").agg(pl.col("x").sum())),
                ("avg grouped", lf.group_by("g").agg(pl.col("x").mean())),
                ("sum window", lf.select(pl.col("x").sum().over("g"))),
                ("avg window", lf.select(pl.col("x").mean().over("g"))),
                ("sum running", lf.select(pl.col("x").cum_sum())),
            ]:
                out = run(q)
                col = out.columns[-1]
                yield name, f"{what} [{engine}]", ", ".join(sign(v) for v in out[col].to_list())


def spark_rows():
    from pyspark.sql import SparkSession

    spark = (
        SparkSession.builder.master("local[1]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )
    print("spark", spark.version)
    for name, xs in CASES.items():
        spark.createDataFrame([(1, x) for x in xs], "g INT, x DOUBLE").createOrReplaceTempView("t")
        for what, q in [
            ("sum", "SELECT SUM(x) FROM t"),
            ("avg", "SELECT AVG(x) FROM t"),
            ("sum grouped", "SELECT SUM(x) FROM t GROUP BY g"),
            ("avg grouped", "SELECT AVG(x) FROM t GROUP BY g"),
            ("sum window", "SELECT SUM(x) OVER (PARTITION BY g) FROM t LIMIT 1"),
            ("avg window", "SELECT AVG(x) OVER (PARTITION BY g) FROM t LIMIT 1"),
            ("sum running", "SELECT SUM(x) OVER (ORDER BY g ROWS UNBOUNDED PRECEDING) FROM t"),
        ]:
            rows = [r[0] for r in spark.sql(q).collect()]
            yield name, what, ", ".join(sign(v) for v in rows)
    spark.stop()


def main() -> None:
    for engine in sys.argv[1:] or ["duckdb", "polars", "spark"]:
        rows = {"duckdb": duckdb_rows, "polars": polars_rows, "spark": spark_rows}[engine]
        try:
            for name, what, v in rows():
                print(f"  {name:>3} {what:<26} {v}")
        except Exception as e:  # report and go on
            print(f"  {engine}: {type(e).__name__}: {str(e)[:160]}")


if __name__ == "__main__":
    main()
