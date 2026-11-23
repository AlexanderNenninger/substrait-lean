"""How DuckDB, Polars and Spark round a double cast to a decimal at exact ties,
beside their rescale of a decimal holding the same value (ruling 278, F2).

Run: python double_to_decimal.py [duckdb|polars|spark ...]

Every value is a binary tie: x * 10^s is exactly n + 0.5 as a double, so the
rounding mode alone decides the result.
"""

import sys
from decimal import Decimal

#: (double, target precision, target scale, decimal source type for the rescale)
CASES = [
    (0.125, 3, 2, (4, 3)),
    (-0.125, 3, 2, (4, 3)),
    (0.375, 3, 2, (4, 3)),
    (2.5, 2, 0, (2, 1)),
    (-2.5, 2, 0, (2, 1)),
    (3.5, 2, 0, (2, 1)),
    (2.0**51 + 0.5, 17, 0, (18, 1)),
    (-(2.0**51) - 0.5, 17, 0, (18, 1)),
]


def duckdb_rows():
    import duckdb

    con = duckdb.connect()
    print("duckdb", duckdb.__version__)
    for x, p, s, (sp, ss) in CASES:
        lit = repr(x)
        d = con.execute(f"SELECT CAST({lit}::DOUBLE AS DECIMAL({p},{s}))").fetchone()[0]
        r = con.execute(
            f"SELECT CAST(CAST('{Decimal(x)}' AS DECIMAL({sp},{ss})) AS DECIMAL({p},{s}))"
        ).fetchone()[0]
        yield x, p, s, d, r


def polars_rows():
    import polars as pl

    print("polars", pl.__version__)
    for x, p, s, (sp, ss) in CASES:
        lf = pl.LazyFrame({"x": [x]}, schema={"x": pl.Float64})
        d = lf.select(pl.col("x").cast(pl.Decimal(p, s))).collect(engine="streaming").item()
        lf2 = pl.LazyFrame({"x": [Decimal(x)]}, schema={"x": pl.Decimal(sp, ss)})
        r = lf2.select(pl.col("x").cast(pl.Decimal(p, s))).collect(engine="streaming").item()
        yield x, p, s, d, r


def spark_rows():
    from pyspark.sql import SparkSession

    spark = (
        SparkSession.builder.master("local[1]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )
    print("spark", spark.version)
    for x, p, s, (sp, ss) in CASES:
        d = spark.sql(f"SELECT CAST(CAST({x!r} AS DOUBLE) AS DECIMAL({p},{s})) AS v").first()[0]
        r = spark.sql(
            f"SELECT CAST(CAST('{Decimal(x)}' AS DECIMAL({sp},{ss})) AS DECIMAL({p},{s})) AS v"
        ).first()[0]
        yield x, p, s, d, r
    spark.stop()


def main() -> None:
    engines = sys.argv[1:] or ["duckdb", "polars", "spark"]
    for name in engines:
        rows = {"duckdb": duckdb_rows, "polars": polars_rows, "spark": spark_rows}[name]
        try:
            for x, p, s, d, r in rows():
                print(f"  {x!r:>22} -> DECIMAL({p},{s}): cast of double {d}, rescale {r}")
        except Exception as e:  # report and go on to the next engine
            print(f"  {name}: {type(e).__name__}: {str(e)[:160]}")


if __name__ == "__main__":
    main()
