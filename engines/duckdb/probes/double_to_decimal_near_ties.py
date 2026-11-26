"""How DuckDB, Polars and Spark cast a double to a decimal near a tie (ruling 278).

Run: python double_to_decimal_near_ties.py [duckdb|polars|spark ...]

The double is no tie, but `x * 10^s` rounds onto one or near one as a double:
rounding the double product gives one value, rounding the double's shortest
decimal text another (`1.005` is 1.00499999999999989... in binary, its product
100.49999999999999, its text "1.005").
"""

import sys
from decimal import Decimal

#: (double, target precision, target scale)
CASES = [
    (-2.675, 4, 2),
    (2.675, 4, 2),
    (1.005, 3, 2),
    (0.285, 3, 2),
    (8.345, 4, 2),
]


def duckdb_rows():
    import duckdb

    con = duckdb.connect()
    print("duckdb", duckdb.__version__)
    for x, p, s in CASES:
        yield x, p, s, con.execute(f"SELECT CAST({x!r}::DOUBLE AS DECIMAL({p},{s}))").fetchone()[0]


def polars_rows():
    import polars as pl

    print("polars", pl.__version__)
    for x, p, s in CASES:
        lf = pl.LazyFrame({"x": [x]}, schema={"x": pl.Float64})
        yield (
            x,
            p,
            s,
            lf.select(pl.col("x").cast(pl.Decimal(p, s))).collect(engine="streaming").item(),
        )


def spark_rows():
    from pyspark.sql import SparkSession

    spark = (
        SparkSession.builder.master("local[1]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )
    print("spark", spark.version)
    for x, p, s in CASES:
        yield (
            x,
            p,
            s,
            spark.sql(f"SELECT CAST(CAST({x!r} AS DOUBLE) AS DECIMAL({p},{s}))").first()[0],
        )
    spark.stop()


def main() -> None:
    engines = sys.argv[1:] or ["duckdb", "polars", "spark"]
    for name in engines:
        rows = {"duckdb": duckdb_rows, "polars": polars_rows, "spark": spark_rows}[name]
        try:
            for x, p, s, d in rows():
                print(f"  {x!r:>20} ({Decimal(x)}, product {x * 10**s!r}) -> DECIMAL({p},{s}): {d}")
        except Exception as e:  # report and go on to the next engine
            print(f"  {name}: {type(e).__name__}: {str(e)[:160]}")


if __name__ == "__main__":
    main()
