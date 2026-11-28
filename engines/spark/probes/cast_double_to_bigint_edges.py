"""Spark 4.3.0 under ANSI: `CAST(x AS BIGINT)` and `TRY_CAST(x AS BIGINT)` of doubles at
the edges of the 64-bit range (ruling 290, S1, #2630).

Run: python cast_double_to_bigint_edges.py

Each input as a DOUBLE column, both casts, against the reference's truncating cast:
the integer where it fits 64 bits, a raise (`CAST`) or NULL (`TRY_CAST`) elsewhere. Prints
each row and the mismatches."""

import math

from pyspark.sql import SparkSession

T63 = 2.0**63
CASES = [
    ("2^63", T63),
    ("next above 2^63", math.nextafter(T63, math.inf)),
    ("largest below 2^63", math.nextafter(T63, 0.0)),
    ("-2^63", -T63),
    ("next below -2^63", math.nextafter(-T63, -math.inf)),
    ("smallest above -2^63", math.nextafter(-T63, 0.0)),
    ("NaN", math.nan),
    ("+inf", math.inf),
    ("-inf", -math.inf),
    ("-0.0", -0.0),
    ("-1.5", -1.5),
    ("2.5", 2.5),
]


def ref(x: float) -> int | None:
    """`FloatCode.toInt?` then the 64-bit range: None where the reference raises."""
    if math.isnan(x) or math.isinf(x):
        return None
    i = math.trunc(x)
    return i if -(2**63) <= i < 2**63 else None


def main() -> None:
    spark = (
        SparkSession.builder.master("local[1]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )
    print("spark", spark.version)
    bad = []
    for name, x in CASES:
        df = spark.createDataFrame([(x,)], "x double")
        df.createOrReplaceTempView("t")
        try:
            c = spark.sql("SELECT CAST(x AS BIGINT) AS c FROM t").collect()[0][0]
        except Exception as e:  # noqa: BLE001 - the raise is the observation
            c = "raise:" + type(e).__name__
        tc = spark.sql("SELECT TRY_CAST(x AS BIGINT) AS c FROM t").collect()[0][0]
        want = ref(x)
        ok_c = (want is None and str(c).startswith("raise")) or c == want
        ok_t = tc == want
        print(f"{name:22} x={x!r:28} CAST={c!r:30} TRY_CAST={tc!r:22} reference={want!r}")
        if not (ok_c and ok_t):
            bad.append(name)
    print("differs from the reference:", bad)
    spark.stop()


if __name__ == "__main__":
    main()
