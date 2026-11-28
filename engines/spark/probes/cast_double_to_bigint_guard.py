"""Spark 4.3.0 under ANSI: which error the `ftoi` template reports where its guard raises
and the native `CAST` would raise too (ruling 290, S3 and P6, #2630).

Run: python cast_double_to_bigint_guard.py

The template as the Spark dialect writes it, `CASE WHEN x IS NOT NULL AND NOT (x < 2^63)
THEN <sverify's raise> ELSE CAST(x AS BIGINT) END`, on a column and on a constant Spark
folds, at the next double above 2^63, 1e19, NaN, +inf and 2^63. Prints whose error the
query raises: the guard's (sverify's message, the reference's issue kind) or CAST's."""

import math

from pyspark.sql import SparkSession

FAIL = (
    "CAST((CASE WHEN x IS NULL THEN NULL ELSE raise_error(concat("
    "'sverify: CAST to BIGINT out of range: ', CAST(x AS STRING))) END) AS BIGINT)"
)
TEMPLATE = (
    "(CASE WHEN (x IS NOT NULL AND NOT (x < CAST('9.223372036854775808E18' AS DOUBLE))) "
    f"THEN {FAIL} ELSE CAST(x AS BIGINT) END)"
)
CASES = [
    ("next above 2^63", math.nextafter(2.0**63, math.inf)),
    ("1e19", 1e19),
    ("NaN", math.nan),
    ("+inf", math.inf),
    ("2^63", 2.0**63),
]


def main() -> None:
    spark = (
        SparkSession.builder.master("local[1]")
        .config("spark.sql.ansi.enabled", "true")
        .config("spark.ui.enabled", "false")
        .getOrCreate()
    )
    print("spark", spark.version)
    for name, v in CASES:
        for mode in ("column", "folded constant"):
            if mode == "column":
                spark.createDataFrame([(v,)], "x double").createOrReplaceTempView("t")
                q = f"SELECT {TEMPLATE} AS c FROM t"
            else:
                q = "SELECT " + TEMPLATE.replace("x", f"CAST('{v!r}' AS DOUBLE)") + " AS c"
            try:
                out = f"value {spark.sql(q).collect()[0][0]}"
            except Exception as e:  # noqa: BLE001 - the raise is the observation
                guard = "sverify: CAST to BIGINT" in str(e)
                out = "the guard's error" if guard else f"CAST's error: {type(e).__name__}"
            print(f"{name:16} {mode:16} {out}")
    spark.stop()


if __name__ == "__main__":
    main()
