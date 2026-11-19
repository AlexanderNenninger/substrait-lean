"""Spark's `sum` and `avg` of integer-valued doubles are exact (D35,
amended 2026-11-19), over several partitions (`_int_sums.py`)."""

import pytest

from _int_sums import cases, check

pytestmark = pytest.mark.backend("spark")

CASES = cases()


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


@pytest.mark.parametrize(("name", "values"), CASES, ids=[n for n, _ in CASES])
def test_sum_and_mean_are_exact(spark, name, values):
    from pyspark.sql import functions as F
    from pyspark.sql.types import DoubleType, StructField, StructType

    schema = StructType([StructField("x", DoubleType())])
    df = spark.createDataFrame([(float(v),) for v in values], schema).repartition(8)
    row = df.agg(F.sum("x").alias("s"), F.avg("x").alias("m")).collect()[0]
    check(values, row["s"], row["m"])
