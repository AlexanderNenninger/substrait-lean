"""Spark as an engine, through SQL generated from the plan (`pip install
'sverify[spark]'`, and a JVM: Java 17 or 21 on `PATH` or in `JAVA_HOME`).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

`run` writes the plan as Spark SQL with `sverify.sql.to_sql` (whose semantics
are Lean's `Rel.eval`, see `sverify.sql.spark`) and runs it on a Spark
session holding the given tables as temporary views. `session()` is a local
session with the settings of `SPARK_CONF`; on a cluster or Databricks, pass
your own session, configured the same way. Plans that need a table's row
order are refused (`Unsupported`) unless `tie_free=True`.
"""

from __future__ import annotations

import functools
import json
from collections.abc import Mapping
from typing import TYPE_CHECKING

import pyarrow as pa

from sverify.sql import to_sql
from sverify.sql.spark import SPARK, SPARK_CONF

try:
    import pyspark  # noqa: F401
except ImportError as e:
    raise ImportError("the Spark engine needs pyspark: pip install 'sverify[spark]'") from e

if TYPE_CHECKING:
    from pyspark.sql import SparkSession


@functools.cache
def session() -> SparkSession:
    """A local Spark session (one per process) with the settings of `SPARK_CONF`."""
    from pyspark.sql import SparkSession

    builder = SparkSession.builder.master("local[2]").appName("sverify")
    conf = SPARK_CONF | {
        "spark.ui.enabled": "false",
        "spark.sql.shuffle.partitions": "2",
        "spark.log.level": "OFF",
    }
    for k, v in conf.items():
        builder = builder.config(k, v)
    spark = builder.getOrCreate()
    spark.sparkContext.setLogLevel("OFF")
    return spark


def spark_type(t: pa.DataType) -> str:
    """The Spark type of an Arrow column, as `sverify.sql.spark` writes it."""
    if pa.types.is_integer(t):
        return SPARK.type_name("int")
    if pa.types.is_floating(t):
        return SPARK.type_name("float")
    if pa.types.is_timestamp(t):
        if t.tz is not None:
            raise TypeError(f"{t}: only timestamps without a time zone (TIMESTAMP_NTZ)")
        return SPARK.type_name("time")
    if pa.types.is_date(t):
        return SPARK.type_name("date")
    if pa.types.is_boolean(t):
        return SPARK.type_name("bool")
    if pa.types.is_string(t) or pa.types.is_large_string(t):
        return SPARK.type_name("str")
    if pa.types.is_list(t) or pa.types.is_large_list(t):
        return f"ARRAY<{spark_type(t.value_type)}>"
    raise TypeError(f"no Spark type for {t}")


def put_tables(tables: Mapping[str, pa.Table], spark: SparkSession | None = None) -> None:
    """Register each table as a temporary view of that name. Rows go in as
    Python values, so NULL and NaN stay apart."""
    spark = spark or session()
    for name, table in tables.items():
        schema = ", ".join(f"{SPARK.quote(f.name)} {spark_type(f.type)}" for f in table.schema)
        rows = [tuple(r.values()) for r in table.to_pylist()]
        spark.createDataFrame(rows, schema).createOrReplaceTempView(name)


def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table],
    spark: SparkSession | None = None,
    *,
    tie_free: bool = False,
) -> pa.Table:
    """Run a Substrait JSON plan on Spark over `tables` (temporary views).
    This is `sverify.engines.run_spark`.

    The plan is written as Spark SQL by `sverify.engines.to_sql` in the
    `sverify.engines.SPARK` dialect. `sverify.engines.run(con, plan,
    "spark")` runs a plan over a connection's tables the same way.

    Args:
        plan: A Substrait JSON plan, as a string or parsed.
        tables: The tables the plan reads, by name. Each is registered as a
            temporary view of that name, replacing any view of the same name.
        spark: The Spark session to run on, configured with
            `sverify.engines.SPARK_CONF`. Default: a local session with
            those settings.
        tie_free: Promise that no two rows tie on any window's
            `PARTITION BY` and `ORDER BY` columns (what a contract report's
            `deterministic` says), so windows run without a row-order
            tiebreak (see `sverify.engines.to_sql`). Default False.

    Returns:
        The plan's result, as an Arrow table.

    Raises:
        sverify.engines.Unsupported: Spark SQL cannot express the plan with
            Lean's meaning, for example a plan that needs a table's row order
            without `tie_free=True`.
        TypeError: A column has a type Spark cannot hold here, such as a
            timestamp with a time zone.
    """
    spark = spark or session()
    sql = to_sql(json.loads(plan) if isinstance(plan, str) else plan, SPARK, tie_free=tie_free)
    put_tables(tables, spark)
    return spark.sql(sql).toArrow()
