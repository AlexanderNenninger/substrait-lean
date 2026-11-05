"""Spark as an engine, through SQL generated from the plan (`pip install
'sverify[spark]'`, and a JVM: Java 17 or 21 on `PATH` or in `JAVA_HOME`).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

`run` writes the plan as Spark SQL with `sverify.sql.to_sql` (whose semantics
are Lean's `Rel.eval`, see `sverify.sql.spark`) and runs it on a Spark
session holding the given tables as temporary views. `session()` is a local
session with the settings of `SPARK_CONF`; on a cluster or Databricks, pass
your own session, configured the same way. Plans that need a table's row
order are refused (`Unsupported`) unless `deterministic=True`.
"""

from __future__ import annotations

import functools
import os
import re
import sys
import weakref
from collections.abc import Mapping
from typing import TYPE_CHECKING, Any

import pyarrow as pa

from sverify.sql import to_sql
from sverify.sql.spark import SPARK, SPARK_CONF

try:
    import pyspark  # noqa: F401
except ImportError as e:
    raise ImportError("the Spark engine needs pyspark: pip install 'sverify[spark]'") from e

if TYPE_CHECKING:
    from pyspark.sql import SparkSession


#: Settings of the local session beyond `SPARK_CONF`. The parser's ANTLR DFA
#: cache is static and unbounded unless Spark manages it: the nested SQL that
#: `to_sql` writes for date arithmetic (one 51 kB query of
#: `tests/test_backends.py`) left about 740 MB of a 1 GB driver heap in it,
#: and later queries failed with `AGGREGATE_OUT_OF_MEMORY` or could not
#: broadcast. Flushing it at 10 % of the heap keeps it near 100 MB.
LOCAL_CONF: dict[str, str] = {
    "spark.ui.enabled": "false",
    "spark.sql.shuffle.partitions": "2",
    "spark.log.level": "OFF",
    "spark.sql.parser.manageParserCaches": "true",
    "spark.sql.parser.parserDfaCacheFlushRatio": "10",
}


def driver_memory(limit: str) -> str:
    """`SVERIFY_MEMORY_LIMIT` (#783) as Spark's `spark.driver.memory`:
    `"2GB"` is `"2g"`, `"512MB"` is `"512m"`."""
    m = re.fullmatch(r"\s*(\d+)\s*([KMGT])i?B?\s*", limit, re.IGNORECASE)
    if m is None:
        raise ValueError(f"memory limit {limit!r}: write a size such as 2GB or 512MB")
    return f"{m[1]}{m[2].lower()}"


@functools.cache
def session() -> SparkSession:
    """A local Spark session (one per process) with the settings of
    `SPARK_CONF` and `LOCAL_CONF`. `SVERIFY_MEMORY_LIMIT` sets the driver's
    memory (Spark's default is 1 GB) when the session's JVM starts. Python
    workers run this process's interpreter unless `PYSPARK_PYTHON` names
    another."""
    from pyspark.sql import SparkSession

    builder = SparkSession.builder.master("local[2]").appName("sverify")
    conf = SPARK_CONF | LOCAL_CONF
    if limit := os.environ.get("SVERIFY_MEMORY_LIMIT", "").strip():
        conf["spark.driver.memory"] = driver_memory(limit)
    for k, v in conf.items():
        builder = builder.config(k, v)
    spark = builder.getOrCreate()
    spark.sparkContext.setLogLevel("OFF")
    if not os.environ.get("PYSPARK_PYTHON"):
        # Python workers run this interpreter, not whichever `python3` is
        # first on `PATH` (a virtual environment need not be on it).
        spark.sparkContext.pythonExec = sys.executable
    return spark


def spark_type(t: pa.DataType) -> str:
    """The Spark type of an Arrow column, as `sverify.sql.spark` writes it."""
    if pa.types.is_integer(t):
        return SPARK.type_name("int")
    if pa.types.is_decimal(t):
        return f"DECIMAL({t.precision}, {t.scale})"
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


def arrow_type(t: pa.DataType) -> pa.DataType:
    """The Arrow type Spark reads as `spark_type(t)`: 64-bit integers and
    doubles, microsecond timestamps, plain strings and lists."""
    if pa.types.is_integer(t):
        return pa.int64()
    if pa.types.is_floating(t):
        return pa.float64()
    if pa.types.is_timestamp(t):
        return pa.timestamp("us")
    if pa.types.is_string(t) or pa.types.is_large_string(t):
        return pa.string()
    if pa.types.is_list(t) or pa.types.is_large_list(t):
        return pa.list_(arrow_type(t.value_type))
    return t


#: The views sverify registered under its own names (`__sverify_<i>`, which
#: `sverify.engine.run_plan` gives a plan's tables), per session: the Arrow
#: table each holds. A run over the same table does not send it again.
_VIEWS: weakref.WeakKeyDictionary[Any, dict[str, pa.Table]] = weakref.WeakKeyDictionary()


def put_tables(tables: Mapping[str, pa.Table], spark: SparkSession | None = None) -> None:
    """Register each table as a temporary view of that name. The columns go
    to Spark as Arrow, cast to the types `spark_type` names, so NULL and NaN
    stay apart, and no Python worker runs (a table of 100,000 rows takes a
    quarter of the time it took as Python values). A view of sverify's own
    names that holds the same Arrow table already is kept as it is."""
    spark = spark or session()
    held = _VIEWS.setdefault(spark, {})
    for name, table in tables.items():
        own = name.startswith("__sverify_")
        if own and held.get(name) is table:
            continue
        schema = ", ".join(f"{SPARK.quote(f.name)} {spark_type(f.type)}" for f in table.schema)
        target = pa.schema([pa.field(f.name, arrow_type(f.type)) for f in table.schema])
        spark.createDataFrame(table.cast(target), schema).createOrReplaceTempView(name)
        if own:
            held[name] = table


def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table],
    spark: SparkSession | None = None,
    *,
    deterministic: bool = False,
    tie_free: bool | None = None,
) -> pa.Table:
    """Run a Substrait JSON plan on Spark over `tables` (temporary views).
    `sverify.engines.run_spark`, deprecated, calls it.

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
        deterministic: Promise that no two rows tie on any window's
            `PARTITION BY` and `ORDER BY` columns (what a contract report's
            `deterministic` says), so windows run without a row-order
            tiebreak (see `sverify.engines.to_sql`). Default False.
        tie_free: Deprecated alias of `deterministic`.

    Returns:
        The plan's result, as an Arrow table.

    Raises:
        sverify.engines.Unsupported: Spark SQL cannot express the plan with
            Lean's meaning, for example a plan that needs a table's row order
            without `deterministic=True`.
        TypeError: A column has a type Spark cannot hold here, such as a
            timestamp with a time zone.
    """
    if tie_free is not None:
        import warnings

        warnings.warn(
            "run_spark(tie_free=...) is deprecated; write deterministic=...",
            DeprecationWarning,
            stacklevel=2,
        )
        deterministic = tie_free
    spark = spark or session()
    sql = to_sql(plan, SPARK, deterministic=deterministic)
    put_tables(tables, spark)
    return spark.sql(sql).toArrow()
