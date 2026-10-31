"""One local Spark session for the tests, configured by `SPARK_CONF`.

Spark needs a JVM. Without `JAVA_HOME` or a working `java` on `PATH`, the JRE of the
`jdk4py` wheel is used. That runtime lacks the incubating vector module that
Spark's launcher always asks for (`--add-modules=jdk.incubator.vector`), and
plain SQL does not use it, so the launcher calls `java` through a shim that
drops that one flag.
"""

from __future__ import annotations

import functools
import os
import shutil
import subprocess
import tempfile
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import pyarrow as pa
import pytest

from sverify.sql.spark import SPARK, SPARK_CONF

SHIM = """#!/bin/sh
for a; do shift; [ "$a" = --add-modules=jdk.incubator.vector ] || set -- "$@" "$a"; done
exec "{java}" "$@"
"""


def java_home() -> str | None:
    """A JAVA_HOME for Spark, or None when the environment already has one."""
    if os.environ.get("JAVA_HOME"):
        return None
    # macOS has a `java` stub on PATH that only says Java is missing.
    java = shutil.which("java")
    if java and subprocess.run([java, "-version"], capture_output=True).returncode == 0:
        return None
    jdk4py = pytest.importorskip("jdk4py", reason="Spark needs a JVM")
    home = Path(tempfile.mkdtemp(prefix="sverify-java-"))
    (home / "bin").mkdir()
    shim = home / "bin" / "java"
    shim.write_text(SHIM.format(java=Path(jdk4py.JAVA_HOME) / "bin" / "java"))
    shim.chmod(0o755)
    return str(home)


@functools.cache
def session() -> Any:
    """The shared session: one JVM for every Spark test in this process."""
    pytest.importorskip("pyspark")
    from pyspark.sql import SparkSession

    if home := java_home():
        os.environ["JAVA_HOME"] = home
    builder = SparkSession.builder.master("local[2]").appName("sverify-tests")
    conf = SPARK_CONF | {
        "spark.ui.enabled": "false",
        "spark.sql.shuffle.partitions": "2",
        "spark.driver.memory": "1g",
        "spark.log.level": "OFF",
    }
    for k, v in conf.items():
        builder = builder.config(k, v)
    spark = builder.getOrCreate()
    spark.sparkContext.setLogLevel("OFF")
    return spark


def spark_type(t: pa.DataType) -> str:
    if pa.types.is_integer(t):
        return SPARK.type_name("int")
    if pa.types.is_floating(t):
        return SPARK.type_name("float")
    if pa.types.is_timestamp(t):
        return SPARK.type_name("time")
    if pa.types.is_date(t):
        return SPARK.type_name("date")
    if pa.types.is_boolean(t):
        return SPARK.type_name("bool")
    if pa.types.is_string(t) or pa.types.is_large_string(t):
        return SPARK.type_name("str")
    raise TypeError(f"no Spark type for {t}")


def put_tables(tables: Mapping[str, pa.Table]) -> None:
    """Register each table as a temporary view of that name. Rows go in as
    Python values, so NULL, NaN and -0.0 stay apart."""
    spark = session()
    for name, table in tables.items():
        schema = ", ".join(f"{SPARK.quote(f.name)} {spark_type(f.type)}" for f in table.schema)
        rows = [tuple(r.values()) for r in table.to_pylist()]
        spark.createDataFrame(rows, schema).createOrReplaceTempView(name)


def query(sql: str) -> list[tuple]:
    return [tuple(r) for r in session().sql(sql).collect()]
