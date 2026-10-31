"""The Spark session of the tests (`sverify.spark_engine.session`).

Spark needs a JVM (Java 17 or 21): `JAVA_HOME`, or a working `java` on
`PATH`. Without one the Spark tests are skipped.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from collections.abc import Mapping
from typing import Any

import pyarrow as pa
import pytest


def has_java() -> bool:
    if os.environ.get("JAVA_HOME"):
        return True
    # macOS has a `java` stub on PATH that only says Java is missing.
    java = shutil.which("java")
    return (
        java is not None and subprocess.run([java, "-version"], capture_output=True).returncode == 0
    )


def session() -> Any:
    """One JVM for every Spark test in this process."""
    pytest.importorskip("pyspark")
    if not has_java():
        pytest.skip("Spark needs a JVM: set JAVA_HOME or put java on PATH")
    from sverify import spark_engine

    return spark_engine.session()


def put_tables(tables: Mapping[str, pa.Table]) -> None:
    from sverify import spark_engine

    spark_engine.put_tables(tables, session())


def query(sql: str) -> list[tuple]:
    return [tuple(r) for r in session().sql(sql).collect()]
