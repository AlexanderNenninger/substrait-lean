"""Spark Connect reads a scan descriptor on the server (#173, native scans N5,
tier 1 of the design note's cluster tests).

A Connect server (`SparkSession.builder.remote("local[2]")` starts one from the
pyspark package) is a session whose client holds no table: the paths of the
descriptor resolve on the server, no `createDataFrame` of data runs, and only
the answer is collected. The client runs in a process of its own, since a process
holds either a classic session or a remote one. Skipped without the Connect
client's dependencies (`pip install 'pyspark[connect]'`)."""

import json
import subprocess
import sys

import pyarrow as pa
import pyarrow.parquet as pq
import pytest

pytestmark = pytest.mark.backend("spark")

CLIENT = """
import json, sys
import pyarrow as pa
from pyspark.sql import SparkSession
from sverify._scan import Scan
from sverify_spark import engine as E
from sverify_spark.dialect import SPARK_CONF

path = sys.argv[1]
builder = SparkSession.builder.remote("local[2]")
for k, v in SPARK_CONF.items():
    builder = builder.config(k, v)
spark = builder.getOrCreate()

def no_client_data(*args, **kwargs):
    raise AssertionError("the table was sent from the client")

spark.createDataFrame = no_client_data
deleted = pa.table({"file": [path], "pos": pa.array([1], pa.int64())})
scan = Scan((path,), pa.schema([("id", pa.int64()), ("k", pa.string())]), deleted)
E.put_tables({"t": scan}, spark)
print(json.dumps(spark.sql("SELECT id, k FROM t ORDER BY id").toArrow().to_pylist()))
spark.stop()
"""


def test_a_connect_session_reads_the_files_on_the_server(tmp_path):
    pytest.importorskip("grpc")
    pytest.importorskip("pyspark")
    from spark_session import has_java

    if not has_java():
        pytest.skip("Spark needs a JVM")
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array([1, 2, 3], pa.int32()), "k": ["a", None, "c"]}), f)
    out = subprocess.run(
        [sys.executable, "-c", CLIENT, str(f)], capture_output=True, text=True, timeout=300
    )
    assert out.returncode == 0, out.stderr[-2000:]
    assert json.loads(out.stdout.strip().splitlines()[-1]) == [
        {"id": 1, "k": "a"},
        {"id": 3, "k": "c"},
    ]
