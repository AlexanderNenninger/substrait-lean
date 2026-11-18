"""Spark Connect reads a scan descriptor on the server (#173, native scans N5,
tier 1 of the design note's cluster tests).

A Connect server (`SparkSession.builder.remote("local[2]")` starts one from the
pyspark package) is a session whose client holds no table: the paths of the
descriptor resolve on the server, no `createDataFrame` of data runs, and only
the answer is collected. Skipped without the Connect client's dependencies
(`pip install 'pyspark[connect]'`)."""

import pyarrow as pa
import pyarrow.parquet as pq
import pytest

from sverify._scan import Scan
from sverify_spark import engine as E

pytestmark = pytest.mark.backend("spark")


@pytest.fixture(scope="module")
def connect():
    pytest.importorskip("grpc")
    pytest.importorskip("pyspark")
    from pyspark.sql import SparkSession

    from spark_session import has_java

    if not has_java():
        pytest.skip("Spark needs a JVM")
    from sverify_spark.dialect import SPARK_CONF

    builder = SparkSession.builder.remote("local[2]")
    for k, v in SPARK_CONF.items():
        builder = builder.config(k, v)
    spark = builder.getOrCreate()
    yield spark
    spark.stop()


def test_a_connect_session_reads_the_files_on_the_server(connect, tmp_path, monkeypatch):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array([1, 2, 3], pa.int32()), "k": ["a", None, "c"]}), f)
    deleted = pa.table({"file": [str(f)], "pos": pa.array([1], pa.int64())})
    scan = Scan((str(f),), pa.schema([("id", pa.int64()), ("k", pa.string())]), deleted)

    def no_client_data(*args, **kwargs):
        raise AssertionError("the table was sent from the client")

    monkeypatch.setattr(connect, "createDataFrame", no_client_data)
    E.put_tables({"t": scan}, connect)
    got = connect.sql("SELECT id, k FROM t ORDER BY id").toArrow()
    assert got.to_pylist() == [{"id": 1, "k": "a"}, {"id": 3, "k": "c"}]
