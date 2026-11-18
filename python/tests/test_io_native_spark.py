"""Spark reads a scan descriptor itself (#173, native scans N5).

Property 5.1 of the design note: the engine's scan of a descriptor equals the
engine's ingestion of the descriptor's `to_arrow()`, as a multiset, over
generated table histories, and for position deletes, equality deletes and
renamed Iceberg columns. Files whose column types do not widen must raise."""

import warnings
from collections import Counter

import pyarrow as pa
import pyarrow.parquet as pq
import pytest
from deltalake import DeltaTable
from hypothesis import HealthCheck, given, settings
from pyiceberg.catalog.sql import SqlCatalog

from _table_histories import build_delta, build_iceberg, histories
from spark_session import session
from sverify._scan import Scan
from sverify._unsupported import Unsupported
from sverify_spark import engine as E
from sverify_spark.scan import spark_scan
from test_io_iceberg_equality import delete_where_equal, rows
from test_io_native import FIXTURE_DV

pytestmark = pytest.mark.backend("spark")


def bag(t: pa.Table) -> Counter:
    return Counter(
        tuple("nan" if isinstance(v, float) and v != v else v for v in r.values())
        for r in t.to_pylist()
    )


def agree(scan: Scan) -> None:
    """Spark's read of `scan` and its ingestion of `scan.to_arrow()` give the same rows."""
    spark = session()
    E.put_tables({"t": scan, "u": scan.to_arrow()}, spark)
    got, want = spark.sql("SELECT * FROM t").toArrow(), spark.sql("SELECT * FROM u").toArrow()
    assert got.schema.equals(want.schema)
    assert bag(got) == bag(want)


@settings(
    max_examples=20, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(history=histories())
def test_a_delta_scan_over_histories(history, tmp_path_factory):
    path = tmp_path_factory.mktemp("d") / "t"
    src = build_delta(path, history)
    for v in [*range(DeltaTable(str(path)).version() + 1), None]:
        snap = src._native(v)
        if snap is not None:
            agree(snap.scan)


@settings(
    max_examples=15, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(history=histories(renames=True))
def test_an_iceberg_scan_over_histories(history, tmp_path_factory):
    warnings.filterwarnings("ignore", module="pyiceberg")
    root = tmp_path_factory.mktemp("i")
    cat = SqlCatalog("test", uri=f"sqlite:///{root}/catalog.db", warehouse=f"file://{root}")
    cat.create_namespace("db")
    snap = build_iceberg(cat, "db.t", history)._native()
    if snap is not None:
        agree(snap.scan)


def test_delta_deletion_vectors(tmp_path):
    from sverify.io import DeltaSource

    snap = DeltaSource(str(FIXTURE_DV))._native()
    assert snap is not None and snap.scan.deleted is not None
    agree(snap.scan)


def test_equality_deletes_and_a_rename(tmp_path):
    from sverify.io import IcebergSource

    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/c.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    t = cat.create_table("db.t", schema=rows([1]).schema)
    t.append(rows([1, 2, 3, 4], [None, "a", None, "b"]))
    with t.update_schema() as update:
        update.rename_column("k", "key")
    t = cat.load_table("db.t")
    delete_where_equal(t, ["id", "key"], rows([1, 2], [None, "b"]).rename_columns(["id", "key"]))
    snap = IcebergSource(cat, "db.t")._native()
    assert snap is not None and snap.scan.equality
    agree(snap.scan)
    got = spark_scan(session(), snap.scan).toArrow()
    assert sorted(got["id"].to_list()) == [2, 3, 4]


def test_a_type_that_does_not_widen_raises(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array(["x"], pa.string())}), f)
    with pytest.raises(Unsupported, match="column 'id'"):
        spark_scan(session(), Scan((str(f),), pa.schema([("id", pa.int64())])))


def test_a_narrower_integer_widens(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array([1, 2], pa.int32())}), f)
    df = spark_scan(session(), Scan((str(f),), pa.schema([("id", pa.int64())])))
    assert sorted(df.toArrow().column("id").to_pylist()) == [1, 2]


def test_a_string_column_is_not_read_as_a_date(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"d": pa.array(["2024-01-01"], pa.string())}), f)
    for want in (pa.date32(), pa.timestamp("us"), pa.bool_()):
        with pytest.raises(Unsupported, match="column 'd'"):
            spark_scan(session(), Scan((str(f),), pa.schema([("d", want)])))


def test_doubles_are_as_the_model_has_them(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"x": pa.array([-0.0, float("nan"), None, 1.5])}), f)
    got = spark_scan(session(), Scan((str(f),), pa.schema([("x", pa.float64())]))).toArrow()
    assert sorted(str(v) for v in got.column("x").to_pylist() if v == v and v is not None) == [
        "0.0",
        "1.5",
    ]
    assert str(got.column("x").to_pylist()[0]) in ("0.0", "nan")


def test_a_where_is_duckdb_sql_and_stays_on_the_arrow_route(tmp_path):
    from sverify_spark import _table

    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": [1, 2, 3], "d": [None, 5, 7]}), f)
    scan = Scan((str(f),), pa.schema([("id", pa.int64()), ("d", pa.int64())]), where="d > 4")
    with pytest.raises(Unsupported, match="DuckDB SQL"):
        spark_scan(session(), scan)

    class Con:
        def get(self, name):
            return scan

        _arrow = {"t": scan.to_arrow()}

    got = _table(Con(), "t")
    assert isinstance(got, pa.Table) and got.column("id").to_pylist() == [2, 3]


def test_equality_deletes_find_a_file_whose_path_the_session_encodes(tmp_path):
    """The session reports a path percent-encoded (`a%20b`), and as `file:///`; the
    descriptor holds the plain local path. Nothing matches paths as text."""
    from sverify._scan import EqualityDelete

    d = tmp_path / "dir with space%25"
    d.mkdir()
    data, dele = d / "data file.parquet", d / "del.parquet"
    schema = pa.schema([pa.field("id", pa.int64(), metadata={"PARQUET:field_id": "1"})])
    pq.write_table(pa.table({"id": [1, 2, 3]}, schema=schema), data)
    pq.write_table(pa.table({"id": [2]}, schema=schema), dele)
    scan = Scan(
        (str(data),),
        pa.schema([("id", pa.int64())]),
        equality=(EqualityDelete(str(dele), (1,), ("id",), (str(data),)),),
    )
    got = spark_scan(session(), scan).toArrow()
    assert sorted(got.column("id").to_pylist()) == [1, 3]
