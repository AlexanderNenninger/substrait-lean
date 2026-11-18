"""Polars reads a scan descriptor itself (#173, native scans N4).

Property 5.1 of the design note: the engine's scan of a descriptor equals the
engine's ingestion of the descriptor's `to_arrow()`, as a multiset, over
generated table histories, and for position deletes, equality deletes and
renamed Iceberg columns. Files whose column types do not widen must raise."""

import warnings
from collections import Counter

import ibis
import polars as pl
import pyarrow as pa
import pyarrow.parquet as pq
import pytest
from deltalake import DeltaTable
from hypothesis import HealthCheck, given, settings
from pyiceberg.catalog.sql import SqlCatalog

from _table_histories import build_delta, build_iceberg, histories
from sverify._scan import Scan
from sverify._unsupported import Unsupported
from sverify.ibis_substrait import to_substrait_json
from sverify_polars import engine as E
from sverify_polars.scan import lazy_scan
from test_io_iceberg_equality import delete_where_equal, rows
from test_io_native import FIXTURE_DV

pytestmark = pytest.mark.backend("polars")


def plan_of(schema: pa.Schema) -> str:
    t = ibis.table(ibis.Schema.from_pyarrow(schema), name="t")
    return to_substrait_json(t.select(*t.columns))


def bag(t: pa.Table) -> Counter:
    return Counter(
        tuple("nan" if isinstance(v, float) and v != v else v for v in r.values())
        for r in t.to_pylist()
    )


def agree(scan: Scan) -> None:
    """Polars's scan of `scan` and its ingestion of `scan.to_arrow()` give the same rows."""
    plan = plan_of(scan.schema)
    got = E.run(plan, {"t": lazy_scan(scan)})
    want = E.run(plan, {"t": scan.to_arrow()})
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
    got = lazy_scan(snap.scan).collect()
    assert sorted(got["id"].to_list()) == [2, 3, 4]


def test_a_type_that_does_not_widen_raises(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array(["x"], pa.string())}), f)
    scan = Scan((str(f),), pa.schema([("id", pa.int64())]))
    with pytest.raises(Unsupported, match="column 'id'"):
        lazy_scan(scan)


def test_a_narrower_integer_widens(tmp_path):
    f = tmp_path / "a.parquet"
    pq.write_table(pa.table({"id": pa.array([1, 2], pa.int32())}), f)
    assert lazy_scan(Scan((str(f),), pa.schema([("id", pa.int64())]))).collect()[
        "id"
    ].to_list() == [
        1,
        2,
    ]
    assert isinstance(pl.scan_parquet(f), pl.LazyFrame)
