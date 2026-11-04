"""Delta tables named with dots, and `uc://` tables through Unity Catalog (#451)."""

from __future__ import annotations

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from deltalake.exceptions import DeltaError
from ibis import _

import sverify as sv
from sverify.io import DeltaSink, DeltaSource
from sverify.io import delta as delta_io


@sv.transform(ensures=[_.amount > 10])
def big(orders):
    return orders.filter(orders.amount > 10)


def test_a_path_with_dots_refreshes(tmp_path):
    # The repro of #451: the default name kept the dots, and DuckDB read
    # `homelab.metrics.orders` as catalog.schema.table.
    path = str(tmp_path / "homelab.metrics.orders")
    write_deltalake(
        path,
        pa.table({"id": [1, 2], "amount": [30, 5]}),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    src = DeltaSource(path)
    assert src.name == "homelab_metrics_orders"
    big(src).write(DeltaSink(str(tmp_path / "big.v1"))).refresh()
    assert DeltaSource(str(tmp_path / "big.v1")).snapshot().table.to_pylist() == [
        {"id": 1, "amount": 30}
    ]


@pytest.mark.parametrize(
    ("uri", "name"),
    [
        ("uc://homelab.metrics.host_minute", "host_minute"),
        ("UC://homelab.metrics.host_minute", "host_minute"),
        ("s3://bucket/lake/a.b/", "a_b"),
        ("/lake/orders", "orders"),
    ],
)
def test_default_names_are_one_identifier(uri, name):
    assert DeltaSource(uri).name == name
    assert DeltaSink(uri).name == name
    assert DeltaSource(uri, name="mine").name == "mine"


class _Catalog:
    """A stand-in for delta-rs's `DeltaTable` over Unity Catalog: it has the
    tables in `tables`, answers others with the catalog's 404, and hangs (here:
    fails) in `is_deltatable`, as delta-rs 1.6.6 does for `uc://`. Other
    URIs go to delta-rs."""

    tables: dict[str, object] = {}
    error = "Generic error: Invalid table error: TABLE_NOT_FOUND: Table not found: {}"

    def __new__(cls, uri, storage_options=None, **kw):
        if not uri.startswith("uc://"):
            return DeltaTable(uri, storage_options=storage_options, **kw)
        table = uri.removeprefix("uc://")
        if table not in cls.tables:
            raise DeltaError(cls.error.format(table))
        return cls.tables[table]

    @staticmethod
    def is_deltatable(uri, storage_options=None):
        if not uri.startswith("uc://"):
            return DeltaTable.is_deltatable(uri, storage_options=storage_options)
        raise AssertionError("is_deltatable hangs on uc://")


@pytest.fixture
def catalog(monkeypatch):
    monkeypatch.setattr(delta_io, "DeltaTable", _Catalog)
    monkeypatch.setattr(_Catalog, "tables", {})
    monkeypatch.setattr(_Catalog, "error", _Catalog.error)
    return _Catalog


def test_a_uc_sink_opens_a_registered_table_without_is_deltatable(catalog):
    table = object()
    catalog.tables["homelab.metrics.busy"] = table
    assert DeltaSink("uc://homelab.metrics.busy")._table() is table


@pytest.mark.parametrize("missing", ["TABLE_NOT_FOUND", "SCHEMA_NOT_FOUND"])
def test_a_uc_sink_on_an_unregistered_table_says_to_register_it(catalog, missing):
    catalog.error = catalog.error.replace("TABLE_NOT_FOUND", missing)
    sink = DeltaSink("uc://homelab.metrics.busy")
    with pytest.raises(ValueError, match="register it in the catalog first"):
        sink._stored()


def test_a_uc_sink_on_an_unregistered_table_fails_the_refresh(catalog, tmp_path):
    path = str(tmp_path / "orders")
    write_deltalake(path, pa.table({"id": [1, 2], "amount": [30, 5]}))
    node = big(DeltaSource(path)).write(DeltaSink("uc://homelab.metrics.busy"))
    with pytest.raises(ValueError, match="register it in the catalog first"):
        node.refresh()


def test_other_catalog_errors_pass_through(catalog):
    catalog.error = "Failed to get a credential from UnityCatalog client configuration"
    with pytest.raises(DeltaError, match="credential"):
        DeltaSink("uc://homelab.metrics.busy")._table()
