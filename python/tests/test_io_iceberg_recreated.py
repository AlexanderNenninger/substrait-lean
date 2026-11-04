"""An Iceberg source dropped and created again under the same identifier
(#533, the Iceberg case of #516): its sequence numbers start over, and its
table UUID is new. A sink holds rows of the old table, so it must be
rewritten from the new one, whatever the epochs say."""

import warnings

import pyarrow as pa
import pytest
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.io import IcebergSink, IcebergSource

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])
ORDERS, SINK = "db.orders", "db.paid"
NO_TABLE_ID = pytest.mark.xfail(strict=True, reason="#533: IcebergSource has no table identity")


@sv.transform(requires={"orders": [_.amount >= 0]})
def paid(orders):
    return orders.filter(orders.amount > 0)


def create(catalog, ids: list[int]) -> None:
    catalog.create_table(ORDERS, schema=SCHEMA)
    append(catalog, ids)


def append(catalog, ids: list[int]) -> None:
    rows = pa.table({"id": ids, "amount": [5] * len(ids)}, schema=SCHEMA)
    catalog.load_table(ORDERS).append(rows)


def ids(catalog) -> list[int]:
    return sorted(r["id"] for r in catalog.load_table(SINK).scan().to_arrow().to_pylist())


def job(catalog):
    return paid(IcebergSource(catalog, ORDERS, name="orders")).write(IcebergSink(catalog, SINK))


@pytest.fixture
def lake(tmp_path):
    """orders at v4 (ids 1-5), and `paid` stored from it."""
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    create(cat, [1, 2])
    for i in (3, 4, 5):
        append(cat, [i])
    node = job(cat)
    node.refresh()
    assert ids(cat) == [1, 2, 3, 4, 5]
    return cat, node


def recreate(catalog, ids: list[int], more: int = 0) -> None:
    catalog.drop_table(ORDERS)
    create(catalog, ids)
    for i in range(more):
        append(catalog, [100 + i])


def test_recreated_at_lower_versions_same_process(lake):
    cat, node = lake
    recreate(cat, [10, 11])  # now at v1, below the sink's epoch 4
    report = node.refresh()
    assert report.writes[0].mode == "overwrite"
    assert ids(cat) == sorted(node.to_arrow().column("id").to_pylist()) == [10, 11]
    # The next refresh skips: the sink holds this state.
    assert node.refresh().writes[0].mode == "skipped"
    append(cat, [12])
    node.refresh()
    assert ids(cat) == [10, 11, 12]


def test_recreated_at_lower_versions_restarted_job(lake):
    cat, _node = lake
    recreate(cat, [10, 11])
    assert job(cat).refresh().writes[0].mode == "overwrite"
    assert ids(cat) == [10, 11]
    assert job(cat).refresh().writes[0].mode == "skipped"


@NO_TABLE_ID
def test_recreated_at_higher_versions_same_process(lake):
    cat, node = lake
    recreate(cat, [10, 11], more=4)  # now at v5: v4 is the new table's
    report = node.refresh()
    assert "created again" in str(report)
    assert (
        ids(cat) == sorted(node.to_arrow().column("id").to_pylist()) == [10, 11, 100, 101, 102, 103]
    )


@NO_TABLE_ID
def test_recreated_at_higher_versions_restarted_job(lake):
    cat, _node = lake
    recreate(cat, [10, 11], more=4)
    report = job(cat).refresh()
    assert "resumed" not in str(report)
    assert report.writes[0].mode == "overwrite"
    assert ids(cat) == [10, 11, 100, 101, 102, 103]


@NO_TABLE_ID
def test_the_contract_records_the_table_uuid(lake):
    cat, _node = lake
    contract = IcebergSource(cat, SINK).contract()
    assert contract is not None
    assert contract.table_ids == {"orders": str(cat.load_table(ORDERS).metadata.table_uuid)}
