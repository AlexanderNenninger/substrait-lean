"""A Delta source dropped and created again at the same path (#516): its
versions start over, and its table id is new. A sink holds rows of the old
table, so it must be rewritten from the new one, whatever the epochs say."""

import shutil

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.io import DeltaSink, DeltaSource
from sverify.io._common import Contract, other_tables

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])


@sv.transform(requires={"orders": [_.amount >= 0]})
def paid(orders):
    return orders.filter(orders.amount > 0)


def create(src: str, ids: list[int]) -> None:
    DeltaTable.create(src, SCHEMA, configuration={"delta.enableChangeDataFeed": "true"})
    append(src, ids)


def append(src: str, ids: list[int]) -> None:
    write_deltalake(src, pa.table({"id": ids, "amount": [5] * len(ids)}), mode="append")


def ids(uri: str) -> list[int]:
    return sorted(r["id"] for r in DeltaTable(uri).to_pyarrow_table().to_pylist())


@pytest.fixture
def lake(tmp_path):
    """orders at v4 (ids 1-5), and `paid` stored from it."""
    src, sink = str(tmp_path / "orders"), str(tmp_path / "paid")
    create(src, [1, 2])
    for i in (3, 4, 5):
        append(src, [i])
    node = paid(DeltaSource(src)).write(DeltaSink(sink))
    node.refresh()
    assert ids(sink) == [1, 2, 3, 4, 5]
    return src, sink, node


def recreate(src: str, ids: list[int], more: int = 0) -> None:
    shutil.rmtree(src)
    create(src, ids)
    for i in range(more):
        append(src, [100 + i])


def test_recreated_at_lower_versions_same_process(lake):
    src, sink, node = lake
    recreate(src, [10, 11])  # now at v1, below the sink's epoch 4
    report = node.refresh()
    assert "created again" in str(report)
    assert report.writes[0].mode == "overwrite"
    assert ids(sink) == sorted(node.to_arrow().column("id").to_pylist()) == [10, 11]
    # The next refresh skips: the sink holds this state.
    assert node.refresh().writes[0].mode == "skipped"
    append(src, [12])
    node.refresh()
    assert ids(sink) == [10, 11, 12]


def test_recreated_at_lower_versions_restarted_job(lake):
    src, sink, _node = lake
    recreate(src, [10, 11])
    again = paid(DeltaSource(src)).write(DeltaSink(sink))
    assert again.refresh().writes[0].mode == "overwrite"
    assert ids(sink) == [10, 11]
    assert paid(DeltaSource(src)).write(DeltaSink(sink)).refresh().writes[0].mode == "skipped"


def test_recreated_at_higher_versions_same_process(lake):
    src, sink, node = lake
    recreate(src, [10, 11], more=4)  # now at v5: the CDF from v4 is the new table's
    report = node.refresh()
    assert "created again" in str(report)
    assert (
        ids(sink)
        == sorted(node.to_arrow().column("id").to_pylist())
        == [10, 11, 100, 101, 102, 103]
    )


def test_recreated_at_higher_versions_restarted_job(lake):
    src, sink, _node = lake
    recreate(src, [10, 11], more=4)
    again = paid(DeltaSource(src)).write(DeltaSink(sink))
    report = again.refresh()
    assert "resumed" not in str(report)
    assert report.writes[0].mode == "overwrite"
    assert ids(sink) == [10, 11, 100, 101, 102, 103]


def test_the_contract_records_the_table_id(lake):
    src, sink, _node = lake
    contract = DeltaSource(sink).contract()
    assert contract is not None
    assert contract.table_ids == {"orders": DeltaTable(src).metadata().id}


def test_other_tables():
    def contract(sources, table_ids):
        return Contract("v", "p", sources, sum(sources.values()), [], {}, [], table_ids=table_ids)

    done = contract({"a": 4, "b": 2}, {"a": "x"})
    assert other_tables(done, contract({"a": 5, "b": 2}, {"a": "x"})) == []
    assert other_tables(done, contract({"a": 5, "b": 2}, {"a": "y"})) == ["a"]
    assert other_tables(done, contract({"a": 4, "b": 1}, {"a": "x"})) == ["b"]
    # A contract written before table ids were recorded: only the versions.
    assert other_tables(contract({"a": 4}, {}), contract({"a": 5}, {"a": "y"})) == []
