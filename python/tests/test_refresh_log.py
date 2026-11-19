"""A refresh logs one INFO line per node and per commit on the `sverify` logger,
with the summary's words (#1485 item 25)."""

import logging

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.io import DeltaSink, DeltaSource

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])


@sv.transform(requires={"orders": [_.amount >= 0]})
def paid(orders):
    return orders.filter(orders.amount > 0)


@pytest.fixture
def job(tmp_path):
    src = str(tmp_path / "orders")
    DeltaTable.create(src, SCHEMA, configuration={"delta.enableChangeDataFeed": "true"})
    write_deltalake(src, pa.table({"id": [1, 2], "amount": [5, 5]}), mode="append")
    return paid(DeltaSource(src)).write(DeltaSink(str(tmp_path / "paid")))


def test_a_refresh_logs_each_node_and_commit(job, caplog):
    with caplog.at_level(logging.INFO, logger="sverify"):
        refresh = job.refresh()
    lines = [r.getMessage() for r in caplog.records if r.name == "sverify"]
    assert len(lines) == 2, lines
    assert lines[0].startswith("paid: committed "), lines
    assert lines[1] == refresh.summary(), (lines, refresh.summary())
    assert str(refresh.writes[0].version) in lines[0]


def test_a_refresh_that_finds_the_state_committed_logs_it(job, caplog):
    job.refresh()
    caplog.clear()
    with caplog.at_level(logging.INFO, logger="sverify"):
        job.refresh()
    lines = [r.getMessage() for r in caplog.records if r.name == "sverify"]
    assert lines and lines[-1].startswith("paid: "), lines
