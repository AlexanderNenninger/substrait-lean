"""A refresh whose batch breaks an assumed precondition (#575: an overflow to
`±∞`): the node whose batch breaks it writes nothing. The stored node upstream
of it, whose committed table it reads, keeps the epoch it committed, so a
refresh of several nodes is atomic per node, not across them."""

import pytest
from deltalake import DeltaTable

import sverify as sv
from _pipelines import make_orders, paid
from sverify.io import DeltaSink


@sv.transform()
def scaled(paid):
    return paid.select(paid.id, v=paid.amount.cast("float64") * 1e306)


def test_a_node_whose_batch_overflows_writes_nothing(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 500)])
    up = paid(orders).write(DeltaSink(str(tmp_path / "up")))
    down = scaled(up).write(DeltaSink(str(tmp_path / "down")))
    report = scaled.report
    assert report is not None and [i.kind for i in report.assumed] == ["overflow to infinity"]
    with pytest.raises(Exception, match="overflow to infinity"):
        sv.group(up, down).refresh()
    assert DeltaTable(str(tmp_path / "up")).to_pyarrow_table().num_rows == 1
    with pytest.raises(Exception):  # noqa: B017 - nothing was written
        DeltaTable(str(tmp_path / "down"))
