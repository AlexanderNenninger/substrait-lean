"""`Sink._commit`'s decision, case by case, against `Refresh.next` in
`SubstraitLean/Refresh.lean` (#933).

`Refresh.no_corruption` and `Refresh.record_describes_table` are proved of a
transition system whose writers decide with `Refresh.next`; they say something
about sverify only while `Sink._commit` decides the same way. Each row below is
one of `next`'s cases: the sink's record (none, another plan's, this writer's
own, another state of the same plan, ahead of it), whether another
application's commit followed it (`kept`), and the writer's pending write.
The test sets the record and the flag on a sink and checks what `_commit`
does: skip, replace the rows, or write the change (merge). A change to
`next` or to `_commit` that makes them differ fails here.
"""

from dataclasses import replace

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake

import sverify as sv
from sverify.io import DeltaSource, Sink

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])
CDF = {"delta.enableChangeDataFeed": "true"}


@sv.transform()
def paid(orders):
    return orders.filter(orders.amount > 0)


class Scripted(Sink):
    """A sink whose record (`contract()`) and foreign-rows flag (`_foreign`)
    the test sets, and which notes how each write was made."""

    def __init__(self):
        super().__init__("out")
        self.record = None
        self.foreign = False
        self.modes: list[str] = []
        self.raise_once = False

    def contract(self, version=None):
        return self.record

    def _foreign(self):
        return self.foreign

    def write(self, change):
        self.modes.append("replace" if change.replace else "merge")
        if self.raise_once:
            # The commit landed, and the acknowledgement was lost.
            self.raise_once = False
            self.record = change.contract
            raise OSError("connection reset after the commit")
        return None


def append(uri: str, ids: list[int]) -> None:
    write_deltalake(
        uri, pa.table({"id": ids, "amount": [5] * len(ids)}, schema=SCHEMA), mode="append"
    )


def setup(tmp_path):
    """A node over orders@v1, written once (its own record `c1`), then
    orders@v2: the writer's next state is v2."""
    src = str(tmp_path / "orders")
    DeltaTable.create(src, SCHEMA, configuration=CDF)
    append(src, [1, 2])
    sink = Scripted()
    node = paid(DeltaSource(src)).write(sink)
    node.refresh()
    c1 = sink._last
    assert c1 is not None and c1.sources == {"orders": 1}
    append(src, [3])
    return src, node, sink, c1


def decide(node, sink) -> str:
    w = node.refresh().writes[0]
    return "skip" if w.mode == "skipped" else sink.modes[-1]


def at(c, v: int):
    """The record `c` at version `v` of orders."""
    return replace(c, sources={"orders": v}, epoch=v)


# (case, the record, kept, what `Refresh.next` decides)
CASES = [
    ("another plan's record", lambda c1: replace(c1, plan="0" * 64), True, "replace"),
    ("rows another application changed", lambda c1: c1, False, "replace"),
    ("the record is this state", lambda c1: at(c1, 2), True, "skip"),
    ("the record is the writer's own", lambda c1: c1, True, "merge"),
    ("the record is another, older state", lambda c1: at(c1, 0), True, "replace"),
    ("the record is ahead of the writer", lambda c1: at(c1, 3), True, "skip"),
]


@pytest.mark.parametrize(
    ("case", "record", "kept", "want"), CASES, ids=lambda x: x if isinstance(x, str) else ""
)
def test_commit_decides_as_next(tmp_path, case, record, kept, want):
    _, node, sink, c1 = setup(tmp_path)
    sink.record, sink.foreign = record(c1), not kept
    assert decide(node, sink) == want, case


def test_no_record():
    """`next none _ _ = write replace`: the first write replaces."""
    sink = Scripted()
    src = sv.io.StaticSource(pa.table({"id": [1], "amount": [5]}), name="orders")
    paid(src).write(sink).refresh()
    assert sink.modes == ["replace"]


def test_a_lost_acknowledgement(tmp_path):
    """`next`'s pending write: the record is the write that raised, so the
    writer skips to it, then writes its next change on it."""
    src, node, sink, c1 = setup(tmp_path)
    sink.record, sink.raise_once = c1, True
    with pytest.raises(OSError):
        node.refresh()
    assert sink.record.sources == {"orders": 2}
    assert decide(node, sink) == "skip"
    append(src, [4])
    assert decide(node, sink) == "merge"
