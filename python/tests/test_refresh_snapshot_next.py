"""`Sink._commit`'s decision for a source that cannot restore, case by case,
against `RefreshSnap.next` in `analysis/Sverify/Analysis/RefreshSnapshot.lean`
(#933, #988).

`RefreshSnap.no_corruption` and its companions are proved of a transition
system whose writers decide with `RefreshSnap.next`; they say something about
sverify only while `Sink._commit` decides the same way. A `from_frame` source
numbers its reads per process, and the contract's digest of the contents says
whether the sink holds this very state. Each row is one of `next`'s cases: the
sink's record (another plan's, the same contents, other contents at a version
not below the writer's, the writer's own older state, another older state),
whether another application's commit followed it, and the writer's pending
write. The test sets the record and the flag on a sink and checks what
`_commit` does: skip, replace the rows, or write the change (merge). A change
to `next` or to `_commit` that makes them differ fails here. The
durable-source twin is `test_refresh_next.py`.
"""

from dataclasses import replace

import pyarrow as pa
import pytest

import sverify as sv
from sverify.io import Sink, from_frame

SCHEMA = pa.schema([("id", pa.int64()), ("amount", pa.int64())])


def frame(ids: list[int]) -> pa.Table:
    return pa.table({"id": ids, "amount": [5] * len(ids)}, schema=SCHEMA)


@sv.transform()
def paid(payments):
    return payments.filter(payments.amount > 0)


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


def job(table: dict, sink: Sink):
    return paid(from_frame(lambda: table["t"], name="payments")).write(sink)


def setup():
    """A node over a `from_frame` source, written once (its own record `c1`,
    at version 1), then the source's contents change: the writer's next state
    is version 2 with another digest `d2`."""
    table = {"t": frame([1, 2])}
    sink = Scripted()
    node = job(table, sink)
    node.refresh()
    c1 = sink._last
    assert c1 is not None and c1.sources == {"payments": 1}
    table["t"] = frame([1, 2, 3])
    probe = Scripted()
    job(table, probe).refresh()
    assert probe._last is not None
    d2 = probe._last.digests
    assert d2 != c1.digests
    return table, node, sink, c1, d2


def decide(node, sink) -> str:
    w = node.refresh().writes[0]
    return "skip" if w.mode == "skipped" else sink.modes[-1]


def at(c, v: int, digests):
    """The record `c` at version `v`, of the contents `digests`."""
    return replace(c, sources={"payments": v}, epoch=v, digests=digests)


OTHER = {"payments": "f" * 64}

# (case, the record, kept, what `RefreshSnap.next` decides)
CASES = [
    ("another plan's record", lambda c1, d2: replace(c1, plan="0" * 64), True, "replace"),
    ("rows another application changed", lambda c1, d2: c1, False, "replace"),
    ("the same contents at another version", lambda c1, d2: at(c1, 7, d2), True, "skip"),
    ("the same contents at the writer's version", lambda c1, d2: at(c1, 2, d2), True, "skip"),
    ("the record is the writer's own", lambda c1, d2: c1, True, "merge"),
    ("other contents at the writer's version", lambda c1, d2: at(c1, 2, OTHER), True, "replace"),
    ("other contents above the writer's version", lambda c1, d2: at(c1, 5, OTHER), True, "replace"),
    ("another, older state", lambda c1, d2: at(c1, 0, OTHER), True, "replace"),
]


@pytest.mark.parametrize(
    ("case", "record", "kept", "want"), CASES, ids=lambda x: x if isinstance(x, str) else ""
)
def test_commit_decides_as_next(case, record, kept, want):
    _, node, sink, c1, d2 = setup()
    sink.record, sink.foreign = record(c1, d2), not kept
    assert decide(node, sink) == want, case


def test_no_record():
    """`next none _ _ = write replace`: the first write replaces."""
    sink = Scripted()
    job({"t": frame([1])}, sink).refresh()
    assert sink.modes == ["replace"]


def test_a_lost_acknowledgement():
    """`next`'s pending write: the record is the write that raised, so the
    writer skips to it, then writes its next change on it."""
    table, node, sink, c1, d2 = setup()
    sink.record, sink.raise_once = c1, True
    with pytest.raises(OSError):
        node.refresh()
    assert sink.record.sources == {"payments": 2}
    assert decide(node, sink) == "skip"
    table["t"] = frame([1, 2, 3, 4])
    assert decide(node, sink) == "merge"
