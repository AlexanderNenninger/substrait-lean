"""A source's change log drops what every reader has read (#1329, N6c).

`StaticSource.apply` and an `io.Source`'s reads log each change, so a node at
an older version gets exactly the change since. The log used to keep every
change since the source was built: memory in the driver that grew with the
input, beside the views' state in the engine. A pipeline now reports the
version it committed (`ChangeLog.consumed`), and the log drops the changes
every reader has. A reader that lags keeps its changes, and a reader older
than the log gets the whole table to diff, so no result changes."""

from __future__ import annotations

import gc

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify._weighted import ChangeLog
from sverify.incremental import Changes
from sverify.io import StaticSource

pytestmark = pytest.mark.backend("duckdb")


def _rows(start: int, n: int) -> pa.Table:
    ids = list(range(start, start + n))
    return pa.table({"id": ids, "g": [i % 3 for i in ids]})


@sv.transform()
def per_group(t):
    return t.group_by("g").aggregate(n=_.count())


@sv.transform()
def ids(t):
    return t.select("id")


def _counts(node) -> dict[int, int]:
    return {r["g"]: r["n"] for r in node.to_arrow().to_pylist()}


def test_the_log_stays_empty_once_every_reader_has_read():
    src = StaticSource(_rows(0, 3), name="t")
    node = src.pipe(per_group)
    node.refresh()
    for i in range(1, 21):
        src.apply(Changes(inserts=_rows(3 * i, 3)))
        node.refresh()
        assert src._log.entries == []
    assert _counts(node) == {0: 21, 1: 21, 2: 21}


def test_a_lagging_reader_keeps_its_changes():
    src = StaticSource(_rows(0, 3), name="t")
    fast, slow = src.pipe(per_group), src.pipe(ids)
    fast.refresh()
    slow.refresh()
    for i in range(1, 6):
        src.apply(Changes(inserts=_rows(3 * i, 3)))
        fast.refresh()
    # `slow` read version 0: the five changes since are all kept for it.
    assert [v for v, _ in src._log.entries] == [1, 2, 3, 4, 5]
    report = slow.refresh()
    assert "replaced" not in str(report)
    assert sorted(r["id"] for r in slow.to_arrow().to_pylist()) == list(range(18))
    assert src._log.entries == []


def test_a_reader_that_is_gone_holds_nothing():
    log: ChangeLog[str] = ChangeLog()

    class Reader:
        pass

    a, b = Reader(), Reader()
    for v in (1, 2, 3):
        log.add(v, f"c{v}")
    log.consumed(b, 1)
    log.consumed(a, 3)
    assert [v for v, _ in log.entries] == [2, 3]
    del b
    gc.collect()
    log.consumed(a, 3)
    assert log.entries == []
    assert log.since(1) is None  # older than the log: the whole table to diff
    assert log.since(3) == []
