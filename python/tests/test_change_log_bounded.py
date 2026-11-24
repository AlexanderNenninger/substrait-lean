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
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from sverify._weighted import ChangeLog
from sverify.incremental import Changes
from sverify.io import Batch, DeltaSink, Source, StaticSource

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


def test_the_log_keeps_only_the_committed_change_once_every_reader_has_read():
    src = StaticSource(_rows(0, 3), name="t")
    node = src.pipe(per_group)
    node.refresh()
    for i in range(1, 21):
        src.apply(Changes(inserts=_rows(3 * i, 3)))
        node.refresh()
        assert [v for v, _ in src._log.entries] == [i]
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
    assert [v for v, _ in src._log.entries] == [5]


def test_a_reader_that_is_gone_holds_nothing():
    log: ChangeLog[str] = ChangeLog()

    class Reader:
        pass

    a, b = Reader(), Reader()
    for v in (1, 2, 3):
        log.add(v, f"c{v}")
    log.consumed(b, 1)
    log.consumed(a, 3)
    assert [v for v, _ in log.entries] == [1, 2, 3]
    del b
    gc.collect()
    log.consumed(a, 3)
    # The change at the committed version stays, for the sink's cursor.
    assert [v for v, _ in log.entries] == [3]
    assert log.at(3) == "c3"
    assert log.since(1) is None  # older than the log: the whole table to diff
    assert log.since(3) == []


class Log(Source):
    """A log read by sequence number, whose cursor lasts across processes."""

    def __init__(self, entries):
        super().__init__("payments", assumes="entries are only appended")
        self.entries = entries

    def read(self, since):
        new = self.entries[since or 0 :]
        if not new:
            return None
        return Batch(table=pa.Table.from_pylist(new), cursor=len(self.entries))

    def restore(self, cursor):
        return pa.Table.from_pylist(self.entries[:cursor])


def _entry(i: int) -> dict:
    return {"id": i, "g": i % 3}


def _ids(path) -> list[int]:
    return sorted(r["id"] for r in DeltaTable(str(path)).to_pyarrow_table().to_pylist())


def test_a_rebuild_starts_from_what_the_sink_recorded(tmp_path, monkeypatch):
    log = [_entry(i) for i in range(3)]
    src = Log(log)
    node = ids(src).write(DeltaSink(str(tmp_path / "out")))
    node.refresh()
    log += [_entry(3), _entry(4)]
    real = DeltaSink._commit
    monkeypatch.setattr(DeltaSink, "_commit", lambda self: (_ for _ in ()).throw(OSError("down")))
    with pytest.raises(OSError, match="down"):
        node.refresh()
    monkeypatch.setattr(DeltaSink, "_commit", real)
    # The pipeline committed past the sink's version, then the stage is
    # dropped (as a run-time check that fires drops it): the next refresh
    # rebuilds from what the sink recorded, which the log must still keep.
    node._stage = None
    log += [_entry(5)]
    out = node.refresh()["out"]
    # Resumed, not recomputed: a stage loaded at the sink's versions would
    # raise, and fall back to a full recompute, had the log dropped them.
    assert out.started is not None and out.started.startswith("resumed from")
    assert _ids(tmp_path / "out") == list(range(6))


def test_a_lagging_reader_finds_its_cursor():
    log = [_entry(i) for i in range(3)]
    src = Log(log)

    class Reader:
        pass

    lagging, ahead = Reader(), Reader()
    first = src.latest()
    src.consumed(lagging, first)
    log.append(_entry(3))
    src.consumed(ahead, src.latest())
    # The source has read past `first`; a sink of the lagging reader records
    # the cursor read at `first`, which the log keeps.
    assert src._cursor_at(first) == 3
