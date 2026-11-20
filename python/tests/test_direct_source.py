"""#1329 (A1, M1): a source that implements `VersionedSource` directly and
holds no table, the case the gate measures. It makes its rows per call; a
pipeline over it keeps them in the store of its engine, not in the connection
as an Arrow table."""

import gc
import weakref

import pyarrow as pa
import pyarrow.compute as pc
import pytest

import sverify as sv
from _pipelines import rows
from sverify.incremental import Snapshot, SourceBatch


class Direct:
    """Rows `1..n` at version `n`, made on each call: no table held."""

    name = "t"

    def __init__(self) -> None:
        self.n = 3

    @staticmethod
    def make(lo: int, hi: int) -> pa.Table:
        ids = pa.array(range(lo, hi + 1), pa.int64())
        return pa.table({"id": ids, "amt": pc.multiply(ids, 10)})

    def schema(self) -> pa.Schema:
        return self.make(1, 0).schema

    def latest(self) -> int:
        return self.n

    def snapshot(self, version: int | None = None) -> Snapshot:
        return Snapshot(self.n if version is None else version, self.make(1, self.n), [])

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        end = self.n if until is None else until
        if end == since:
            return SourceBatch.unchanged(since)
        return SourceBatch.from_changes(
            since, end, inserts=self.make(since + 1, end), trusted="Δ generated"
        )


@sv.transform()
def total(t):
    return t.aggregate(rows=t.id.count(), amt=t.amt.sum())


def test_the_source_holds_no_table_between_calls():
    src = Direct()
    snap = weakref.ref(src.snapshot().table)
    gc.collect()
    assert snap() is None
    assert not [v for v in vars(src).values() if isinstance(v, pa.Table)]


def test_a_pipeline_over_it_keeps_the_rows_in_the_store():
    src = Direct()
    node = total(src)
    node.refresh()
    assert rows(node) == [(3, 60)]
    src.n = 5
    [entry] = node.refresh()[node.name].report.sources
    assert (entry.mode, entry.inserts) == ("change_feed", 2)
    assert rows(node) == [(5, 150)]
    pipe = node._stage.pipe
    assert "t" in pipe.inputs
    assert not isinstance(pipe.con.get("t"), pa.Table)


def test_the_audit_compares_the_store_with_the_source():
    src = Direct()
    node = total(src)
    node.refresh()
    src.n = 4
    node.refresh(audit=True)
    assert rows(node) == [(4, 100)]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_snapshot_diff_counts_the_change_on_the_store(engine):
    class Snapshots(Direct):
        def changes(self, since, until=None):
            end = self.n if until is None else until
            if end == since:
                return SourceBatch.unchanged(since)
            return SourceBatch.from_snapshot(since, end, self.make(1, end), reason="no feed")

    src = Snapshots()
    node = total(src)
    node.refresh(engine=engine)
    src.n = 6
    [entry] = node.refresh(engine=engine)[node.name].report.sources
    assert (entry.mode, entry.inserts, entry.deletes) == ("recomputed", 3, 0)
    assert rows(node) == [(6, 210)]
