"""#1329 (A1, M1): a source that implements `VersionedSource` directly and
holds no table, the case the gate measures. It makes its rows per call; a
pipeline over it keeps them in the store of its engine, not in the connection
as an Arrow table."""

import gc
import weakref

import pyarrow as pa
import pytest

import sverify as sv
from _pipelines import rows
from sverify._state import arrow_of
from sverify.incremental import IncrementalView, Snapshot, SourceBatch

ENGINES = [
    "duckdb",
    pytest.param("polars", marks=pytest.mark.backend("polars")),
    pytest.param("spark", marks=pytest.mark.backend("spark")),
]


class Direct:
    """Rows `1..n` at version `n`, made on each call: no table held."""

    name = "t"

    def __init__(self) -> None:
        self.n = 3
        self.deletes = None

    @staticmethod
    def make(lo: int, hi: int) -> pa.Table:
        ids = pa.array(range(lo, hi + 1), pa.int64())
        return pa.table(
            {"id": ids, "amt": pa.array([i * 10 for i in range(lo, hi + 1)], pa.int64())}
        )

    def schema(self) -> pa.Schema:
        return self.make(1, 0).schema

    def latest(self) -> int:
        return self.n

    def snapshot(self, version: int | None = None) -> Snapshot:
        return Snapshot(
            version=self.n if version is None else version, table=self.make(1, self.n), facts=[]
        )

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        end = self.n if until is None else until
        if end == since:
            return SourceBatch.unchanged(since)
        gone = {} if self.deletes is None else {"deletes": self.deletes}
        return SourceBatch.from_changes(
            since, end, inserts=self.make(since + 1, end), trusted="Δ generated", **gone
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


@pytest.mark.parametrize("engine", ENGINES)
def test_a_pipeline_over_it_keeps_the_rows_in_the_store(engine):
    src = Direct()
    node = total(src)
    node.refresh(engine=engine)
    assert rows(node) == [(3, 60)]
    src.n = 5
    [entry] = node.refresh(engine=engine)[node.name].report.sources
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


@pytest.mark.parametrize("engine", ENGINES)
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


def input_ids(node) -> list[int]:
    return sorted(arrow_of(node._stage.pipe.con.get("t")).column("id").to_pylist())


@pytest.mark.parametrize("engine", ENGINES)
def test_a_delete_of_a_missing_row_is_refused_and_changes_nothing(engine):
    src = Direct()
    node = total(src)
    node.refresh(engine=engine)
    src.n = 4
    src.deletes = Direct.make(99, 99)
    with pytest.raises(ValueError, match=r"cannot delete rows from t: no such row.*99"):
        node.refresh(engine=engine)
    assert rows(node) == [(3, 60)]
    assert input_ids(node) == [1, 2, 3]
    src.deletes = None
    node.refresh(engine=engine)
    assert rows(node) == [(4, 100)]
    assert input_ids(node) == [1, 2, 3, 4]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_refresh_that_fails_after_the_input_changed_leaves_it_as_it_was(engine, monkeypatch):
    src = Direct()
    node = total(src)
    node.refresh(engine=engine)
    src.n = 5
    real = IncrementalView._record

    def fail(self, delta):
        raise RuntimeError("the commit failed")

    monkeypatch.setattr(IncrementalView, "_record", fail)
    with pytest.raises(RuntimeError, match="the commit failed"):
        node.refresh(engine=engine)
    monkeypatch.setattr(IncrementalView, "_record", real)
    assert rows(node) == [(3, 60)]
    assert input_ids(node) == [1, 2, 3]
    node.refresh(engine=engine)  # the batch applies once
    assert rows(node) == [(5, 150)]
    assert input_ids(node) == [1, 2, 3, 4, 5]


def test_duckdb_puts_the_input_rows_back_when_its_update_fails_after_committing(monkeypatch):
    from sverify_duckdb import DuckDBStore

    src = Direct()
    node = total(src)
    node.refresh(engine="duckdb")
    src.n = 5
    real = DuckDBStore.apply
    calls = []

    def committed_then_failed(self, updates):
        real(self, updates)
        if not calls:
            calls.append(1)
            raise RuntimeError("after the commit")

    monkeypatch.setattr(DuckDBStore, "apply", committed_then_failed)
    with pytest.raises(RuntimeError, match="after the commit"):
        node.refresh(engine="duckdb")
    assert rows(node) == [(3, 60)]
    assert input_ids(node) == [1, 2, 3]
    node.refresh(engine="duckdb")
    assert rows(node) == [(5, 150)]
    assert input_ids(node) == [1, 2, 3, 4, 5]
