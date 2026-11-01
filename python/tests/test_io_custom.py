"""Sources and sinks written by users (`sverify.io.Source`, `Sink`, the
`from_*` helpers and `sink_from`) in pipelines, end to end, including a job
restarted against what its sinks recorded."""

import pickle
from pathlib import Path

import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.parquet as pq
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from sverify.errors import AuditError, PreconditionError
from sverify.io import (
    Batch,
    Contract,
    DeltaSink,
    DeltaSource,
    Sink,
    Snapshot,
    Source,
    SourceBatch,
    StaticSource,
    Storage,
    from_files,
    from_frame,
    from_query,
    sink_from,
)


@sv.transform(requires={"payments": [_.amount >= 0]}, ensures=[_.amount > 10, _.amount.notnull()])
def big(payments):
    return payments.filter(payments.amount > 10)


@sv.transform()
def ids(t):
    return t.select(t.id)


def rows_of(node):
    return sorted(tuple(r.values()) for r in node.to_arrow().to_pylist())


class Feed:
    """A table that grows, read by a high-water mark on `ts`."""

    def __init__(self, rows):
        self.table = pa.Table.from_pylist(rows)

    def add(self, *rows):
        self.table = pa.concat_tables([self.table, pa.Table.from_pylist(list(rows))])

    def since(self, ts):
        if ts is None:
            return self.table
        return self.table.filter(pc.call_function("greater", [self.table["ts"], ts]))


def feed():
    return Feed([{"id": 1, "ts": 10, "amount": 30}, {"id": 2, "ts": 20, "amount": 5}])


# -- sources ---------------------------------------------------------------


def test_from_query_appends_by_its_cursor():
    f = feed()
    node = big(from_query(f.since, cursor_on="ts", name="payments"))
    node.refresh()
    assert rows_of(node) == [(1, 10, 30)]
    f.add({"id": 3, "ts": 30, "amount": 50})
    report = node.refresh()
    [entry] = report["big"].report.sources
    assert (entry.start, entry.end, entry.mode) == (1, 2, "change feed")
    assert "appended to payments v1→v2" in entry.detail
    assert "assuming rows only arrive with a greater ts" in entry.detail
    assert rows_of(node) == [(1, 10, 30), (3, 30, 50)]
    # Nothing new: no new version.
    assert node.refresh()["big"].report.sources[0].mode == "unchanged"


def test_audit_catches_a_row_the_cursor_missed():
    f = feed()
    node = big(from_query(f.since, cursor_on="ts", name="payments"))
    node.refresh()
    f.add({"id": 3, "ts": 5, "amount": 70})  # late: below the cursor
    node.refresh()
    assert rows_of(node) == [(1, 10, 30)]  # missed, as the report warned
    with pytest.raises(AuditError, match="read again in full"):
        node.refresh(audit=True)
    f.add({"id": 4, "ts": 40, "amount": 80})
    with pytest.raises(AuditError, match="does not turn the state"):
        node.refresh(audit=True)
    # Rows arriving after the cursor are not a mismatch.
    g = feed()
    ok = big(from_query(g.since, cursor_on="ts", name="payments"))
    ok.refresh()
    g.add({"id": 3, "ts": 30, "amount": 50})
    ok.refresh(audit=True)


def test_preconditions_are_checked_on_the_rows():
    f = feed()
    node = big(from_query(f.since, cursor_on="ts", name="payments"))
    node.refresh()
    f.add({"id": 3, "ts": 30, "amount": -1})
    with pytest.raises(PreconditionError):
        node.refresh()
    assert node.versions == {"payments": 1}


def test_from_frame_diffs_full_reads():
    table = {"t": pa.table({"id": [1, 2], "ts": [1, 2], "amount": [30, 50]})}
    src = from_frame(lambda: table["t"], name="payments")
    node = big(src)
    node.refresh()
    table["t"] = pa.table({"id": [2, 3], "ts": [2, 3], "amount": [50, 60]})
    [entry] = node.refresh()["big"].report.sources
    assert (entry.mode, entry.inserts, entry.deletes) == ("snapshot diff", 1, 1)
    assert "full reads" in entry.detail and "assuming" not in entry.detail
    assert rows_of(node) == [(2, 2, 50), (3, 3, 60)]
    # The same table again is no new version.
    assert node.refresh()["big"].report.sources[0].mode == "unchanged"
    assert src.latest() == 2


def test_a_source_of_changes_and_polars_frames():
    pl = pytest.importorskip("polars")
    batches = [Batch(pl.DataFrame({"id": [1, 2], "ts": [1, 2], "amount": [30, 40]}), cursor=1)]
    later = [
        Batch(
            pl.DataFrame({"id": [3], "ts": [3], "amount": [50]}),
            cursor=2,
            kind="changes",
            deletes=pl.DataFrame({"id": [1], "ts": [1], "amount": [30]}),
        ),
    ]

    class Changes(Source):
        def read(self, since):
            n = 0 if since is None else since
            return batches[n] if n < len(batches) else None

    node = big(Changes("payments"))
    node.refresh()
    batches += later
    [entry] = node.refresh()["big"].report.sources
    assert (entry.inserts, entry.deletes) == (1, 1)
    assert rows_of(node) == [(2, 2, 40), (3, 3, 50)]


def test_a_schema_for_a_source_that_starts_empty():
    schema = pa.schema([("id", pa.int64()), ("ts", pa.int64()), ("amount", pa.int64())])
    f = Feed([])
    f.table = schema.empty_table()
    with pytest.raises(ValueError, match="give the source schema="):
        big(from_query(lambda s: None, cursor_on="ts", name="payments"))
    node = big(from_query(f.since, cursor_on="ts", name="payments", schema=schema))
    node.refresh()
    assert rows_of(node) == []
    f.add({"id": 1, "ts": 1, "amount": 20})
    node.refresh()
    assert rows_of(node) == [(1, 1, 20)]


def test_a_batch_in_another_schema_is_refused():
    f = feed()
    node = big(from_query(f.since, cursor_on="ts", name="payments"))
    node.refresh()
    f.table = pa.table({"id": [9], "ts": [99]})
    with pytest.raises(ValueError, match="does not fit the source's schema"):
        node.refresh()


def test_from_files_reads_new_files(tmp_path):
    drop = tmp_path / "drop"
    drop.mkdir()
    pq.write_table(pa.table({"id": [1], "ts": [1], "amount": [30]}), drop / "a.parquet")
    node = big(from_files(str(drop), name="payments"))
    node.refresh()
    pq.write_table(pa.table({"id": [2], "ts": [2], "amount": [40]}), drop / "b.parquet")
    (drop / "notes.txt").write_text("not a parquet file")
    [entry] = node.refresh()["big"].report.sources
    assert entry.inserts == 1 and "files are only added" in entry.detail
    assert rows_of(node) == [(1, 1, 30), (2, 2, 40)]
    node.refresh(audit=True)
    # A file rewritten in place is only noticed by an audit.
    pq.write_table(pa.table({"id": [1], "ts": [1], "amount": [31]}), drop / "a.parquet")
    with pytest.raises(AuditError):
        node.refresh(audit=True)


class Versioned:
    """A table format of its own: the full protocol, with the helpers."""

    def __init__(self):
        self.name = "payments"
        self.versions = [pa.table({"id": [1], "ts": [1], "amount": [30]})]

    def schema(self):
        return self.versions[-1].schema

    def latest(self):
        return len(self.versions) - 1

    def snapshot(self, version=None):
        v = self.latest() if version is None else version
        return Snapshot(v, self.versions[v], [])

    def changes(self, since, until=None):
        end = self.latest() if until is None else until
        if end == since:
            return SourceBatch.unchanged(since)
        if since == 0:
            return SourceBatch.from_snapshot(since, end, self.versions[end], reason="no log")
        new = self.versions[end].slice(self.versions[since].num_rows)
        return SourceBatch.from_changes(since, end, inserts=new, trusted="Δ from the log")


def test_a_versioned_source_built_with_the_batch_helpers():
    src = Versioned()
    node = big(src)
    node.refresh()
    src.versions.append(
        pa.concat_tables([src.versions[0], pa.table({"id": [2], "ts": [2], "amount": [40]})])
    )
    [entry] = node.refresh()["big"].report.sources
    assert (entry.mode, entry.detail) == ("recomputed", "no log; Δ = snapshot v1 − state")
    src.versions.append(
        pa.concat_tables([src.versions[1], pa.table({"id": [3], "ts": [3], "amount": [50]})])
    )
    [entry] = node.refresh()["big"].report.sources
    assert (entry.mode, entry.detail, entry.inserts) == ("change feed", "Δ from the log", 1)
    assert rows_of(node) == [(1, 1, 30), (2, 2, 40), (3, 3, 50)]


# -- sinks -----------------------------------------------------------------


class ParquetSink(Sink):
    """The docs' example: a Parquet file and its contract next to it."""

    def __init__(self, path):
        super().__init__(Path(path).stem, location=str(path))
        self.path = Path(path)
        self.record = self.path.with_suffix(".contract.json")
        self.changes = []

    def committed(self):
        if not self.record.exists():
            return None
        return Contract.from_json(self.record.read_text())

    def write(self, change):
        self.changes.append((change.replace, change.inserts.num_rows, change.deletes.num_rows))
        pq.write_table(change.table, self.path)
        self.record.write_text(change.contract.to_json())


def payments_source():
    return StaticSource(pa.table({"id": [1, 2], "ts": [1, 2], "amount": [30, 5]}), name="payments")


def test_sink_from_writes_each_state_once():
    written = []
    src = payments_source()
    node = big(src).write(sink_from(written.append, name="big"))
    first = node.refresh().writes[0]
    assert (first.mode, first.version, first.inserted) == ("overwrite", None, 1)
    assert node.refresh().writes[0].mode == "skipped"
    src.apply(sv.Changes(inserts=[(3, 3, 50)]))
    node.refresh()
    assert [t.num_rows for t in written] == [1, 2]
    # Proved NOT NULL columns are not nullable in what the sink gets.
    assert written[0].schema.field("amount").nullable is False


def test_a_sink_of_its_own_gets_the_change(tmp_path):
    src = payments_source()
    sink = ParquetSink(tmp_path / "big.parquet")
    node = big(src).write(sink)
    node.refresh()
    src.apply(sv.Changes(inserts=[(3, 3, 50)], deletes=[(1, 1, 30)]))
    w = node.refresh().writes[0]
    assert (w.mode, w.inserted, w.deleted) == ("update", 1, 1)
    assert sink.changes == [(True, 1, 0), (False, 1, 1)]
    assert pq.read_table(sink.path).to_pylist() == [{"id": 3, "ts": 3, "amount": 50}]
    assert str(w) == "big from payments@v1: update, 1 row(s) written, 1 deleted"
    assert str(node.status()).endswith(f"stored in {sink.path}")


def test_a_restarted_job_skips_what_its_sink_committed(tmp_path):
    src = payments_source()
    big(src).write(ParquetSink(tmp_path / "big.parquet")).refresh()
    again = ParquetSink(tmp_path / "big.parquet")
    node = big(payments_source()).write(again)
    assert node.refresh().writes[0].mode == "skipped"
    assert again.changes == []


def test_nodes_read_a_stored_node_from_what_was_written(tmp_path):
    src = payments_source()
    stored = big(src).write(ParquetSink(tmp_path / "big.parquet"))
    out = ids(stored)
    out.refresh()
    src.apply(sv.Changes(inserts=[(3, 3, 50)]))
    [entry] = out.refresh()["ids"].report.sources
    assert (entry.mode, entry.inserts) == ("change feed", 1)
    assert entry.detail == "Δ as written to big v1→v2"
    assert rows_of(out) == [(1,), (3,)]


def test_a_restarted_job_numbers_versions_above_the_recorded_ones(tmp_path):
    f = feed()

    def job():
        src = from_query(f.since, cursor_on="ts", name="payments")
        return big(src).write(DeltaSink(str(tmp_path / "big")))

    node = job()
    node.refresh()
    f.add({"id": 3, "ts": 30, "amount": 50})
    node.refresh()
    recorded = DeltaSource(str(tmp_path / "big")).contract()
    assert recorded is not None and recorded.sources == {"payments": 2}
    # The restarted job reads the table again: version 3, and the sink
    # overwrites rather than skipping a state it never wrote.
    restarted = job()
    w = restarted.refresh().writes[0]
    assert (w.mode, w.contract.sources) == ("overwrite", {"payments": 3})
    assert DeltaTable(str(tmp_path / "big")).transaction_version("sverify:big") == 3
    assert restarted.refresh().writes[0].mode == "skipped"


def test_versions_continue_through_a_stored_node_in_memory(tmp_path):
    f = feed()

    def job():
        src = from_query(f.since, cursor_on="ts", name="payments")
        mid = big(src).write(sink_from(lambda t: None, name="mid"))
        return ids(mid).write(DeltaSink(str(tmp_path / "ids")))

    node = job()
    node.refresh()
    f.add({"id": 3, "ts": 30, "amount": 50})
    node.refresh()
    restarted = job()
    w = restarted.refresh()["ids"].write
    assert w is not None and w.mode == "overwrite" and w.contract.sources == {"mid": 3}


def test_a_contract_with_fields_it_does_not_know():
    c = Contract("v", "p", {"t": 1}, 1, [], {}, [])
    text = c.to_json().replace('"view"', '"later": 1, "view"')
    assert Contract.from_json(text) == c


# -- storage ---------------------------------------------------------------


def test_storage_keeps_secrets_out_of_repr_and_renews_them(tmp_path):
    fixed = Storage({"AWS_REGION": "eu-central-1", "AWS_SECRET_ACCESS_KEY": "s3cr3t"})
    assert "s3cr3t" not in repr(fixed)
    assert repr(fixed) == "Storage(AWS_REGION, AWS_SECRET_ACCESS_KEY)"
    calls = []

    def fresh():
        calls.append(1)
        return {}

    s = Storage(fresh)
    assert repr(s).startswith("Storage(") and "fresh" in repr(s)
    sink = DeltaSink(str(tmp_path / "big"), storage_options=s)
    node = big(payments_source()).write(sink)
    node.refresh()
    before = len(calls)
    node.refresh()
    assert len(calls) > before  # called again for every table opened
    # A function can be given directly too.
    src = DeltaSource(str(tmp_path / "big"), storage_options=dict)
    assert src.latest() == DeltaTable(str(tmp_path / "big")).version()


def test_a_storage_with_a_function_pickles_without_its_results():
    s = Storage(dict)
    assert pickle.loads(pickle.dumps(s)).options() == {}
