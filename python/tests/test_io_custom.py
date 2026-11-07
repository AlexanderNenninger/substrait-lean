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
from _pipelines import rows
from sverify.errors import AuditError, PreconditionError
from sverify.io import (
    Batch,
    Changes,
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
    assert rows(node) == [(1, 10, 30)]
    f.add({"id": 3, "ts": 30, "amount": 50})
    report = node.refresh()
    [entry] = report["big"].report.sources
    assert (entry.start, entry.end, entry.mode) == (1, 2, "change_feed")
    assert "appended to payments v1→v2" in entry.detail
    assert "assuming rows only arrive with a greater ts" in entry.detail
    assert rows(node) == [(1, 10, 30), (3, 30, 50)]
    # Nothing new: no new version.
    assert node.refresh()["big"].report.sources[0].mode == "unchanged"


def test_audit_catches_a_row_the_cursor_missed():
    f = feed()
    node = big(from_query(f.since, cursor_on="ts", name="payments"))
    node.refresh()
    f.add({"id": 3, "ts": 5, "amount": 70})  # late: below the cursor
    node.refresh()
    assert rows(node) == [(1, 10, 30)]  # missed, as the report warned
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


def test_sources_of_your_own_pipe_into_steps():
    f = feed()
    node = from_query(f.since, cursor_on="ts", name="payments").pipe(big).pipe(ids)
    node.refresh()
    assert rows(node) == [(1,)]
    regions = from_frame(lambda: pa.table({"id": [1], "region": ["eu"]}), name="regions")
    out = regions.pipe(ids)
    out.refresh()
    assert rows(out) == [(1,)]


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
    assert (entry.mode, entry.inserts, entry.deletes) == ("snapshot_diff", 1, 1)
    assert "full reads" in entry.detail and "assuming" not in entry.detail
    assert rows(node) == [(2, 2, 50), (3, 3, 60)]
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
    assert rows(node) == [(2, 2, 40), (3, 3, 50)]


def test_a_schema_for_a_source_that_starts_empty():
    schema = pa.schema([("id", pa.int64()), ("ts", pa.int64()), ("amount", pa.int64())])
    f = Feed([])
    f.table = schema.empty_table()
    with pytest.raises(ValueError, match="give the source schema="):
        big(from_query(lambda s: None, cursor_on="ts", name="payments"))
    node = big(from_query(f.since, cursor_on="ts", name="payments", schema=schema))
    node.refresh()
    assert rows(node) == []
    f.add({"id": 1, "ts": 1, "amount": 20})
    node.refresh()
    assert rows(node) == [(1, 1, 20)]


class Down(Source):
    """A source whose server is down until `up` is set."""

    up = False

    def read(self, since):
        if not self.up:
            raise ConnectionError("server down")
        if since is not None:
            return None
        return Batch(pa.table({"id": [1], "ts": [1], "amount": [20]}), cursor=1)


def test_a_declared_schema_proves_without_reading():
    schema = pa.schema([("id", pa.int64()), ("ts", pa.int64()), ("amount", pa.int64())])
    src = Down("payments", schema=schema)
    node = big(src)
    assert src.schema() == schema
    with pytest.raises(ConnectionError):
        node.refresh()
    src.up = True
    node.refresh()
    assert rows(node) == [(1, 1, 20)]


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
    assert rows(node) == [(1, 1, 30), (2, 2, 40)]
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
    assert (entry.mode, entry.detail, entry.inserts) == ("change_feed", "Δ from the log", 1)
    assert rows(node) == [(1, 1, 30), (2, 2, 40), (3, 3, 50)]


# -- sinks -----------------------------------------------------------------


class ParquetSink(Sink):
    """The docs' example: a Parquet file and its contract next to it."""

    def __init__(self, path):
        super().__init__(Path(path).stem, location=str(path))
        self.path = Path(path)
        self.record = self.path.with_suffix(".contract.json")
        self.changes = []

    def contract(self, version=None):
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
    src.apply(Changes(inserts=[(3, 3, 50)]))
    node.refresh()
    assert [t.num_rows for t in written] == [1, 2]
    # Proved NOT NULL columns are not nullable in what the sink gets.
    assert written[0].schema.field("amount").nullable is False


def test_a_sink_of_its_own_gets_the_change(tmp_path):
    src = payments_source()
    sink = ParquetSink(tmp_path / "big.parquet")
    node = big(src).write(sink)
    node.refresh()
    src.apply(Changes(inserts=[(3, 3, 50)], deletes=[(1, 1, 30)]))
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


def test_a_restarted_job_with_another_plan_overwrites_its_sink(tmp_path):
    big(payments_source()).write(ParquetSink(tmp_path / "big.parquet")).refresh()
    # Same source version, so the same epoch: only the plan tells them apart.
    again = ParquetSink(tmp_path / "big.parquet")
    node = ids(payments_source()).write(again)
    w = node.refresh().writes[0]
    assert (w.mode, w.inserted) == ("overwrite", 2)
    assert again.changes == [(True, 2, 0)]
    # A view's rows come in no particular order.
    assert sorted(r["id"] for r in pq.read_table(again.path).to_pylist()) == [1, 2]
    assert node.refresh().writes[0].mode == "skipped"


def test_nodes_read_a_stored_node_from_what_was_written(tmp_path):
    src = payments_source()
    stored = big(src).write(ParquetSink(tmp_path / "big.parquet"))
    out = ids(stored)
    out.refresh()
    src.apply(Changes(inserts=[(3, 3, 50)]))
    [entry] = out.refresh()["ids"].report.sources
    assert (entry.mode, entry.inserts) == ("change_feed", 1)
    assert entry.detail == "Δ as written to big v1→v2"
    assert rows(out) == [(1,), (3,)]


class Log(Source):
    """A log read by sequence number: the cursor is the number of entries
    read, and it lasts across processes."""

    def __init__(self, entries, *, durable=True):
        super().__init__("payments", assumes="entries are only appended")
        self.entries, self.durable, self.reads = entries, durable, []

    def read(self, since):
        self.reads.append(since)
        new = self.entries[since or 0 :]
        if not new:
            return None
        return Batch(pa.Table.from_pylist(new), cursor=len(self.entries))

    def restore(self, cursor):
        if not self.durable or cursor > len(self.entries):
            return None
        self.reads.append(("restore", cursor))
        return pa.Table.from_pylist(self.entries[:cursor])


def entries():
    return [{"id": 1, "ts": 10, "amount": 30}, {"id": 2, "ts": 20, "amount": 5}]


def test_a_restarted_job_resumes_from_the_cursor_its_sink_recorded(tmp_path):
    log = entries()

    def job():
        src = Log(log)
        return src, big(src).write(DeltaSink(str(tmp_path / "big")))

    _, node = job()
    node.refresh()
    log.append({"id": 3, "ts": 30, "amount": 50})
    node.refresh()
    recorded = DeltaSource(str(tmp_path / "big")).contract()
    assert recorded is not None and recorded.cursors == {"payments": 3}
    log.append({"id": 4, "ts": 40, "amount": 70})
    src, restarted = job()
    out = restarted.refresh()["big"]
    # The table as of the cursor, then only the entry after it (the read
    # before is for the schema).
    assert src.reads[-2:] == [("restore", 3), 3]
    assert out.started is not None and out.started.startswith("resumed from")
    w = out.write
    assert w is not None and (w.mode, w.inserted, w.deleted) == ("merge", 1, 0)
    assert w.contract.sources == {"payments": 3} and w.contract.cursors == {"payments": 4}
    assert sorted(
        r["id"] for r in DeltaTable(str(tmp_path / "big")).to_pyarrow_table().to_pylist()
    ) == [1, 3, 4]
    assert restarted.refresh().writes[0].mode == "skipped"


def test_a_restarted_job_with_nothing_new_skips_its_commit(tmp_path):
    log = entries()
    big(Log(log)).write(DeltaSink(str(tmp_path / "big"))).refresh()
    src = Log(log)
    w = big(src).write(DeltaSink(str(tmp_path / "big"))).refresh().writes[0]
    assert (w.mode, w.contract.sources) == ("skipped", {"payments": 1})
    assert src.reads[-2:] == [("restore", 2), 2]


def test_of_two_sinks_the_one_further_ahead_resumes(tmp_path):
    log = entries()

    def nodes(src):
        a = big(src).write(DeltaSink(str(tmp_path / "a")))
        b = ids(src).write(DeltaSink(str(tmp_path / "b")))
        return a, b

    src = Log(log)
    a, b = nodes(src)
    sv.group(a, b).refresh()
    log.append({"id": 3, "ts": 30, "amount": 50})
    b.refresh()  # b is at payments v2, a at v1
    a, b = nodes(Log(log))
    out = sv.group(a, b).refresh()
    assert out["b"].started is not None and out["b"].started.startswith("resumed from")
    w = out["a"].write
    # a's state at v1 is gone: it is computed at v2 and overwrites its sink.
    assert w is not None and (w.mode, w.contract.sources) == ("overwrite", {"payments": 2})
    assert out["b"].write is not None and out["b"].write.mode == "skipped"


def test_a_stale_cursor_reads_the_whole_table_again(tmp_path):
    log = entries()
    big(Log(log)).write(DeltaSink(str(tmp_path / "big"))).refresh()
    del log[1:]  # the log was truncated: cursor 2 is gone
    src = Log(log)
    w = big(src).write(DeltaSink(str(tmp_path / "big"))).refresh().writes[0]
    assert src.reads == [None, 1]
    assert (w.mode, w.contract.sources) == ("overwrite", {"payments": 2})
    assert DeltaTable(str(tmp_path / "big")).to_pyarrow_table()["id"].to_pylist() == [1]


def test_from_query_resumes_from_a_timestamp_cursor(tmp_path):
    from datetime import datetime

    t0 = datetime(2026, 11, 3, 12, 0)
    f = Feed([{"id": 1, "ts": t0, "amount": 30}])

    def job():
        src = from_query(f.since, cursor_on="ts", name="payments")
        return big(src).write(DeltaSink(str(tmp_path / "big")))

    job().refresh()
    recorded = DeltaSource(str(tmp_path / "big")).contract()
    assert recorded is not None
    assert recorded.cursors == {"payments": {"$cursor": "datetime", "value": t0.isoformat()}}
    f.add({"id": 2, "ts": datetime(2026, 11, 3, 12, 1), "amount": 40})
    w = job().refresh().writes[0]
    assert (w.mode, w.inserted, w.contract.sources) == ("merge", 1, {"payments": 2})


def test_from_files_resumes_unless_a_file_it_read_is_gone(tmp_path):
    drop = tmp_path / "drop"
    drop.mkdir()
    pq.write_table(pa.table({"id": [1], "ts": [1], "amount": [30]}), drop / "a.parquet")

    def job():
        src = from_files(str(drop), name="payments")
        return big(src).write(DeltaSink(str(tmp_path / "big")))

    job().refresh()
    pq.write_table(pa.table({"id": [2], "ts": [2], "amount": [40]}), drop / "b.parquet")
    w = job().refresh().writes[0]
    assert (w.mode, w.inserted, w.contract.sources) == ("merge", 1, {"payments": 2})
    (drop / "a.parquet").unlink()
    w = job().refresh().writes[0]
    assert (w.mode, w.inserted, w.contract.sources) == ("overwrite", 1, {"payments": 3})


@pytest.mark.parametrize(
    "cursor",
    [
        None,
        3,
        "x",
        [1, "a"],
        (1, 2),
        {"a": 1, "$cursor": 2},
        __import__("decimal").Decimal("1.50"),
        b"\x00\xff",
        __import__("datetime").date(2026, 1, 2),
        __import__("datetime").datetime(2026, 1, 2, 3, 4, 5, 6),
    ],
)
def test_cursors_round_trip_through_json(cursor):
    import json

    from sverify.io._common import cursor_json, cursor_value

    assert cursor_value(json.loads(json.dumps(cursor_json(cursor)))) == cursor


def test_a_cursor_without_json_form_is_not_recorded():
    from sverify.io._common import UNRECORDED, cursor_json

    assert cursor_json(float("nan")) is UNRECORDED
    assert cursor_json([object()]) is UNRECORDED


def test_a_restarted_job_numbers_versions_above_the_recorded_ones(tmp_path):
    log = entries()

    def job():
        src = Log(log, durable=False)
        return big(src).write(DeltaSink(str(tmp_path / "big")))

    node = job()
    node.refresh()
    log.append({"id": 3, "ts": 30, "amount": 50})
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
    text = c.to_json().replace('"node"', '"later": 1, "node"')
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


# -- a source that cannot restore, across processes (#889, #965) ------------


def frame(rows: list[dict]) -> pa.Table:
    return pa.Table.from_pylist(
        rows, schema=pa.schema([("id", pa.int64()), ("ts", pa.int64()), ("amount", pa.int64())])
    )


def frame_job(tmp_path, table: dict):
    """What one process builds: a `from_frame` source read from `table["t"]`."""
    src = from_frame(lambda: table["t"], name="payments")
    return big(src).write(DeltaSink(str(tmp_path / "big")))


def sink_ids(tmp_path) -> list[int]:
    return sorted(r["id"] for r in DeltaTable(str(tmp_path / "big")).to_pyarrow_table().to_pylist())


def test_a_new_process_resumes_an_unchanged_from_frame_source(tmp_path):
    """#889: three refreshes, each in a new process, of an unchanged
    `from_frame` source: the first writes, the others resume and write
    nothing."""
    table = {"t": frame(entries())}
    first = frame_job(tmp_path, table).refresh()["big"]
    assert first.write is not None and first.write.mode == "created"
    for _run in range(2):
        again = frame_job(tmp_path, table).refresh()["big"]
        assert again.started.startswith("resumed from")
        assert again.write is not None and again.write.mode == "skipped"
    assert DeltaTable(str(tmp_path / "big")).transaction_version("sverify:big") == 1
    # A new process whose read differs numbers its version above the record.
    table["t"] = frame([*entries(), {"id": 3, "ts": 30, "amount": 50}])
    w = frame_job(tmp_path, table).refresh()["big"].write
    assert w is not None and w.contract.sources == {"payments": 2}
    assert sink_ids(tmp_path) == [1, 3]


def test_two_processes_numbering_other_contents_alike(tmp_path, monkeypatch):
    """#965 (the TLA+ model's `today-collision`): P and Q start from the
    sink's record of payments@v1 and both number their first read v2, with
    other contents. Q, past `_continue_versions` when P commits, must not
    take P's commit at v2 for its own state."""
    table = {"t": frame(entries())}
    frame_job(tmp_path, table).refresh()
    with_3 = frame([*entries(), {"id": 3, "ts": 30, "amount": 50}])
    with_4 = frame([*entries(), {"id": 4, "ts": 40, "amount": 60}])
    table["t"] = with_4
    q = frame_job(tmp_path, table)
    original = DeltaSink._stored

    def p_commits(self):
        out = original(self)
        if self is q.sink:
            monkeypatch.setattr(DeltaSink, "_stored", original)
            table["t"] = with_3
            frame_job(tmp_path, table).refresh()
            assert sink_ids(tmp_path) == [1, 3]
            table["t"] = with_4
        return out

    monkeypatch.setattr(DeltaSink, "_stored", p_commits)
    w = q.refresh()["big"].write
    assert w is not None and w.mode != "skipped" and w.contract.sources == {"payments": 3}
    assert sink_ids(tmp_path) == [1, 4]
    # Q writes on from its own state.
    table["t"] = frame(
        [*entries(), {"id": 4, "ts": 40, "amount": 60}, {"id": 5, "ts": 50, "amount": 70}]
    )
    q.refresh()
    assert sink_ids(tmp_path) == [1, 4, 5]


def test_a_new_process_resumes_a_static_source_from_its_sink(tmp_path):
    """The digests of the view's static tables are compared table by table:
    the pipeline does not hold the view while it is being built."""

    def job():
        return big(payments_source()).write(DeltaSink(str(tmp_path / "big")))

    job().refresh()
    again = job().refresh()["big"]
    assert again.started.startswith("resumed from")
    assert again.write is not None and again.write.mode == "skipped"
