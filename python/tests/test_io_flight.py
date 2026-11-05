"""`sverify.io.flight`: `FlightSource` reading `FlightLog`, a real Flight
server in this process, in pipelines: appends, batches dropped past the
server's retention, an empty log and a source restored at a cursor."""

import json

import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import rows

fl = pytest.importorskip("pyarrow.flight")

from sverify.io import DeltaSink, DeltaSource  # noqa: E402
from sverify.io.flight import FlightLog, FlightSource  # noqa: E402

SAMPLES = pa.schema([("host", pa.string()), ("ts", pa.int64()), ("cpu", pa.float64())])


@sv.transform(ensures=[_.cpu > 0.25])
def busy(samples):
    return samples.filter(samples.cpu > 0.25)


@pytest.fixture
def server():
    s = FlightLog()
    yield s
    s.shutdown()


def location(server):
    return f"grpc://127.0.0.1:{server.port}"


def put(server, table, *batches):
    """Send each of `batches` (lists of rows) as one batch; their numbers."""
    client = fl.connect(location(server))
    writer, acks = client.do_put(fl.FlightDescriptor.for_path(table), SAMPLES)
    seqs = []
    for batch in batches:
        writer.write_batch(pa.RecordBatch.from_pylist(batch, schema=SAMPLES))
        seqs.append(json.loads(acks.read().to_pybytes())["seq"])
    writer.close()
    client.close()
    return seqs


def cursor(src):
    """The cursor of `src`'s last read."""
    assert src._state is not None
    return src._state.cursor


def read(src, since):
    batch = src.read(since)
    assert batch is not None
    return batch


def sample(host, ts, cpu):
    return {"host": host, "ts": ts, "cpu": cpu}


def test_appends_by_the_number_of_the_last_batch(server):
    assert put(server, "samples", [sample("a", 1, 0.5)], [sample("b", 1, 0.1)]) == [1, 2]
    src = FlightSource(location(server), "samples")
    node = busy(src)
    node.refresh()
    assert rows(node) == [("a", 1, 0.5)]
    # One counter across tables.
    assert put(server, "other", [sample("x", 1, 0.9)]) == [3]
    assert put(server, "samples", [sample("b", 2, 0.75), sample("a", 2, 0.25)]) == [4]
    [entry] = node.refresh()["busy"].report.sources
    assert (entry.start, entry.end, entry.mode) == (1, 2, "change_feed")
    assert (entry.inserts, entry.deletes) == (2, 0)
    assert "appended to samples v1→v2" in entry.detail
    assert "numbers batches in order of arrival" in entry.detail
    assert rows(node) == [("a", 1, 0.5), ("b", 2, 0.75)]
    assert cursor(src) == {"seq": 4, "floor": 1}
    assert json.loads(json.dumps(cursor(src))) == cursor(src)
    # Nothing new: no new version.
    [entry] = node.refresh()["busy"].report.sources
    assert entry.start == entry.end == 2
    node.refresh(audit=True)


def test_batches_below_the_floor_come_back_as_deletes(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    src = FlightSource(location(server), "samples")
    node = busy(src)
    node.refresh()
    assert rows(node) == [("a", 1, 0.5), ("a", 2, 0.6)]
    put(server, "samples", [sample("a", 3, 0.7)])
    server.drop("samples", below=2)
    [entry] = node.refresh()["busy"].report.sources
    assert (entry.inserts, entry.deletes) == (1, 1)
    assert "changes read from samples" in entry.detail
    assert rows(node) == [("a", 2, 0.6), ("a", 3, 0.7)]
    # Everything dropped: the floor is the next number to come.
    server.drop("samples", below=99)
    [entry] = node.refresh()["busy"].report.sources
    assert (entry.inserts, entry.deletes) == (0, 2)
    assert rows(node) == []
    assert src.snapshot().table.num_rows == 0
    node.refresh(audit=True)


def test_a_server_that_keeps_some_batches(server):
    kept = FlightLog(keep=2)
    try:
        put(kept, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)], [sample("a", 3, 0.7)])
        node = busy(FlightSource(location(kept), "samples"))
        node.refresh()
        assert rows(node) == [("a", 2, 0.6), ("a", 3, 0.7)]
        node.refresh(audit=True)
    finally:
        kept.shutdown()


def test_the_window_is_the_batches_as_received(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)], [sample("a", 3, 0.7)])
    src = FlightSource(location(server), "samples")
    node = busy(src)
    node.refresh()
    server.drop("samples", below=2)
    node.refresh()
    table = src.snapshot().table
    held = list(src._held.values())
    assert table.num_rows == 2
    # The table's chunks are the received batches' buffers: no copy.
    addresses = [c.buffers()[1].address for c in table.column("ts").chunks]
    assert addresses == [b.column("ts").buffers()[1].address for b in held]


def test_an_empty_log(server):
    with pytest.raises(ValueError, match="give the source schema="):
        busy(FlightSource(location(server), "samples")).refresh()
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    node = busy(src)
    node.refresh()
    assert rows(node) == []
    assert cursor(src) is None
    put(server, "samples", [sample("a", 1, 0.5)])
    node.refresh()
    assert rows(node) == [("a", 1, 0.5)]
    node.refresh(audit=True)


def test_a_declared_schema_needs_no_server():
    src = FlightSource("grpc://127.0.0.1:1", "samples", schema=SAMPLES, timeout=1)
    busy(src)  # proves the contract without a read
    assert src.schema() == SAMPLES


def test_a_source_restored_at_a_cursor_deletes_what_the_server_drops(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    first = FlightSource(location(server), "samples")
    busy(first).refresh()
    recorded = cursor(first)
    # Another process, restored at the cursor a sink recorded.
    resumed = FlightSource(location(server), "samples", schema=SAMPLES)
    put(server, "samples", [sample("a", 3, 0.7)])
    assert resumed.restore(recorded).to_pylist() == [sample("a", 1, 0.5), sample("a", 2, 0.6)]
    batch = read(resumed, recorded)
    assert (batch.kind, batch.cursor) == ("append", {"seq": 3, "floor": 1})
    assert batch.table.to_pylist() == [sample("a", 3, 0.7)]
    server.drop("samples", below=2)
    batch = read(resumed, batch.cursor)
    assert (batch.kind, batch.cursor, batch.table.num_rows) == (
        "changes",
        {"seq": 3, "floor": 2},
        0,
    )
    assert batch.deletes.to_pylist() == [sample("a", 1, 0.5)]


def test_a_cursor_does_not_restore_after_the_server_dropped_batches(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    first = FlightSource(location(server), "samples")
    busy(first).refresh()
    recorded = cursor(first)
    server.drop("samples", below=2)
    # Batch 1's row is gone: no restore, the job reads the whole log again.
    assert FlightSource(location(server), "samples").restore(recorded) is None
    assert FlightSource(location(server), "samples").restore(None) is None


def test_an_empty_log_restores_to_no_rows(server):
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    busy(src).refresh()
    assert cursor(src) is None
    put(server, "samples", [sample("a", 1, 0.5)])
    busy(src).refresh()
    put(server, "other", [sample("b", 1, 0.5)])
    # Nothing of the table up to a cursor before its first batch.
    assert (
        FlightSource(location(server), "samples", schema=SAMPLES)
        .restore({"seq": 0, "floor": 1})
        .num_rows
        == 0
    )


def test_a_bearer_token(monkeypatch):
    class Token(fl.ServerMiddlewareFactory):
        def start_call(self, info, headers):
            if "Bearer s3cret" not in headers.get("authorization", []):
                raise fl.FlightUnauthenticatedError("a valid bearer token is needed")

    s = FlightLog(middleware={"token": Token()})
    try:
        with pytest.raises(fl.FlightUnauthenticatedError):
            FlightSource(location(s), "samples", schema=SAMPLES).latest()
        monkeypatch.setenv("SVERIFY_TEST_FLIGHT_TOKEN", "s3cret")
        src = FlightSource(
            location(s), "samples", schema=SAMPLES, secret="env:SVERIFY_TEST_FLIGHT_TOKEN"
        )
        assert src.latest() == 0
        assert "s3cret" not in repr(src)
        with pytest.warns(DeprecationWarning, match="secret="):
            old = FlightSource(location(s), "samples", schema=SAMPLES, token="s3cret")
        assert old.latest() == 0
    finally:
        s.shutdown()


# -- a restart from what a DeltaSink recorded --------------------------------


def restart_job(server, path):
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    return src, busy(src).write(DeltaSink(path))


def stored_ts(path):
    return sorted(r["ts"] for r in DeltaTable(path).to_pyarrow_table().to_pylist())


def test_a_restarted_job_resumes_and_reads_later_drops_as_deletes(server, tmp_path):
    path = str(tmp_path / "busy")
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    _, node = restart_job(server, path)
    node.refresh()
    recorded = DeltaSource(path).contract()
    assert recorded is not None and recorded.cursors == {"samples": {"seq": 2, "floor": 1}}
    put(server, "samples", [sample("a", 3, 0.7)])
    _, restarted = restart_job(server, path)
    out = restarted.refresh()["busy"]
    assert out.started is not None and out.started.startswith("resumed from")
    assert out.write is not None and (out.write.mode, out.write.inserted) == ("merge", 1)
    assert stored_ts(path) == [1, 2, 3]
    server.drop("samples", below=2)
    w = restarted.refresh().writes[0]
    assert (w.mode, w.deleted) == ("merge", 1)
    assert stored_ts(path) == [2, 3]


def test_a_drop_while_down_recomputes(server, tmp_path):
    path = str(tmp_path / "busy")
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    restart_job(server, path)[1].refresh()
    server.drop("samples", below=2)
    _, restarted = restart_job(server, path)
    w = restarted.refresh().writes[0]
    assert w.mode == "overwrite"
    assert stored_ts(path) == [2]
