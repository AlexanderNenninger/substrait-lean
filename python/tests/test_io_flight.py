"""`sverify.io.flight`: `FlightSource` reading `FlightLog`, a real Flight
server in this process, in pipelines: appends, batches dropped past the
server's retention, an empty log and a source resumed at a cursor."""

import json

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import rows

fl = pytest.importorskip("pyarrow.flight")

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
    assert (entry.start, entry.end, entry.mode) == (1, 2, "change feed")
    assert (entry.inserts, entry.deletes) == (2, 0)
    assert "appended to samples v1→v2" in entry.detail
    assert "numbers batches in order of arrival" in entry.detail
    assert rows(node) == [("a", 1, 0.5), ("b", 2, 0.75)]
    assert cursor(src) == 4 and json.loads(json.dumps(cursor(src))) == 4
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


def test_a_source_resumed_at_a_cursor_deletes_what_the_server_drops(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    first = FlightSource(location(server), "samples")
    busy(first).refresh()
    # Another process, resumed at the cursor the first one recorded.
    resumed = FlightSource(location(server), "samples", schema=SAMPLES)
    put(server, "samples", [sample("a", 3, 0.7)])
    batch = read(resumed, cursor(first))
    assert (batch.kind, batch.cursor) == ("append", 3)
    assert batch.table.to_pylist() == [sample("a", 3, 0.7)]
    server.drop("samples", below=2)
    batch = read(resumed, 3)
    assert (batch.kind, batch.cursor, batch.table.num_rows) == ("changes", 3, 0)
    assert batch.deletes.to_pylist() == [sample("a", 1, 0.5)]


def test_a_restart_resumes_from_the_batch_number_its_sink_recorded(server, tmp_path):
    from deltalake import DeltaTable

    from sverify.io import DeltaSink, DeltaSource

    put(server, "samples", [sample("a", 1, 0.5)], [sample("b", 1, 0.1)], [sample("a", 2, 0.6)])
    uri = str(tmp_path / "busy")

    def job():
        src = FlightSource(location(server), "samples", schema=SAMPLES)
        return src, busy(src).write(DeltaSink(uri))

    _, node = job()
    node.refresh()
    contract = DeltaSource(uri).contract()
    assert contract is not None and contract.cursors == {"samples": 3}
    put(server, "samples", [sample("a", 3, 0.7)])
    src, again = job()
    entry = again.refresh()["busy"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    w = entry.write
    assert w is not None and (w.mode, w.inserted, w.contract.cursors) == (
        "merge",
        1,
        {"samples": 4},
    )
    assert sorted(DeltaTable(uri).to_pyarrow_table()["ts"].to_pylist()) == [1, 2, 3]
    # The batches held since the restore come back as deletes when dropped.
    server.drop("samples", below=2)
    w = again.refresh()["busy"].write
    assert w is not None and (w.mode, w.deleted) == ("merge", 1)
    assert rows(again) == [("a", 2, 0.6), ("a", 3, 0.7)]


def test_a_restart_with_nothing_held_and_no_schema_reads_the_window(server, tmp_path):
    from sverify.io import DeltaSink

    put(server, "samples", [sample("a", 1, 0.5)])
    uri = str(tmp_path / "busy")
    busy(FlightSource(location(server), "samples")).write(DeltaSink(uri)).refresh()
    put(server, "samples", [sample("a", 2, 0.6)])
    server.drop("samples", below=2)  # batch 1, the cursor's, is gone
    src = FlightSource(location(server), "samples")
    w = busy(src).write(DeltaSink(uri)).refresh().writes[0]
    assert (w.mode, w.inserted) == ("overwrite", 1)


def test_a_bearer_token():
    class Token(fl.ServerMiddlewareFactory):
        def start_call(self, info, headers):
            if "Bearer s3cret" not in headers.get("authorization", []):
                raise fl.FlightUnauthenticatedError("a valid bearer token is needed")

    s = FlightLog(middleware={"token": Token()})
    try:
        with pytest.raises(fl.FlightUnauthenticatedError):
            FlightSource(location(s), "samples", schema=SAMPLES).latest()
        src = FlightSource(location(s), "samples", schema=SAMPLES, token="s3cret")
        assert src.latest() == 0
    finally:
        s.shutdown()
