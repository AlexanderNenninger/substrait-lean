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
from sverify.io.flight import FlightSource  # noqa: E402
from sverify.testing import FlightLog  # noqa: E402

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
            location(s), "samples", schema=SAMPLES, credentials="env:SVERIFY_TEST_FLIGHT_TOKEN"
        )
        assert src.latest() == 0
        assert "s3cret" not in repr(src)
        with pytest.raises(TypeError):
            FlightSource(location(s), "samples", schema=SAMPLES, token="s3cret")  # type: ignore[call-arg]
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
    assert out.write is not None and (out.write.mode, out.write.inserts) == ("merge", 1)
    assert stored_ts(path) == [1, 2, 3]
    server.drop("samples", below=2)
    w = restarted.refresh().writes[0]
    assert (w.mode, w.deletes) == ("merge", 1)
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


# -- the protocol's edges -----------------------------------------------------


def get(server, ticket):
    """The server's answer to a raw ticket, called in this process."""
    return server.do_get(None, fl.Ticket(ticket))


@pytest.mark.parametrize(
    "ticket",
    [
        b"not json",
        b"[1]",
        b"5",
        b'{"after": 1}',
        b'{"table": ["samples"]}',
        b'{"table": "samples", "after": "2"}',
        b'{"table": "samples", "until": 2.5}',
        b'{"table": "samples", "after": true}',
    ],
)
def test_a_malformed_ticket_is_refused_with_the_ticket_shape(server, ticket):
    # #2427: a wrongly typed value got a Python traceback, not this message.
    with pytest.raises(fl.FlightServerError, match="the ticket is"):
        get(server, ticket)


def test_a_malformed_ticket_reaches_the_client_as_the_ticket_shape(server):
    client = fl.connect(location(server))
    with pytest.raises(fl.FlightServerError, match="the ticket is") as e:
        client.do_get(fl.Ticket(b'{"table": "samples", "after": "2"}')).read_all()
    assert "Traceback" not in str(e.value)
    client.close()


def test_a_ticket_picks_the_batches_in_its_range(server):
    put(server, "samples", *[[sample("a", t, 0.5)] for t in (1, 2, 3, 4)])
    put(server, "other", [sample("x", 9, 0.9)])

    def seqs(ticket):
        reader = fl.connect(location(server)).do_get(fl.Ticket(json.dumps(ticket).encode()))
        meta = reader.schema.metadata
        got = [json.loads(c.app_metadata.to_pybytes())["seq"] for c in reader]
        return got, int(meta[b"floor"])

    assert seqs({"table": "samples"}) == ([1, 2, 3, 4], 1)
    assert seqs({"table": "samples", "after": 1, "until": 3}) == ([2, 3], 1)
    assert seqs({"table": "samples", "after": None, "until": None}) == ([1, 2, 3, 4], 1)
    # A table nothing was sent to: no batches, and the floor is the next number.
    assert seqs({"table": "nothing"}) == ([], 6)


@pytest.mark.parametrize(
    ("descriptor", "schema", "error"),
    [
        (fl.FlightDescriptor.for_path("a", "b"), SAMPLES, "a path of one table name"),
        (fl.FlightDescriptor.for_command(b"samples"), SAMPLES, "a path of one table name"),
        (
            fl.FlightDescriptor.for_path("samples"),
            pa.schema([("host", pa.string())]),
            "samples: the batches' schema is not the table's",
        ),
    ],
)
def test_a_put_the_log_cannot_take_is_refused(server, descriptor, schema, error):
    put(server, "samples", [sample("a", 1, 0.5)])
    client = fl.connect(location(server))
    with pytest.raises(fl.FlightServerError, match=error):
        writer, _ = client.do_put(descriptor, schema)
        writer.write_batch(pa.RecordBatch.from_pylist([{"host": "a"}], schema=pa.schema(schema)))
        writer.close()
    client.close()
    # Nothing was stored.
    assert [s for s, _ in server.tables["samples"][1]] == [1]


def test_an_empty_batch_takes_no_number(server):
    client = fl.connect(location(server))
    writer, _ = client.do_put(fl.FlightDescriptor.for_path("samples"), SAMPLES)
    writer.write_batch(pa.RecordBatch.from_pylist([], schema=SAMPLES))
    writer.close()
    client.close()
    assert server.tables["samples"][1] == [] and server.seq == 0


def test_dropping_from_a_table_the_log_lacks_does_nothing(server):
    server.drop("nothing", below=5)
    assert server.tables == {}


class _NoFloor(fl.FlightServerBase):
    """A Flight server that streams a batch with no floor in its schema."""

    def do_get(self, context, ticket):
        return fl.RecordBatchStream(pa.table({"host": ["a"], "ts": [1], "cpu": [0.5]}))


def test_a_stream_without_a_floor_is_refused():
    s = _NoFloor("grpc://127.0.0.1:0")
    try:
        src = FlightSource(location(s), "samples", name="busy_samples", schema=SAMPLES)
        with pytest.raises(ValueError, match="busy_samples: the Flight stream names no floor"):
            src.read(None)
    finally:
        s.shutdown()


def test_an_unreachable_server_connects_again_on_the_next_read():
    s = FlightLog()
    port = s.port
    s.shutdown()
    src = FlightSource(f"grpc://127.0.0.1:{port}", "samples", schema=SAMPLES, timeout=2)
    with pytest.raises(fl.FlightUnavailableError):
        src.read(None)
    assert src._client is None


def test_a_source_pickles_without_its_connection(server):
    import pickle

    put(server, "samples", [sample("a", 1, 0.5)])
    src = FlightSource(location(server), "samples")
    read(src, None)
    assert src._client is not None
    copy = pickle.loads(pickle.dumps(src))
    assert copy._client is None and src._client is not None
    assert list(copy._held) == [1] and repr(copy) == repr(src)
    # The copy connects again when it reads.
    put(server, "samples", [sample("a", 2, 0.6)])
    assert read(copy, {"seq": 1, "floor": 1}).cursor == {"seq": 2, "floor": 1}


def test_an_audit_before_any_read_compares_no_rows(server):
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    busy(src).refresh()
    assert src.reread(None).num_rows == 0
    assert src.reread(None).schema == src.snapshot().table.schema


def test_a_cursor_of_another_shape_does_not_restore(server):
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    for bad in (None, 3, {"seq": 3}, {"floor": 1}, "seq"):
        assert src.restore(bad) is None
