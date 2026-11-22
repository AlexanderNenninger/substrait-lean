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
    assert cursor(src) == {"seq": 4, "floor": 1, "log": server.id}
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
    assert (batch.kind, batch.cursor) == ("append", {"seq": 3, "floor": 1, "log": server.id})
    assert batch.table.to_pylist() == [sample("a", 3, 0.7)]
    server.drop("samples", below=2)
    batch = read(resumed, batch.cursor)
    assert (batch.kind, batch.cursor, batch.table.num_rows) == (
        "changes",
        {"seq": 3, "floor": 2, "log": server.id},
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
        .restore({"seq": 0, "floor": 1, "log": server.id})
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
    assert recorded is not None and recorded.cursors == {
        "samples": {"seq": 2, "floor": 1, "log": server.id}
    }
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


# -- a server that restarted numbers its batches from 1 again ----------------------


def restarted(server):
    """A new log at the address of `server`, which is shut down: batches from 1
    again, under another identity."""
    port = server.port
    server.shutdown()
    return FlightLog(f"grpc://127.0.0.1:{port}")


def test_a_restarted_log_is_another_log(server):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)], [sample("a", 3, 0.7)])
    src = FlightSource(location(server), "samples")
    busy(src).refresh()
    recorded = cursor(src)
    assert recorded["seq"] == 3 and recorded["log"] == server.id
    old = server.id
    new = restarted(server)
    try:
        assert new.id != old
        put(new, "samples", [sample("b", 1, 0.5)], [sample("b", 2, 0.6)], [sample("b", 3, 0.7)])
        # A refresh of the running source asks for the batches after 3: it
        # refuses, where it used to skip batch 3 of the new log.
        with pytest.raises(ValueError, match="now serves the log") as e:
            src.read(recorded)
        assert str(old) in str(e.value) and str(new.id) in str(e.value)
        assert "new sink" in str(e.value)
        # So does a source restored at the cursor a sink recorded.
        with pytest.raises(ValueError, match="now serves the log"):
            FlightSource(location(new), "samples", schema=SAMPLES).restore(recorded)
        # And the audit's read up to the cursor.
        with pytest.raises(ValueError, match="now serves the log"):
            src.reread(recorded)
        # Reading the new log from the start is the other source's choice.
        fresh = FlightSource(location(new), "samples")
        batch = read(fresh, None)
        assert batch.table.num_rows == 3
        assert batch.cursor == {"seq": 3, "floor": 1, "log": new.id}
    finally:
        new.shutdown()


def test_a_cursor_that_names_no_log_is_refused_by_a_server_that_names_one(server):
    put(server, "samples", [sample("a", 1, 0.5)])
    old_cursor = {"seq": 1, "floor": 1}  # recorded before logs had identities
    src = FlightSource(location(server), "samples", schema=SAMPLES)
    with pytest.raises(ValueError, match="a log that was not named"):
        src.restore(old_cursor)
    with pytest.raises(ValueError, match="a log that was not named"):
        src.read(old_cursor)


def test_a_restarted_job_is_refused_by_the_log_it_did_not_read(server, tmp_path):
    path = str(tmp_path / "busy")
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    restart_job(server, path)[1].refresh()
    new = restarted(server)
    try:
        put(new, "samples", [sample("b", 1, 0.5)], [sample("b", 2, 0.6)], [sample("b", 3, 0.7)])
        _, job = restart_job(new, path)
        with pytest.raises(ValueError, match="now serves the log"):
            job.refresh()
        assert stored_ts(path) == [1, 2]  # nothing of the new log was written
    finally:
        new.shutdown()


def test_a_server_that_names_no_log_is_read_as_before(server):
    """A server of another make names no log: its cursors carry none, and a
    cursor with or without one reads and restores."""
    server.id = None
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    src = FlightSource(location(server), "samples")
    batch = read(src, None)
    assert batch.cursor == {"seq": 2, "floor": 1}
    put(server, "samples", [sample("a", 3, 0.7)])
    resumed = FlightSource(location(server), "samples", schema=SAMPLES)
    assert resumed.restore(batch.cursor).num_rows == 2
    assert read(resumed, batch.cursor).cursor == {"seq": 3, "floor": 1}
    # A cursor an earlier run recorded against a log that named one reads too.
    named = {"seq": 2, "floor": 1, "log": "an-earlier-log"}
    assert resumed.restore(named).num_rows == 2
    assert read(resumed, named).table.to_pylist() == [sample("a", 3, 0.7)]
    assert resumed.reread(named).num_rows == 2


def test_the_audit_refuses_a_restarted_log(server, tmp_path):
    put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)])
    src = FlightSource(location(server), "samples")
    node = busy(src)
    node.refresh()
    new = restarted(server)
    try:
        put(new, "samples", [sample("b", 1, 0.5)], [sample("b", 2, 0.6)], [sample("b", 3, 0.7)])
        with pytest.raises(ValueError, match="now serves the log"):
            node.refresh(audit=True)
    finally:
        new.shutdown()


# -- two writers of one sink that read different servers (#2441) --------------------


def test_a_second_writer_reading_another_server_is_refused(server, tmp_path):
    """Two nodes share a sink and its app id, and read different servers
    under one source name. A Flight source has no table id, so versions were
    all that told them apart; the contract names the source now."""
    path = str(tmp_path / "busy")
    other = FlightLog()
    # Servers that name no log (a log that does names itself: the cursor of
    # the first server is refused by the second, `test_a_restarted_log_...`).
    server.id = other.id = None
    try:
        put(server, "samples", [sample("a", 1, 0.5)], [sample("a", 2, 0.6)], [sample("a", 3, 0.7)])
        put(other, "samples", [sample("b", 1, 0.5)])
        first = busy(FlightSource(location(server), "samples", schema=SAMPLES)).write(
            DeltaSink(path)
        )
        first.refresh()
        recorded = DeltaSource(path).contract()
        assert recorded is not None
        assert recorded.fingerprints == {"samples": f"flight:{location(server)}/samples"}
        # The second writer is at a lower version (1 against 3), and refused.
        second = busy(FlightSource(location(other), "samples", schema=SAMPLES)).write(
            DeltaSink(path)
        )
        with pytest.raises(ValueError, match="Two writers with one app_id") as e:
            second.refresh()
        assert location(server) in str(e.value) and location(other) in str(e.value)
        # And one at a higher version (5 against 3).
        put(other, "samples", *[[sample("b", i, 0.5)] for i in range(2, 6)])
        third = busy(FlightSource(location(other), "samples", schema=SAMPLES)).write(
            DeltaSink(path)
        )
        with pytest.raises(ValueError, match="Two writers with one app_id"):
            third.refresh()
        assert stored_ts(path) == [1, 2, 3]  # nothing of the other server was written
        # The first writer goes on.
        put(server, "samples", [sample("a", 4, 0.8)])
        first.refresh()
        assert stored_ts(path) == [1, 2, 3, 4]
    finally:
        other.shutdown()


def test_a_record_without_fingerprints_is_not_compared():
    from sverify.io._common import Contract, check_same_sources

    def record(**kw):
        return Contract(
            node="n",
            plan="p" * 64,
            sources={"t": 1},
            epoch=1,
            not_null=[],
            checks={},
            unique=[],
            **kw,
        )

    old = record()  # written before fingerprints
    check_same_sources("sink", old, record(fingerprints={"t": "flight:x/t"}))
    check_same_sources("sink", record(fingerprints={"t": "flight:x/t"}), old)
    check_same_sources(
        "sink", record(fingerprints={"t": "flight:x/t"}), record(fingerprints={"t": "flight:x/t"})
    )
    with pytest.raises(ValueError, match="Two writers"):
        check_same_sources(
            "sink",
            record(fingerprints={"t": "flight:x/t"}),
            record(fingerprints={"t": "flight:y/t"}),
        )


def test_a_table_and_a_source_without_an_id_are_not_the_same_source(tmp_path):
    """Under one source name, a Delta table has an id and a static table has
    none, so the writers read different sources, in either order."""
    from _pipelines import make_orders, orders_table, paid
    from sverify.io import StaticSource

    rows = [(1, "ada", 5), (2, "ada", 5), (3, "bob", 1)]

    def static():
        return StaticSource(orders_table(rows), name="orders")

    for n, (first, second) in enumerate(
        [
            (lambda: make_orders(tmp_path / "x" / "orders", rows), static),
            (static, lambda: make_orders(tmp_path / "y" / "orders", rows)),
        ]
    ):
        path = str(tmp_path / f"sink{n}")
        paid(first()).write(DeltaSink(path)).refresh()
        with pytest.raises(ValueError, match="Two writers with one app_id"):
            paid(second()).write(DeltaSink(path)).refresh()


def test_the_fingerprint_of_a_location_with_userinfo_holds_no_secret():
    src = FlightSource("grpc://ada:s3cret@pi3:8815?token=t0k", "samples", schema=SAMPLES)
    assert src._fingerprint() == "flight:grpc://pi3:8815/samples"


def test_a_table_id_and_a_fingerprint_are_different_kinds_of_source():
    from sverify.io._common import Contract, check_same_sources

    def record(**kw):
        return Contract(
            node="n",
            plan="p" * 64,
            sources={"t": 1},
            epoch=1,
            not_null=[],
            checks={},
            unique=[],
            **kw,
        )

    table = record(table_ids={"t": "abc"}, sverify="1")
    flight = record(fingerprints={"t": "flight:grpc://x/t"}, sverify="1")
    for a, b in [(table, flight), (flight, table)]:
        with pytest.raises(ValueError, match="Two writers"):
            check_same_sources("sink", a, b)
    # A record from before `sverify` was recorded names neither: versions decide.
    old = record()
    check_same_sources("sink", old, table)
    check_same_sources("sink", old, flight)
