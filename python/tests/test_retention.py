"""Retention by watermark (#294): `arrives_within` on a source, checked on
every batch, and a view over time buckets of it that drops the final buckets
from its state (`sverify._retention`, `SubstraitLean/Retention.lean`)."""

import math
import random
from collections import Counter
from datetime import datetime, timedelta

import pyarrow as pa
import pytest
from deltalake import write_deltalake
from ibis import _

import sverify as sv
from _pipelines import recomputed
from sverify._state import arrow_of
from sverify.errors import PreconditionError
from sverify.io import Changes, DeltaSink, DeltaSource, Sink, StaticSource, sink_from

T0 = datetime(2026, 11, 3)
SCHEMA = pa.schema([("host", pa.string()), ("ts", pa.timestamp("us")), ("cpu", pa.int64())])
BOUNDS = [_.ts >= datetime(2000, 1, 1), _.ts < datetime(2100, 1, 1), _.cpu.notnull()]


def samples(rows) -> pa.Table:
    """`(host, ts, cpu)` rows, `ts` in minutes after `T0`."""
    return pa.table(
        {
            "host": [h for h, _, _ in rows],
            "ts": [T0 + timedelta(minutes=m) for _, m, _ in rows],
            "cpu": [c for _, _, c in rows],
        },
        schema=SCHEMA,
    )


def rollup(lateness=timedelta(hours=2), bucket=lambda ts: ts.truncate("h")):
    @sv.transform(requires={"samples": [sv.arrives_within("ts", lateness), *BOUNDS]})
    def hourly(samples):
        return samples.group_by(["host", bucket(samples.ts).name("bucket")]).aggregate(
            n=samples.count(), cpu=samples.cpu.sum(), peak=samples.cpu.max()
        )

    return hourly


def view(node):
    assert node._stage is not None
    return node._stage.view


def state_rows(node) -> int:
    return arrow_of(view(node).state).num_rows


class Recorder(Sink):
    """A sink that applies each change to its rows, and keeps what the view
    retires."""

    keeps_retired = True

    def __init__(self, name="rollup"):
        super().__init__(name)
        self.rows: Counter = Counter()

    def write(self, change):
        if change.replace:
            self.rows = Counter()
        self.rows.update(tuple(r.values()) for r in change.inserts.to_pylist())
        self.rows.subtract(tuple(r.values()) for r in change.deletes.to_pylist())
        self.rows = +self.rows

    def sorted(self):
        return sorted(self.rows.elements(), key=repr)


def arrivals(out) -> str:
    """How a node's refresh checked `arrives_within`."""
    assert out.report is not None
    [found] = [p for p in out.report.preconditions if p.condition.startswith("arrives_within")]
    return found.source


def full(node, src):
    return sorted(recomputed(node, src), key=repr)


# -- the state stays bounded --------------------------------------------------


@pytest.mark.slow
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_long_stream_keeps_its_state_bounded(engine):
    src = StaticSource(samples([("a", m, 1) for m in range(0, 60, 10)]), name="samples")
    node = src.pipe(rollup())
    node.refresh(engine=engine)
    bound = math.ceil(2 / 1) + 1
    sizes = []
    for minute in range(60, 60 * 48, 10):
        src.apply(Changes(inserts=samples([("a", minute, 1), ("b", minute, 2)])))
        entry = node.refresh(engine=engine)["hourly"]
        (report,) = entry.retention
        assert report.open <= report.bound == bound
        sizes.append(state_rows(node))
    # Two hosts, at most `bound` buckets each, after two days of samples.
    assert max(sizes) <= 2 * bound
    assert sizes[-1] == 2 * bound
    # The latest sample is at 47:50: buckets up to 44:50 are final.
    assert view(node).retired_through == T0 + timedelta(hours=44, minutes=50)


def test_the_report_counts_open_and_retired_buckets():
    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    node = src.pipe(rollup())
    entry = node.refresh()["hourly"]
    (report,) = entry.retention
    # Latest 4:30, watermark 2:30: buckets 0:00 and 1:00 are final.
    assert (report.open, report.retired, report.bound, report.rows) == (3, 2, 3, 3)
    assert report.watermark == T0 + timedelta(hours=2, minutes=30)
    assert "3 bucket(s) open (bound 3), 2 retired" in str(entry)
    assert [
        r[1] for r in sorted(map(tuple, (r.values() for r in node.to_arrow().to_pylist())))
    ] == [T0 + timedelta(hours=h) for h in (2, 3, 4)]


def test_the_summary_shows_open_and_retired_buckets():
    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    node = src.pipe(rollup())
    node.refresh()
    # 5:30 moves the watermark to 3:30: bucket 2:00 is final, 5:00 opens.
    src.apply(Changes(inserts=samples([("a", 330, 1)])))
    line = node.refresh()["hourly"].summary()
    assert "\n" not in line
    assert line.endswith("bucket: 3/3 bucket(s) open, 1 retired")
    assert "requires checked on 1 row(s)" in line


@pytest.mark.slow
@pytest.mark.parametrize(
    ("lateness", "bound"),
    [
        (timedelta(0), 1),
        (timedelta(minutes=30), 2),
        (timedelta(minutes=90), 3),
        (timedelta(hours=2), 3),
    ],
)
def test_the_bound_is_lateness_over_width_plus_one(lateness, bound):
    src = StaticSource(samples([("a", 0, 1)]), name="samples")
    node = src.pipe(rollup(lateness))
    node.refresh()
    rng = random.Random(7)
    latest, most = 0, 0
    for _step in range(200):
        latest += rng.randrange(0, 25)
        wm = latest - lateness / timedelta(minutes=1)
        ts = [rng.uniform(max(wm, 0), latest) for _ in range(3)]
        rows = [("a", t, 1) for t in ts] + [("a", latest, 1)]
        src.apply(Changes(inserts=samples(rows)))
        (report,) = node.refresh()["hourly"].retention
        assert report.bound == bound
        assert report.open <= bound
        most = max(most, report.open)
    assert most == bound


# -- the precondition ---------------------------------------------------------


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_late_row_is_rejected(engine):
    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    node = src.pipe(rollup())
    node.refresh(engine=engine)
    before = (sorted(map(repr, node.to_arrow().to_pylist())), node.versions)
    # The watermark is 2:30; a row at 2:00 is late, one at 2:30 is not.
    src.apply(Changes(inserts=samples([("a", 120, 5)])))
    with pytest.raises(
        PreconditionError,
        match=r"1 inserted row\(s\) of samples violate "
        r"arrives_within\(ts, 2h\): ts before the watermark 2026-11-03 02:30",
    ):
        node.refresh(engine=engine)
    assert (sorted(map(repr, node.to_arrow().to_pylist())), node.versions) == before


def test_a_delete_in_a_final_bucket_is_an_expiry():
    rows = [("a", m, 1) for m in range(0, 300, 30)]
    src = StaticSource(samples(rows), name="samples")
    sink = Recorder()
    node = src.pipe(rollup()).write(sink)
    node.refresh()
    kept = sink.sorted()
    # The latest is 4:30 and the watermark 2:30: the hours before 2:00 are
    # final, so deleting the row at 0:00 is the source's retention.
    src.apply(Changes(deletes=samples([rows[0]])))
    out = node.refresh()["rollup"]
    assert arrivals(out).endswith("1 expired row(s) deleted from final buckets")
    assert sink.sorted() == kept
    # The row at 2:00 is before the watermark, in the hour that is still open.
    src.apply(Changes(deletes=samples([rows[4]])))
    with pytest.raises(PreconditionError, match=r"1 deleted row\(s\) of samples .* not final yet"):
        node.refresh()
    assert sink.sorted() == kept


def test_without_a_view_that_retires_every_early_delete_is_an_expiry():
    rows = [("a", m, 1) for m in range(0, 300, 30)]
    src = StaticSource(samples(rows), name="samples")
    node = src.pipe(rollup()).write(sink_from(lambda change: None, name="rollup"))
    node.refresh()
    src.apply(Changes(deletes=samples([rows[4]])))
    node.refresh()
    # The view keeps every bucket and applies the delete.
    assert sorted(map(tuple, (r.values() for r in node.to_arrow().to_pylist()))) == full(node, src)


def test_null_times_are_rejected():
    rows = samples([("a", 0, 1)])
    nulls = rows.set_column(1, "ts", pa.array([None], pa.timestamp("us")))
    with pytest.raises(PreconditionError, match="ts is NULL"):
        StaticSource(pa.concat_tables([rows, nulls]), name="samples").pipe(rollup()).refresh()
    src = StaticSource(rows, name="samples")
    node = src.pipe(rollup())
    node.refresh()
    src.apply(Changes(inserts=nulls))
    with pytest.raises(PreconditionError, match="ts is NULL; the batch was rejected"):
        node.refresh()


def test_arrives_within_needs_a_timestamp_and_no_negative_lateness():
    with pytest.raises(ValueError, match="lateness of 0 or more"):
        sv.arrives_within("ts", timedelta(hours=-1))

    @sv.transform(requires={"t": [sv.arrives_within("cpu", "PT1H")]})
    def keep(t):
        return t

    with pytest.raises(ValueError, match="not a timestamp"):
        StaticSource(samples([("a", 0, 1)]), name="t").pipe(keep).refresh()


def test_verify_does_not_prove_lateness():
    report = sv.verify(
        "select * from t", tables={"t": SCHEMA}, ensures=[sv.arrives_within("ts", "PT1H")]
    )
    assert not report.proved
    assert report.ensures[0].value == "lateness is checked on a source's batches"


# -- equality with a full recompute --------------------------------------------


def random_stream(seed, batches=80, expire=False):
    """Batches that respect a lateness of 2 h: every insert and delete at or
    after the latest time seen before the batch, minus 2 h. With `expire`,
    batches also delete rows of the final hours (the source's retention)."""
    rng = random.Random(seed)
    first = [(rng.choice("ab"), m, rng.randrange(100)) for m in range(0, 240, 20)]
    live = list(first)
    latest = max(m for _h, m, _c in first)
    out = []
    for _step in range(batches):
        wm = latest - 120
        top = latest + rng.randrange(0, 45)
        ins = [
            (rng.choice("abc"), rng.randrange(wm, top + 1), rng.randrange(100))
            for _ in range(rng.randrange(4))
        ]
        late_enough = [r for r in live if r[1] >= wm]
        dels = rng.sample(late_enough, min(len(late_enough), rng.randrange(3)))
        # Hours that end at or before the watermark are final.
        final = [r for r in live if r[1] < (wm // 60) * 60 and r not in dels]
        if expire and final:
            dels += rng.sample(final, min(len(final), rng.randrange(3)))
        for d in dels:
            live.remove(d)
        live += ins
        if ins:
            latest = max(latest, *(m for _h, m, _c in ins))
        out.append((ins, dels))
    return first, out


@pytest.mark.slow
@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("seed", range(4))
@pytest.mark.parametrize("expire", [False, True])
def test_retention_matches_a_full_recompute(seed, engine, expire):
    first, stream = random_stream(seed, expire=expire)
    src = StaticSource(samples(first), name="samples")
    # Every row inserted, less the deletes after the watermark: what the
    # sink holds when the source expires rows of final buckets.
    history = StaticSource(samples(first), name="samples")
    sink = Recorder()
    node = src.pipe(rollup()).write(sink)
    node.refresh(engine=engine)
    retired = 0
    for ins, dels in stream:
        latest = max(view(node).pipeline.latest.values())
        wm = (latest - T0) / timedelta(minutes=1) - 120
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
        history.apply(
            Changes(inserts=samples(ins), deletes=samples([d for d in dels if d[1] >= wm]))
        )
        entry = node.refresh(engine=engine)["rollup"]
        retired += entry.retention[0].retired
        want = full(node, history)
        # The sink has every bucket; the state the open ones.
        assert sink.sorted() == want
        cut = view(node).retired_through
        kept = sorted((r for r in want if cut is None or r[1] > cut), key=repr)
        state = sorted(map(tuple, (r.values() for r in node.to_arrow().to_pylist())), key=repr)
        assert state == kept
    assert retired > 0


@pytest.mark.slow
def test_a_bucket_expression_with_an_offset():
    src = StaticSource(samples([("a", m, 1) for m in range(0, 240, 5)]), name="samples")
    sink = Recorder()
    bucket = lambda ts: ts.bucket(minutes=15, offset=sv_minutes(5))  # noqa: E731
    node = src.pipe(rollup(timedelta(minutes=30), bucket)).write(sink)
    (report,) = node.refresh()["rollup"].retention
    assert (report.bound, report.open) == (3, 3)
    for m in range(240, 400, 5):
        src.apply(Changes(inserts=samples([("a", m, 1)])))
        node.refresh()
    assert sink.sorted() == full(node, src)
    assert state_rows(node) <= 3


def sv_minutes(n):
    import ibis

    return ibis.interval(minutes=n)


# -- sinks and restarts --------------------------------------------------------


def test_a_sink_that_rewrites_whole_tables_turns_retention_off():
    written = []
    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    node = src.pipe(rollup()).write(sink_from(written.append, name="rollup"))
    (report,) = node.refresh()["rollup"].retention
    assert report.off is not None and "may rewrite its whole table" in report.off
    assert state_rows(node) == 5


def test_an_aggregate_under_a_projection_retires_its_buckets():
    """#394: a projection over the aggregate reads only its own row, though
    its fields lead into the aggregate's reductions."""

    @sv.transform(requires={"samples": [sv.arrives_within("ts", "PT2H"), *BOUNDS]})
    def percent(samples):
        g = samples.group_by(["host", samples.ts.truncate("h").name("bucket")]).aggregate(
            peak=samples.cpu.max()
        )
        return g.filter(g.peak >= 0).select("host", "bucket", pct=g.peak / 10)

    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    sink = Recorder("percent")
    node = src.pipe(percent).write(sink)
    (report,) = node.refresh()["percent"].retention
    assert report.off is None
    assert (report.open, report.retired) == (3, 2)
    src.apply(Changes(inserts=samples([("a", 330, 5)])))
    (report,) = node.refresh()["percent"].retention
    assert report.retired == 1
    assert sink.sorted() == full(node, src)


@pytest.mark.parametrize(
    ("body", "reason"),
    [
        (lambda t: t.filter(t.cpu > 0), "not an aggregate"),
        (lambda t: t.group_by(m=t.ts.truncate("M")).aggregate(n=t.count()), "no fixed width"),
        (lambda t: t.group_by("host").aggregate(n=t.count()), "no GROUP BY key"),
    ],
)
def test_views_retention_does_not_apply_to_say_why(body, reason):
    @sv.transform(requires={"samples": [sv.arrives_within("ts", "PT2H"), *BOUNDS]})
    def other(samples):
        return body(samples)

    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    (report,) = src.pipe(other).refresh()["other"].retention
    assert report.off is not None and reason in report.off


@pytest.mark.slow
def test_a_delta_sink_keeps_the_retired_buckets_across_a_restart(tmp_path):
    uri = str(tmp_path / "samples")
    write_deltalake(
        uri,
        samples([("a", m, 1) for m in range(0, 300, 10)]),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    out = str(tmp_path / "rollup")

    def job():
        return DeltaSource(uri).pipe(rollup()).write(DeltaSink(out))

    node = job()
    node.refresh()
    for m in range(300, 600, 10):
        write_deltalake(uri, samples([("a", m, 1), ("b", m, 3)]), mode="append")
        (report,) = node.refresh()["rollup"].retention
        assert report.open <= 3 and state_rows(node) <= 6
    stored = sorted(map(tuple, (r.values() for r in DeltaSource(out).snapshot().table.to_pylist())))
    assert stored == sorted(recomputed(node, DeltaSource(uri)))
    # A restarted job resumes from the sink, drops the final buckets again,
    # and goes on with the watermark of the source.
    write_deltalake(uri, samples([("a", 600, 1)]), mode="append")
    again = job()
    entry = again.refresh()["rollup"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    (report,) = entry.retention
    assert report.retired > 0 and report.open == 3 and state_rows(again) == 5
    stored = sorted(map(tuple, (r.values() for r in DeltaSource(out).snapshot().table.to_pylist())))
    assert stored == sorted(recomputed(again, DeltaSource(uri)))
    write_deltalake(uri, samples([("a", 400, 1)]), mode="append")
    with pytest.raises(PreconditionError, match="violate arrives_within"):
        again.refresh()


def test_a_pipeline_reports_retention_without_nodes():
    from sverify.incremental import Pipeline

    src = StaticSource(samples([("a", m, 1) for m in range(0, 300, 30)]), name="samples")
    con = sv.connect()
    pipe = Pipeline(con)
    table = pipe.source("samples", src)
    v = pipe.view("hourly", rollup()(table))
    assert v.retention is not None and v.retention.bound == 3
    src.apply(Changes(inserts=samples([("a", 300, 1)])))
    report = pipe.refresh()
    (r,) = report.retention
    assert (r.view, r.column, r.open, r.retired) == ("hourly", "bucket", 3, 3)
    assert "retention hourly.bucket" in str(report)


# -- a source with its own retention ----------------------------------------------


def flight_job(log, sink):
    from sverify.io.flight import FlightSource

    src = FlightSource(f"grpc://127.0.0.1:{log.port}", "samples", schema=SCHEMA)
    return src.pipe(rollup()).write(sink)


def put_hour(log, hour):
    """One batch: both hosts' samples of hour `hour`, every 10 minutes."""
    fl = pytest.importorskip("pyarrow.flight")
    client = fl.connect(f"grpc://127.0.0.1:{log.port}")
    writer, acks = client.do_put(fl.FlightDescriptor.for_path("samples"), SCHEMA)
    rows = [(h, 60 * hour + m, m) for m in range(0, 60, 10) for h in "ab"]
    writer.write_batch(samples(rows).to_batches()[0])
    acks.read()
    writer.close()
    client.close()
    return rows


@pytest.mark.slow
def test_a_flight_log_that_expires_batches():
    pytest.importorskip("pyarrow.flight")
    from sverify.testing import FlightLog

    # The log keeps 4 one-hour batches; with 2 h of lateness, a batch
    # expires once its hour is final.
    log = FlightLog(keep=4)
    try:
        sink = Recorder()
        node = flight_job(log, sink)
        history = StaticSource(samples([]), name="samples")
        for hour in range(12):
            history.apply(Changes(inserts=samples(put_hour(log, hour))))
            out = node.refresh()["rollup"]
            (report,) = out.retention
            assert report.off is None and report.open <= report.bound == 3
            assert sink.sorted() == full(node, history)
        assert arrivals(out).endswith("12 expired row(s) deleted from final buckets")
    finally:
        log.shutdown()
    # A log that keeps 3 batches expires rows before the watermark of an
    # hour that is still open: at 3:00 the watermark is 0:50.
    log = FlightLog(keep=3)
    try:
        node = flight_job(log, Recorder())
        for hour in range(3):
            put_hour(log, hour)
        node.refresh()
        put_hour(log, 3)
        with pytest.raises(PreconditionError, match="not final yet"):
            node.refresh()
    finally:
        log.shutdown()
