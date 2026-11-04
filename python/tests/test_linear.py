"""Delta rules for COUNT, SUM and DISTINCT (`sverify._linear`,
`SubstraitLean/IncrementalAgg.lean`, #248): the view keeps a state per group
and adds each batch's change to it, and its rows equal a full recompute over
random change streams."""

import random

import pyarrow as pa
import pytest

import sverify as sv
from _pipelines import recomputed, rows
from sverify._state import arrow_of
from sverify.io import StaticSource

SCHEMA = pa.schema([("host", pa.string()), ("minute", pa.int64()), ("cpu", pa.int64())])
ENGINES = ["duckdb", "polars", "datafusion"]


def samples(rows) -> pa.Table:
    return pa.table(
        {n: [r[i] for r in rows] for i, n in enumerate(SCHEMA.names)},
        schema=SCHEMA,
    )


def per_minute(samples):
    return samples.group_by(["host", "minute"]).aggregate(
        n=samples.count(),
        total=samples.cpu.sum(),
        values=samples.cpu.count(),
        hot=samples.cpu.sum(where=samples.cpu > 10),
        cold=samples.count(where=samples.cpu < 0),
    )


def view(node):
    assert node._stage is not None
    return node._stage.view


def random_batches(seed, steps=40):
    """Inserts and deletes over few keys, NULLs among them, so that groups
    appear, grow, shrink and disappear."""
    rng = random.Random(seed)
    hosts = ["a", "b", None]
    live: list[tuple[str | None, int, int | None]] = [
        (rng.choice(hosts), rng.randrange(4), rng.randrange(-50, 50)) for _ in range(12)
    ]
    first = list(live)
    out = []
    for _ in range(steps):
        ins = [
            (rng.choice(hosts), rng.randrange(5), rng.choice([None, rng.randrange(-50, 50)]))
            for _ in range(rng.randrange(4))
        ]
        dels = rng.sample(live, min(len(live), rng.randrange(4)))
        for d in dels:
            live.remove(d)
        live += ins
        out.append((ins, dels))
    return first, out


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("seed", range(3))
def test_count_and_sum_match_a_full_recompute(seed, engine):
    first, batches = random_batches(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(per_minute)
    node.refresh(engine=engine)
    assert view(node).strategy == "delta rules"
    for ins, dels in batches:
        src.apply(sv.Changes(inserts=samples(ins), deletes=samples(dels)))
        out = node.refresh(engine=engine)["per_minute"]
        assert out.report is not None
        assert not out.report.touched and not out.report.diffed
        assert rows(node) == recomputed(node, src)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("seed", range(3))
def test_distinct_matches_a_full_recompute(seed, engine):
    first, batches = random_batches(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(keys)
    node.refresh(engine=engine)
    assert view(node).strategy == "delta rules"
    for ins, dels in batches:
        src.apply(sv.Changes(inserts=samples(ins), deletes=samples(dels)))
        node.refresh(engine=engine)
        assert rows(node) == recomputed(node, src)


def test_groups_appear_and_disappear():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    src.apply(sv.Changes(inserts=samples([("b", 2, None), ("b", 2, 20)])))
    node.refresh(audit=True)
    assert rows(node) == [("a", 1, 1, 5, 1, None, 0), ("b", 2, 2, 20, 1, 20, 0)]
    src.apply(sv.Changes(deletes=samples([("a", 1, 5), ("b", 2, 20)])))
    node.refresh(audit=True)
    # SUM of no values is NULL; the group stays while it has a row.
    assert rows(node) == [("b", 2, 1, None, 0, None, 0)]
    src.apply(sv.Changes(deletes=samples([("b", 2, None)])))
    node.refresh(audit=True)
    assert rows(node) == []
    assert view(node).groups.num_rows == 0


def keys(samples):
    return samples.select("host", "minute").distinct()


def test_distinct_keeps_a_row_while_it_has_copies():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(keys)
    node.refresh()
    for batch, want in [
        (sv.Changes(inserts=samples([("a", 1, 6)])), [("a", 1)]),
        (sv.Changes(deletes=samples([("a", 1, 5)])), [("a", 1)]),
        (sv.Changes(deletes=samples([("a", 1, 6)])), []),
        (sv.Changes(inserts=samples([("a", 1, 7), (None, 2, 1)])), [("a", 1), (None, 2)]),
    ]:
        src.apply(batch)
        node.refresh(audit=True)
        assert rows(node) == want


def test_status_says_the_view_is_maintained():
    src = StaticSource(samples([("a", 1, 5), ("b", 1, 3)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    status = node.status().nodes[0]
    assert status.recomputed is None and status.touched is None
    assert "recomputed" not in str(node.status())
    src.apply(sv.Changes(inserts=samples([("a", 1, 9)])))
    out = node.refresh()["per_minute"]
    assert "recomputed" not in out.summary()
    assert rows(node) == recomputed(node, src)


def test_a_filter_and_projection_over_the_aggregate():
    def busy(samples):
        t = per_minute(samples)
        return t.filter(t.n > 1).select("minute", "host", "total")

    src = StaticSource(samples([("a", 1, 5), ("a", 1, 7), ("b", 1, 3)]), name="samples")
    node = src.pipe(busy)
    node.refresh()
    assert view(node).strategy == "delta rules"
    for batch in [
        sv.Changes(inserts=samples([("b", 1, 9)])),
        sv.Changes(deletes=samples([("a", 1, 7)])),
        sv.Changes(inserts=samples([("a", 1, 1), ("c", 4, 2), ("c", 4, 8)])),
    ]:
        src.apply(batch)
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, src)


def test_an_aggregate_over_a_join():
    hosts = pa.table({"host": ["a", "b"], "team": ["x", "y"]})

    def by_team(samples, hosts):
        j = samples.join(hosts, "host")
        return j.group_by(["team", "minute"]).aggregate(total=j.cpu.sum(), n=j.count())

    src = StaticSource(samples([("a", 1, 5), ("b", 1, 3)]), name="samples")
    teams = StaticSource(hosts, name="hosts")
    node = src.pipe(by_team, hosts=teams)
    node.refresh()
    assert view(node).strategy == "delta rules"
    src.apply(sv.Changes(inserts=samples([("a", 1, 9), ("b", 2, 1)])))
    teams.apply(sv.Changes(inserts=pa.table({"host": ["c"], "team": ["x"]})))
    node.refresh(audit=True)
    src.apply(sv.Changes(inserts=samples([("c", 1, 20)]), deletes=samples([("a", 1, 9)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src, teams)


def test_other_measures_keep_touched_groups():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(
        lambda samples: samples.group_by("host").aggregate(top=samples.cpu.max(), n=samples.count())
    )
    node.refresh()
    assert view(node).strategy == "touched groups"


def test_a_maintained_sum_that_leaves_64_bits_raises_and_changes_nothing():
    big = 2**62
    src = StaticSource(samples([("a", 1, big)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    before = rows(node)
    src.apply(sv.Changes(inserts=samples([("a", 1, big), ("b", 1, 1)])))
    with pytest.raises(Exception, match="(?i)overflow|out of range|64"):
        node.refresh()
    assert rows(node) == before
    # Deleting the first value brings the sum back within 64 bits.
    src.apply(sv.Changes(deletes=samples([("a", 1, big)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src)


@pytest.mark.parametrize("seed", range(2))
@pytest.mark.parametrize("expire", [False, True])
def test_retention_drops_the_retired_groups_from_the_state(seed, expire):
    import test_retention as tr

    @sv.transform(requires={"samples": [sv.arrives_within("ts", seconds=7200), *tr.BOUNDS]})
    def hourly(samples):
        return samples.group_by(["host", samples.ts.truncate("h").name("bucket")]).aggregate(
            n=samples.count(), cpu=samples.cpu.sum()
        )

    first, stream = tr.random_stream(seed, expire=expire)
    src = StaticSource(tr.samples(first), name="samples")
    history = StaticSource(tr.samples(first), name="samples")
    sink = tr.Recorder()
    node = src.pipe(hourly).write(sink)
    node.refresh()
    assert view(node).strategy == "delta rules"
    retired = 0
    for ins, dels in stream:
        latest = max(view(node).pipeline.latest.values())
        wm = (latest - tr.T0) / tr.timedelta(minutes=1) - 120
        src.apply(sv.Changes(inserts=tr.samples(ins), deletes=tr.samples(dels)))
        history.apply(
            sv.Changes(inserts=tr.samples(ins), deletes=tr.samples([d for d in dels if d[1] >= wm]))
        )
        retired += node.refresh()[node.name].retention[0].retired
        assert sink.sorted() == tr.full(node, history)
        # The state per group holds the open buckets only, like the view.
        assert view(node).groups.num_rows == arrow_of(view(node).state).num_rows
    assert retired > 0
