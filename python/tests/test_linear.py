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
from sverify.io import Changes, StaticSource

SCHEMA = pa.schema([("host", pa.string()), ("minute", pa.int64()), ("cpu", pa.int64())])
ENGINES = ["duckdb", "polars"]


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
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
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
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
        node.refresh(engine=engine)
        assert rows(node) == recomputed(node, src)


def test_groups_appear_and_disappear():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    src.apply(Changes(inserts=samples([("b", 2, None), ("b", 2, 20)])))
    node.refresh(audit=True)
    assert rows(node) == [("a", 1, 1, 5, 1, None, 0), ("b", 2, 2, 20, 1, 20, 0)]
    src.apply(Changes(deletes=samples([("a", 1, 5), ("b", 2, 20)])))
    node.refresh(audit=True)
    # SUM of no values is NULL; the group stays while it has a row.
    assert rows(node) == [("b", 2, 1, None, 0, None, 0)]
    src.apply(Changes(deletes=samples([("b", 2, None)])))
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
        (Changes(inserts=samples([("a", 1, 6)])), [("a", 1)]),
        (Changes(deletes=samples([("a", 1, 5)])), [("a", 1)]),
        (Changes(deletes=samples([("a", 1, 6)])), []),
        (Changes(inserts=samples([("a", 1, 7), (None, 2, 1)])), [("a", 1), (None, 2)]),
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
    src.apply(Changes(inserts=samples([("a", 1, 9)])))
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
        Changes(inserts=samples([("b", 1, 9)])),
        Changes(deletes=samples([("a", 1, 7)])),
        Changes(inserts=samples([("a", 1, 1), ("c", 4, 2), ("c", 4, 8)])),
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
    src.apply(Changes(inserts=samples([("a", 1, 9), ("b", 2, 1)])))
    teams.apply(Changes(inserts=pa.table({"host": ["c"], "team": ["x"]})))
    node.refresh(audit=True)
    src.apply(Changes(inserts=samples([("c", 1, 20)]), deletes=samples([("a", 1, 9)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src, teams)


def test_other_measures_keep_touched_groups():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(
        lambda samples: samples.group_by("host").aggregate(m=samples.cpu.mean(), n=samples.count())
    )
    node.refresh()
    assert view(node).strategy == "touched groups"


def test_a_maintained_sum_that_leaves_64_bits_raises_and_changes_nothing():
    big = 2**62
    src = StaticSource(samples([("a", 1, big)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    before = rows(node)
    src.apply(Changes(inserts=samples([("a", 1, big), ("b", 1, 1)])))
    with pytest.raises(Exception, match="(?i)overflow|out of range|64"):
        node.refresh()
    assert rows(node) == before
    # Deleting the first value brings the sum back within 64 bits.
    src.apply(Changes(deletes=samples([("a", 1, big)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src)


@pytest.mark.parametrize("seed", range(2))
@pytest.mark.parametrize("expire", [False, True])
@pytest.mark.parametrize("measure", ["sum", "max"])
def test_retention_drops_the_retired_groups_from_the_state(seed, expire, measure):
    import test_retention as tr

    @sv.transform(requires={"samples": [sv.arrives_within("ts", "PT2H"), *tr.BOUNDS]})
    def hourly(samples):
        cpu = samples.cpu.sum() if measure == "sum" else samples.cpu.max()
        return samples.group_by(["host", samples.ts.truncate("h").name("bucket")]).aggregate(
            n=samples.count(), cpu=cpu
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
        src.apply(Changes(inserts=tr.samples(ins), deletes=tr.samples(dels)))
        history.apply(
            Changes(inserts=tr.samples(ins), deletes=tr.samples([d for d in dels if d[1] >= wm]))
        )
        retired += node.refresh()[node.name].retention[0].retired
        assert sink.sorted() == tr.full(node, history)
        # The state per group holds the open buckets only, like the view.
        assert view(node).groups.num_rows == arrow_of(view(node).state).num_rows
    assert retired > 0


def test_count_of_a_string_column():
    src = StaticSource(samples([("a", 1, 5), (None, 1, 3)]), name="samples")
    node = src.pipe(lambda samples: samples.group_by("minute").aggregate(n=samples.host.count()))
    node.refresh()
    assert view(node).strategy == "delta rules"
    src.apply(Changes(inserts=samples([("b", 1, 1), (None, 2, 2)]), deletes=samples([("a", 1, 5)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src) == [(1, 1), (2, 0)]


def test_a_state_the_checker_refuses_falls_back(monkeypatch):
    from sverify import _linear

    def refuse(name, query):
        raise ValueError("substrait-check rejects the plan")

    monkeypatch.setattr(_linear, "plan", refuse)
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    assert view(node).strategy == "touched groups"
    src.apply(Changes(inserts=samples([("a", 1, 9)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src)


# -- MIN, MAX and exact AVG (#248, stage 2) --------------------------------------


def extremes(samples):
    return samples.group_by(["host", "minute"]).aggregate(
        n=samples.count(),
        low=samples.cpu.min(),
        high=samples.cpu.max(),
        hot=samples.cpu.max(where=samples.cpu < 10),
        total=samples.cpu.sum(),
    )


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("seed", range(3))
def test_min_and_max_match_a_full_recompute(seed, engine):
    first, batches = random_batches(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(extremes)
    node.refresh(engine=engine)
    assert view(node).strategy == "delta rules"
    assert view(node).linear.regroup is not None
    for ins, dels in batches:
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
        out = node.refresh(engine=engine)["extremes"]
        assert out.report is not None
        assert not out.report.touched and not out.report.diffed
        assert rows(node) == recomputed(node, src)


def test_inserts_merge_and_deletes_recompute_only_their_groups(monkeypatch):
    from sverify import incremental

    src = StaticSource(samples([("a", 1, 5), ("a", 1, 9), ("b", 1, 3)]), name="samples")
    node = src.pipe(extremes)
    node.refresh()
    regroup = view(node).linear.regroup
    keys = []
    real = incremental.run_plan_on

    def spy(con, plan, *a):
        if plan == regroup:
            keys.append(sorted(con.get(f"{view(node).name}$keys").to_pylist(), key=str))
        return real(con, plan, *a)

    monkeypatch.setattr(incremental, "run_plan_on", spy)
    # Only inserts: every group merges, the input is not read.
    src.apply(Changes(inserts=samples([("a", 1, 11), ("b", 1, 1), ("c", 2, None)])))
    node.refresh(audit=True)
    assert keys == []
    assert rows(node) == [
        ("a", 1, 3, 5, 11, 9, 25),
        ("b", 1, 2, 1, 3, 3, 4),
        ("c", 2, 1, None, None, None, None),
    ]
    # Deleting a's MAX: only a's group is recomputed.
    src.apply(Changes(deletes=samples([("a", 1, 11)]), inserts=samples([("b", 1, 0)])))
    node.refresh(audit=True)
    assert keys == [[{"k0": "a", "k1": 1}]]
    assert rows(node) == recomputed(node, src)
    assert rows(node)[0] == ("a", 1, 2, 5, 9, 9, 14)
    # Deleting a group's last rows removes it from the state and the view.
    src.apply(Changes(deletes=samples([("c", 2, None)])))
    node.refresh(audit=True)
    assert [r[0] for r in rows(node)] == ["a", "b"]
    assert view(node).groups.num_rows == 2


def test_a_filter_over_min_and_max():
    def spread(samples):
        t = extremes(samples)
        return t.filter(t.high > t.low).select("host", "minute", "high")

    src = StaticSource(samples([("a", 1, 5), ("a", 1, 7), ("b", 1, 3)]), name="samples")
    node = src.pipe(spread)
    node.refresh()
    assert view(node).strategy == "delta rules"
    for batch in [
        Changes(inserts=samples([("b", 1, 9)])),
        Changes(deletes=samples([("a", 1, 7)])),
        Changes(inserts=samples([("a", 1, 1), ("c", 4, 2), ("c", 4, 8)])),
        Changes(deletes=samples([("b", 1, 9), ("c", 4, 2)])),
    ]:
        src.apply(batch)
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, src)


def test_min_and_max_of_strings_and_dates():
    import datetime as d

    schema = pa.schema([("k", pa.int64()), ("s", pa.string()), ("day", pa.date32())])

    def table(rows):
        return pa.table(
            {n: [r[i] for r in rows] for i, n in enumerate(schema.names)}, schema=schema
        )

    def bounds(t):
        return t.group_by("k").aggregate(first=t.s.min(), last=t.s.max(), since=t.day.min())

    day = d.date(2026, 1, 1)
    src = StaticSource(table([(1, "b", day), (1, "c", None)]), name="t")
    node = src.pipe(bounds)
    node.refresh()
    assert view(node).strategy == "delta rules"
    for batch in [
        Changes(inserts=table([(1, "a", day - d.timedelta(1)), (2, None, None)])),
        Changes(deletes=table([(1, "a", day - d.timedelta(1))])),
        Changes(deletes=table([(1, "c", None)]), inserts=table([(2, "z", day)])),
    ]:
        src.apply(batch)
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, src)


DEC = pa.schema([("host", pa.string()), ("amount", pa.decimal128(10, 2))])


def amounts(rows) -> pa.Table:
    return pa.table(
        {n: [r[i] for r in rows] for i, n in enumerate(DEC.names)},
        schema=DEC,
    )


def decimal_means(t):
    return t.group_by("host").aggregate(
        mean=t.amount.mean(),
        total=t.amount.sum(),
        top=t.amount.max(),
        small=t.amount.mean(where=t.amount < 0),
    )


@pytest.mark.parametrize("seed", range(3))
def test_decimal_avg_and_sum_match_a_full_recompute(seed):
    from decimal import Decimal

    rng = random.Random(seed)

    def row():
        value = rng.choice([None, Decimal(rng.randrange(-10_000, 10_000)) / 100])
        return (rng.choice(["a", "b", None]), value)

    live = [row() for _ in range(10)]
    src = StaticSource(amounts(live), name="amounts")
    node = src.pipe(decimal_means)
    node.refresh()
    assert view(node).strategy == "delta rules"
    for _ in range(30):
        ins = [row() for _ in range(rng.randrange(4))]
        dels = rng.sample(live, min(len(live), rng.randrange(4)))
        for d in dels:
            live.remove(d)
        live += ins
        src.apply(Changes(inserts=amounts(ins), deletes=amounts(dels)))
        node.refresh()
        assert rows(node) == recomputed(node, src)


def test_a_decimal_avg_keeps_its_exact_type_and_rounds_half_away_from_zero():
    from decimal import Decimal as D

    src = StaticSource(amounts([("a", D("-36.20")), ("a", D("-36.19"))]), name="amounts")
    node = src.pipe(lambda t: t.group_by("host").aggregate(mean=t.amount.mean()))
    node.refresh()
    assert view(node).strategy == "delta rules"
    assert rows(node) == [("a", D("-36.195000"))]
    src.apply(Changes(inserts=amounts([("a", D("1.00")), ("b", None)])))
    node.refresh(audit=True)
    # -71.39 / 3 = -23.79666…: six decimal places, the last rounded.
    assert rows(node) == recomputed(node, src) == [("a", D("-23.796667")), ("b", None)]


def test_an_integer_avg_is_left_to_touched_groups():
    src = StaticSource(samples([("a", 1, 5)]), name="samples")
    node = src.pipe(lambda t: t.group_by("host").aggregate(m=t.cpu.mean()))
    node.refresh()
    assert view(node).strategy == "touched groups"
