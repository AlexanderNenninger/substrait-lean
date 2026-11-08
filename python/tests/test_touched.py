"""Touched-group recompute (`sverify._touched`, `SubstraitLean/TouchedGroups.lean`):
an aggregate without delta rules recomputes only the groups a batch touches,
and its state equals a full recompute."""

import random
from datetime import datetime, timedelta

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _engines import PROFILED, PROFILED_ORDERED
from _pipelines import recomputed, rows
from sverify import incremental
from sverify.io import Changes, StaticSource

SCHEMA = pa.schema([("host", pa.string()), ("minute", pa.int64()), ("cpu", pa.int64())])


def samples(rows) -> pa.Table:
    return pa.table(
        {n: [r[i] for r in rows] for i, n in enumerate(SCHEMA.names)},
        schema=SCHEMA,
    )


def per_minute(samples):
    return samples.group_by(["host", "minute"]).aggregate(
        n=samples.count(),
        total=samples.cpu.sum(),
        low=samples.cpu.min(),
        high=samples.cpu.max(),
        mean=samples.cpu.mean(),
    )


def view(node):
    assert node._stage is not None
    return node._stage.view


def stream(rng, start, row, steps, most):
    """30 rows from `start`, then `steps` batches, each inserting fewer than
    `most` rows from `row` and deleting up to two live rows."""
    live = [start() for _ in range(30)]
    first = list(live)
    out = []
    for _ in range(steps):
        ins = [row() for _ in range(rng.randrange(most))]
        dels = rng.sample(live, min(len(live), rng.randrange(3)))
        for d in dels:
            live.remove(d)
        live += ins
        out.append((ins, dels))
    return first, out


def random_batches(seed, steps=40):
    rng = random.Random(seed)
    hosts = ["a", "b", None]
    return stream(
        rng,
        lambda: (rng.choice(hosts), rng.randrange(10), rng.randrange(-50, 50)),
        lambda: (rng.choice(hosts), rng.randrange(12), rng.choice([None, rng.randrange(-50, 50)])),
        steps,
        4,
    )


#: Spark loses a NULL-key group in seeds 1 and 2 (#1006).
NULL_KEY_GROUPS = pytest.mark.xfail(
    strict=True, reason="Spark's touched-groups refresh loses a NULL-key group (#1006)"
)


@pytest.mark.parametrize(
    ("seed", "engine"),
    [
        (s, e) if not (e == "spark" and s in (1, 2)) else pytest.param(s, e, marks=NULL_KEY_GROUPS)
        for s in range(3)
        for e in PROFILED
    ],
)
def test_touched_groups_match_a_full_recompute(seed, engine):
    first, batches = random_batches(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(per_minute)
    node.refresh(engine=engine)
    assert view(node).strategy == "touched groups"
    for ins, dels in batches:
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
        out = node.refresh(engine=engine, audit=True)["per_minute"]
        assert out.report is not None
        touched = {(h, m) for h, m, _ in ins + dels}
        if touched:
            assert out.report.touched == {"per_minute": len(touched)}
        assert rows(node) == recomputed(node, src)


def test_status_and_summary_say_which_strategy_ran():
    src = StaticSource(samples([("a", 1, 5), ("a", 2, 7), ("b", 1, 3)]), name="samples")
    node = src.pipe(per_minute)
    node.refresh()
    assert "touched groups recomputed (no delta rules:" in str(node.status())
    assert node.status().nodes[0].recomputed is None
    src.apply(Changes(inserts=samples([("a", 1, 9)])))
    out = node.refresh()["per_minute"]
    assert "1 touched group(s) recomputed" in out.summary()
    assert "view per_minute: 1 touched group(s) recomputed" in str(out.report)
    assert rows(node) == recomputed(node, src)


def test_a_filter_and_projection_over_the_aggregate():
    def busy(samples):
        t = per_minute(samples)
        return t.filter(t.n > 1).select("minute", "host", "high")

    src = StaticSource(samples([("a", 1, 5), ("a", 1, 7), ("b", 1, 3)]), name="samples")
    node = src.pipe(busy)
    node.refresh()
    assert view(node).strategy == "touched groups"
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
        return j.group_by(["team", "minute"]).aggregate(peak=j.cpu.mean(), n=j.count())

    src = StaticSource(samples([("a", 1, 5), ("b", 1, 3)]), name="samples")
    teams = StaticSource(hosts, name="hosts")
    node = src.pipe(by_team, hosts=teams)
    node.refresh()
    assert view(node).strategy == "touched groups"
    src.apply(Changes(inserts=samples([("a", 1, 9), ("b", 2, 1)])))
    teams.apply(Changes(inserts=pa.table({"host": ["c"], "team": ["x"]})))
    node.refresh(audit=True)
    src.apply(Changes(inserts=samples([("c", 1, 20)]), deletes=samples([("a", 1, 9)])))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src, teams)


def test_an_input_without_delta_rules_is_recomputed_and_diffed():
    def busiest(samples):
        t = per_minute(samples)
        return t.group_by("host").aggregate(top=t.high.max())

    src = StaticSource(samples([("a", 1, 5), ("b", 1, 3)]), name="samples")
    node = src.pipe(busiest)
    node.refresh()
    assert view(node).strategy == "recompute and diff"
    assert "no touched groups: the aggregate's input has no delta rules" in str(node.status())
    src.apply(Changes(inserts=samples([("a", 2, 9)])))
    out = node.refresh()["busiest"]
    assert out.report is not None and out.report.diffed == ["busiest"]
    assert "recomputed and diffed" in out.summary()
    assert rows(node) == recomputed(node, src)


def test_a_view_downstream_of_touched_groups():
    def hot(per_minute):
        return per_minute.filter(per_minute.high > 6)

    src = StaticSource(samples([("a", 1, 5), ("b", 1, 3)]), name="samples")
    agg = src.pipe(per_minute)
    node = agg.pipe(hot)
    node.refresh()
    for batch in [
        Changes(inserts=samples([("a", 1, 9)])),
        Changes(deletes=samples([("a", 1, 9)]), inserts=samples([("b", 1, 8)])),
    ]:
        src.apply(batch)
        node.refresh(audit=True)
    assert rows(node) == [("b", 1, 2, 11, 3, 8, 5.5)]


# -- a time bucket among the keys: only the touched range is read -------------

T0 = datetime(2026, 11, 3)
TIMES = pa.schema([("host", pa.string()), ("ts", pa.timestamp("us")), ("cpu", pa.int64())])


def timed(rows) -> pa.Table:
    """`(host, seconds after T0 or None, cpu)` rows."""
    return pa.table(
        {
            "host": [h for h, _, _ in rows],
            "ts": [None if s is None else T0 + timedelta(seconds=s) for _, s, _ in rows],
            "cpu": [c for _, _, c in rows],
        },
        schema=TIMES,
    )


def per_bucket(samples):
    return samples.group_by(["host", samples.ts.truncate("m").name("minute")]).aggregate(
        n=samples.count(), high=samples.cpu.mean()
    )


@pytest.mark.parametrize("engine", PROFILED)
def test_a_time_bucket_key_reads_only_the_touched_range(engine, monkeypatch):
    rng = random.Random(7)
    live: list[tuple[str, int | None, int]] = [
        (rng.choice("ab"), rng.randrange(600), rng.randrange(100)) for _ in range(40)
    ]
    src = StaticSource(timed(live), name="samples")
    node = src.pipe(per_bucket)
    node.refresh(engine=engine)
    spec = view(node).touched
    assert spec is not None and spec.ranged is not None and spec.ranged.key == 1
    ran = []
    real = incremental.run_plan_on
    monkeypatch.setattr(
        incremental, "run_plan_on", lambda con, plan, *a: ran.append(plan) or real(con, plan, *a)
    )
    for step in range(15):
        ins: list[tuple[str, int | None, int]] = [
            (rng.choice("ab"), rng.randrange(600, 700), rng.randrange(100))
        ]
        if step == 7:
            ins.append(("a", None, 1))  # a NULL time: the whole input is read
        dels = rng.sample([r for r in live if r[1] is not None], 2)
        for d in dels:
            live.remove(d)
        live += ins
        src.apply(Changes(inserts=timed(ins), deletes=timed(dels)))
        node.refresh(engine=engine, audit=True)
        assert rows(node) == recomputed(node, src)
    assert ran.count(spec.recompute) == 1
    assert ran.count(spec.ranged.plan) == 14


# -- windows: the partitions a batch touches ----------------------------------


def windowed(samples):
    w = ibis.window(group_by="host", order_by="minute", preceding=2, following=0)
    return samples.select(
        "host",
        "minute",
        "cpu",
        rn=ibis.row_number().over(group_by="host", order_by="minute"),
        recent=samples.cpu.sum().over(w),
        before=samples.cpu.lag().over(group_by="host", order_by="minute"),
    )


def unique_stream(seed, steps=30):
    """Batches over distinct `(host, minute)` pairs, so windows have no ties."""
    rng = random.Random(seed)
    minutes = iter(rng.sample(range(10_000), 400))
    hosts = ["a", "b", "c", None]

    def row():
        return (rng.choice(hosts), next(minutes), rng.randrange(100))

    return stream(rng, row, row, steps, 3)


@pytest.mark.parametrize("engine", PROFILED_ORDERED)
@pytest.mark.parametrize("seed", range(2))
def test_touched_partitions_match_a_full_recompute(seed, engine):
    first, batches = unique_stream(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(windowed)
    node.refresh(engine=engine)
    assert view(node).strategy == "touched groups"
    for ins, dels in batches:
        src.apply(Changes(inserts=samples(ins), deletes=samples(dels)))
        out = node.refresh(engine=engine, audit=True)["windowed"]
        assert out.report is not None
        if touched := {h for h, _, _ in ins + dels}:
            assert out.report.touched == {"windowed": len(touched)}
        assert rows(node) == recomputed(node, src)


def test_windows_with_different_partitions_are_recomputed():
    def mixed(samples):
        return samples.select(
            "host",
            "minute",
            a=ibis.row_number().over(group_by="host", order_by="minute"),
            b=ibis.row_number().over(order_by="minute"),
        )

    src = StaticSource(samples([("a", 1, 5), ("b", 2, 3)]), name="samples")
    node = src.pipe(mixed)
    node.refresh()
    assert view(node).strategy == "recompute and diff"
    assert "do not share one PARTITION BY" in str(node.status())


# -- #742 on deletes: LEFT JOIN, windows, double SUM and AVG (#248) -------------

DOUBLES = pa.schema([("host", pa.string()), ("minute", pa.int64()), ("cpu", pa.float64())])
HOSTS = pa.schema([("host", pa.string()), ("team", pa.string())])


def _left_join(samples, hosts):
    return samples.left_join(hosts, samples.host == hosts.host).select(
        samples.host, samples.minute, hosts.team
    )


def _running(samples):
    return samples.select(
        "host", "minute", total=samples.cpu.sum().over(group_by="host", order_by="minute")
    )


@sv.transform(requires={"samples": [ibis._.cpu.between(0, 100)]})
def _double_sums(samples):
    return samples.group_by("host").aggregate(total=samples.cpu.sum(), mean=samples.cpu.mean())


@pytest.mark.parametrize(
    ("step", "schema", "strategy", "why"),
    [
        (
            _left_join,
            SCHEMA,
            "recomputed and diffed",
            "recomputed (not incrementally maintainable (left join",
        ),
        (
            _running,
            SCHEMA,
            "1 touched group(s) recomputed",
            "no delta rules: not incrementally maintainable (left join, fetch or window)",
        ),
        (_double_sums, DOUBLES, "1 touched group(s) recomputed", "total is a SUM of float64"),
    ],
    ids=["left_join", "window", "double_sum_avg"],
)
def test_a_batch_that_deletes_rows_says_why_the_node_recomputes(step, schema, strategy, why):
    """#742's rule where a batch deletes rows (#248): the node is recomputed
    (in full or by the groups the batch touches), its status says why, the
    refresh report says how, and the state equals a full recompute."""

    def table(data):
        return pa.table(
            {n: [r[i] for r in data] for i, n in enumerate(schema.names)}, schema=schema
        )

    cpu = 7.5 if schema is DOUBLES else 7
    src = StaticSource(table([("a", 1, 5), ("a", 2, cpu), ("b", 1, 3)]), name="samples")
    hosts = StaticSource(pa.table({"host": ["a"], "team": ["x"]}, schema=HOSTS), name="hosts")
    inputs = (src, hosts) if step is _left_join else (src,)
    node = src.pipe(step, hosts=hosts) if step is _left_join else src.pipe(step)
    node.refresh()
    src.apply(Changes(deletes=table([("a", 2, cpu)])))
    out = node.refresh(audit=True)[node.name]
    assert strategy in out.summary()
    assert rows(node) == recomputed(node, *inputs)
    assert why in str(node.status())
