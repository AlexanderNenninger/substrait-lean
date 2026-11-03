"""Windows over bounded RANGE frames of a time column, maintained by
recomputing the rows near the change (`sverify._touched.Framed`). Lean does
not prove this strategy yet (#294), so these tests carry it: every refresh
equals a full recompute on random streams with late rows, rows on the frame
edges, duplicate times and NULL times."""

import random
from datetime import datetime, timedelta

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from _pipelines import recomputed, rows
from sverify.io import StaticSource

T0 = datetime(2026, 11, 3)
SCHEMA = pa.schema([("host", pa.string()), ("ts", pa.timestamp("us")), ("cpu", pa.int64())])


def samples(rows) -> pa.Table:
    """`(host, minutes after T0 or None, cpu)` rows: whole minutes, so many
    rows sit exactly on the frames' edges."""
    return pa.table(
        {
            "host": [h for h, _, _ in rows],
            "ts": [None if m is None else T0 + timedelta(minutes=m) for _, m, _ in rows],
            "cpu": [c for _, _, c in rows],
        },
        schema=SCHEMA,
    )


def frames(by):
    """Two windows with different frames: the last 5 minutes, and from 10
    minutes before to 3 minutes before (a frame that ends before the row)."""

    def windows(samples):
        recent = ibis.window(
            group_by=by, order_by="ts", range=(-ibis.interval(minutes=5), ibis.interval(0))
        )
        earlier = ibis.window(
            group_by=by,
            order_by="ts",
            range=(-ibis.interval(minutes=10), -ibis.interval(minutes=3)),
        )
        return samples.select(
            "host",
            "ts",
            "cpu",
            total=samples.cpu.sum().over(recent),
            n=samples.cpu.count().over(recent),
            low=samples.cpu.min().over(earlier),
        )

    return windows


def stream(seed, steps=40, lateness=30):
    """Batches whose inserts and deletes lie at most `lateness` minutes
    before the latest time seen, with duplicate times and a few NULLs."""
    rng = random.Random(seed)
    hosts = ["a", "b", None]
    live: list[tuple[str | None, int | None, int]] = [
        (rng.choice(hosts), rng.randrange(60), rng.randrange(-20, 20)) for _ in range(40)
    ]
    first = list(live)
    latest = max(m for _, m, _ in live if m is not None)
    out = []
    for step in range(steps):
        ins = [
            (
                rng.choice(hosts),
                rng.randrange(latest - lateness, latest + 6),
                rng.randrange(-20, 20),
            )
            for _ in range(rng.randrange(4))
        ]
        if step % 13 == 5:
            ins.append(("a", None, 7))  # a NULL time is in no frame
        recent = [r for r in live if (m := r[1]) is not None and m >= latest - lateness]
        dels = rng.sample(recent, min(len(recent), rng.randrange(3)))
        for d in dels:
            live.remove(d)
        live += ins
        latest = max([latest, *(m for _, m, _ in ins if m is not None)])
        out.append((ins, dels))
    return first, out


def view(node):
    assert node._stage is not None
    return node._stage.view


@pytest.mark.parametrize("by", [["host"], []], ids=["partitioned", "whole"])
@pytest.mark.parametrize("seed", range(3))
def test_framed_windows_match_a_full_recompute(seed, by):
    first, batches = stream(seed)
    src = StaticSource(samples(first), name="samples")
    node = src.pipe(frames(by))
    node.refresh()
    assert view(node).strategy == "touched frames"
    spec = view(node).touched
    assert spec is not None and spec.framed is not None
    assert (spec.framed.start, spec.framed.end) == (-timedelta(minutes=10), timedelta(0))
    for ins, dels in batches:
        src.apply(sv.Changes(inserts=samples(ins), deletes=samples(dels)))
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, src)


def test_a_change_far_from_the_rest_recomputes_only_its_neighbourhood():
    src = StaticSource(samples([("a", m, 1) for m in range(0, 600, 2)]), name="samples")
    node = src.pipe(frames(["host"]))
    node.refresh()
    src.apply(sv.Changes(inserts=samples([("a", 301, 5)])))
    out = node.refresh(audit=True)["windows"]
    assert out.report is not None
    # Rows from 4:51 to 5:11 can have 5:01 in a frame: 11 of them, and 5:01.
    assert out.report.framed == {"windows": 11}
    assert rows(node) == recomputed(node, src)


def test_status_and_summary_say_the_strategy_is_tested_not_proved():
    src = StaticSource(samples([("a", 1, 5), ("a", 2, 7)]), name="samples")
    node = src.pipe(frames(["host"]))
    node.refresh()
    assert "touched frames recomputed (tested, not proved;" in str(node.status())
    src.apply(sv.Changes(inserts=samples([("a", 3, 9)])))
    out = node.refresh()["windows"]
    assert "row(s) in touched frames recomputed (tested, not proved)" in out.summary()
    assert "(tested, not proved)" in str(out.report)


def test_a_rows_frame_or_an_unbounded_frame_is_not_framed():
    def running(samples):
        return samples.select(
            "host", "ts", total=samples.cpu.sum().over(group_by="host", order_by="ts")
        )

    src = StaticSource(samples([("a", 1, 5), ("b", 2, 7)]), name="samples")
    node = src.pipe(running)
    node.refresh()
    # Partitions are recomputed instead (proved).
    assert view(node).strategy == "touched groups"
