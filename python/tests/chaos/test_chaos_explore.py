"""Hypothesis picks where and when refreshes fail.

A run is a few rounds: the sources change some number of times, then a
refresh runs with at most one fault armed, at any point the world reaches,
before or after its `nth` call (so the second or third sink, or a later
plan). Failed refreshes are left as they are. At the end, a refresh with no
fault must bring every sink up to date, in this process and in a restarted
one (`_world.check`).

Faults that hit a bug already filed are left out (`known`), so that a run
finds new ones. `SVERIFY_CHAOS_EXAMPLES` sets the budget (default 200;
`poe test-chaos` runs 2000).
"""

from __future__ import annotations

import os
import shutil
import tempfile
from pathlib import Path

from hypothesis import HealthCheck, assume, given, note, settings
from hypothesis import strategies as st

import sverify._state
import sverify.incremental
import sverify_duckdb
from _faults import POINTS_BY_KIND, Faults
from _world import SETUPS, World, check, quiet

#: Filed bugs, by the fault that hits them: (point, when) -> issue.
KNOWN: dict[tuple[str, str], int] = {}
#: A fault inside `Pipeline._commit` after DuckDB updated a view's state in
#: place leaves the view ahead of its versions.
#: #515. The explorer leaves these runs out so that it finds other bugs.
ISSUE_PARTIAL_COMMIT = 515

fault = st.one_of(
    st.none(),
    st.tuples(
        st.sampled_from(sorted({p for ps in POINTS_BY_KIND.values() for p in ps})),
        st.sampled_from(["before", "after"]),
        st.integers(1, 4),
    ),
)
rounds = st.lists(st.tuples(st.integers(0, 2), fault), min_size=1, max_size=4)


@settings(
    max_examples=int(os.environ.get("SVERIFY_CHAOS_EXAMPLES", "200")),
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)
@given(kind=st.sampled_from(sorted(POINTS_BY_KIND)), rounds=rounds)
def test_any_fault_is_recovered(monkeypatch, scenario, kind, rounds):
    scenario["setup"] = {"name": kind, "rounds": rounds}
    root = Path(tempfile.mkdtemp(prefix="chaos-"))
    with monkeypatch.context() as m:
        SETUPS[kind].use(m)
        commit = Commit(m)
        try:
            run(SETUPS[kind].world(root / "w"), rounds, commit)
        finally:
            shutil.rmtree(root, ignore_errors=True)


class Commit:
    """Whether a fault fired inside `Pipeline._commit`, after the in-place
    update of DuckDB-held state (`ISSUE_PARTIAL_COMMIT`)."""

    def __init__(self, m):
        self.inside = self.applied = self.partial = False
        commit = sverify.incremental.Pipeline._commit
        apply = sverify_duckdb.DuckDBStore.apply

        def _commit(pipe, pending):
            self.inside, self.applied = True, False
            try:
                return commit(pipe, pending)
            except BaseException:
                self.partial |= self.applied
                raise
            finally:
                self.inside = False

        def _apply(store, updates):
            out = apply(store, updates)
            self.applied = self.inside
            return out

        m.setattr(sverify.incremental.Pipeline, "_commit", _commit)
        m.setattr(sverify_duckdb.DuckDBStore, "apply", _apply)


def run(world: World, rounds, commit: Commit) -> None:
    world.create()
    job = world.job()
    step = 0
    for changes, f in rounds:
        for _ in range(changes):
            step += 1
            world.step(step)
        with Faults() as faults:
            if f is not None and f[0] in POINTS_BY_KIND.get(world.kind, POINTS_BY_KIND["delta"]):
                if (f[0], f[1]) in KNOWN:
                    continue
                faults.arm(f[0], when=f[1], nth=f[2])  # type: ignore[arg-type]
            try:
                job.refresh()
                note(f"refresh with {f}: ok")
            except Exception as e:  # noqa: BLE001
                note(f"refresh with {f}: {e!r}")
            assume(not commit.partial)
    job.refresh()
    check(world, job)
    quiet(job)
    fresh = world.job()
    fresh.refresh()
    check(world, fresh)
