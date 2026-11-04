"""The process dies (SIGKILL) at a fault point, and a fresh process resumes.

A worker process (`_worker.py`) refreshes the job and is killed at the
point, before or after the real call: nothing runs after it, no `finally`,
no flush. A second worker builds the job again and refreshes; then every
sink must equal a full recompute of the sources and record it
(`_world.check`), and a third refresh, in this process, writes nothing.
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from _faults import POINTS_BY_KIND
from _ledger import Violation
from _proc import run_worker
from _world import SETUPS, Setup, World, check, quiet

CASES = [
    (setup, point)
    for setup, points in POINTS_BY_KIND.items()
    for point in points
    # Points inside the pipeline's own memory die with it, whatever they
    # did: one of them, for each setup, is enough.
    if not point.startswith("state.") or point == "state.put"
]


def spec(world: World, setup: Setup, **fault) -> dict:
    out: dict = {"root": str(world.root), "setup": setup.record()}
    if fault:
        out["faults"] = [fault]
    return out


@pytest.mark.parametrize("how", ["group", "node"])
@pytest.mark.parametrize("when", ["before", "after"])
@pytest.mark.parametrize("at", ["first", "later"])
@pytest.mark.parametrize(("setup", "point"), CASES)
def test_a_killed_refresh_resumes_in_a_fresh_process(
    tmp_path, monkeypatch, scenario, setup, point, at, when, how
):
    s = replace(SETUPS[setup], how=how)
    scenario["setup"] = {**s.record(), "name": setup, "at": at, "recovery": "restart"}
    scenario["fault"] = {"point": point, "when": when, "nth": 1, "action": "kill"}
    world = s.world(tmp_path / "w").create()
    if at == "later":
        done = run_worker(spec(world, s))
        assert done.status == 0, done.err
        world.step(1)
    died = run_worker(spec(world, s, point=point, when=when, action="kill"))
    if died.status == 0:
        pytest.skip(f"{point}, {when} call 1 is not reached")
    assert died.killed, died.err
    resumed = run_worker(spec(world, s))
    if resumed.status != 0:
        raise Violation(
            "stuck", f"a fresh process refreshes (raised in {resumed.where()})", resumed.err[-2000:]
        )
    check(world)
    world.step(2)
    s.use(monkeypatch)
    job = world.job()
    job.refresh()
    check(world, job)
    quiet(job)
