"""Two processes refresh the same sinks at once.

The race is made deterministic: process A refreshes and is held at a fault
point (`"pause"`); process B refreshes from start to end; then A goes on.
With `inputs="newer"`, the sources change once more before B starts, so B
commits a later epoch than A's.

One of them may fail (Delta's conflict check), but the sinks must hold a
state one of them could have written alone: each sink equals a recompute of
its input at the versions its last commit records (`_world.check_recorded`),
and a refresh after the race brings every sink up to date (`_world.check`).
"""

from __future__ import annotations

import time

import pytest

from _ledger import Violation
from _proc import run_worker, start, wait
from _world import Setup, check, check_recorded, quiet

#: Where A is held: having read what the sink committed, before the write,
#: and just before its commit (DuckDB's files, or delta-rs's MERGE).
CASES = [
    ("delta.committed", "after", True),
    ("delta.write", "before", True),
    ("delta.txn", "before", True),
    ("delta.committed", "after", False),
    ("delta.write", "before", False),
    ("delta.merge", "before", False),
]


def params():
    for point, when, native in CASES:
        for inputs in ("same", "newer"):
            yield pytest.param(
                point,
                when,
                native,
                inputs,
                id=f"{point}-{when}-{'native' if native else 'arrow'}-{inputs}",
            )


def until(cond, what: str, timeout: float = 120) -> None:
    deadline = time.monotonic() + timeout
    while not cond():
        assert time.monotonic() < deadline, what
        time.sleep(0.05)


@pytest.mark.parametrize(("point", "when", "native", "inputs"), params())
def test_a_refresh_held_while_another_commits(
    tmp_path, monkeypatch, scenario, point, when, native, inputs
):
    setup = Setup("delta", native=native)
    scenario["setup"] = {**setup.record(), "inputs": inputs}
    scenario["fault"] = {"point": point, "when": when, "nth": 1, "action": "pause"}
    setup.use(monkeypatch)
    world = setup.world(tmp_path / "w").create()
    world.job().refresh()
    world.step(1)
    barrier = tmp_path / "barrier"
    spec = {"root": str(world.root), "setup": setup.record()}
    hold = {"point": point, "when": when, "action": "pause", "barrier": str(barrier)}
    a = start({**spec, "faults": [hold]})
    until(lambda: barrier.exists() and any(barrier.iterdir()), "A never reached the point")
    if inputs == "newer":
        world.step(2)
    b = run_worker(spec)
    (barrier / "go").touch()
    done_a = wait(a)
    if b.status != 0:
        raise Violation("stuck", f"B refreshes alone (raised in {b.where()})", b.err[-2000:])
    assert done_a.status in (0, 3), done_a.err
    check_recorded(world)
    job = world.job()
    job.refresh()
    check(world, job)
    quiet(job)
