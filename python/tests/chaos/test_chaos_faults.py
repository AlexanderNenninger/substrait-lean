"""A refresh fails at one point, in this process; then the same process, or
a restarted one, carries on.

The matrix: every fault point a setup reaches (`_faults.POINTS_BY_KIND`) ×
the setups (`_world.SETUPS`) × refreshing as a group or node by node × the
first refresh (the sinks are created) or a later one (they write a change)
× before or after the real call × recovering in the same process or a
restarted one. After the fault:

- the error the refresh raised is the injected one, or raised from it, so
  the message names what failed (else `unclear-error`);
- the same process retries with no new input, then with new input
  (`recovery="same"`), or a fresh process builds the job again and
  refreshes (`recovery="restart"`);
- every sink equals a full recompute of the sources, its epoch the sum of
  the versions it records, and a refresh with no new input writes nothing
  (`_world.check`, `_world.quiet`).

A point a setup never reaches is skipped (`not-reached` in the ledger).
"""

from __future__ import annotations

from dataclasses import replace

import pytest

from _faults import POINTS_BY_KIND, Crash, Faults, caused_by_crash
from _ledger import Violation
from _world import SETUPS, World, check, quiet


def inject(job, scenario, point: str, when: str, nth: int = 1) -> BaseException | None:
    """Refresh `job` with one fault armed; the error it raised, if any."""
    with Faults() as faults:
        fault = faults.arm(point, when=when, nth=nth)  # type: ignore[arg-type]
        scenario["fault"] = fault.record()
        try:
            job.refresh()
        except Exception as e:  # noqa: BLE001
            error: BaseException | None = e
        else:
            error = None
    if not fault.fired:
        pytest.skip(f"{fault.describe()} is not reached")
    return error


def names_the_fault(error: BaseException | None) -> None:
    """The error the user sees is the injected one, or raised from it."""
    if error is None:
        return  # handled: the checks after it say whether that was right
    crash = caused_by_crash(error)
    if crash is None or not (isinstance(error, Crash) or str(crash) in str(error)):
        raise Violation("unclear-error", "the error names the fault", repr(error)) from error


def recover(world: World, job, how: str, step: int) -> None:
    if how == "restart":
        job = world.job()
    else:
        # A retry with no new input finishes what failed.
        job.refresh()
        check(world, job)
    world.step(step)
    job.refresh()
    check(world, job)
    quiet(job)
    if how == "same":
        # And a restart after it resumes from the sinks.
        fresh = world.job()
        fresh.refresh()
        check(world, fresh)


def params():
    for setup, points in POINTS_BY_KIND.items():
        for point in points:
            for how in ("group", "node"):
                for at in ("first", "later"):
                    for when in ("before", "after"):
                        for recovery in ("same", "restart"):
                            yield pytest.param(
                                setup,
                                how,
                                point,
                                at,
                                when,
                                recovery,
                                id=f"{setup}-{how}-{point}-{at}-{when}-{recovery}",
                            )


@pytest.mark.parametrize(("setup", "how", "point", "at", "when", "recovery"), params())
def test_a_fault_is_recovered(
    tmp_path, monkeypatch, scenario, setup, how, point, at, when, recovery
):
    s = replace(SETUPS[setup], how=how)
    scenario["setup"] = {**s.record(), "name": setup, "at": at, "recovery": recovery}
    s.use(monkeypatch)
    world = s.world(tmp_path / "w").create()
    job = world.job()
    if at == "later":
        job.refresh()
        world.step(1)
    error = inject(job, scenario, point, when)
    names_the_fault(error)
    recover(world, job, recovery, 2)
