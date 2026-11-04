"""The sources change or vanish while a refresh runs, or while the job is
down.

A refresh reads each source at the version it found when it started, so a
change made mid-refresh waits for the next one. A source whose rows went
(vacuumed files, a dropped file, a table dropped and created again) makes
the job read it in full: the sinks then still equal a recompute.
"""

from __future__ import annotations

import shutil

import pytest
from deltalake import DeltaTable, write_deltalake

from _faults import Faults
from _pipelines import orders_table
from _world import INITIAL, World, check, quiet

#: Points mid-refresh, for each kind: after the sources are read, before
#: and after a sink's commit.
MID = {
    "delta": ["engine.run", "state.put", "delta.write", "delta.version"],
    "files": ["engine.run", "state.put", "delta.write", "delta.version"],
    "iceberg": ["engine.run", "state.put", "iceberg.write", "iceberg.commit"],
}


@pytest.mark.parametrize("when", ["before", "after"])
@pytest.mark.parametrize(("kind", "point"), [(k, p) for k, points in MID.items() for p in points])
def test_a_source_that_changes_mid_refresh_is_read_next_time(tmp_path, scenario, kind, point, when):
    scenario["setup"] = {"kind": kind}
    scenario["fault"] = {"point": point, "when": when, "nth": 1, "action": "call: source step"}
    world = World(tmp_path / "w", kind).create()
    job = world.job()
    job.refresh()
    world.step(1)
    with Faults() as faults:
        fault = faults.arm(point, when=when, action="call", callback=lambda: world.step(2))
        job.refresh()
    assert fault.fired
    job.refresh()
    check(world, job)
    quiet(job)


def vacuum(uri: str) -> None:
    """Compact the table and remove every file the latest version does not
    need: its older versions can no longer be read."""
    dt = DeltaTable(uri)
    dt.optimize.compact()
    DeltaTable(uri).vacuum(retention_hours=0, dry_run=False, enforce_retention_duration=False)


@pytest.mark.parametrize("point", ["delta.source.changes", "engine.run", "delta.write"])
def test_a_source_vacuumed_mid_refresh(tmp_path, scenario, point):
    scenario["setup"] = {"kind": "delta"}
    scenario["fault"] = {"point": point, "when": "before", "nth": 1, "action": "call: vacuum"}
    world = World(tmp_path / "w", "delta").create()
    job = world.job()
    job.refresh()
    world.step(1)
    with Faults() as faults:
        faults.arm(point, action="call", callback=lambda: vacuum(world.orders_uri))
        try:
            job.refresh()
        except Exception as e:  # noqa: BLE001
            # Its files are gone: the error says which table.
            assert "orders" in str(e), e
    world.step(2)
    job.refresh()
    check(world, job)
    quiet(job)


def test_a_source_vacuumed_while_the_job_is_down(tmp_path):
    world = World(tmp_path / "w", "delta").create()
    world.job().refresh()
    world.step(1)
    world.step(2)
    vacuum(world.orders_uri)
    job = world.job()
    job.refresh()
    check(world, job)
    quiet(job)


def test_a_dropped_file_read_before_is_gone_after_a_restart(tmp_path):
    # The recorded cursor names a file that is gone: `restore` returns None,
    # and the job reads the directory in full.
    world = World(tmp_path / "w", "files").create()
    world.job().refresh()
    world.step(1)
    world.job().refresh()
    (world.drops / "0001.parquet").unlink()
    world.step(2)
    job = world.job()
    job.refresh()
    check(world, job)
    quiet(job)


def test_a_source_dropped_mid_refresh_is_named(tmp_path):
    world = World(tmp_path / "w", "delta").create()
    job = world.job()
    job.refresh()
    world.step(1)
    with (
        Faults() as faults,
        pytest.raises(Exception, match="orders") as raised,
    ):
        faults.arm(
            "delta.source.changes",
            action="call",
            callback=lambda: shutil.rmtree(world.orders_uri),
        )
        job.refresh()
    assert raised.value is not None


def recreate(world: World, n: int) -> None:
    """Drop the source table and create it again, with fewer versions than
    before: version 1 holds the rows of `INITIAL` and `n` new orders."""
    shutil.rmtree(world.orders_uri)
    DeltaTable.create(
        world.orders_uri,
        orders_table([]).schema,
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    rows = [*INITIAL, *[(500 + i, "dee", i) for i in range(n)]]
    write_deltalake(world.orders_uri, orders_table(rows), mode="append")


@pytest.mark.parametrize("restart", [False, True], ids=["same", "restart"])
def test_a_source_recreated_with_lower_versions(tmp_path, scenario, restart):
    scenario["setup"] = {"kind": "delta", "recovery": "restart" if restart else "same"}
    # The sinks recorded orders@v5; the new table is at v1, with other rows.
    world = World(tmp_path / "w", "delta").create()
    job = world.job()
    job.refresh()
    for i in (1, 2, 3):
        world.step(i)
        job.refresh()
    recreate(world, 3)
    if restart:
        job = world.job()
    job.refresh()
    check(world, job)
