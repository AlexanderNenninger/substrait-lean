"""Deterministic fault points for the chaos tests.

A fault point is a callable reached by a dotted path (`module.func` or
`module.Class.method`). `Faults.arm` wraps it so that its `nth` call fails:
`"before"` the real call (nothing it does happens) or `"after"` it (its
effect lands, then the caller sees an error). Failing means one of:

- `"raise"`: raise `Crash`, whose message names the point;
- `"kill"`: SIGKILL the process, as a crash or an OOM kill would;
- `"pause"`: wait at a barrier until `parties` processes reach it (two
  refreshes racing on one sink), then go on;
- `"call"`: call `callback` and go on (the source changes or vanishes
  mid-refresh, the store goes down).

The points the suite injects at are in `POINTS`, by name. Each process arms
its own: the subprocess worker (`_worker.py`) arms them from the command
line.
"""

from __future__ import annotations

import functools
import importlib
import os
import signal
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal

When = Literal["before", "after"]
Action = Literal["raise", "kill", "pause", "call"]


class Crash(Exception):
    """The injected failure."""


#: Where a refresh can fail, by name: the callable, and what failing there
#: stands for.
POINTS: dict[str, tuple[str, str]] = {
    # Reading the sources.
    "delta.source.changes": (
        "sverify.io.delta.DeltaSource.changes",
        "reading a Delta source's change feed",
    ),
    "delta.source.latest": (
        "sverify.io.delta.DeltaSource.latest",
        "reading a Delta source's latest version",
    ),
    "files.source.read": ("sverify.io._source._Files.read", "listing and reading dropped files"),
    "iceberg.source.changes": (
        "sverify.io.iceberg.IcebergSource.changes",
        "reading an Iceberg source's snapshots",
    ),
    # The engine.
    "engine.run": ("sverify.incremental.run_plan", "the engine running a plan"),
    # The pipeline's own state, in the process.
    "state.apply": (
        "sverify_duckdb.DuckDBStore.apply",
        "updating DuckDB-held state in place",
    ),
    "state.put": ("sverify.incremental.put_table", "replacing a table of the pipeline"),
    "state.merge": ("sverify._state.Merger.__call__", "adding up weighted state"),
    # What the sink records: the contract, with the epoch and the cursors.
    "cursor.record": ("sverify.io._common._cursors", "recording the sources' cursors"),
    "sink.committed": ("sverify.io._sink.Sink.contract", "reading what the sink committed"),
    "delta.committed": (
        "sverify.io.delta.DeltaSink.contract",
        "reading the Delta sink's last transaction",
    ),
    # The Delta sink, before, during and after its commit.
    "delta.write": ("sverify.io.delta.DeltaSink.write", "the Delta sink's write as a whole"),
    "delta.create": ("deltalake.DeltaTable.create", "creating the Delta table"),
    "delta.constraint": (
        "deltalake.table.TableAlterer.add_constraint",
        "adding a CHECK constraint (its own commit)",
    ),
    "delta.merge": ("deltalake.table.TableMerger.execute", "the MERGE commit"),
    "delta.overwrite": ("sverify.io.delta.write_deltalake", "the overwrite commit"),
    "delta.txn": (
        "deltalake.DeltaTable.create_write_transaction",
        "the native path's commit",
    ),
    "delta.version": ("deltalake.DeltaTable.version", "reading a Delta table's version"),
    # The quarantine table (#184), written before the node's sink.
    "quarantine.write": (
        "sverify.nodes._write_quarantine",
        "writing the rows a node sets aside",
    ),
    # The Iceberg sink.
    "iceberg.write": ("sverify.io.iceberg.IcebergSink.write", "the Iceberg sink's write"),
    "iceberg.create": (
        "pyiceberg.catalog.sql.SqlCatalog.create_table",
        "creating the Iceberg table",
    ),
    "iceberg.commit": (
        "pyiceberg.table.Transaction.commit_transaction",
        "an Iceberg snapshot commit",
    ),
}


#: The points each kind of world reaches, and so injects at.
COMMON = ["engine.run", "state.apply", "state.put", "state.merge", "cursor.record"]
DELTA_SINK = [
    "delta.committed",
    "delta.write",
    "delta.create",
    "delta.constraint",
    "delta.merge",
    "delta.overwrite",
    "delta.txn",
    "delta.version",
]
POINTS_BY_KIND = {
    "delta": ["delta.source.changes", "delta.source.latest", *COMMON, *DELTA_SINK],
    # The same, with the sinks writing through delta-rs (MERGE) rather than
    # DuckDB's files (the path for object stores).
    "delta-arrow": ["delta.source.changes", *COMMON, *DELTA_SINK],
    # Without the Change Data Feed: snapshots diffed, views recomputed.
    "delta-full": ["delta.source.latest", *COMMON, *DELTA_SINK],
    "files": ["files.source.read", *COMMON, *DELTA_SINK],
    # Dirty data, set aside by `on_violation="quarantine"` (#184).
    "delta-quarantine": [
        "delta.source.changes",
        *COMMON,
        "quarantine.write",
        *DELTA_SINK,
    ],
    "iceberg": [
        "iceberg.source.changes",
        *COMMON,
        "iceberg.write",
        "iceberg.create",
        "iceberg.commit",
    ],
}


def resolve(path: str) -> tuple[Any, str]:
    """The object holding the attribute `path` names, and its name."""
    parts = path.split(".")
    for i in range(len(parts) - 1, 0, -1):
        try:
            owner: Any = importlib.import_module(".".join(parts[:i]))
        except ImportError:
            continue
        for p in parts[i:-1]:
            owner = getattr(owner, p)
        return owner, parts[-1]
    raise ImportError(path)


@dataclass
class Fault:
    point: str
    when: When = "before"
    nth: int = 1
    action: Action = "raise"
    barrier: Path | None = None
    parties: int = 2
    callback: Callable[[], object] | None = None
    calls: int = 0
    fired: bool = False

    def record(self) -> dict[str, object]:
        return {"point": self.point, "when": self.when, "nth": self.nth, "action": self.action}

    def describe(self) -> str:
        return f"{self.point} ({POINTS[self.point][1]}), {self.when} call {self.nth}"

    def fail(self) -> None:
        self.fired = True
        if self.action == "kill":
            os.kill(os.getpid(), signal.SIGKILL)
        if self.action == "call":
            assert self.callback is not None
            self.callback()
            return
        if self.action == "pause":
            assert self.barrier is not None
            self.barrier.mkdir(parents=True, exist_ok=True)
            (self.barrier / str(os.getpid())).touch()
            deadline = time.monotonic() + 60
            while len(list(self.barrier.iterdir())) < self.parties:
                if time.monotonic() > deadline:
                    raise TimeoutError(f"barrier {self.barrier}: the other party never came")
                time.sleep(0.01)
            return
        raise Crash(f"injected fault at {self.describe()}")


@dataclass
class Faults:
    """The armed faults of this process. `undo` restores every patch."""

    faults: list[Fault] = field(default_factory=list)
    _undo: list[Callable[[], None]] = field(default_factory=list)

    def arm(
        self,
        point: str,
        *,
        when: When = "before",
        nth: int = 1,
        action: Action = "raise",
        barrier: Path | None = None,
        parties: int = 2,
        callback: Callable[[], object] | None = None,
    ) -> Fault:
        fault = Fault(point, when, nth, action, barrier, parties, callback)
        owner, name = resolve(POINTS[point][0])
        own = not isinstance(owner, type) or name in owner.__dict__
        # A method a class inherits is looked up on its bases, patched on the
        # class, and removed from it again on `undo`.
        real = (
            getattr(owner, name)
            if not isinstance(owner, type)
            else next(c.__dict__[name] for c in owner.__mro__ if name in c.__dict__)
        )
        static = isinstance(real, staticmethod | classmethod)
        func = real.__func__ if static else real

        @functools.wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            fault.calls += 1
            hit = fault.calls == fault.nth
            if hit and when == "before":
                fault.fail()
            out = func(*args, **kwargs)
            if hit and when == "after":
                fault.fail()
            return out

        patched: Any = wrapper
        if isinstance(real, staticmethod):
            patched = staticmethod(wrapper)
        elif isinstance(real, classmethod):
            patched = classmethod(wrapper)
        setattr(owner, name, patched)
        self._undo.append(
            (lambda: setattr(owner, name, real)) if own else (lambda: delattr(owner, name))
        )
        self.faults.append(fault)
        return fault

    def undo(self) -> None:
        while self._undo:
            self._undo.pop()()

    def __enter__(self) -> Faults:
        return self

    def __exit__(self, *exc: object) -> None:
        self.undo()


def caused_by_crash(e: BaseException) -> Crash | None:
    """The injected `Crash` behind `e` (it, or what it was raised from)."""
    seen: set[int] = set()
    cur: BaseException | None = e
    while cur is not None and id(cur) not in seen:
        seen.add(id(cur))
        if isinstance(cur, Crash):
            return cur
        cur = cur.__cause__ or cur.__context__
    return None
