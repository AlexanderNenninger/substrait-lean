"""The inputs, the jobs and the checks of the chaos tests.

A `World` is everything on disk: the source tables and the sinks. It moves
on by numbered steps (`step(i)`), each a deterministic change to the
sources, so a test, a killed subprocess and the fresh process after it all
see the same inputs. A job is the nodes a process builds over a world
(`job`); building it again is what a restarted process does.

Three kinds of world:

- `delta`: a Delta table of orders (Change Data Feed on) → `paid` stored in
  a `DeltaSink` → `doubled` and `totals`, each stored in a `DeltaSink`,
  refreshed as one group.
- `iceberg`: the same over an Iceberg table and `IcebergSink`s.
- `files`: Parquet files dropped in a directory (`sverify.io.from_files`,
  whose cursor, the files read, the sinks record) → the same nodes, stored
  in Delta.

`check` is what must hold after a fault, once a refresh succeeds: every
sink equals a full recompute of the inputs (an oracle in plain Arrow, not
sverify), each records the versions it reflects, and its transaction epoch
is their sum.
"""

from __future__ import annotations

import os
import warnings
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import pyarrow as pa
import pyarrow.dataset as pads
import pyarrow.parquet as pq
from deltalake import DeltaTable, write_deltalake

import sverify as sv
from _ledger import Violation, bag_outcome
from _pipelines import ORDERS, doubled, orders_table, paid
from sverify.io import DeltaSink, DeltaSource, IcebergSink, IcebergSource, from_files

Kind = Literal["delta", "iceberg", "files"]
KINDS: tuple[Kind, ...] = ("delta", "iceberg", "files")
CUSTOMERS = ("ada", "bob", "cy")


@sv.transform()
def totals(t):
    """Per customer: the sum of the amounts and the number of orders. A
    change applied twice or lost shows in the sums."""
    return t.group_by("customer").aggregate(total=t.amount.sum(), n=t.count())


def _row(i: int) -> tuple:
    """The `i`-th order."""
    return (i, CUSTOMERS[i % 3], (i * 7) % 50)


#: The orders before the first step.
INITIAL = [_row(i) for i in range(4)]


@dataclass
class World:
    root: Path
    kind: Kind
    storage: dict | None = None
    """Where the Delta sinks are, if not under `root`: `{"uri": "s3://bucket",
    "options": {...}}` (the outage tests' S3)."""
    cdf: bool = True
    """Whether the Delta source has its Change Data Feed: without it, each
    refresh diffs snapshots and the views are recomputed."""
    how: Literal["group", "node"] = "group"
    """How the job refreshes: `sv.group(...).refresh()`, or `refresh()` on
    each top node."""

    # -- where things are ----------------------------------------------------

    @property
    def orders_uri(self) -> str:
        return str(self.root / "orders")

    @property
    def drops(self) -> Path:
        return self.root / "drops"

    def sink_uri(self, name: str) -> str:
        if self.storage is not None:
            return f"{self.storage['uri']}/sinks/{name}"
        return str(self.root / "sinks" / name)

    @property
    def options(self) -> dict | None:
        return None if self.storage is None else self.storage["options"]

    def sink_table(self, name: str) -> DeltaTable:
        return DeltaTable(self.sink_uri(name), storage_options=self.options)

    def catalog(self) -> Any:
        from pyiceberg.catalog.sql import SqlCatalog

        warnings.filterwarnings("ignore", module="pyiceberg")
        return SqlCatalog(
            "chaos",
            uri=f"sqlite:///{self.root}/catalog.db",
            warehouse=f"file://{self.root}/warehouse",
        )

    # -- the inputs ----------------------------------------------------------

    def create(self) -> World:
        """The sources, with `INITIAL`."""
        self.root.mkdir(parents=True, exist_ok=True)
        if self.kind == "delta":
            DeltaTable.create(
                self.orders_uri,
                ORDERS,
                configuration={"delta.enableChangeDataFeed": "true"} if self.cdf else None,
            )
            write_deltalake(self.orders_uri, orders_table(INITIAL), mode="append")
        elif self.kind == "iceberg":
            cat = self.catalog()
            cat.create_namespace("db")
            (self.root / "warehouse").mkdir(exist_ok=True)
            cat.create_table("db.orders", schema=ORDERS).append(orders_table(INITIAL))
        else:
            self.drops.mkdir()
            self._drop(0, INITIAL)
        return self

    def _drop(self, i: int, rows: list[tuple]) -> None:
        tmp = self.drops / f".{i:04d}.tmp"
        pq.write_table(orders_table(rows), tmp)
        os.replace(tmp, self.drops / f"{i:04d}.parquet")

    def step(self, i: int) -> None:
        """Change the sources, the `i`-th time (from 1): two new orders; on
        even steps an amount changes, on every third a row goes (Delta and
        Iceberg; dropped files are only ever added)."""
        new = [_row(100 + 2 * i), _row(101 + 2 * i)]
        if self.kind == "files":
            self._drop(i, new)
            return
        if self.kind == "delta":
            write_deltalake(self.orders_uri, orders_table(new), mode="append")
            dt = DeltaTable(self.orders_uri)
            if i % 2 == 0:
                dt.update(updates={"amount": "amount + 1"}, predicate=f"id = {i % 4}")
            if i % 3 == 0:
                DeltaTable(self.orders_uri).delete(f"id = {99 + 2 * i}")
            return
        t = self.catalog().load_table("db.orders")
        t.append(orders_table(new))
        if i % 3 == 0:
            self.catalog().load_table("db.orders").delete(f"id = {99 + 2 * i}")

    def orders(self) -> pa.Table:
        """The source table now, read without sverify."""
        if self.kind == "delta":
            return DeltaTable(self.orders_uri).to_pyarrow_table()
        if self.kind == "iceberg":
            return self.catalog().load_table("db.orders").scan().to_arrow()
        return pads.dataset(str(self.drops), format="parquet", schema=ORDERS).to_table()

    def source_versions(self) -> int | None:
        """The source's latest version, where it has one of its own."""
        if self.kind == "delta":
            return DeltaTable(self.orders_uri).version()
        return None

    # -- the job ---------------------------------------------------------------

    def source(self) -> Any:
        if self.kind == "delta":
            return DeltaSource(self.orders_uri, name="orders")
        if self.kind == "iceberg":
            return IcebergSource(self.catalog(), "db.orders", name="orders")
        return from_files(str(self.drops), name="orders", schema=ORDERS)

    def sink(self, name: str) -> Any:
        if self.kind == "iceberg":
            return IcebergSink(self.catalog(), f"db.{name}")
        return DeltaSink(self.sink_uri(name), storage_options=self.options)

    def job(self) -> Job:
        """The nodes a process builds: `paid` stored, and `doubled` and
        `totals` over it, stored; refreshed as one group."""
        p = paid(self.source()).write(self.sink("paid"))
        d = doubled(p).write(self.sink("doubled"))
        t = totals(p).write(self.sink("totals"))
        return Job(self, p, d, t)

    # -- what the sinks hold -----------------------------------------------------

    def sink_rows(self, name: str) -> pa.Table:
        if self.kind == "iceberg":
            return self.catalog().load_table(f"db.{name}").scan().to_arrow()
        return self.sink_table(name).to_pyarrow_table()

    def contract(self, name: str) -> Any:
        """The contract the sink's last commit recorded, with its epoch."""
        if self.kind == "iceberg":
            return IcebergSink(self.catalog(), f"db.{name}").contract()
        return DeltaSink(self.sink_uri(name), storage_options=self.options).contract()

    def txn(self, name: str) -> int | None:
        """The epoch the sink's transaction records (Delta's `txn` action;
        Iceberg's snapshot summary)."""
        c = self.contract(name)
        if self.kind == "iceberg":
            return None if c is None else c.epoch
        return self.sink_table(name).transaction_version(f"sverify:{name}")

    def version(self, name: str) -> int:
        if self.kind == "iceberg":
            snap = self.catalog().load_table(f"db.{name}").current_snapshot()
            return 0 if snap is None else snap.sequence_number
        return self.sink_table(name).version()


@dataclass
class Job:
    world: World
    paid: Any
    doubled: Any
    totals: Any

    def group(self) -> Any:
        return sv.group(self.doubled, self.totals)

    def refresh(self, how: Literal["group", "node"] | None = None, **kw: Any) -> Any:
        if (how or self.world.how) == "node":
            # Node.refresh, on each top node: `paid` is written once, by the first.
            self.doubled.refresh(**kw)
            return self.totals.refresh(**kw)
        return self.group().refresh(**kw)


# -- the oracle ------------------------------------------------------------------


def _bag(table: pa.Table, columns: list[str]) -> Counter:
    return Counter(tuple(r[c] for c in columns) for r in table.to_pylist())


def expected(orders: pa.Table) -> dict[str, Counter]:
    """What each sink must hold, from the source table alone."""
    rows = [r for r in orders.to_pylist() if r["amount"] is not None]
    by: dict[str, list[int]] = {}
    for r in rows:
        by.setdefault(r["customer"], []).append(r["amount"])
    return {
        "paid": Counter((r["id"], r["customer"], r["amount"]) for r in rows),
        "doubled": Counter((r["id"], r["customer"], 2 * r["amount"]) for r in rows),
        "totals": Counter((c, sum(a), len(a)) for c, a in by.items()),
    }


COLUMNS = {
    "paid": ["id", "customer", "amount"],
    "doubled": ["id", "customer", "doubled"],
    "totals": ["customer", "total", "n"],
}


def _same(got: Counter, want: Counter, invariant: str) -> None:
    if got != want:
        raise Violation(
            bag_outcome(got, want),
            invariant,
            f"  missing: {dict(want - got)}\n  extra:   {dict(got - want)}",
        )


def _holds(ok: bool, outcome: str, invariant: str, detail: object = "") -> None:
    if not ok:
        raise Violation(outcome, invariant, str(detail))


def check(world: World, job: Job | None = None) -> None:
    """Every sink equals a full recompute of the sources, and records it:
    the versions it reflects, and an epoch that is their sum. With `job`,
    its nodes' in-memory state equals it too. Raises `Violation`."""
    want = expected(world.orders())
    for name, columns in COLUMNS.items():
        _same(_bag(world.sink_rows(name), columns), want[name], "sink = recompute")
        c = world.contract(name)
        _holds(c is not None, "lost-change", "sink records a contract", name)
        _holds(
            c.epoch == sum(c.sources.values()),
            "wrong-result",
            "epoch = sum of recorded versions",
            (name, c.epoch, c.sources),
        )
        _holds(world.txn(name) == c.epoch, "wrong-result", "txn = epoch", (name, world.txn(name)))
    paid_c = world.contract("paid")
    if (v := world.source_versions()) is not None:
        _holds(
            paid_c.sources == {"orders": v},
            "lost-change",
            "sink records the latest source version",
            (paid_c.sources, v),
        )
    if world.kind == "files":
        files = sorted(str(p) for p in world.drops.glob("*.parquet"))
        _holds(
            sorted(paid_c.cursors.get("orders") or []) == files,
            "lost-change",
            "cursor = the files read",
            paid_c.cursors,
        )
    if world.kind != "iceberg":
        for name in ("doubled", "totals"):
            _holds(
                world.contract(name).sources == {"paid": world.version("paid")},
                "lost-change",
                "downstream sink records the latest paid",
                name,
            )
    if job is not None:
        for name, node in (("paid", job.paid), ("doubled", job.doubled), ("totals", job.totals)):
            _same(_bag(node.to_arrow(), COLUMNS[name]), want[name], "node state = recompute")


def check_recorded(world: World) -> None:
    """Each Delta sink equals a recompute of its input at the version its
    last commit records, and its epoch is their sum: what holds between
    refreshes, also when another writer raced it."""
    assert world.kind == "delta"
    c = world.contract("paid")
    orders = DeltaTable(world.orders_uri, version=c.sources["orders"]).to_pyarrow_table()
    invariant = "sink = recompute at its recorded versions"
    _same(_bag(world.sink_rows("paid"), COLUMNS["paid"]), expected(orders)["paid"], invariant)
    for name in ("doubled", "totals"):
        c = world.contract(name)
        _holds(
            world.txn(name) == c.epoch == sum(c.sources.values()),
            "wrong-result",
            "txn = epoch = sum of recorded versions",
            name,
        )
        at = c.sources["paid"]
        paid_rows = DeltaTable(world.sink_uri("paid"), version=at).to_pyarrow_table()
        _same(_bag(world.sink_rows(name), COLUMNS[name]), expected(paid_rows)[name], invariant)


def quiet(job: Job) -> None:
    """With no new input, a refresh writes nothing."""
    out = job.refresh()
    modes = {w.contract.view: w.mode for w in out.writes}
    _holds(
        set(modes.values()) == {"skipped"}, "wrong-result", "a quiet refresh writes nothing", modes
    )


@dataclass(frozen=True)
class Setup:
    """One column of the matrix: the world's kind, whether Delta sinks write
    DuckDB's files (`native`) or MERGE through delta-rs, whether the Delta
    source has its Change Data Feed (else every refresh recomputes), and
    whether the job refreshes as a group or node by node."""

    kind: Kind
    native: bool = True
    cdf: bool = True
    how: Literal["group", "node"] = "group"

    def world(self, root: Path, **kw: Any) -> World:
        return World(root, self.kind, cdf=self.cdf, how=self.how, **kw)

    def use(self, monkeypatch: Any) -> None:
        """Set this process up for the setup: the Delta sinks' write path."""
        if not self.native:
            monkeypatch.setattr("sverify.io.delta.local_path", lambda uri: None)

    def record(self) -> dict[str, Any]:
        return {"kind": self.kind, "native": self.native, "cdf": self.cdf, "how": self.how}


#: The setups, by name: Delta (DuckDB-written files, delta-rs MERGE, or no
#: Change Data Feed), dropped files with a cursor, and Iceberg.
SETUPS = {
    "delta": Setup("delta"),
    "delta-arrow": Setup("delta", native=False),
    "delta-full": Setup("delta", cdf=False),
    "files": Setup("files"),
    "iceberg": Setup("iceberg"),
}
