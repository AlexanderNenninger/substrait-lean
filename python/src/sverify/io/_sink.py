"""Sinks: where `Node.write` stores a node. sverify decides what to write
and when (exactly once per state, with the contract); a sink only writes.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public names (`Sink`, `SinkChange`, `sink_from`) are re-exported by
`sverify.io`.
"""

from __future__ import annotations

from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass
from functools import cached_property
from typing import TYPE_CHECKING, Any

import pyarrow as pa

from sverify.incremental import Snapshot, SourceBatch, Stored, VersionedSource
from sverify.io._common import (
    Contract,
    SinkWrite,
    check_same_state,
    sink_schema,
    view_contract_record,
)

if TYPE_CHECKING:
    from sverify.incremental import IncrementalView

KEEP = 64
"""Writes the in-memory table of a sink keeps for the nodes reading it."""


class SinkChange:
    """What a sink writes for one state of its node: the change since the
    state it wrote last, or the whole table.

    The tables are built when first used, so a sink that reads only
    `inserts` and `deletes` does not build `table`.

    Attributes:
        contract: What to record with the write (`Contract`): the node, the
            plan, the source versions and what the node proved about every
            row. `contract.epoch` grows with every state; a sink that stores
            it can tell the state it holds (`Sink.committed`).
        schema: The table's schema: the node's columns, NOT NULL where the
            node proves it.
        replace: True if the sink's contents must be replaced by `table`:
            the first write, or contents this process did not write. Then
            `inserts` is `table` and `deletes` is empty.
    """

    def __init__(
        self,
        view: IncrementalView,
        contract: Contract,
        schema: pa.Schema,
        old: Counter[tuple] | None,
    ):
        self.contract, self.schema = contract, schema
        self.replace = old is None
        self._view, self._old, self._new = view, old, Counter(view.counts)

    @cached_property
    def table(self) -> pa.Table:
        """The node's whole state."""
        return self._view._arrow(self._new).cast(self.schema)

    @cached_property
    def inserts(self) -> pa.Table:
        """The rows to add (with `replace`, every row)."""
        if self._old is None:
            return self.table
        return self._view._arrow(self._new - self._old).cast(self.schema)

    @cached_property
    def deletes(self) -> pa.Table:
        """The rows to remove, one copy each (with `replace`, none)."""
        if self._old is None:
            return self.schema.empty_table()
        return self._view._arrow(self._old - self._new).cast(self.schema)


class Sink:
    """Where `node.write(sink)` stores a node: subclass it and implement
    `write`.

    Every refresh hands `write` the node's new state as a `SinkChange`: the
    rows added and removed since the last write, or the whole table, with
    the contract to record. sverify writes each state exactly once: it skips
    a state whose `contract.epoch` the sink has already committed
    (`committed`). By default that record is kept in memory; override
    `committed` to read it back from the sink, so a restarted job does not
    write a state again. The nodes reading the stored node read what this
    process wrote, with its exact changes, unless `source` returns a source
    that reads the sink. A restarted job writes its first state in full.

    Args:
        name: The stored table's name in the plans that read it.
        app_id: Identifies the writer in what the sink records. Default:
            `"sverify:<name>"`.
        location: Where the table is, for reports and errors. Default:
            `name`.

    Attributes:
        name: The stored table's name in the plans that read it.
        app_id: Identifies the writer.
        location: Where the table is.

    Examples:
        A sink that writes each state as a Parquet file, and keeps the
        contract next to it:

        ```python
        import tempfile
        from pathlib import Path

        import pyarrow as pa
        import pyarrow.parquet as pq
        import sverify as sv
        from sverify.io import Contract, Sink, StaticSource


        class ParquetSink(Sink):
            def __init__(self, path):
                super().__init__(Path(path).stem, location=str(path))
                self.path = Path(path)
                self.record = self.path.with_suffix(".contract.json")

            def committed(self):
                if not self.record.exists():
                    return None
                return Contract.from_json(self.record.read_text())

            def write(self, change):
                pq.write_table(change.table, self.path)
                self.record.write_text(change.contract.to_json())


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")
        out = Path(tempfile.mkdtemp()) / "big_orders.parquet"
        big = big_orders(orders).write(ParquetSink(out))
        print(big.refresh().writes[0])  # big_orders from orders@v0: overwrite, 1 row(s) ...
        print(big.refresh().writes[0])  # big_orders from orders@v0: already committed
        ```
    """

    name: str
    app_id: str
    location: str
    view: IncrementalView | None = None
    _written: Counter[tuple] | None = None
    _last: Contract | None = None
    _kept: _Kept | None = None

    def __init__(self, name: str, *, app_id: str | None = None, location: str | None = None):
        self.name = name
        self.app_id = app_id or f"sverify:{name}"
        self.location = location or name

    # -- what a sink implements ---------------------------------------------

    def write(self, change: SinkChange) -> SinkWrite | None:
        """Write one state of the node.

        Args:
            change: The change since the last write, or the whole table
                (`change.replace`), with the contract to record.

        Returns:
            What the write did, or None: then the refresh report says the
            sink wrote `change.inserts` and `change.deletes`.
        """
        raise NotImplementedError(f"{type(self).__name__} does not implement write()")

    def committed(self) -> Contract | None:
        """The contract of the last state the sink committed, so that a
        state is written once. Override it to read the contract back from
        the sink (see the example).

        Returns:
            The contract the last write recorded, or None if there is none.
            Default: the one this process wrote last.
        """
        return self._last

    def source(self) -> VersionedSource | None:
        """The stored table as a versioned source, for the nodes reading the
        stored node.

        Returns:
            A source that reads the sink, or None (the default): they read
            what this process wrote.
        """
        return None

    # -- what `Node.write` and `refresh` call --------------------------------

    def _attach(self, view: IncrementalView) -> None:
        """Write `view` from now on."""
        self.view = view
        self._written = None
        if view.stored is not None and view.stored[0] == self.location:
            self._written = view.stored[1]

    def _stored(self) -> Stored | None:
        """The state a restarted job resumes from: none by default."""
        return None

    def _source(self) -> VersionedSource:
        source = self.source()
        if source is not None:
            return source
        if self._kept is None:
            self._kept = _Kept(self.name)
        return self._kept

    def _version(self) -> int | None:
        """The sink's version, for the refresh report."""
        return None

    def _commit(self) -> SinkWrite:
        """Write the attached view's state, unless the sink has it."""
        view = self.view
        if view is None:
            raise ValueError(f"no node is stored in {self.location}: node.write(sink) attaches one")
        contract = view_contract_record(view)
        done = self.committed()
        if done is not None and done.epoch >= contract.epoch:
            check_same_state(self.location, done, contract)
            self._written = Counter(view.counts)
            self._keep(view, contract, None)
            return SinkWrite("skipped", self._version(), contract)
        change = SinkChange(view, contract, sink_schema(view, contract.not_null), self._written)
        out = self.write(change)
        if out is None:
            mode = "overwrite" if change.replace else "update"
            n_in, n_out = change.inserts.num_rows, change.deletes.num_rows
            out = SinkWrite(mode, self._version(), contract, n_in, n_out)
        self._written = Counter(view.counts)
        self._last = contract
        self._keep(view, contract, change)
        return out

    def _keep(self, view: IncrementalView, contract: Contract, change: SinkChange | None) -> None:
        """Hand the written state to the nodes reading the stored node, when
        they read it from this process."""
        kept = self._kept
        if kept is None or (kept.table is not None and kept.epoch == contract.epoch):
            return
        table = view.con.arrow[view.name]
        if change is None or change.replace or kept.table is None:
            kept.put(contract.epoch, table, None)
        else:
            kept.put(contract.epoch, table, (change.inserts, change.deletes))


@dataclass
class _Write:
    version: int
    inserts: pa.Table | None
    deletes: pa.Table | None


class _Kept:
    """A stored node's table as this process wrote it: the source of the
    nodes reading it when the sink has none. Each write is a version."""

    def __init__(self, name: str):
        self.name = name
        self.version = 0
        self.epoch: int | None = None
        """The epoch of the state it holds."""
        self.table: pa.Table | None = None
        self.log: list[_Write] = []
        self.floor = 0

    def put(self, epoch: int, table: pa.Table, change: tuple[pa.Table, pa.Table] | None) -> None:
        """The next version: `table`, which `change` (inserts, deletes) made
        from the last, or which replaces it (None)."""
        self.version += 1
        self.epoch, self.table = epoch, table
        if change is None:
            self.log, self.floor = [], self.version
        else:
            self._log(_Write(self.version, *change))

    def _log(self, write: _Write) -> None:
        self.log.append(write)
        if len(self.log) > KEEP:
            self.floor = self.log.pop(0).version

    def _resume_after(self, version: int) -> None:
        """Number the versions above `version`, which a sink downstream
        recorded in an earlier process (`sverify.io.Source._resume_after`)."""
        if self.version > version:
            return
        if self.table is None:
            self.version = version
        else:
            self.version = version + 1
            self._log(_Write(self.version, None, None))

    def _table(self) -> pa.Table:
        if self.table is None:
            raise RuntimeError(f"{self.name} has not been written yet")
        return self.table

    def schema(self) -> pa.Schema:
        return self._table().schema

    def latest(self) -> int:
        self._table()
        return self.version

    def snapshot(self, version: int | None = None) -> Snapshot:
        if version not in (None, self.version):
            raise ValueError(f"{self.name} keeps only its latest write, v{self.version}")
        return Snapshot(self.version, self._table(), [])

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        table = self._table()
        if until not in (None, self.version):
            raise ValueError(f"{self.name} keeps only its latest write, v{self.version}")
        if since == self.version:
            return SourceBatch.unchanged(since)
        if since < self.floor:
            return SourceBatch.from_snapshot(
                since, self.version, table, reason=f"{self.name} was rewritten since v{since}"
            )
        writes = [w for w in self.log if w.version > since]
        empty = table.schema.empty_table()

        def rows(tables: list[pa.Table | None]) -> pa.Table:
            kept = [t.cast(table.schema) for t in tables if t is not None]
            return pa.concat_tables([*kept, empty])

        return SourceBatch.from_changes(
            since,
            self.version,
            inserts=rows([w.inserts for w in writes]),
            deletes=rows([w.deletes for w in writes]),
            trusted=f"Δ as written to {self.name} v{since}→v{self.version}",
            schema=table.schema,
        )


class _FnSink(Sink):
    def __init__(self, fn: Callable[[pa.Table], Any], name: str):
        super().__init__(name)
        self.fn = fn

    def write(self, change: SinkChange) -> SinkWrite:
        self.fn(change.table)
        return SinkWrite("overwrite", None, change.contract, change.table.num_rows, 0)


def sink_from(fn: Callable[[pa.Table], Any], *, name: str) -> Sink:
    """A sink that hands the node's whole table to `fn` whenever it
    changes: `node.write(sink_from(save, name="paid"))`.

    Each state is written once per process: a refresh that changes nothing
    does not call `fn`. A restarted job calls it again with the table it
    computes.

    Args:
        fn: Called with the table (an Arrow table) to store; what it returns
            is ignored.
        name: The stored table's name in the plans that read it.

    Returns:
        The sink.

    Examples:
        ```python
        import pyarrow as pa
        import sverify as sv
        from sverify.io import StaticSource, sink_from

        orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        big = big_orders(orders).write(
            sink_from(lambda t: t.to_pandas().to_csv("big.csv"), name="big")
        )
        ```
    """
    return _FnSink(fn, name)
