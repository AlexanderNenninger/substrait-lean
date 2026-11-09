"""Sinks: where `Node.write` stores a node. sverify decides what to write
and when (exactly once per state, with the contract); a sink only writes.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public names (`Sink`, `SinkChange`, `sink_from`) are re-exported by
`sverify.io`.
"""

from __future__ import annotations

import warnings
from abc import ABC, abstractmethod
from collections.abc import Callable, Sequence
from dataclasses import dataclass, replace
from functools import cached_property
from typing import TYPE_CHECKING, Any, ClassVar

import pyarrow as pa

from sverify import _deprecated
from sverify._scan import Resident
from sverify._state import arrow_of
from sverify._unsupported import SverifyWarning
from sverify._weighted import ChangeLog, consolidated, expanded, split, weighted
from sverify.incremental import Snapshot, SourceBatch, Stored, VersionedSource, first_line
from sverify.io._common import (
    ConcurrentWriteError,
    Contract,
    SinkWrite,
    check_same_state,
    other_tables,
    public_uri,
    sink_schema,
    view_contract_record,
)
from sverify.io._credentials import declared
from sverify.io._secrets import Secret
from sverify.observation import PLAN_BOUND, Observation
from sverify_duckdb import DuckDBStore

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
            it can tell the state it holds (`Sink.contract`).
        schema: The table's schema: the node's columns, NOT NULL where the
            node proves it.
        replace: True if the sink's contents must be replaced by `table`:
            the first write, contents this process did not write, or
            contents another plan wrote. Then `inserts` is `table` and
            `deletes` is empty.
    """

    def __init__(
        self,
        view: IncrementalView,
        contract: Contract,
        schema: pa.Schema,
        change: pa.Table | None,
    ):
        self.contract, self.schema = contract, schema
        self.replace = change is None
        self._view, self._change = view, change

    @cached_property
    def table(self) -> pa.Table:
        """The node's whole state."""
        return expanded(arrow_of(self._view.state)).cast(self.schema)

    @property
    def change(self) -> pa.Table:
        """The weighted change from the state written last to this one
        (`sverify._weighted`): the copies each row gains or loses, as the
        view's changes since then add up."""
        assert self._change is not None
        return self._change

    @cached_property
    def _native(self) -> tuple[Resident, Resident] | None:
        """The state and the change as tables DuckDB holds, when the view
        keeps its state in DuckDB (`sverify._state.DuckDBStore`): the new
        state's rows (a DuckDB view), and the weighted change since the
        state written last (with `replace`, the whole state), computed by
        the view's merge plan in DuckDB. None otherwise: write the Arrow
        tables."""
        view = self._view
        state = view.state
        if not isinstance(state, Resident):
            return None
        rows = view.store.expanded(state)
        assert isinstance(rows, Resident)
        if self._change is None:
            return rows, state
        return rows, DuckDBStore().keep_table(self._change)

    @cached_property
    def _split(self) -> tuple[pa.Table, pa.Table]:
        if self._change is None:
            return self.table, self.schema.empty_table()
        inserts, deletes = split(self.change)
        return inserts.cast(self.schema), deletes.cast(self.schema)

    @property
    def inserts(self) -> pa.Table:
        """The rows to add (with `replace`, every row)."""
        return self._split[0]

    @property
    def deletes(self) -> pa.Table:
        """The rows to remove, one copy each (with `replace`, none)."""
        return self._split[1]


class Sink:
    """Where `node.write(sink)` stores a node: subclass it and implement
    `write`.

    Every refresh hands `write` the node's new state as a `SinkChange`: the
    rows added and removed since the last write, or the whole table, with
    the contract to record. sverify writes each state exactly once: it skips
    a state whose `contract.epoch` the sink has already committed
    (`contract`), unless another plan (`contract.plan`) committed it, or
    the committed state was computed from other tables (a source with
    another table id, `contract.table_ids`, or at a lower version: dropped
    and created again): then the whole table replaces those rows. By default that record is
    kept in memory; override `contract` to read it back from the sink, so
    a restarted job does not write a state again. The nodes reading the stored node read what this
    process wrote, with its exact changes, unless `source` returns a source
    that reads the sink. A restarted job writes its first state in full.

    When two processes refresh the same sink, `write` must fail for the one
    that commits second: raise `sverify.errors.ConcurrentWriteError` if the
    sink no longer holds what `contract` returned. Its next refresh then
    writes the whole table, or skips the state the other writer committed.

    Args:
        name: The stored table's name in the plans that read it.
        app_id: Identifies the writer in what the sink records. Default:
            `"sverify:<name>"`.
        location: Where the table is, for reports and errors. Default:
            `name`.
        reproducible: What a rerun of a state must reproduce
            (`sv.equivalent(...)`): the sink commits each epoch
            once, so a rerun has to give the same rows up to this. Default:
            rows as a multiset, doubles within the bound the checker proves
            for the plan (`Report.epsilon`, `sv.equivalent(floats="plan")`),
            other values exact. A sink whose consumers need the same bits
            on a rerun states `sv.equivalent()`; one with a fixed tolerance
            states it, for example `sv.equivalent(floats=sv.within(rel=1e-12))`.

    Attributes:
        name: The stored table's name in the plans that read it.
        app_id: Identifies the writer.
        location: Where the table is.
        reproducible: What a rerun must reproduce.

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

            def contract(self, version=None):
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
    reproducible: Observation = PLAN_BOUND
    _view: IncrementalView | None = None
    _written: int | None = None
    _keeps_retired = False
    """Whether the sink keeps the rows a view drops from its state
    (`sverify.arrives_within`): it writes each change, and the whole table
    only when `SinkChange.replace`. A view with a sink that does not retires
    nothing."""
    """The view's serial (`IncrementalView.serial`) at the state written
    last; None: the sink's contents are replaced on the next write."""
    _last: Contract | None = None
    _synced: tuple | None = None
    """The record (`_state_key`) of the commit `_written` is: the one this
    process wrote, skipped to or resumed from. A change is written only on
    top of it; another commit there means another writer's state (#963)."""
    _kept: _Kept | None = None
    _pending: tuple[int, Contract] | None = None
    """The view's serial and the contract of a write that raised: its commit
    may have landed before the error (reading the version back, say)."""

    def __init__(
        self,
        name: str,
        *,
        app_id: str | None = None,
        location: str | None = None,
        reproducible: Observation | None = None,
    ):
        self.name = name
        self.app_id = app_id or f"sverify:{name}"
        self.location = public_uri(location) if location else name
        if reproducible is not None:
            self.reproducible = reproducible

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

    def contract(self, version: int | None = None) -> Contract | None:
        """The contract of the last state the sink committed, so that a
        state is written once. Override it to read the contract back from
        the sink (see the example).

        Args:
            version: The sink's version to look at, where it keeps a
                history (`DeltaSink`, `IcebergSink`). Default: the latest.

        Returns:
            The contract the last write recorded, or None if there is none.
            Default: the one this process wrote last.

        Raises:
            ValueError: A `version` for a sink that keeps no history.
        """
        if version is not None:
            raise ValueError(f"{type(self).__name__} keeps no history: contract(version=None)")
        return self._last

    def committed(self) -> Contract | None:
        """Deprecated: `contract()`."""
        warnings.warn(
            "Sink.committed() is deprecated; call sink.contract()",
            DeprecationWarning,
            stacklevel=2,
        )
        return self.contract()

    def __init_subclass__(cls, **kwargs: Any) -> None:
        super().__init_subclass__(**kwargs)
        # A sink of 0.x overrides `committed`: read it as `contract`.
        if "committed" in cls.__dict__ and "contract" not in cls.__dict__:
            warnings.warn(
                f"{cls.__name__} overrides Sink.committed(), which is deprecated; "
                "override contract(version=None) instead",
                DeprecationWarning,
                stacklevel=2,
            )
            legacy = cls.__dict__["committed"]

            def contract(self: Sink, version: int | None = None) -> Contract | None:
                if version is not None:
                    raise ValueError(f"{type(self).__name__} keeps no history")
                return legacy(self)

            cls.contract = contract  # type: ignore[method-assign]

    def source(self) -> VersionedSource | None:
        """The stored table as a versioned source, for the nodes reading the
        stored node.

        Returns:
            A source that reads the sink, or None (the default): they read
            what this process wrote.
        """
        return None

    # -- what `Node.write` and `refresh` call --------------------------------

    def _attach(self, view: IncrementalView, stored: Stored | None = None) -> None:
        """Write `view` from now on; `stored` is what the view resumed from."""
        self._view = view
        view._sinks.append(self)
        self._written, self._pending, self._synced = None, None, None
        if view.stored is not None and view.stored[0] == self.location and stored is not None:
            self._written = view.serial
            self._synced = _state_key(stored)

    def _foreign(self) -> bool:
        """Whether another writer changed rows after the commit `contract()`
        read last (#966): then the sink does not hold the state its record
        names. False by default: the sink is trusted as its only writer."""
        return False

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

    # -- the quarantine table (#184) ------------------------------------------

    def _quarantine_default(self) -> Sink | None:
        """Where the rows a node sets aside go when `write` names no
        `quarantine`: a table next to this one, or None (kept in memory)."""
        return None

    def _write_quarantine(self, rows: pa.Table, record: dict[str, Any]) -> None:
        """Replace the table's rows by `rows` (`_quarantine.TABLE_SCHEMA`),
        recording `record` with the commit."""
        raise TypeError(f"{type(self).__name__} cannot hold a node's quarantine")

    def _read_quarantine(self) -> tuple[pa.Table, dict[str, Any]] | None:
        """The rows and the record of the last quarantine write, or None."""
        return None

    def _commit(self) -> SinkWrite:
        """Write the attached view's state, unless the sink has it."""
        view = self._view
        if view is None:
            raise ValueError(f"no node is stored in {self.location}: node.write(sink) attaches one")
        contract = view_contract_record(view)
        done = self.contract()
        pending, self._pending = self._pending, None
        if (
            pending is not None
            and done is not None
            and (done.plan, done.epoch, done.digests)
            == (pending[1].plan, pending[1].epoch, pending[1].digests)
        ):
            # The last write raised after its commit landed: the sink holds
            # that state, as a restarted job finds it. Write on from there.
            self._written, self._last = pending
            self._synced = _state_key(pending[1])
        if done is not None and done.plan == contract.plan and not other_tables(done, contract):
            contract = _align(view, done, contract)
        if done is not None and (
            done.plan != contract.plan or other_tables(done, contract) or self._foreign()
        ):
            # Another plan's rows, rows computed from other tables (a
            # source dropped and created again, #516), or rows another
            # writer changed since (#966): neither skip this epoch, which
            # says nothing about these rows, nor write a change on top of
            # them; replace them.
            self._written = None
        elif done is not None and (
            done.epoch >= contract.epoch or _same_contents(view, done, contract)
        ):
            check_same_state(self.location, done, contract)
            # The sink holds this view's state only if it was computed from
            # the same source versions (or the same contents of a source that
            # cannot restore); else (another writer is ahead, #517) the next
            # write replaces it.
            same = done.sources == contract.sources or _same_contents(view, done, contract)
            self._written = view.serial if same else None
            self._synced = _state_key(done) if self._written is not None else None
            self._keep(view, contract, None)
            return SinkWrite("skipped", self._version(), contract)
        elif self._written is not None and done is not None and _state_key(done) != self._synced:
            # Another commit than the one this process wrote, skipped to or
            # resumed from: a change since `_written` would land on a state
            # it was not computed from (a second writer, or the late commit
            # of a crashed one). Replace the rows (#963).
            self._written = None
        since = None if self._written is None else view.changes_since(self._written)
        change = SinkChange(view, contract, sink_schema(view, contract.not_null), since)
        self._pending = (view.serial, contract)
        try:
            out = self.write(change)
        except ConcurrentWriteError:
            # Not committed: the sink holds another writer's state, so the
            # next write replaces it (or skips, if it is this state).
            self._pending, self._written = None, None
            raise
        self._pending = None
        if out is None:
            mode = "overwrite" if change.replace else "update"
            n_in, n_out = change.inserts.num_rows, change.deletes.num_rows
            out = SinkWrite(mode, self._version(), contract, n_in, n_out)
        self._written = view.serial
        self._last = contract
        self._synced = _state_key(contract)
        self._keep(view, contract, change)
        return out

    def _keep(self, view: IncrementalView, contract: Contract, change: SinkChange | None) -> None:
        """Hand the written state to the nodes reading the stored node, when
        they read it from this process."""
        kept = self._kept
        if kept is None or (kept.table is not None and kept.epoch == contract.epoch):
            return
        table = view.con._arrow[view.name]
        before = kept.table
        retired = view.retired_through is not None and before is not None
        if retired and change is not None and not change.replace:
            # The view's rows are its open buckets; the kept table has them all.
            old = weighted(before.cast(table.schema), 1)
            table = expanded(consolidated(old, change.change)).cast(table.schema)
        if change is None or change.replace or kept.table is None:
            kept.put(contract.epoch, table, None)
        else:
            kept.put(contract.epoch, table, (change.inserts, change.deletes))


_UNREAD = object()
"""`_TableSink._read` before `contract` ran."""


_deprecated.add(Sink, {"view": "_view", "keeps_retired": "_keeps_retired"})
_deprecated.add(SinkChange, {"native": "_native"})


class _TableSink[T](Sink, ABC):
    """What `DeltaSink` and `IcebergSink` share: the contract and epoch read
    back from the table (`contract`), the write (create or open the table,
    then DuckDB's files, else Arrow, then read the version back), the check
    that no other writer committed in between (#517, #534), and maintenance
    after every `compact_every` writes.

    A subclass implements the hooks on its table `T`: `_open`, `_epoch_of`,
    `_contract_of`, `_create`, `_write_native`, `_write_arrow`, `_maintain`
    and `_version`, and may override `_opened`."""

    _create_errors: ClassVar[tuple[type[Exception], ...]] = ()
    """What `_create` raises when another writer created the table first."""
    _commit_errors: ClassVar[tuple[type[Exception], ...]] = ()
    """What a commit raises when another writer committed first."""

    def __init__(
        self,
        name: str,
        *,
        app_id: str | None,
        location: str,
        compact_every: int | None,
        reproducible: Observation | None = None,
    ):
        super().__init__(name, app_id=app_id, location=location, reproducible=reproducible)
        if compact_every is not None and compact_every < 1:
            raise ValueError(f"compact_every must be at least 1, got {compact_every}")
        self.compact_every = compact_every
        self._writes = 0
        """Writes of this process since the last compaction."""
        self._read: int | None | object = _UNREAD
        """The epoch of this sink's `app_id` that `committed` read last: a
        write commits only on top of it (#517, #534)."""
        self._read_kept = True
        """Whether every commit after the app's last one, when `contract()`
        read it, kept its rows (`last_record(...).kept`)."""
        self._read_table: T | None = None
        """The table `contract()` read, which the next write goes through: the
        table format's own conflict check then covers every commit since the
        read. An epoch's value can come back (another plan's commit at the
        same epoch, #964), so comparing it alone lets a stale write through."""

    # -- what a table format implements --------------------------------------

    @abstractmethod
    def _open(self) -> T | None:
        """The table as it is now, or None if there is none."""

    @abstractmethod
    def _epoch_of(self, table: T) -> int | None:
        """The epoch of the last commit of `app_id` in `table`, or None."""

    @abstractmethod
    def _contract_of(self, table: T) -> Contract | None:
        """The contract `table` records, or None."""

    def _head_of(self, table: T) -> tuple[int | None, Contract | None, bool]:
        """The epoch of the app's last commit in `table` (or None), the
        contract `table` records, and whether every commit after the app's
        last one keeps its rows. Default: `_epoch_of`, `_contract_of`, kept."""
        done = self._epoch_of(table)
        return done, None if done is None else self._contract_of(table), True

    @abstractmethod
    def _create(self, change: SinkChange) -> T:
        """Create the table for `change`, empty or with its rows; raises one
        of `_create_errors` if it exists by then."""

    def _opened(self, table: T, created: bool, change: SinkChange) -> T:
        """Get the table ready for the write, once it exists. Default: as
        it is."""
        return table

    @abstractmethod
    def _write_native(self, table: T, created: bool, change: SinkChange) -> SinkWrite | None:
        """Commit the files DuckDB writes (`change._native`): the state, if
        `created`, else the change. None if only `_write_arrow` can write
        it. The version is filled in afterwards."""

    @abstractmethod
    def _write_arrow(self, table: T, created: bool, change: SinkChange) -> SinkWrite:
        """Commit the Arrow tables of `change`: the state, if `created` or
        `change.replace`, else the change."""

    @abstractmethod
    def _maintain(self) -> None:
        """The maintenance every `compact_every` writes."""

    # -- the shared skeleton ---------------------------------------------------

    def contract(self, version: int | None = None) -> Contract | None:
        """The contract of the last commit with this sink's `app_id`, with
        its epoch, or None.

        Args:
            version: The table's version to look at (a Delta version, an
                Iceberg snapshot's sequence number): the contract recorded
                up to it, as the table as a source reads it
                (`source().contract(version)`). Default: the latest.
        """
        if version is not None:
            return self.source().contract(version)  # type: ignore[union-attr]
        table = self._open()
        done, contract, kept = (None, None, True) if table is None else self._head_of(table)
        self._read, self._read_kept, self._read_table = done, kept, table
        if done is None or contract is None:
            return None
        return replace(contract, epoch=done)

    def _foreign(self) -> bool:
        return not self._read_kept

    def write(self, change: SinkChange) -> SinkWrite:
        """Create the table, overwrite it, or write the change, in a commit
        that records the contract and the epoch.

        The commit is conditional: it is made only while the epoch of
        `app_id` in the table is still the one `contract` read. Otherwise
        the losing writer raises `ConcurrentWriteError`."""
        try:
            return self._write(change)
        except self._commit_errors as e:
            raise self._conflict(change.contract, self._commit_error(e)) from e

    def _commit_error(self, e: Exception) -> str:
        """Why a commit failed, for `ConcurrentWriteError`."""
        return first_line(e)

    def _conflict(self, contract: Contract, why: str) -> ConcurrentWriteError:
        read = "none" if self._read in (None, _UNREAD) else f"epoch {self._read}"
        return ConcurrentWriteError(
            f"{self.location}: another writer committed to the sink ({self.app_id}) while this "
            f"refresh wrote epoch {contract.epoch}, after it read {read} ({why}); this state "
            "was not committed. Is another process refreshing the same sink? The next "
            "refresh writes the whole table, or skips the state the other writer committed."
        )

    def _version_after(self, table: T) -> int | None:
        """The sink's version after a write through `table`. Default: read
        again (`_version`)."""
        return self._version()

    def _check(self, table: T, contract: Contract, then: int | None | object) -> None:
        """Raise unless `table` still has the epoch `then`: what `committed`
        read, or what this write committed last."""
        if then is _UNREAD:
            return
        now = self._epoch_of(table)
        if now != then:
            raise self._conflict(contract, f"the table now has epoch {now}")

    def _write(self, change: SinkChange) -> SinkWrite:
        contract, read = change.contract, self._read
        table, self._read_table = self._read_table, None
        if table is None:
            table = self._open()
        created = table is None
        if table is None:
            if read not in (None, _UNREAD):
                raise self._conflict(contract, "the table is gone")
            try:
                table = self._create(change)
            except self._create_errors as e:
                if self._open() is not None:
                    raise self._conflict(contract, "it created the table") from e
                raise
        else:
            self._check(table, contract, read)
        table = self._opened(table, created, change)
        out = None
        if change._native is not None and (created or not change.replace):
            out = self._write_native(table, created, change)
        if out is None:
            out = self._write_arrow(table, created, change)
        return replace(out, version=self._version_after(table))

    def _commit(self) -> SinkWrite:
        out = super()._commit()
        if out.mode == "skipped" or self.compact_every is None:
            return out
        self._writes += 1
        if self._writes >= self.compact_every:
            self._writes = 0
            try:
                self._maintain()
            except Exception as e:  # noqa: BLE001 - the write is committed
                warnings.warn(
                    f"{self.location}: maintenance failed: {first_line(e)}",
                    SverifyWarning,
                    stacklevel=2,
                )
        return out


def _state_key(record: Contract | Stored) -> tuple:
    """What identifies the state a sink's record names: the plan, the source
    versions and the static tables' digests."""
    return record.plan, sorted(record.sources.items()), sorted(record.digests.items())


def _snapshot_sources(view: IncrementalView) -> dict[str, Any]:
    """The sources of `view` that cannot restore (`Source` without
    `restore`): their versions count this process's reads."""
    from sverify.io._source import Source

    return {
        t: s for t, s in view.pipeline.sources.items() if isinstance(s, Source) and not s._durable()
    }


def _same_contents(view: IncrementalView, done: Contract, contract: Contract) -> bool:
    """Whether `done` names the state `contract` does: the same versions,
    or for a source that cannot restore, the same content digest."""
    if done.sources.keys() != contract.sources.keys():
        return False
    snapshots = _snapshot_sources(view)
    return all(
        n == done.sources[t]
        or (
            t in snapshots
            and contract.digests.get(t) is not None
            and contract.digests.get(t) == done.digests.get(t)
        )
        for t, n in contract.sources.items()
    )


def _align(view: IncrementalView, done: Contract, contract: Contract) -> Contract:
    """Number a source that cannot restore above the version `done`
    records, where `done` records other contents at a version not below
    this process's: two processes number their reads independently, so an
    equal or higher version says nothing about which contents are newer
    (#965). The renumbered version changes nothing (`Source._above`); the
    contract to write is then above `done`'s."""
    moved = False
    versions = view.pipeline.versions
    for t, src in _snapshot_sources(view).items():
        theirs, ours = done.sources.get(t), contract.sources.get(t)
        if theirs is None or ours is None or theirs < ours:
            continue
        if done.digests.get(t) == contract.digests.get(t):
            continue
        st = src._state
        if st is None or st.version != ours or versions.get(t) != ours:
            continue
        src._above(theirs)
        versions[t] = st.version
        moved = True
    return view_contract_record(view) if moved else contract


@dataclass
class _Write:
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
        self.log: ChangeLog[_Write] = ChangeLog(KEEP)

    def put(self, epoch: int, table: pa.Table, change: tuple[pa.Table, pa.Table] | None) -> None:
        """The next version: `table`, which `change` (inserts, deletes) made
        from the last, or which replaces it (None)."""
        self.version += 1
        self.epoch, self.table = epoch, table
        if change is None:
            self.log.reset(self.version)
        else:
            self.log.add(self.version, _Write(*change))

    def _resume_after(self, version: int, cursor: object = None, digest: object = None) -> None:
        """Number the versions above `version`, which a sink downstream
        recorded in an earlier process (`sverify.io.Source._resume_after`;
        a stored node records no cursor)."""
        if self.version > version:
            return
        if self.table is None:
            self.version = version
        else:
            self.version = version + 1
            self.log.add(self.version, _Write(None, None))

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
        writes = self.log.since(since)
        if writes is None:
            return SourceBatch.from_snapshot(
                since, self.version, table, reason=f"{self.name} was rewritten since v{since}"
            )
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
        self.credentials: tuple[Secret, ...] = ()

    def write(self, change: SinkChange) -> SinkWrite:
        self.fn(change.table)
        return SinkWrite("overwrite", None, change.contract, change.table.num_rows, 0)


def sink_from(
    fn: Callable[[pa.Table], Any],
    *,
    name: str,
    credentials: str | Secret | Sequence[str | Secret] | None = None,
) -> Sink:
    """A sink that hands the node's whole table to `fn` whenever it
    changes: `node.write(sink_from(save, name="paid"))`.

    Each state is written once per process: a refresh that changes nothing
    does not call `fn`. A restarted job calls it again with the table it
    computes.

    Args:
        fn: Called with the table (an Arrow table) to store; what it returns
            is ignored.
        name: The stored table's name in the plans that read it.
        credentials: The secrets `fn` writes with, by name or reference
            (`sverify.io.Secret`), so reports list them. Read one
            inside `fn` with `Secret(name).value()`. Default: none.

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
    out = _FnSink(fn, name)
    out.credentials = declared(credentials)
    return out
