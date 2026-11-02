"""Iceberg tables (pyiceberg) as change sources and sinks.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Versions are snapshot sequence numbers. An `IcebergSource` reads the
change between two versions from the data files the snapshots in between
added, when all of them are appends (trusted, like a Delta change feed).
Otherwise (row-level deletes, overwrites) it diffs the two snapshots on the
data files that changed between them: a file removed or added, or one whose
delete files changed. Files with the same path and delete files are the same
rows in both (Iceberg files are immutable), so they cancel out of the diff
(`ChangeFeed.of_changed_files`), and only the changed files are read. Facts:
`required` fields (the schema) and per-file statistics from the manifests.

Iceberg has no CHECK constraints, so an `IcebergSink` stores the node's
contract in the table properties and the summary of every snapshot it
writes. A reader trusts that contract only while every snapshot of the
table was written under it (no other writer appended in between). The sink
writes a change as position delete files and a data file of the new rows,
one commit the size of the change.
"""

from __future__ import annotations

import uuid
from collections import Counter
from collections.abc import Iterable, Sequence
from dataclasses import replace
from typing import Any, Literal

import pyarrow as pa
import pyarrow.parquet as pq

try:
    from pyiceberg.catalog import Catalog
    from pyiceberg.expressions import AlwaysTrue
    from pyiceberg.io.pyarrow import (
        ArrowScan,
        _dataframe_to_data_files,
        _pyarrow_schema_ensure_small_types,
    )
    from pyiceberg.manifest import (
        DataFile,
        DataFileContent,
        FileFormat,
        ManifestContent,
        ManifestEntry,
        ManifestEntryStatus,
        ManifestFile,
        ManifestWriterV2,
    )
    from pyiceberg.table import FileScanTask, Table, Transaction
    from pyiceberg.table.snapshots import Operation
    from pyiceberg.table.snapshots import Snapshot as IcebergSnapshot
    from pyiceberg.table.update.snapshot import _FastAppendFiles
    from pyiceberg.typedef import Record
except ImportError as e:
    raise ImportError("sverify.io.iceberg needs iceberg: pip install 'sverify[iceberg]'") from e

from sverify._weighted import expanded, negated, positive
from sverify.contracts import Fact
from sverify.incremental import (
    Snapshot,
    SourceBatch,
    Stored,
    arrow_rows,
    first_line,
    row_key,
    snapshot_diff,
)
from sverify.io._common import ColumnStats, Contract, SinkWrite, q, stats_facts
from sverify.io._sink import Sink, SinkChange
from sverify.steps import Pipeable

CONTRACT = "Iceberg contract"
KEY = "sverify.contract"
PLAN = "sverify.plan"
EPOCH = "sverify.epoch"
APP = "sverify.app"


def _arrow_schema(t: Table) -> pa.Schema:
    return pa.schema([f.remove_metadata() for f in t.schema().as_arrow()])


def _layout(schema: pa.Schema) -> list[tuple[str, bool, pa.DataType]]:
    return [(f.name, f.nullable, f.type) for f in _pyarrow_schema_ensure_small_types(schema)]


def _replace_schema(tx: Transaction, old: pa.Schema, new: pa.Schema) -> None:
    """Make the table's schema `new` in `tx`, for rows that replace the
    table's (of another plan, maybe): drop the columns that are not in
    `new` as they are, then add the ones it lacks."""
    if _layout(old) == _layout(new):
        return
    keep = set(_layout(new))
    gone = [f.name for f, lay in zip(old, _layout(old), strict=True) if lay not in keep]
    if gone:
        with tx.update_schema(allow_incompatible_changes=True) as update:
            for name in gone:
                update.delete_column(name)
    with tx.update_schema(allow_incompatible_changes=True) as update:
        update.union_by_name(new)


def _ancestry(t: Table) -> list[IcebergSnapshot]:
    """The current snapshot and its ancestors, newest first."""
    out = []
    s = t.current_snapshot()
    while s is not None:
        out.append(s)
        s = None if s.parent_snapshot_id is None else t.snapshot_by_id(s.parent_snapshot_id)
    return out


def _at(t: Table, version: int) -> IcebergSnapshot | None:
    return next((s for s in _ancestry(t) if s.sequence_number == version), None)


def _version(s: IcebergSnapshot | None) -> int:
    return 0 if s is None else int(s.sequence_number or 0)


def _read(t: Table, s: IcebergSnapshot | None) -> pa.Table:
    schema = _arrow_schema(t)
    if s is None:
        return schema.empty_table()
    return t.scan(snapshot_id=s.snapshot_id).to_arrow().cast(schema)


def _live_files(t: Table, s: IcebergSnapshot | None) -> list[dict[str, Any]]:
    """Manifest entries of the data files in snapshot `s`."""
    if s is None:
        return []
    entries = t.inspect.entries(snapshot_id=s.snapshot_id).to_pylist()
    return [e for e in entries if e["status"] != 2 and e["data_file"]["content"] == 0]


def _stats(entry: dict[str, Any], names: list[str]) -> dict[str, ColumnStats]:
    """A data file's statistics. With delete files, they describe all its
    physical rows, which is still correct (`ColStats.Correct`)."""
    metrics = entry.get("readable_metrics") or {}
    rows = entry["data_file"].get("record_count")
    out = {}
    for c in names:
        m = metrics.get(c) or {}
        out[c] = ColumnStats(
            m.get("lower_bound"),
            m.get("upper_bound"),
            m.get("null_value_count"),
            rows,
            m.get("nan_value_count"),
        )
    return out


def _tasks(t: Table, s: IcebergSnapshot | None) -> dict[str, FileScanTask]:
    """The data files of snapshot `s`, each with the delete files it reads."""
    if s is None:
        return {}
    return {task.file.file_path: task for task in t.scan(snapshot_id=s.snapshot_id).plan_files()}


def _deletes_of(task: FileScanTask) -> frozenset[str]:
    return frozenset(d.file_path for d in task.delete_files)


def _changed_tasks(
    t: Table, old: IcebergSnapshot | None, new: IcebergSnapshot | None
) -> tuple[list[FileScanTask], list[FileScanTask]]:
    """The data files of `old` and of `new` that are not in the other with
    the same delete files: everything else is the same rows in both."""
    before, after = _tasks(t, old), _tasks(t, new)

    def same(task: FileScanTask, other: dict[str, FileScanTask]) -> bool:
        twin = other.get(task.file.file_path)
        return twin is not None and _deletes_of(twin) == _deletes_of(task)

    gone = [task for task in before.values() if not same(task, after)]
    came = [task for task in after.values() if not same(task, before)]
    return gone, came


def _scan(t: Table, tasks: Sequence[FileScanTask]) -> pa.Table:
    """The rows of `tasks` (data files with their deletes applied)."""
    if not tasks:
        return _arrow_schema(t).empty_table()
    return ArrowScan(t.metadata, t.io, t.schema(), AlwaysTrue()).to_table(tasks)


def contract_facts(t: Table) -> list[Fact]:
    """The contract the table's properties record, if every snapshot of the
    table was written under it."""
    text = t.properties.get(KEY)
    if text is None:
        return []
    c = Contract.from_json(text)
    if not all(s.summary is not None and s.summary.get(PLAN) == c.plan for s in _ancestry(t)):
        return []
    return [Fact(f"{q(col)} IS NOT NULL", CONTRACT) for col in c.not_null] + [
        Fact(sql, CONTRACT) for sql in c.checks.values()
    ]


class IcebergSource(Pipeable):
    """An Iceberg table of a catalog, read by snapshot sequence number, as
    the input of transforms. `name` is the table's name in the plans that
    read it (default: the last part of `identifier`).

    A refresh reads the files that appends added since the version a node's
    state was computed from; after row-level deletes or overwrites it diffs
    the data files that changed. Tables with equality deletes cannot be
    read.

    Args:
        catalog: A pyiceberg catalog.
        identifier: The table's identifier in it, e.g. `"db.readings"`.
        name: The table's name in the plans that read it. Default: the last
            part of `identifier`.

    Attributes:
        catalog: The catalog.
        identifier: The table's identifier.
        name: The table's name in the plans that read it.
    """

    def __init__(self, catalog: Catalog, identifier: str, *, name: str | None = None):
        self.catalog, self.identifier = catalog, identifier
        self.name = name or identifier.rsplit(".", 1)[-1]

    def table(self) -> Table:
        """The table as the catalog loads it now (a `pyiceberg.table.Table`)."""
        return self.catalog.load_table(self.identifier)

    def schema(self) -> pa.Schema:
        """The table's current schema, as Arrow."""
        return _arrow_schema(self.table())

    def latest(self) -> int:
        """The current snapshot's sequence number (0 before the first)."""
        return _version(self.table().current_snapshot())

    def _facts(self, t: Table, files: list[dict[str, Any]], source: str) -> list[Fact]:
        schema = _arrow_schema(t)
        stats = [_stats(e, schema.names) for e in files]
        return contract_facts(t) + stats_facts(stats, schema, source)

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The table's rows at a snapshot, with what its metadata says about
        every row (`required` fields, file statistics, and the contract of
        an `IcebergSink` that wrote every snapshot).

        Args:
            version: A snapshot sequence number of the current snapshot's
                ancestry; 0 is the empty table before the first snapshot.
                Default: the current snapshot.

        Returns:
            The version, the rows and the facts.

        Raises:
            ValueError: No ancestor has that sequence number.
        """
        t = self.table()
        s = t.current_snapshot() if version is None else _at(t, version)
        if version is not None and s is None and version != 0:
            raise ValueError(f"{self.identifier} has no snapshot with sequence number {version}")
        v = _version(s)
        files = _live_files(t, s)
        return Snapshot(v, _read(t, s), self._facts(t, files, f"file stats @v{v}"))

    def contract(self) -> Contract | None:
        """The contract the table property `sverify.contract` records, or
        None if it has none."""
        text = self.table().properties.get(KEY)
        return None if text is None else Contract.from_json(text)

    def stored(self) -> Stored | None:
        """The node state the current snapshot stored, if an `IcebergSink`
        wrote it under the table's contract. A restarted job's first refresh
        resumes the sink's node from it, when it was stored by the same plan
        from the same sources.

        Returns:
            The stored state, or None if the current snapshot was not
            written under the contract.
        """
        t = self.table()
        s, text = t.current_snapshot(), t.properties.get(KEY)
        if s is None or s.summary is None or text is None:
            return None
        c = Contract.from_json(text)
        if s.summary.get(PLAN) != c.plan or s.summary.get(EPOCH) != str(c.epoch):
            return None
        where = f"{self.identifier}@v{_version(s)}"
        return Stored(where, self.identifier, c.plan, c.sources, c.digests, _read(t, s))

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        """The change from sequence number `since` to `until`, as a refresh
        reads it.

        Args:
            since: The version the node's state was computed from.
            until: A snapshot sequence number to read up to. Default: the
                current snapshot.

        Returns:
            The rows of the files appends added (trusted), or the diff of
            the data files that changed (exact); or, where snapshot `since`
            is gone or unreadable, the snapshot at `until` and the reason.

        Raises:
            ValueError: No ancestor has sequence number `until`.
        """
        t = self.table()
        current = t.current_snapshot() if until is None else _at(t, until)
        if until is not None and current is None and until != 0:
            raise ValueError(f"{self.identifier} has no snapshot with sequence number {until}")
        end = _version(current)
        files = _live_files(t, current)
        snapshot_facts = self._facts(t, files, f"file stats @v{end}")
        if end == since:
            return SourceBatch.unchanged(since, snapshot_facts)
        between = [s for s in _ancestry(t) if since < _version(s) <= end]
        old = _at(t, since)
        schema = _arrow_schema(t)
        if since != 0 and old is None:
            return SourceBatch.from_snapshot(
                since,
                end,
                _read(t, current),
                reason=f"Iceberg snapshot v{since} is not an ancestor of v{end} (expired?)",
                snapshot_facts=snapshot_facts,
                schema=schema,
            )
        appends = all(
            s.summary is not None and s.summary.operation == Operation.APPEND for s in between
        )
        if not appends:
            ops = sorted({str(s.summary.operation.value) for s in between if s.summary})
            try:
                gone, came = _changed_tasks(t, old, current)
                diff = snapshot_diff(_scan(t, gone).cast(schema), _scan(t, came).cast(schema))
            except Exception as e:
                return SourceBatch.from_snapshot(
                    since,
                    end,
                    _read(t, current),
                    reason=f"Iceberg snapshots v{since}→v{end} unreadable: {first_line(e)}",
                    snapshot_facts=snapshot_facts,
                    schema=schema,
                )
            paths = {task.file.file_path for task in came}
            changed = [e for e in files if e["data_file"]["file_path"] in paths]
            return SourceBatch.from_changes(
                since,
                end,
                inserts=expanded(positive(diff)),
                deletes=expanded(positive(negated(diff))),
                facts=self._facts(t, changed, f"file stats @v{end} (changed files)"),
                snapshot_facts=snapshot_facts,
                kind="snapshot diff",
                schema=schema,
                trusted=(
                    f"Δ = snapshot v{end} − snapshot v{since} on the {len(gone)} + "
                    f"{len(came)} data file(s) that changed (not append-only: "
                    f"{', '.join(ops)}); only the snapshots are trusted"
                ),
            )
        added = [e for e in files if int(e["sequence_number"]) > since]
        paths = {e["data_file"]["file_path"] for e in added}
        assert current is not None
        tasks = [
            task
            for task in t.scan(snapshot_id=current.snapshot_id).plan_files()
            if task.file.file_path in paths
        ]
        inserted = ArrowScan(t.metadata, t.io, t.schema(), AlwaysTrue()).to_table(tasks)
        return SourceBatch.from_changes(
            since,
            end,
            inserts=inserted.cast(schema),
            facts=self._facts(t, added, f"file stats @v{end} (new files)"),
            snapshot_facts=snapshot_facts,
            trusted=f"Δ trusted as the files Iceberg appends v{since}→v{end} added",
            schema=schema,
        )


# Field ids of a position delete file's columns (Iceberg spec).
PATH_ID, POS_ID = 2147483546, 2147483545
POSITIONS = pa.schema(
    [
        pa.field(
            "file_path", pa.string(), nullable=False, metadata={"PARQUET:field_id": str(PATH_ID)}
        ),
        pa.field("pos", pa.int64(), nullable=False, metadata={"PARQUET:field_id": str(POS_ID)}),
    ]
)


class _DeleteManifestWriter(ManifestWriterV2):
    def content(self) -> ManifestContent:
        return ManifestContent.DELETES

    @property
    def _meta(self) -> dict[str, str]:
        return {**super()._meta, "content": "deletes"}


class _RowLevel(_FastAppendFiles):
    """A snapshot that adds data files and position delete files: pyiceberg
    0.12 writes no delete files itself (its deletes rewrite whole files)."""

    def __init__(self, deletes: list[DataFile], **kwargs: Any):
        super().__init__(**kwargs)
        self._deletes = deletes

    def _manifests(self) -> list[ManifestFile]:
        out = super()._manifests()
        if self._deletes:
            writer = _DeleteManifestWriter(
                spec=self._transaction.table_metadata.spec(),
                schema=self.schema(),
                output_file=self.new_manifest_output(),
                snapshot_id=self._snapshot_id,
                avro_compression=self._compression,
            )
            with writer:
                for f in self._deletes:
                    writer.add(
                        ManifestEntry.from_args(
                            status=ManifestEntryStatus.ADDED,
                            snapshot_id=self._snapshot_id,
                            sequence_number=None,
                            file_sequence_number=None,
                            data_file=f,
                        )
                    )
            out.append(writer.to_manifest_file())
        return out


def _positions(t: Table, schema: pa.Schema, remove: Counter[tuple]) -> dict[str, list[int]] | None:
    """Positions in the current snapshot's data files of `remove` (row key
    -> how many copies), skipping deleted positions; None if the table does
    not hold them all. Only files whose bounds admit a removed row are read."""
    need = +remove
    out: dict[str, list[int]] = {}
    current = t.current_snapshot()
    stats = {e["data_file"]["file_path"]: _stats(e, schema.names) for e in _live_files(t, current)}
    rows = {k: row for k, row in zip(need, map(_unkey, need), strict=True)}
    for task in _tasks(t, current).values():
        if not need:
            break
        path = task.file.file_path
        if not any(_admits(stats.get(path, {}), schema, rows[k]) for k in need):
            continue
        deleted: set[int] = set()
        for d in task.delete_files:
            ds = pq.read_table(t.io.new_input(d.file_path).open()).to_pylist()
            deleted |= {r["pos"] for r in ds if r["file_path"] == path}
        data = pq.read_table(t.io.new_input(path).open(), columns=schema.names)
        for pos, row in enumerate(arrow_rows(data.cast(schema))):
            k = row_key(row)
            if need[k] > 0 and pos not in deleted:
                need[k] -= 1
                out.setdefault(path, []).append(pos)
        need = +need
    return None if need else out


def _unkey(key: tuple) -> tuple:
    """A row from its key (`row_key` only changes NaN and -0.0)."""
    return tuple(float("nan") if x == "NaN" else x for x in key)


def _admits(stats: dict[str, ColumnStats], schema: pa.Schema, row: tuple) -> bool:
    """Whether a file with these statistics may hold `row`: every integer,
    date or timestamp value lies within the file's bounds. (Bounds of a file
    with deletes cover its physical rows, so they still bound.)"""
    for f, v in zip(schema, row, strict=True):
        s = stats.get(f.name)
        if (
            s is None
            or v is None
            or not (pa.types.is_integer(f.type) or pa.types.is_temporal(f.type))
        ):
            continue
        try:
            if (s.lo is not None and v < s.lo) or (s.hi is not None and v > s.hi):
                return False
        except TypeError:
            continue
    return True


def _position_deletes(t: Table, positions: dict[str, list[int]]) -> list[DataFile]:
    """One position delete file per data file, with the data file's path as
    both bounds of `file_path`, so readers apply it to that file only."""
    out = []
    for path, pos in positions.items():
        name = t.location_provider().new_data_location(f"{uuid.uuid4()}-deletes.parquet")
        table = pa.table({"file_path": [path] * len(pos), "pos": sorted(pos)}, schema=POSITIONS)
        with t.io.new_output(name).create(overwrite=True) as f:
            pq.write_table(table, f)
        out.append(
            DataFile.from_args(
                content=DataFileContent.POSITION_DELETES,
                file_path=name,
                file_format=FileFormat.PARQUET,
                partition=Record(),
                record_count=len(pos),
                file_size_in_bytes=len(t.io.new_input(name)),
                column_sizes={},
                value_counts={PATH_ID: len(pos), POS_ID: len(pos)},
                null_value_counts={PATH_ID: 0, POS_ID: 0},
                nan_value_counts={},
                lower_bounds={PATH_ID: path.encode()},
                upper_bounds={PATH_ID: path.encode()},
                spec_id=t.spec().spec_id,
            )
        )
    return out


def _commit_rows(
    tx: Transaction, t: Table, rows: pa.Table, deletes: list[DataFile], props: dict[str, str]
) -> None:
    """One snapshot that deletes by position and appends `rows`."""
    snapshot = _RowLevel(
        deletes,
        operation=Operation.OVERWRITE if deletes else Operation.APPEND,
        transaction=tx,
        io=t.io,
        snapshot_properties=props,
    )
    added: Iterable[DataFile] = (
        _dataframe_to_data_files(tx.table_metadata, rows, t.io) if rows.num_rows else []
    )
    for f in added:
        snapshot.append_data_file(f)
    snapshot.commit()


class IcebergSink(Sink):
    """Stores a node in an Iceberg table, exactly once per state:
    `node.write(IcebergSink(catalog, identifier))`, written by every
    `refresh`.

    After the first write, each state is one snapshot the size of the change:
    position delete files for the rows that went (one copy each, so
    duplicates are exact) and a data file of the rows that came. A new sink
    on an existing table, or a table that does not hold the rows the sink
    wrote, is overwritten. Every snapshot carries the contract's plan hash,
    the epoch (sum of source versions) and the app id; a state whose epoch
    the last snapshot of this app already has is skipped, unless another
    plan wrote it: then the table is overwritten, schema included. The
    contract is also the table property `sverify.contract`, and columns the
    view proves NOT NULL are `required`. `name` is the table's name in the
    plans that read the stored node (default: the last part of
    `identifier`); `app_id` defaults to `sverify:<name>`.

    The node `write` returns reads the table as an `IcebergSource` and builds
    on the contract the stored node proved. A restarted job that builds the
    same nodes resumes from the table on its first refresh. The refresh's
    report includes what each write did (`SinkWrite`). It raises
    `ValueError` if the table holds this state's epoch from other contents
    of a `StaticSource`.

    Args:
        catalog: A pyiceberg catalog.
        identifier: The sink table's identifier; the first write creates it.
        app_id: The application id recorded in each snapshot. Default:
            `"sverify:<name>"`.
        name: The table's name in the plans that read the stored node.
            Default: the last part of `identifier`.

    Attributes:
        catalog: The catalog.
        identifier: The sink table's identifier.
        name: The table's name in the plans that read the stored node.
    """

    def __init__(
        self,
        catalog: Catalog,
        identifier: str,
        *,
        app_id: str | None = None,
        name: str | None = None,
    ):
        self.catalog, self.identifier = catalog, identifier
        name = name or identifier.rsplit(".", 1)[-1]
        super().__init__(name, app_id=app_id, location=identifier)

    def source(self) -> IcebergSource:
        """The table as a source, for the nodes that read the stored node."""
        return IcebergSource(self.catalog, self.identifier, name=self.name)

    def _stored(self) -> Stored | None:
        if not self.catalog.table_exists(self.identifier):
            return None
        return self.source().stored()

    def _version(self) -> int | None:
        if not self.catalog.table_exists(self.identifier):
            return None
        return _version(self.catalog.load_table(self.identifier).current_snapshot())

    def committed(self) -> Contract | None:
        """The table's contract, with the epoch of the last snapshot this
        sink's `app_id` wrote, or None."""
        if not self.catalog.table_exists(self.identifier):
            return None
        t = self.catalog.load_table(self.identifier)
        mine = [s for s in _ancestry(t) if s.summary and s.summary.get(APP) == self.app_id]
        text = t.properties.get(KEY)
        if not mine or text is None:
            return None
        epoch = int(mine[0].summary.get(EPOCH, "-1"))  # type: ignore[union-attr]
        return replace(Contract.from_json(text), epoch=epoch)

    def write(self, change: SinkChange) -> SinkWrite:
        """Create or overwrite the table, or write the change as position
        deletes and new rows, in one snapshot that records the contract."""
        contract, schema = change.contract, change.schema
        props = {PLAN: contract.plan, EPOCH: str(contract.epoch), APP: self.app_id}
        created = not self.catalog.table_exists(self.identifier)
        if created:
            t = self.catalog.create_table(
                self.identifier, schema=schema, properties={KEY: contract.to_json()}
            )
        else:
            t = self.catalog.load_table(self.identifier)
        positions: dict[str, list[int]] | None = None
        if not created and not change.replace and t.spec().is_unpartitioned():
            # The rows that went: as many as the change deletes, so tuples.
            removed = Counter(map(row_key, arrow_rows(change.deletes)))
            positions = _positions(t, schema, removed) if removed else {}
        mode: Literal["created", "append", "row-level", "overwrite"]
        if positions is None:
            mode = "created" if created else "overwrite"
            rows = change.table
            deleted = 0
        else:
            mode = "row-level" if positions else "append"
            rows = change.inserts
            deleted = sum(len(p) for p in positions.values())
        with t.transaction() as tx:
            tx.set_properties({KEY: contract.to_json()})
            if positions is None:
                if not created:
                    _replace_schema(tx, _arrow_schema(t), schema)
                tx.overwrite(rows, snapshot_properties=props)
            else:
                _commit_rows(tx, t, rows, _position_deletes(t, positions), props)
        version = _version(self.catalog.load_table(self.identifier).current_snapshot())
        return SinkWrite(mode, version, contract, rows.num_rows, deleted)
