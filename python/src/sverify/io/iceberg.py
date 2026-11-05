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
writes a change as position delete files and data files of the new rows,
one commit the size of the change. In a partitioned table, it reads only
the data files of the partitions the deleted rows fall in, each delete file
carries the partition of the data file it applies to, and the new rows go to
one data file per partition (#466).
"""

from __future__ import annotations

import contextlib
import os
import uuid
import warnings
from collections import Counter
from collections.abc import Callable, Mapping, Sequence
from datetime import UTC, datetime, timedelta
from typing import Any, Literal

import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.parquet as pq

try:
    from pyiceberg.catalog import Catalog
    from pyiceberg.conversions import to_bytes
    from pyiceberg.exceptions import CommitFailedException, TableAlreadyExistsError
    from pyiceberg.expressions import AlwaysTrue
    from pyiceberg.io.pyarrow import (
        ArrowScan,
        _dataframe_to_data_files,
        _get_field_from_arrow_table,
        _pyarrow_schema_ensure_small_types,
        bin_pack_arrow_table,
        parquet_file_to_data_file,
        pyarrow_to_schema,
        write_file,
    )
    from pyiceberg.manifest import (
        DataFile,
        DataFileContent,
        FileFormat,
        ManifestContent,
        ManifestEntry,
        ManifestEntryStatus,
        ManifestFile,
        ManifestWriter,
        ManifestWriterV2,
    )
    from pyiceberg.partitioning import (
        PartitionFieldValue,
        PartitionKey,
        PartitionSpec,
        _to_partition_representation,
    )
    from pyiceberg.schema import Schema, index_name_by_id
    from pyiceberg.table import FileScanTask, Table, TableProperties, Transaction, WriteTask
    from pyiceberg.table.metadata import TableMetadata
    from pyiceberg.table.snapshots import Operation, Summary
    from pyiceberg.table.snapshots import Snapshot as IcebergSnapshot
    from pyiceberg.table.update.snapshot import _FastAppendFiles
    from pyiceberg.transforms import Transform, UnknownTransform, parse_transform
    from pyiceberg.typedef import Record
except ImportError as e:
    raise ImportError("sverify.io.iceberg needs iceberg: pip install 'sverify[iceberg]'") from e

from sverify._scan import Scan, ScanSnapshot, local_path
from sverify._unsupported import SverifyWarning
from sverify._weighted import split
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
from sverify.io import _engine
from sverify.io._common import (
    ColumnStats,
    Contract,
    LastRecord,
    SinkWrite,
    _TableSource,
    filter_rows,
    last_record,
    q,
)
from sverify.io._sink import _UNREAD, SinkChange, _TableSink
from sverify.observation import Observation

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


def _table_id(t: Table) -> str:
    return str(t.metadata.table_uuid)


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


def _by_name(t: Table) -> bool:
    """Whether reading the data files by column name reads the columns
    pyiceberg reads by field id: no field had another name in any of the
    table's schemas and no name meant another field, no name mapping (for
    files without field ids), and no partition fields (whose values files
    added from elsewhere may lack)."""
    if t.properties.get(TableProperties.DEFAULT_NAME_MAPPING):
        return False
    if any(spec.fields for spec in t.specs().values()):
        return False
    names: dict[int, str] = {}
    ids: dict[str, int] = {}
    for schema in t.metadata.schemas:
        for fid, name in index_name_by_id(schema).items():
            if names.setdefault(fid, name) != name or ids.setdefault(name, fid) != fid:
                return False
    return True


def _deleted_rows(paths: dict[str, set[str]]) -> pa.Table:
    """The rows position delete files delete: from each delete file's path
    to the data files it applies to, as `Scan.deleted` (local paths)."""
    parts = []
    for delete, data in paths.items():
        local = local_path(delete)
        assert local is not None
        rows = pq.read_table(local, columns=["file_path", "pos"])
        rows = rows.filter(
            pc.call_function(
                "is_in", [rows.column("file_path")], pc.SetLookupOptions(pa.array(sorted(data)))
            )
        )
        files = [local_path(f) for f in rows.column("file_path").to_pylist()]
        parts.append(
            pa.table(
                {"file": pa.array(files, pa.string()), "pos": rows.column("pos").cast(pa.int64())}
            )
        )
    if not parts:
        return pa.table({"file": pa.array([], pa.string()), "pos": pa.array([], pa.int64())})
    return pa.concat_tables(parts)


def _last_record(
    t: Table, record: Callable[[Summary], Summary | None], keeps: Callable[[Summary], bool]
) -> LastRecord[IcebergSnapshot, Summary]:
    """The newest snapshot whose summary is a `record`, walking the current
    snapshot's ancestry back through snapshots that `keep` what it recorded
    (`last_record`); a snapshot without a summary keeps nothing."""
    return last_record(
        _ancestry(t),
        lambda s: None if s.summary is None else record(s.summary),
        lambda s: s.summary is not None and keeps(s.summary),
        stop=True,
    )


def _rewrites(summary: Summary) -> bool:
    """Whether the snapshot only rewrites files (`replace`, a compaction)."""
    return summary.operation == Operation.REPLACE


def contract_facts(t: Table) -> list[Fact]:
    """The contract the table's properties record, if every snapshot of the
    table was written under it."""
    text = t.properties.get(KEY)
    if text is None:
        return []
    c = Contract.from_json(text)
    if not _last_record(t, lambda _: None, lambda m: m.get(PLAN) == c.plan).kept:
        return []
    return [Fact(f"{q(col)} IS NOT NULL", CONTRACT) for col in c.not_null] + [
        Fact(sql, CONTRACT) for sql in c.checks.values()
    ]


class IcebergSource(_TableSource):
    """An Iceberg table of a catalog, read by snapshot sequence number, as
    the input of transforms. `name` is the table's name in the plans that
    read it (default: the last part of `identifier`).

    A refresh reads the files that appends added since the version a node's
    state was computed from; after row-level deletes or overwrites it diffs
    the data files that changed. A table dropped and created again under
    `identifier` (a new table UUID) is read in full. Tables with equality
    deletes cannot be read.

    With `where` (a SQL condition on the columns), the source is the rows on
    which it is TRUE: snapshots read only the data files whose statistics do
    not rule it out, and changes are filtered.

    Args:
        catalog: A pyiceberg catalog.
        identifier: The table's identifier in it, e.g. `"db.readings"`.
        where: A SQL condition on the columns. The source is the rows on
            which it is TRUE; data files are skipped only where Lean proves
            from their statistics that it is TRUE on none of their rows
            (`Rel.eval_pruned` in `SubstraitLean/Pruning.lean`). Default:
            None, every row.
        name: The table's name in the plans that read it. Default: the last
            part of `identifier`.

    Attributes:
        catalog: The catalog.
        identifier: The table's identifier.
        where: The SQL condition, or None.
        name: The table's name in the plans that read it.
        skipped: The data files the last snapshot did not read.
    """

    def __init__(
        self,
        catalog: Catalog,
        identifier: str,
        *,
        where: str | None = None,
        name: str | None = None,
    ):
        self.catalog, self.identifier = catalog, identifier
        super().__init__(name or identifier.rsplit(".", 1)[-1], where)

    def table(self) -> Table:
        """The table as the catalog loads it now (a `pyiceberg.table.Table`)."""
        return self.catalog.load_table(self.identifier)

    def schema(self) -> pa.Schema:
        """The table's current schema, as Arrow."""
        return _arrow_schema(self.table())

    def latest(self) -> int:
        """The current snapshot's sequence number (0 before the first)."""
        return _version(self.table().current_snapshot())

    def _id_at(self, version: int | None) -> str:
        # A catalog loads only the table it has now. Its UUID is the id at
        # every version: a version the table never had is another table's,
        # which `other_tables` tells by the version going down.
        return _table_id(self.table())

    def _read_at(self, t: Table, version: int) -> None:
        """Remember the id of the table read at `version`."""
        self._seen(version, _table_id(t))

    def _facts(self, t: Table, files: list[dict[str, Any]], source: str) -> list[Fact]:
        schema = _arrow_schema(t)
        stats = [_stats(e, schema.names) for e in files]
        return self._facts_of(contract_facts(t), stats, schema, source)

    def _keep_entries(
        self, t: Table, files: list[dict[str, Any]], *, record: bool = True
    ) -> list[dict[str, Any]]:
        """The manifest entries of the data files that may hold rows passing
        `where` (`_keep`)."""
        if self.where is None:
            return files
        schema = _arrow_schema(t)
        stats = {e["data_file"]["file_path"]: _stats(e, schema.names) for e in files}
        keep = self._keep(stats, schema, record=record)
        return [e for e in files if e["data_file"]["file_path"] in keep]

    def _filter(self, rows: pa.Table) -> pa.Table:
        return rows if self.where is None else filter_rows(rows, self.where)

    def _rows(self, t: Table, s: IcebergSnapshot | None) -> tuple[pa.Table, list[dict[str, Any]]]:
        """The source's rows at snapshot `s`, and the manifest entries of the
        files they come from."""
        files = _live_files(t, s)
        if self.where is None:
            return _read(t, s), files
        keep = self._keep_entries(t, files)
        paths = {e["data_file"]["file_path"] for e in keep}
        tasks = [task for p, task in _tasks(t, s).items() if p in paths]
        return self._filter(_scan(t, tasks).cast(_arrow_schema(t))), keep

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
        self._read_at(t, v)
        rows, files = self._rows(t, s)
        return Snapshot(v, rows, self._facts(t, files, f"file stats @v{v}"))

    def _native(self, version: int | None = None) -> ScanSnapshot | None:
        """The snapshot at `version` as the Parquet files DuckDB reads
        itself (#173), with their position deletes, and the same facts as
        `snapshot`. None where reading the files by column name may not give
        pyiceberg's rows (`_by_name`), and for equality deletes, other file
        formats and object stores."""
        t = self.table()
        s = t.current_snapshot() if version is None else _at(t, version)
        if (version is not None and s is None and version != 0) or not _by_name(t):
            return None
        live = self._keep_entries(t, _live_files(t, s))
        paths = {e["data_file"]["file_path"] for e in live}
        files: list[str] = []
        deletes: dict[str, set[str]] = {}
        for task in _tasks(t, s).values():
            if task.file.file_path not in paths:
                continue
            local = local_path(task.file.file_path)
            if local is None or task.file.file_format != FileFormat.PARQUET:
                return None
            files.append(local)
            for d in task.delete_files:
                if d.content != DataFileContent.POSITION_DELETES:
                    return None
                if d.file_format != FileFormat.PARQUET or local_path(d.file_path) is None:
                    return None
                deletes.setdefault(d.file_path, set()).add(task.file.file_path)
        v = _version(s)
        self._read_at(t, v)
        deleted = _deleted_rows(deletes) if deletes else None
        scan = Scan(
            tuple(sorted(files)), _arrow_schema(t), deleted, self.where, f"{self.name}@v{v}"
        )
        return ScanSnapshot(v, scan, self._facts(t, live, f"file stats @v{v}"))

    def contract(self) -> Contract | None:
        """The contract the table property `sverify.contract` records, or
        None if it has none."""
        text = self.table().properties.get(KEY)
        return None if text is None else Contract.from_json(text)

    def stored(self) -> Stored | None:
        """The node state the current snapshot holds, if an `IcebergSink`
        wrote it under the table's contract: the current snapshot is the
        sink's, or the snapshots after the sink's last one only rewrite
        files (`replace`, as compaction does). A restarted job's first
        refresh resumes the sink's node from it, when it was stored by the
        same plan from the same sources.

        Returns:
            The stored state, or None if a snapshot after the sink's last
            one changed rows.
        """
        t = self.table()
        s, text = t.current_snapshot(), t.properties.get(KEY)
        if s is None or text is None:
            return None
        c = Contract.from_json(text)
        mine = _last_record(
            t,
            lambda m: m if m.get(PLAN) == c.plan and m.get(EPOCH) == str(c.epoch) else None,
            _rewrites,
        )
        if mine.record is None:
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
        now = _table_id(t)
        was = self._other_table(since, now)
        self._read_at(t, end)
        files = _live_files(t, current)
        snapshot_facts = self._facts(
            t, self._keep_entries(t, files, record=False), f"file stats @v{end}"
        )
        schema = _arrow_schema(t)
        if was is not None:
            # Dropped and created again: v`since` was another table's (#533).
            return self._full(
                since,
                end,
                self._rows(t, current)[0],
                f"{self.identifier} was created again since v{since} (table uuid {was} → {now})",
                snapshot_facts,
                schema,
            )
        if end == since:
            return SourceBatch.unchanged(since, snapshot_facts)
        between = [s for s in _ancestry(t) if since < _version(s) <= end]
        old = _at(t, since)
        if since != 0 and old is None:
            return self._full(
                since,
                end,
                self._rows(t, current)[0],
                f"Iceberg snapshot v{since} is not an ancestor of v{end} (expired?)",
                snapshot_facts,
                schema,
            )
        appends = all(
            s.summary is not None and s.summary.operation == Operation.APPEND for s in between
        )
        if not appends:
            ops = sorted({str(s.summary.operation.value) for s in between if s.summary})
            try:
                gone, came = _changed_tasks(t, old, current)
                diff = snapshot_diff(
                    self._filter(_scan(t, gone).cast(schema)),
                    self._filter(_scan(t, came).cast(schema)),
                )
            except Exception as e:
                return self._full(
                    since,
                    end,
                    self._rows(t, current)[0],
                    f"Iceberg snapshots v{since}→v{end} unreadable: {first_line(e)}",
                    snapshot_facts,
                    schema,
                )
            paths = {task.file.file_path for task in came}
            changed = [e for e in files if e["data_file"]["file_path"] in paths]
            inserts, deletes = split(diff)
            return SourceBatch.from_changes(
                since,
                end,
                inserts=inserts,
                deletes=deletes,
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
        # Appended files whose statistics rule `where` out add no rows.
        added = self._keep_entries(
            t, [e for e in files if int(e["sequence_number"]) > since], record=False
        )
        paths = {e["data_file"]["file_path"] for e in added}
        assert current is not None
        tasks = [
            task
            for task in t.scan(snapshot_id=current.snapshot_id).plan_files()
            if task.file.file_path in paths
        ]
        inserted = _scan(t, tasks)
        return SourceBatch.from_changes(
            since,
            end,
            inserts=self._filter(inserted.cast(schema)),
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


def _partition_keys(spec: PartitionSpec, schema: Schema, rows: pa.Table) -> list[Record]:
    """The partition of each row of `rows` under `spec`, as the manifests
    record it. Transforms run on each value in Python: pyiceberg 0.12 needs
    `pyiceberg-core` for the Arrow kernels of every transform but `identity`."""
    if not spec.fields:
        return [Record()] * rows.num_rows
    columns = []
    for f in spec.fields:
        source = schema.find_field(f.source_id).field_type
        name = schema.find_column_name(f.source_id)
        assert name is not None
        fn = f.transform.transform(source)
        values = _get_field_from_arrow_table(rows, name).to_pylist()
        columns.append([fn(_to_partition_representation(source, v)) for v in values])
    return [Record(*vals) for vals in zip(*columns, strict=True)]


def _data_files(metadata: TableMetadata, rows: pa.Table, io: Any) -> list[DataFile]:
    """Data files of `rows` under the table's current spec: one or more per
    partition."""
    spec = metadata.spec()
    if not rows.num_rows:
        return []
    if spec.is_unpartitioned():
        return list(_dataframe_to_data_files(metadata, rows, io))
    schema = metadata.schema()
    groups: dict[Record, list[int]] = {}
    for i, key in enumerate(_partition_keys(spec, schema, rows)):
        groups.setdefault(key, []).append(i)
    target = int(
        metadata.properties.get(
            TableProperties.WRITE_TARGET_FILE_SIZE_BYTES,
            TableProperties.WRITE_TARGET_FILE_SIZE_BYTES_DEFAULT,
        )
    )
    task_schema = pyarrow_to_schema(
        rows.schema, name_mapping=schema.name_mapping, format_version=metadata.format_version
    )
    write_uuid, tasks = uuid.uuid4(), []
    for key, at in groups.items():
        partition = PartitionKey(
            field_values=[
                PartitionFieldValue(field=f, value=key[i]) for i, f in enumerate(spec.fields)
            ],
            partition_spec=spec,
            schema=schema,
        )
        part = rows.take(pa.array(at, pa.int64())).combine_chunks()
        for batches in bin_pack_arrow_table(part, target):
            tasks.append(
                WriteTask(
                    write_uuid=write_uuid,
                    task_id=len(tasks),
                    record_batches=batches,
                    partition_key=partition,
                    schema=task_schema,
                )
            )
    return list(write_file(io=io, table_metadata=metadata, tasks=iter(tasks)))


def _positions(
    t: Table, schema: pa.Schema, remove: Counter[tuple], removed: pa.Table
) -> tuple[dict[str, list[int]], dict[str, DataFile]] | None:
    """Positions in the current snapshot's data files of `remove` (row key
    -> how many copies, the rows of `removed`), skipping deleted positions,
    with the data files they are in; None if the table does not hold them
    all, or holds some in a data file of an older partition spec. Only files
    of the partitions the removed rows fall in, whose bounds admit a removed
    row, are read."""
    need = +remove
    out: dict[str, list[int]] = {}
    files: dict[str, DataFile] = {}
    current = t.current_snapshot()
    spec = t.spec()
    stats = {e["data_file"]["file_path"]: _stats(e, schema.names) for e in _live_files(t, current)}
    rows = {k: row for k, row in zip(need, map(_unkey, need), strict=True)}
    touched: set[Record] | None = None
    if not spec.is_unpartitioned():
        try:
            touched = set(_partition_keys(spec, t.schema(), removed))
        except Exception:
            touched = None  # A transform pyiceberg can't run here: read every file.
    for task in _tasks(t, current).values():
        if not need:
            break
        path = task.file.file_path
        if (
            touched is not None
            and task.file.spec_id == spec.spec_id
            and task.file.partition not in touched
        ):
            continue
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
                files[path] = task.file
        need = +need
    if need or any(f.spec_id != spec.spec_id for f in files.values()):
        return None
    return out, files


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


def _position_deletes(
    t: Table, positions: dict[str, list[int]], files: dict[str, DataFile]
) -> list[DataFile]:
    """One position delete file per data file (of the current spec), in the
    data file's partition, with its path as both bounds of `file_path`, so
    readers apply it to that file only."""
    out = []
    for path, pos in positions.items():
        data = files[path]
        name = t.location_provider().new_data_location(f"{uuid.uuid4()}-deletes.parquet")
        table = pa.table({"file_path": [path] * len(pos), "pos": sorted(pos)}, schema=POSITIONS)
        with t.io.new_output(name).create(overwrite=True) as f:
            pq.write_table(table, f)
        out.append(
            DataFile.from_args(
                content=DataFileContent.POSITION_DELETES,
                file_path=name,
                file_format=FileFormat.PARQUET,
                partition=data.partition,
                record_count=len(pos),
                file_size_in_bytes=len(t.io.new_input(name)),
                column_sizes={},
                value_counts={PATH_ID: len(pos), POS_ID: len(pos)},
                null_value_counts={PATH_ID: 0, POS_ID: 0},
                nan_value_counts={},
                lower_bounds={PATH_ID: path.encode()},
                upper_bounds={PATH_ID: path.encode()},
                spec_id=data.spec_id,
            )
        )
    return out


def _commit_rows(
    tx: Transaction,
    t: Table,
    rows: pa.Table | list[DataFile],
    deletes: list[DataFile],
    props: dict[str, str],
) -> None:
    """One snapshot that deletes by position and appends `rows` (or data
    files already written)."""
    snapshot = _RowLevel(
        deletes,
        operation=Operation.OVERWRITE if deletes else Operation.APPEND,
        transaction=tx,
        io=t.io,
        snapshot_properties=props,
    )
    added = rows if isinstance(rows, list) else _data_files(tx.table_metadata, rows, t.io)
    for f in added:
        snapshot.append_data_file(f)
    snapshot.commit()


PartitionField = tuple[str, str | Transform[Any, Any]] | tuple[str, str | Transform[Any, Any], str]
"""A partition field of `IcebergSink(partition_by=...)`: a column, a
transform (`"identity"`, `"day"`, `"bucket[16]"`, … or a pyiceberg
`Transform`) and optionally the field's name."""


def _partition_fields(
    fields: Sequence[PartitionField],
) -> list[tuple[str, Transform[Any, Any], str | None]]:
    out: list[tuple[str, Transform[Any, Any], str | None]] = []
    for f in fields:
        column, transform = f[0], f[1]
        name = f[2] if len(f) > 2 else None
        t = parse_transform(transform) if isinstance(transform, str) else transform
        if isinstance(t, UnknownTransform) or not isinstance(t, Transform):
            raise ValueError(f"partition_by: unknown transform {transform!r} of {column!r}")
        out.append((column, t, name))
    return out


def _spec_fields(t: Table) -> list[tuple[str | None, str]]:
    """The current spec's fields as (source column, transform)."""
    schema = t.schema()
    return [(schema.find_column_name(f.source_id), str(f.transform)) for f in t.spec().fields]


EMPTY: dict[str, str] = {}


class _Rewrite(_FastAppendFiles):
    """A `replace` snapshot: it removes data files and delete files and adds
    data files of the same rows (compaction). pyiceberg 0.12 has no
    compaction, writes no delete manifests, and refuses the summary of a
    `replace`."""

    def __init__(self, removed: list[DataFile], **kwargs: Any):
        super().__init__(operation=Operation.OVERWRITE, **kwargs)
        self._removed = {f.file_path for f in removed}
        for f in removed:
            self.delete_data_file(f)

    def _validate_concurrency(self) -> None:
        # A retry on top of another writer's snapshot would drop delete files
        # that writer added for the files this one rewrites: fail instead.
        if self._commit_window is not None and not self._commit_window.is_empty():
            raise CommitFailedException("the table changed during the compaction")

    def _existing_manifests(self) -> list[ManifestFile]:
        """The parent's manifests, without the removed files: rewritten (as
        `existing` entries) where they held one, dropped where they held
        nothing else."""
        out = []
        for manifest in super()._existing_manifests():
            entries = manifest.fetch_manifest_entry(io=self._io, discard_deleted=True)
            kept = [e for e in entries if e.data_file.file_path not in self._removed]
            if len(kept) == len(entries):
                out.append(manifest)
                continue
            if not kept:
                continue
            spec = self.spec(manifest.partition_spec_id)
            writer: ManifestWriter = (
                _DeleteManifestWriter(
                    spec=spec,
                    schema=self.schema(),
                    output_file=self.new_manifest_output(),
                    snapshot_id=self._snapshot_id,
                    avro_compression=self._compression,
                )
                if manifest.content == ManifestContent.DELETES
                else self.new_manifest_writer(spec)
            )
            with writer:
                for e in kept:
                    writer.add_entry(
                        ManifestEntry.from_args(
                            status=ManifestEntryStatus.EXISTING,
                            snapshot_id=e.snapshot_id,
                            sequence_number=e.sequence_number,
                            file_sequence_number=e.file_sequence_number,
                            data_file=e.data_file,
                        )
                    )
            out.append(writer.to_manifest_file())
        return out

    def _summary(self, snapshot_properties: dict[str, str] = EMPTY) -> Summary:
        out = super()._summary(snapshot_properties)
        return Summary(Operation.REPLACE, **out.additional_properties)


def _compaction(t: Table) -> tuple[list[FileScanTask], list[DataFile]]:
    """What a compaction of the current snapshot rewrites: in each partition
    of the current spec, the data files with position deletes and, if there
    are two or more, the files under the target file size; and the delete
    files that no data file it keeps reads."""
    s = t.current_snapshot()
    if s is None:
        return [], []
    spec = t.spec()
    target = int(
        t.properties.get(
            TableProperties.WRITE_TARGET_FILE_SIZE_BYTES,
            TableProperties.WRITE_TARGET_FILE_SIZE_BYTES_DEFAULT,
        )
    )
    groups: dict[Record, list[FileScanTask]] = {}
    tasks = list(_tasks(t, s).values())
    for task in tasks:
        if task.file.spec_id == spec.spec_id and task.file.file_format == FileFormat.PARQUET:
            groups.setdefault(task.file.partition, []).append(task)
    rewrite: list[FileScanTask] = []
    for group in groups.values():
        if any(
            d.content != DataFileContent.POSITION_DELETES for x in group for d in x.delete_files
        ):
            continue
        small = [x for x in group if x.file.file_size_in_bytes < target]
        deleted = [x for x in group if x.delete_files]
        picked = {x.file.file_path: x for x in deleted + (small if len(small) > 1 else [])}
        rewrite += picked.values()
    chosen = {x.file.file_path for x in rewrite}
    read = {d.file_path for x in tasks if x.file.file_path not in chosen for d in x.delete_files}
    gone: dict[str, DataFile] = {}
    for x in tasks:
        for d in x.delete_files:
            if d.file_path not in read:
                gone[d.file_path] = d
    return rewrite, list(gone.values())


def _compact(t: Table, props: dict[str, str]) -> dict[str, int]:
    """Rewrite what `_compaction` picks as one `replace` snapshot with the
    snapshot properties `props`; the counts of files it removed and added."""
    rewrite, deletes = _compaction(t)
    if not rewrite and not deletes:
        return {"data_files_removed": 0, "delete_files_removed": 0, "data_files_added": 0}
    rows = _scan(t, rewrite)
    with t.transaction() as tx:
        added = _data_files(tx.table_metadata, rows, t.io)
        snapshot = _Rewrite(
            [x.file for x in rewrite] + deletes,
            transaction=tx,
            io=t.io,
            snapshot_properties=props,
        )
        for f in added:
            snapshot.append_data_file(f)
        snapshot.commit()
    return {
        "data_files_removed": len(rewrite),
        "delete_files_removed": len(deletes),
        "data_files_added": len(added),
    }


def _files(t: Table, snapshots: Sequence[IcebergSnapshot], seen: dict[str, set[str]]) -> set[str]:
    """Every file the snapshots reference: manifest lists, manifests, and
    the data and delete files of their entries. `seen` caches manifests."""
    out: set[str] = set()
    for s in snapshots:
        out.add(s.manifest_list)
        for m in s.manifests(t.io):
            if m.manifest_path not in seen:
                entries = m.fetch_manifest_entry(io=t.io, discard_deleted=False)
                seen[m.manifest_path] = {e.data_file.file_path for e in entries}
            out.add(m.manifest_path)
            out |= seen[m.manifest_path]
    return out


def _expire(t: Table, keep: set[int], older_than: datetime) -> tuple[int, int]:
    """Expire the snapshots older than `older_than` that are not in `keep`
    nor a branch or tag head, and delete the files only they referenced.
    The numbers of snapshots expired and files deleted."""
    protected = {ref.snapshot_id for ref in t.metadata.refs.values()}
    cutoff = older_than.timestamp() * 1000
    gone = [
        s
        for s in t.snapshots()
        if s.timestamp_ms < cutoff and s.snapshot_id not in keep | protected
    ]
    if not gone:
        return 0, 0
    ids = {s.snapshot_id for s in gone}
    seen: dict[str, set[str]] = {}
    before = _files(t, gone, seen)
    t.maintenance.expire_snapshots().by_ids(sorted(ids)).commit()
    t = t.refresh()
    unused = before - _files(t, t.snapshots(), seen)
    for path in sorted(unused):
        with contextlib.suppress(FileNotFoundError):
            t.io.delete(path)
    return len(gone), len(unused)


class _Conflict(CommitFailedException):
    """Another writer of the sink committed while this one did (#534)."""


class _Guarded(Transaction):
    """A transaction whose commit fails where pyiceberg would retry it on
    top of another writer's snapshot and `check` (of the table refreshed
    for the retry) raises `_Conflict`: a retry on top of another writer of
    the sink would write the change a second time (#534)."""

    def __init__(self, table: Table, check: Callable[[Table], None]):
        super().__init__(table)
        self._check = check

    def _rebuild_snapshot_updates(self) -> None:
        self._check(self._table)
        super()._rebuild_snapshot_updates()


class IcebergSink(_TableSink[Table]):
    """Stores a node in an Iceberg table, exactly once per state:
    `node.write(IcebergSink(catalog, identifier))`, written by every
    `refresh`.

    After the first write, each state is one snapshot the size of the change:
    position delete files for the rows that went (one copy each, so
    duplicates are exact) and a data file of the rows that came. In a
    partitioned table, the deletes and the new rows go to the partitions
    the change touches, and the other partitions keep their files. A new sink
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

    The first write creates the table with `location`, the partition fields
    of `partition_by` and the table `properties` beside the sink's own, in
    one commit (#468). A catalog without a default location, such as Unity
    Catalog's Iceberg REST catalog on a schema without a managed storage
    root, needs `location`. They only apply to a table the sink creates: an
    overwrite keeps the table's location, spec and properties, and a sink on
    an existing table that differs from them warns once
    (`IcebergSink.create_options_ignored`).

    Every write adds a snapshot and small files: a refresh that deletes rows
    adds a position delete file and a data file, which readers open and the
    sink's next write searches. `compact_every` compacts the table
    (`maintain`) after every so many writes: in each partition, it rewrites
    the data files with position deletes, and the small files where there
    are two or more, as data files of their live rows, and drops the delete
    files no remaining data file reads, in one `replace` snapshot. With
    `snapshot_retention`, it then expires the snapshots older than that
    (keeping the `min_snapshots` newest and the sink's own last snapshot)
    and deletes the files only they referenced. A compaction snapshot
    carries the contract, and a restarted job resumes past it, as it does
    past another writer's compaction. pyiceberg rewrites the table's
    metadata file on every commit; the table properties
    `write.metadata.delete-after-commit.enabled` and
    `write.metadata.previous-versions-max` (`properties`) bound those.

    Args:
        catalog: A pyiceberg catalog.
        identifier: The sink table's identifier; the first write creates it.
        app_id: The application id recorded in each snapshot. Default:
            `"sverify:<name>"`.
        name: The table's name in the plans that read the stored node.
            Default: the last part of `identifier`.
        location: The location of the table the first write creates.
            Default: None, the catalog's default.
        partition_by: The partition fields of the table the first write
            creates, each `(column, transform)` or `(column, transform,
            name)`; a transform is `"identity"`, `"year"`, `"month"`,
            `"day"`, `"hour"`, `"bucket[N]"`, `"truncate[W]"` or a pyiceberg
            `Transform`. Default: None, unpartitioned.
        properties: Table properties of the table the first write creates,
            such as `"write.target-file-size-bytes"`, besides the sink's own
            (`sverify.*`). Default: None.
        compact_every: Compact the table after every this many writes of
            this process (`maintain`). Default: None, never.
        snapshot_retention: With `compact_every`, then expire the snapshots
            older than this and delete the files only they referenced
            (`maintain(expire=...)`). Nodes reading the stored node from an
            expired snapshot read the whole table, so keep it longer than
            the gap between their refreshes. Default: None, no expiry.
        min_snapshots: The newest snapshots of the table's history an
            expiry keeps, however old. Default: 1.
        reproducible: What a rerun of a state must reproduce
            (`sv.equivalent(...)`, #444 D20). Default: rows as a multiset,
            doubles within the plan's bound (`sv.equivalent(floats="plan")`),
            other values exact; `sv.equivalent()` asks for the same bits.

    Raises:
        ValueError: A transform of `partition_by` is unknown, or
            `properties` sets a `sverify.*` property, or `compact_every` or
            `min_snapshots` is below 1.

    Attributes:
        catalog: The catalog.
        identifier: The sink table's identifier.
        name: The table's name in the plans that read the stored node.
        table_location: `location`, or None.
        partition_by: The partition fields, as `(column, Transform, name or
            None)`.
        properties: `properties`, or an empty dict.
        compact_every: Writes between compactions, or None.
        snapshot_retention: The expiry's retention after a compaction, or
            None.
        min_snapshots: The newest snapshots an expiry keeps.

    Examples:
        A sink partitioned by day, at a location of its own:

        ```python
        IcebergSink(
            catalog,
            "lake.daily",
            location="s3://lake/daily",
            partition_by=[("day", "day"), ("host", "identity")],
            properties={"write.target-file-size-bytes": str(64 << 20)},
        )
        ```
    """

    create_options_ignored = "create options ignored"
    """The start of the warning a sink on an existing table gives when the
    table differs from its `location`, `partition_by` or `properties`."""
    _create_errors = (TableAlreadyExistsError, CommitFailedException)
    _commit_errors = (_Conflict,)

    def __init__(
        self,
        catalog: Catalog,
        identifier: str,
        *,
        app_id: str | None = None,
        name: str | None = None,
        location: str | None = None,
        partition_by: Sequence[PartitionField] | None = None,
        properties: Mapping[str, str] | None = None,
        compact_every: int | None = None,
        snapshot_retention: timedelta | None = None,
        min_snapshots: int = 1,
        reproducible: Observation | None = None,
    ):
        self.catalog, self.identifier = catalog, identifier
        name = name or identifier.rsplit(".", 1)[-1]
        if min_snapshots < 1:
            raise ValueError(f"min_snapshots must be at least 1, got {min_snapshots}")
        super().__init__(
            name,
            app_id=app_id,
            location=identifier,
            compact_every=compact_every,
            reproducible=reproducible,
        )
        self.table_location = location
        self.partition_by = _partition_fields(partition_by or [])
        self.properties = {str(k): str(v) for k, v in (properties or {}).items()}
        if mine := sorted(k for k in self.properties if k.startswith("sverify.")):
            raise ValueError(f"properties: {mine} are the sink's own")
        self._checked = False
        """Whether an existing table was compared with the create options."""
        self.snapshot_retention, self.min_snapshots = snapshot_retention, min_snapshots

    def source(self) -> IcebergSource:
        """The table as a source, for the nodes that read the stored node."""
        return IcebergSource(self.catalog, self.identifier, name=self.name)

    def _stored(self) -> Stored | None:
        if not self.catalog.table_exists(self.identifier):
            return None
        return self.source().stored()

    def _version(self) -> int | None:
        t = self._open()
        return None if t is None else _version(t.current_snapshot())

    def _open(self) -> Table | None:
        if not self.catalog.table_exists(self.identifier):
            return None
        return self.catalog.load_table(self.identifier)

    def _epoch_of(self, table: Table) -> int | None:
        """The epoch of the last snapshot this sink's `app_id` wrote."""
        for s in _ancestry(table):
            if s.summary is not None and s.summary.get(APP) == self.app_id:
                return int(s.summary.get(EPOCH, "-1"))
        return None

    def _contract_of(self, table: Table) -> Contract | None:
        """The table property `sverify.contract`."""
        text = table.properties.get(KEY)
        return None if text is None else Contract.from_json(text)

    def _transaction(self, t: Table) -> Transaction:
        """A transaction on `t` that commits only while the table has the
        epoch `committed` read (`_Guarded`)."""
        then = self._read

        def check(now: Table) -> None:
            if then is not _UNREAD and (epoch := self._epoch_of(now)) != then:
                raise _Conflict(f"the table now has epoch {epoch}")

        return _Guarded(t, check)

    def _own(self, t: Table) -> tuple[list[IcebergSnapshot], dict[str, str]]:
        """The current snapshot's ancestry down to the sink's last snapshot,
        and that snapshot's sverify properties, if the snapshots after it only
        rewrite files (`replace`); else nothing."""
        text = t.properties.get(KEY)
        if text is None:
            return [], {}
        plan = Contract.from_json(text).plan
        mine = _last_record(
            t, lambda m: m if m.get(APP) == self.app_id and m.get(PLAN) == plan else None, _rewrites
        )
        if mine.record is None:
            return [], {}
        own = {k: mine.record.get(k) for k in (PLAN, EPOCH, APP)}
        return mine.walked, {k: v for k, v in own.items() if v is not None}

    def maintain(
        self, *, expire: timedelta | None = None, min_snapshots: int | None = None
    ) -> dict[str, int]:
        """Compact the table, and with `expire`, expire the snapshots older
        than that and delete the files only they referenced. The compaction
        rewrites, in each partition of the current spec, the data files with
        position deletes, and the files under `write.target-file-size-bytes`
        where there are two or more, as data files of their live rows, and
        drops the delete files that no remaining data file reads, in one
        `replace` snapshot. It records the sverify properties of the sink's
        last snapshot, if no other writer changed rows since, so a restarted
        job resumes past it. The expiry keeps the `min_snapshots` newest
        snapshots, the sink's last snapshot and the ones after it, and branch
        and tag heads.

        Args:
            expire: How old a snapshot may be and still be read. Nodes
                reading the stored node from an older snapshot read the
                whole table. Default: None, no expiry.
            min_snapshots: The newest snapshots the expiry keeps. Default:
                the sink's `min_snapshots`.

        Returns:
            The counts of data files the compaction removed and added
            (`"data_files_removed"`, `"data_files_added"`) and of delete
            files it removed (`"delete_files_removed"`), and with `expire`,
            of snapshots expired (`"snapshots_expired"`) and files deleted
            (`"files_deleted"`); empty if the table does not exist.

        Raises:
            CommitFailedException: Another writer committed to the table
                during the compaction (pyiceberg's).
        """
        if not self.catalog.table_exists(self.identifier):
            return {}
        t = self.catalog.load_table(self.identifier)
        out: dict[str, int] = dict(_compact(t, self._own(t)[1]))
        if expire is not None:
            t = self.catalog.load_table(self.identifier)
            run, _ = self._own(t)
            keep = {
                s.snapshot_id for s in run + _ancestry(t)[: min_snapshots or self.min_snapshots]
            }
            now = datetime.now(UTC)
            out["snapshots_expired"], out["files_deleted"] = _expire(t, keep, now - expire)
        return out

    def _maintain(self) -> None:
        self.maintain(expire=self.snapshot_retention)

    def _create(self, change: SinkChange) -> Table:
        """Create the table with the create options and the contract, in
        one commit."""
        self._checked = True
        schema = change.schema
        props = {**self.properties, KEY: change.contract.to_json()}
        if not self.partition_by:
            return self.catalog.create_table(
                self.identifier, schema=schema, location=self.table_location, properties=props
            )
        tx = self.catalog.create_table_transaction(
            self.identifier, schema=schema, location=self.table_location, properties=props
        )
        with tx.update_spec() as update:
            for column, transform, field in self.partition_by:
                update.add_field(column, transform, field)
        return tx.commit_transaction()

    def _opened(self, table: Table, created: bool, change: SinkChange) -> Table:
        if not created:
            self._check_existing(table)
        return table

    def _check_existing(self, t: Table) -> None:
        """Warn, once, where an existing table differs from the create
        options, which apply only to a table the sink creates."""
        if self._checked:
            return
        self._checked = True
        differs = []
        if self.table_location is not None and (
            t.location().rstrip("/") != self.table_location.rstrip("/")
        ):
            differs.append(f"location {t.location()!r}, not {self.table_location!r}")
        if self.partition_by:
            want = [(c, str(tr)) for c, tr, _ in self.partition_by]
            if _spec_fields(t) != want:
                differs.append(f"partition fields {_spec_fields(t)}, not {want}")
        other = {k: v for k, v in self.properties.items() if t.properties.get(k) != v}
        if other:
            differs.append(f"other values of the properties {sorted(other)}")
        if differs:
            warnings.warn(
                f"{self.identifier}: {self.create_options_ignored}: the existing table has "
                + "; ".join(differs),
                SverifyWarning,
                stacklevel=2,
            )

    def _props(self, contract: Contract) -> dict[str, str]:
        """The sverify properties of the snapshot of `contract`."""
        return {PLAN: contract.plan, EPOCH: str(contract.epoch), APP: self.app_id}

    def _write_native(self, table: Table, created: bool, change: SinkChange) -> SinkWrite | None:
        """Have DuckDB write the data file of the state (`created`) or of the
        rows the change inserts, find the positions of the rows it deletes,
        and commit them as one snapshot with the contract. None where only
        the Arrow path writes: partitioned tables, nested columns, object
        stores, or a table that does not hold the rows the change deletes."""
        t = table
        assert change.native is not None
        contract, props = change.contract, self._props(change.contract)
        rows, delta = change.native
        schema = change.schema
        fields = t.schema().fields
        if not t.spec().is_unpartitioned() or any(pa.types.is_nested(f.type) for f in schema):
            return None
        ids = {f.name: f.field_id for f in fields}

        def data_file(sql: str) -> list[DataFile]:
            uri = t.location_provider().new_data_location(f"{uuid.uuid4()}-sverify.parquet")
            local = local_path(uri)
            assert local is not None
            os.makedirs(os.path.dirname(local), exist_ok=True)
            if not _engine.copy(sql, local, schema, ids):
                os.remove(local)
                return []
            f = parquet_file_to_data_file(t.io, t.metadata, uri)
            types = {fld.name: fld.field_type for fld in fields}
            for c, (lo, hi) in _engine.float_bounds(local, schema).items():
                f.lower_bounds[ids[c]] = to_bytes(types[c], lo)
                f.upper_bounds[ids[c]] = to_bytes(types[c], hi)
            return [f]

        if local_path(t.location()) is None:
            return None
        if created:
            with self._transaction(t) as tx:
                tx.set_properties({KEY: contract.to_json()})
                _commit_rows(tx, t, data_file(_engine.rows_sql(rows, schema)), [], props)
            return SinkWrite("created", None, contract, _engine.rows_count(rows), 0)
        inserted, deleted = _engine.counts(delta)
        deletes: list[DataFile] = []
        if deleted:
            snap = self.source()._native()
            gone = _engine.deletes_by_file(None if snap is None else snap.scan, delta)
            if gone is None:
                return None
            tasks = _tasks(t, t.current_snapshot())
            uris = {local_path(p): p for p in tasks}
            by_file = {uris[f]: pos for f, pos in gone.items()}
            data = {p: tasks[p].file for p in by_file}
            deletes = _position_deletes(t, by_file, data)
        added = data_file(_engine.inserts_sql(delta, schema)) if inserted else []
        with self._transaction(t) as tx:
            tx.set_properties({KEY: contract.to_json()})
            _commit_rows(tx, t, added, deletes, props)
        return SinkWrite("row-level" if deleted else "append", None, contract, inserted, deleted)

    def _write_arrow(self, table: Table, created: bool, change: SinkChange) -> SinkWrite:
        """Create or overwrite the table, or write the change as position
        deletes and new rows, in one snapshot that records the contract."""
        t = table
        contract, schema, props = change.contract, change.schema, self._props(change.contract)
        found: tuple[dict[str, list[int]], dict[str, DataFile]] | None = None
        if not created and not change.replace:
            # The rows that went: as many as the change deletes, so tuples.
            removed = Counter(map(row_key, arrow_rows(change.deletes)))
            found = _positions(t, schema, removed, change.deletes) if removed else ({}, {})
        mode: Literal["created", "append", "row-level", "overwrite"]
        if found is None:
            mode = "created" if created else "overwrite"
            rows = change.table
            deleted = 0
            deletes: list[DataFile] = []
        else:
            positions, files = found
            mode = "row-level" if positions else "append"
            rows = change.inserts
            deleted = sum(len(p) for p in positions.values())
            deletes = _position_deletes(t, positions, files)
        with self._transaction(t) as tx:
            tx.set_properties({KEY: contract.to_json()})
            if found is None:
                if not created:
                    _replace_schema(tx, _arrow_schema(t), schema)
                if tx.table_metadata.spec().is_unpartitioned():
                    tx.overwrite(rows, snapshot_properties=props)
                else:
                    # pyiceberg's overwrite splits rows by partition with
                    # Arrow kernels that need `pyiceberg-core` for `day()`
                    # and the other transforms: delete, then append ours.
                    if t.current_snapshot() is not None:
                        tx.delete(AlwaysTrue(), snapshot_properties=props)
                    _commit_rows(tx, t, rows, [], props)
            else:
                _commit_rows(tx, t, rows, deletes, props)
        return SinkWrite(mode, None, contract, rows.num_rows, deleted)
