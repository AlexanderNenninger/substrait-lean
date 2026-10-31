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
from typing import Any, Literal

import pyarrow as pa
import pyarrow.parquet as pq

try:
    from pyiceberg.catalog import Catalog
    from pyiceberg.expressions import AlwaysTrue
    from pyiceberg.io.pyarrow import ArrowScan, _dataframe_to_data_files
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

from sverify.contracts import Fact
from sverify.incremental import (
    Changes,
    IncrementalView,
    Snapshot,
    SourceBatch,
    Stored,
    arrow_rows,
    consolidate,
    first_line,
    row_key,
)
from sverify.io._common import (
    ColumnStats,
    Contract,
    SinkWrite,
    check_same_state,
    q,
    sink_schema,
    stats_facts,
    view_contract_record,
)

CONTRACT = "Iceberg contract"
KEY = "sverify.contract"
PLAN = "sverify.plan"
EPOCH = "sverify.epoch"
APP = "sverify.app"


def _arrow_schema(t: Table) -> pa.Schema:
    return pa.schema([f.remove_metadata() for f in t.schema().as_arrow()])


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


class IcebergSource:
    """An Iceberg table of a catalog, read by snapshot sequence number, as
    the input of transforms. `name` is the table's name in the plans that
    read it (default: the last part of `identifier`)."""

    def __init__(self, catalog: Catalog, identifier: str, *, name: str | None = None):
        self.catalog, self.identifier = catalog, identifier
        self.name = name or identifier.rsplit(".", 1)[-1]

    def table(self) -> Table:
        return self.catalog.load_table(self.identifier)

    def schema(self) -> pa.Schema:
        return _arrow_schema(self.table())

    def latest(self) -> int:
        return _version(self.table().current_snapshot())

    def _facts(self, t: Table, files: list[dict[str, Any]], source: str) -> list[Fact]:
        schema = _arrow_schema(t)
        stats = [_stats(e, schema.names) for e in files]
        return contract_facts(t) + stats_facts(stats, schema, source)

    def snapshot(self, version: int | None = None) -> Snapshot:
        t = self.table()
        s = t.current_snapshot() if version is None else _at(t, version)
        if version is not None and s is None and version != 0:
            raise ValueError(f"{self.identifier} has no snapshot with sequence number {version}")
        v = _version(s)
        files = _live_files(t, s)
        return Snapshot(v, _read(t, s), self._facts(t, files, f"file stats @v{v}"))

    def contract(self) -> Contract | None:
        text = self.table().properties.get(KEY)
        return None if text is None else Contract.from_json(text)

    def stored(self) -> Stored | None:
        """The view state the current snapshot stored, if an `IcebergSink`
        wrote it under the table's contract (to resume a pipeline from)."""
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
        t = self.table()
        current = t.current_snapshot() if until is None else _at(t, until)
        if until is not None and current is None and until != 0:
            raise ValueError(f"{self.identifier} has no snapshot with sequence number {until}")
        end = _version(current)
        files = _live_files(t, current)
        snapshot_facts = self._facts(t, files, f"file stats @v{end}")
        if end == since:
            return SourceBatch(since, end, snapshot_facts)
        between = [s for s in _ancestry(t) if since < _version(s) <= end]
        old = _at(t, since)
        schema = _arrow_schema(t)
        if since != 0 and old is None:
            return SourceBatch(
                since,
                end,
                snapshot_facts,
                snapshot=_read(t, current),
                schema=schema,
                fallback=f"Iceberg snapshot v{since} is not an ancestor of v{end} (expired?)",
            )
        appends = all(
            s.summary is not None and s.summary.operation == Operation.APPEND for s in between
        )
        if not appends:
            ops = sorted({str(s.summary.operation.value) for s in between if s.summary})
            try:
                gone, came = _changed_tasks(t, old, current)
                changes = consolidate(
                    Changes(
                        inserts=arrow_rows(_scan(t, came).cast(schema)),
                        deletes=arrow_rows(_scan(t, gone).cast(schema)),
                    )
                )
            except Exception as e:
                return SourceBatch(
                    since,
                    end,
                    snapshot_facts,
                    snapshot=_read(t, current),
                    schema=schema,
                    fallback=f"Iceberg snapshots v{since}→v{end} unreadable: {first_line(e)}",
                )
            paths = {task.file.file_path for task in came}
            changed = [e for e in files if e["data_file"]["file_path"] in paths]
            return SourceBatch(
                since,
                end,
                snapshot_facts,
                changes=changes,
                facts=self._facts(t, changed, f"file stats @v{end} (changed files)"),
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
        return SourceBatch(
            since,
            end,
            snapshot_facts,
            changes=Changes(inserts=arrow_rows(inserted.cast(schema))),
            facts=self._facts(t, added, f"file stats @v{end} (new files)"),
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


class IcebergSink:
    """Stores a node in an Iceberg table, exactly once per state:
    `node.write(IcebergSink(catalog, identifier))`.

    After the first write, each state is one snapshot the size of the change:
    position delete files for the rows that went (one copy each, so
    duplicates are exact) and a data file of the rows that came. A new sink
    on an existing table, or a table that does not hold the rows the sink
    wrote, is overwritten. Every snapshot carries the contract's plan hash,
    the epoch (sum of source versions) and the app id; a state whose epoch
    the last snapshot of this app already has is skipped. The contract is
    also the table property `sverify.contract`, and columns the view proves
    NOT NULL are `required`. `name` is the table's name in the plans that
    read the stored node (default: the last part of `identifier`); `app_id`
    defaults to `sverify:<node name>`."""

    def __init__(
        self,
        catalog: Catalog,
        identifier: str,
        view: IncrementalView | None = None,
        *,
        app_id: str | None = None,
        name: str | None = None,
    ):
        self.catalog, self.identifier = catalog, identifier
        self.name = name or identifier.rsplit(".", 1)[-1]
        self.app_id = app_id
        self.view: IncrementalView | None = None
        self._written: Counter[tuple] | None = None
        # Until every caller writes through `node.write(sink)`: a view given
        # here, written by `write()`.
        if view is not None:
            self._attach(view)

    def write(self) -> SinkWrite:
        """Write the view given to the constructor (until callers use `node.write`)."""
        return self._commit()

    def _attach(self, view: IncrementalView) -> None:
        """Write `view` from now on."""
        self.view = view
        self.app_id = self.app_id or f"sverify:{view.name}"
        self._written = None
        if view.stored is not None and view.stored[0] == self.identifier:
            self._written = view.stored[1]

    def _source(self) -> IcebergSource:
        """The table as a source, for the nodes that read the stored node."""
        return IcebergSource(self.catalog, self.identifier, name=self.name)

    def _stored(self) -> Stored | None:
        if not self.catalog.table_exists(self.identifier):
            return None
        return self._source().stored()

    def _commit(self) -> SinkWrite:
        """Write the attached view's state, unless the table has it."""
        if self.view is None or self.app_id is None:
            raise ValueError(
                f"no node is stored in {self.identifier}: node.write(sink) attaches one"
            )
        view, app_id = self.view, self.app_id
        contract = view_contract_record(view)
        schema = sink_schema(view, contract.not_null)
        props = {PLAN: contract.plan, EPOCH: str(contract.epoch), APP: app_id}
        if not self.catalog.table_exists(self.identifier):
            t = self.catalog.create_table(
                self.identifier, schema=schema, properties={KEY: contract.to_json()}
            )
            created = True
        else:
            t = self.catalog.load_table(self.identifier)
            mine = [s for s in _ancestry(t) if s.summary and s.summary.get(APP) == app_id]
            if mine and int(mine[0].summary.get(EPOCH, "-1")) >= contract.epoch:  # type: ignore[union-attr]
                text = t.properties.get(KEY)
                committed = None if text is None else Contract.from_json(text)
                check_same_state(self.identifier, committed, contract)
                self._written = Counter(view.counts)
                return SinkWrite("skipped", _version(t.current_snapshot()), contract)
            created = False
        counts, old = view.counts, self._written
        positions: dict[str, list[int]] | None = None
        if not created and old is not None and t.spec().is_unpartitioned():
            removed = Counter({k: old[k] - counts[k] for k in old if old[k] > counts[k]})
            positions = _positions(t, schema, removed) if removed else {}
        mode: Literal["created", "append", "row-level", "overwrite"]
        if positions is None:
            mode = "created" if created else "overwrite"
            rows = view._arrow(counts).cast(schema)
            deleted = 0
        else:
            assert old is not None
            mode = "row-level" if positions else "append"
            rows = view._arrow(Counter({k: n - old[k] for k, n in counts.items()})).cast(schema)
            deleted = sum(len(p) for p in positions.values())
        with t.transaction() as tx:
            tx.set_properties({KEY: contract.to_json()})
            if positions is None:
                tx.overwrite(rows, snapshot_properties=props)
            else:
                _commit_rows(tx, t, rows, _position_deletes(t, positions), props)
        self._written = Counter(counts)
        version = _version(self.catalog.load_table(self.identifier).current_snapshot())
        return SinkWrite(mode, version, contract, rows.num_rows, deleted)
