"""Iceberg tables (pyiceberg) as change sources and sinks.

Versions are snapshot sequence numbers. An `IcebergSource` reads the
change between two versions from the data files the snapshots in between
added, when all of them are appends (trusted, like a Delta change feed).
Otherwise (row-level deletes, overwrites) the two snapshots are diffed, which
needs no trust in the format beyond the snapshots themselves
(`ChangeFeed.of_diff`). Facts: `required` fields (the schema) and per-file
statistics from the manifests.

Iceberg has no CHECK constraints, so an `IcebergSink` stores the view's
contract in the table properties and the summary of every snapshot it
writes. A reader trusts that contract only while every snapshot of the
table was written under it (no other writer appended in between).
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Any, Literal

import pyarrow as pa

try:
    from pyiceberg.catalog import Catalog
    from pyiceberg.expressions import AlwaysTrue
    from pyiceberg.io.pyarrow import ArrowScan
    from pyiceberg.table import Table
    from pyiceberg.table.snapshots import Operation
    from pyiceberg.table.snapshots import Snapshot as IcebergSnapshot
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
    first_line,
    snapshot_diff,
)
from sverify.io._common import (
    ColumnStats,
    Contract,
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
    """An Iceberg table of a catalog, read by snapshot sequence number."""

    def __init__(self, catalog: Catalog, identifier: str):
        self.catalog, self.identifier = catalog, identifier

    def table(self) -> Table:
        return self.catalog.load_table(self.identifier)

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

    def changes(self, since: int) -> SourceBatch:
        t = self.table()
        current = t.current_snapshot()
        end = _version(current)
        files = _live_files(t, current)
        snapshot_facts = self._facts(t, files, f"file stats @v{end}")
        if end == since:
            return SourceBatch(since, end, snapshot_facts)
        between = [s for s in _ancestry(t) if _version(s) > since]
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
                changes = snapshot_diff(_read(t, old), _read(t, current))
            except Exception as e:
                return SourceBatch(
                    since,
                    end,
                    snapshot_facts,
                    snapshot=_read(t, current),
                    schema=schema,
                    fallback=f"Iceberg snapshot v{since} unreadable: {first_line(e)}",
                )
            return SourceBatch(
                since,
                end,
                snapshot_facts,
                changes=changes,
                facts=snapshot_facts,
                kind="snapshot diff",
                schema=schema,
                trusted=(
                    f"Δ = snapshot v{end} − snapshot v{since} (not append-only: {', '.join(ops)}); "
                    "only the snapshots are trusted"
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


@dataclass
class IcebergWrite:
    mode: Literal["created", "append", "overwrite", "skipped"]
    version: int
    contract: Contract
    inserted: int = 0

    def __str__(self) -> str:
        src = ", ".join(f"{t}@v{n}" for t, n in self.contract.sources.items())
        return f"{self.contract.view} from {src}: {self.mode} v{self.version}"


class IcebergSink:
    """Writes a view's state to an Iceberg table, exactly once per state.

    A change that only inserts rows is appended; any other change overwrites
    the table. Every snapshot carries the contract's plan hash, the epoch
    (sum of source versions) and the app id; a state whose epoch the last
    snapshot of this app already has is skipped. The contract is also the
    table property `sverify.contract`, and columns the view proves NOT NULL
    are `required`."""

    def __init__(
        self,
        catalog: Catalog,
        identifier: str,
        view: IncrementalView,
        *,
        app_id: str | None = None,
    ):
        self.catalog, self.identifier, self.view = catalog, identifier, view
        self.app_id = app_id or f"sverify:{view.name}"
        self._written: Counter[tuple] | None = None
        if view.stored is not None and view.stored[0] == identifier:
            self._written = view.stored[1]

    def write(self) -> IcebergWrite:
        contract = view_contract_record(self.view)
        schema = sink_schema(self.view, contract.not_null)
        props = {PLAN: contract.plan, EPOCH: str(contract.epoch), APP: self.app_id}
        mode: Literal["created", "append", "overwrite"]
        if not self.catalog.table_exists(self.identifier):
            t = self.catalog.create_table(
                self.identifier, schema=schema, properties={KEY: contract.to_json()}
            )
            mode = "created"
        else:
            t = self.catalog.load_table(self.identifier)
            mine = [s for s in _ancestry(t) if s.summary and s.summary.get(APP) == self.app_id]
            if mine and int(mine[0].summary.get(EPOCH, "-1")) >= contract.epoch:  # type: ignore[union-attr]
                text = t.properties.get(KEY)
                committed = None if text is None else Contract.from_json(text)
                check_same_state(self.identifier, committed, contract)
                self._written = Counter(self.view.counts)
                return IcebergWrite("skipped", _version(t.current_snapshot()), contract)
            mode = "overwrite"
        counts, old = self.view.counts, self._written
        if mode != "created" and old is not None and all(counts[k] >= n for k, n in old.items()):
            mode = "append"
            rows = self.view._arrow(Counter({k: counts[k] - old[k] for k in counts}))
        else:
            rows = self.view._arrow(counts)
        rows = rows.cast(schema)
        with t.transaction() as tx:
            tx.set_properties({KEY: contract.to_json()})
            if mode == "append":
                tx.append(rows, snapshot_properties=props)
            else:
                tx.overwrite(rows, snapshot_properties=props)
        self._written = Counter(counts)
        version = _version(self.catalog.load_table(self.identifier).current_snapshot())
        return IcebergWrite(mode, version, contract, rows.num_rows)
