"""Delta Lake tables (delta-rs) as change sources and sinks.

A `DeltaSource` hands a pipeline Arrow tables: the snapshot at a version,
and the change between two versions from the Change Data Feed, where
`insert` and `update_postimage` rows have weight +1 and `delete` and
`update_preimage` rows weight -1. Its metadata gives facts about every row:
schema nullability (enforced by writers), CHECK constraints
(`delta.constraints.*`, enforced by writers) and per-file statistics from the
add actions (trusted).

A `DeltaSink` writes a view to a Delta table, one commit per state, exactly
once (Delta's transaction identifiers), with the view's proved guarantees as
NOT NULL columns and CHECK constraints, and the contract in the commit
metadata. A restarted pipeline resumes from it (`DeltaSource.stored`).
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from datetime import timedelta
from typing import Literal

import pyarrow as pa
import pyarrow.dataset as ds

try:
    from deltalake import (
        CommitProperties,
        DeltaTable,
        QueryBuilder,
        Transaction,
        write_deltalake,
    )
except ImportError as e:
    raise ImportError("sverify.io.delta needs delta: pip install 'sverify[delta]'") from e

from sverify.contracts import Fact
from sverify.incremental import (
    Changes,
    IncrementalView,
    Row,
    Snapshot,
    SourceBatch,
    Stored,
    arrow_rows,
    first_line,
)
from sverify.io._common import (
    FILTER,
    ColumnStats,
    Contract,
    check_same_state,
    filter_rows,
    prune,
    q,
    sink_schema,
    stats_facts,
    view_contract_record,
)

CONSTRAINT = "Delta constraint"
INSERT = ("insert", "update_postimage")
DELETE = ("delete", "update_preimage")
METADATA_KEY = "sverify"
# Delta keeps timestamp statistics in milliseconds, truncated.
TIMESTAMP_SLACK = timedelta(microseconds=999)


def _arrow_schema(dt: DeltaTable) -> pa.Schema:
    return pa.schema(dt.schema().to_arrow())


def _deletion_vectors(dt: DeltaTable) -> bool:
    return "deletionVectors" in (dt.protocol().reader_features or [])


def _read(dt: DeltaTable) -> pa.Table:
    if _deletion_vectors(dt):
        # delta-rs's Arrow reader refuses deletion vectors; its DataFusion
        # reader applies them.
        reader = QueryBuilder().register("t", dt).execute("SELECT * FROM t")
        return pa.table(reader.read_all()).cast(_arrow_schema(dt))
    return pa.table(dt.to_pyarrow_table()).cast(_arrow_schema(dt))


def constraint_facts(dt: DeltaTable) -> list[Fact]:
    prefix = "delta.constraints."
    config = dt.metadata().configuration
    return [Fact(sql, CONSTRAINT) for k, sql in sorted(config.items()) if k.startswith(prefix)]


def file_stats(dt: DeltaTable) -> dict[str, dict[str, ColumnStats]]:
    """Per data file (by path), the statistics of each top-level column.

    With deletion vectors, a file's statistics describe all its physical
    rows, deleted ones included (`tightBounds: false`): bounds and NULL
    counts of a superset are still correct, but the row count is left out,
    as the protocol does not say that it counts the same rows as the NULL
    count."""
    actions = pa.table(dt.get_add_actions(flatten=True)).to_pylist()
    names = _arrow_schema(dt).names
    exact = not _deletion_vectors(dt)
    return {
        a["path"]: {
            c: ColumnStats(
                a.get(f"min.{c}"),
                a.get(f"max.{c}"),
                a.get(f"null_count.{c}"),
                a.get("num_records") if exact else None,
            )
            for c in names
        }
        for a in actions
    }


def _facts(dt: DeltaTable, files: dict[str, dict[str, ColumnStats]], source: str) -> list[Fact]:
    return constraint_facts(dt) + stats_facts(
        list(files.values()), _arrow_schema(dt), source, hi_slack=TIMESTAMP_SLACK
    )


# Operations that leave the table's configuration as it was.
_SAME_CONFIG = {
    "WRITE",
    "DELETE",
    "UPDATE",
    "MERGE",
    "OPTIMIZE",
    "VACUUM START",
    "VACUUM END",
    "ADD CONSTRAINT",
    "DROP CONSTRAINT",
    "STREAMING UPDATE",
}
CDF_KEY = "delta.enableChangeDataFeed"


def _cdf_on(dt: DeltaTable) -> bool:
    return dt.metadata().configuration.get(CDF_KEY, "false").lower() == "true"


class DeltaSource:
    """A Delta table read by version; see the module docstring.

    Pass it to `Pipeline.source`. `refresh` then reads the Change Data Feed
    (`delta.enableChangeDataFeed`) between the recorded version and the
    latest; where the feed is off or its files are gone, the new snapshot is
    diffed instead.

    Args:
        uri: The table's location: a path, or a URI such as `s3://...`.
        storage_options: Options for delta-rs's object store (credentials,
            region). Default: None.
        where: A SQL condition on the columns. The source is the rows on
            which it is TRUE; files are skipped only where Lean proves from
            their statistics that it is TRUE on none of their rows. Default:
            None, every row.

    Attributes:
        skipped: The files the last snapshot did not read.
    """

    def __init__(
        self,
        uri: str,
        *,
        storage_options: dict[str, str] | None = None,
        where: str | None = None,
    ):
        """With `where` (a SQL condition on the columns), the source is the
        rows on which it is TRUE: snapshots read only the files whose
        statistics do not rule it out (`prune`), and changes are filtered."""
        self.uri, self.storage_options, self.where = str(uri), storage_options, where
        self.skipped: list[str] = []
        """The files the last snapshot did not read."""

    def _facts(
        self, dt: DeltaTable, files: dict[str, dict[str, ColumnStats]], source: str
    ) -> list[Fact]:
        filtered = [] if self.where is None else [Fact(self.where, FILTER)]
        return _facts(dt, files, source) + filtered

    def _rows(self, dt: DeltaTable) -> tuple[pa.Table, dict[str, dict[str, ColumnStats]]]:
        """The source's rows at `dt`'s version, and the files they come from."""
        files = file_stats(dt)
        if self.where is None:
            return _read(dt), files
        keep = prune(files, _arrow_schema(dt), self.where, hi_slack=TIMESTAMP_SLACK)
        self.skipped = sorted(set(files) - keep)
        if _deletion_vectors(dt):
            table = _read(dt)  # delta-rs reads deletion vectors only whole
        else:
            dataset = dt.to_pyarrow_dataset()
            frags = [f for f in dataset.get_fragments() if any(f.path.endswith(p) for p in keep)]
            table = ds.FileSystemDataset(
                frags, dataset.schema, dataset.format, dataset.filesystem
            ).to_table()
        rows = filter_rows(table.cast(_arrow_schema(dt)), self.where)
        return rows, {p: s for p, s in files.items() if p in keep}

    def table(self, version: int | None = None) -> DeltaTable:
        """The table as delta-rs opens it.

        Args:
            version: The version to load. Default: the latest.

        Returns:
            A `deltalake.DeltaTable`.
        """
        dt = DeltaTable(self.uri, storage_options=self.storage_options)
        if version is not None:
            dt.load_as_version(version)
        return dt

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The table's rows at a version, with what its metadata says about
        every row (schema nullability, CHECK constraints, file statistics).

        Args:
            version: The version to read. Default: the latest.

        Returns:
            The version, the rows (those passing `where`, if given) and the
            facts.
        """
        dt = self.table(version)
        v = dt.version()
        rows, files = self._rows(dt)
        return Snapshot(v, rows, self._facts(dt, files, f"file stats @v{v}"))

    def contract(self, version: int | None = None) -> Contract | None:
        """The contract the last sverify commit up to `version` recorded.

        Args:
            version: The latest version to look at. Default: the latest.

        Returns:
            The contract a `DeltaSink` stored in the commit metadata, or None
            if no commit has one.
        """
        dt = self.table(version)
        for commit in dt.history():
            if METADATA_KEY in commit:
                return Contract.from_json(commit[METADATA_KEY])
        return None

    def stored(self) -> Stored | None:
        """The view state the table's last commit stored, if a `DeltaSink`
        made that commit (to resume a pipeline from).

        Returns:
            The stored state, to pass to `Pipeline.view(..., resume=...)`,
            or None if another writer made the last commit.

        Examples:
            ```python
            stored = DeltaSource("data/big").stored()
            pipe = sv.Pipeline(sv.connect())
            orders = pipe.source("orders", DeltaSource("data/orders"),
                                 version=stored.sources["orders"])
            big = pipe.view("big", big_orders(orders), resume=stored)
            print(big.resumed)  # resumed from data/big@v3
            ```
        """
        dt = self.table()
        last = dt.history(1)
        if not last or METADATA_KEY not in last[0]:
            return None
        c = Contract.from_json(last[0][METADATA_KEY])
        where = f"{self.uri}@v{dt.version()}"
        return Stored(where, self.uri, c.plan, c.sources, c.digests, _read(dt))

    def _check_cdf(self, dt: DeltaTable, since: int, end: int) -> None:
        """Raise unless every commit after `since` up to `end` wrote its
        changes to the feed. delta-rs reads appends of a table without CDF
        as inserts, but its deletes would be missing."""
        ops = {c["version"]: c.get("operation") for c in dt.history(end - since)}
        versions = range(since + 1, end + 1)
        if any(ops.get(v) is None for v in versions):
            raise ValueError(f"the log lacks commits between v{since} and v{end}")
        if all(ops[v] in _SAME_CONFIG for v in versions):
            check = [dt]
        else:
            check = [self.table(v) for v in versions]
        if not all(_cdf_on(t) for t in check):
            raise ValueError(f"{CDF_KEY} is not set for every commit")

    def changes(self, since: int) -> SourceBatch:
        """The change from version `since` to the latest, as
        `Pipeline.refresh` reads it.

        Args:
            since: The version the pipeline recorded.

        Returns:
            The net change from the Change Data Feed, with facts from the
            statistics of the files added since; or, where the feed is
            unavailable for some commit, the latest snapshot and the reason.
        """
        dt = self.table()
        end = dt.version()
        files = file_stats(dt)
        snapshot_facts = self._facts(dt, files, f"file stats @v{end}")
        schema = _arrow_schema(dt)
        if end == since:
            return SourceBatch(since, end, snapshot_facts, schema=schema)
        try:
            old: DeltaTable | None = self.table(since)
        except Exception:
            old = None  # its log is gone: no statistics for the batch
        try:
            self._check_cdf(dt, since, end)
            cdf = pa.table(dt.load_cdf(starting_version=since + 1, ending_version=end).read_all())
        except Exception as e:
            return SourceBatch(
                since,
                end,
                snapshot_facts,
                snapshot=self._rows(dt)[0],
                fallback=f"Delta CDF v{since}→v{end} unavailable: {first_line(e)}",
                schema=schema,
            )
        if self.where is not None:
            cdf = filter_rows(cdf, self.where)
        kinds = cdf.column("_change_type").to_pylist()
        rows = arrow_rows(cdf.select(schema.names).cast(schema))
        changes = Changes(
            inserts=[r for r, k in zip(rows, kinds, strict=True) if k in INSERT],
            deletes=[r for r, k in zip(rows, kinds, strict=True) if k in DELETE],
        )
        # The net inserts are rows at `end` written after `since`, so they
        # lie in the files `end` has and `since` had not.
        if old is not None:
            before = file_stats(old)
            new_files = {p: s for p, s in files.items() if p not in before}
            facts = self._facts(dt, new_files, f"file stats @v{end} (new files)")
        else:
            facts = self._facts(dt, {}, "")
        return SourceBatch(
            since,
            end,
            snapshot_facts,
            changes=changes,
            facts=facts,
            trusted=f"Δ trusted as coming from Delta CDF v{since}→v{end}",
            schema=schema,
        )


@dataclass
class SinkWrite:
    """What one `DeltaSink.write` did. `print` it for a one-line summary.

    Attributes:
        mode: `"created"` (the first write made the table), `"overwrite"`
            (a new sink replaced the table's rows), `"merge"` (the view's
            change in one MERGE commit) or `"skipped"` (the table already
            has this state's epoch).
        contract: What the commit recorded.
        inserted: Rows written.
        deleted: Rows deleted.
        constraints: The table's CHECK constraints from the view's
            guarantees, by name.
    """

    mode: Literal["created", "overwrite", "merge", "skipped"]
    version: int
    """The sink table's version afterwards."""
    contract: Contract
    inserted: int = 0
    deleted: int = 0
    constraints: dict[str, str] = field(default_factory=dict)

    def __str__(self) -> str:
        src = ", ".join(f"{t}@v{n}" for t, n in self.contract.sources.items())
        if self.mode == "skipped":
            return f"{self.contract.view} from {src}: already committed (v{self.version})"
        return (
            f"{self.contract.view} from {src}: {self.mode} v{self.version}, "
            f"{self.inserted} row(s) written, {self.deleted} deleted"
        )


OP = "__sverify_op"


class DeltaSink:
    """Writes a view's state to a Delta table, exactly once per state.

    Each commit carries the transaction `(app_id, epoch)`, where the epoch is
    the sum of the view's source versions; a state whose epoch the table has
    already committed is skipped. The first write creates the table with
    Change Data Feed enabled, NOT NULL columns and CHECK constraints for the
    view's proved guarantees; later writes MERGE the view's change (each
    changed row deleted and re-inserted with its new multiplicity) in one
    commit. A new sink on an existing table first overwrites it.

    The view must read only sources (`Pipeline.source`), so each state has
    source versions to key its commit by.

    Args:
        uri: The sink table's location: a path, or a URI such as `s3://...`.
        view: The view to write.
        app_id: The transaction's application id. Default:
            `"sverify:<view name>"`.
        storage_options: Options for delta-rs's object store. Default: None.

    Examples:
        ```python
        sink = DeltaSink("data/big", big)
        sink.write()     # creates the table, with the contract's constraints
        pipe.refresh()
        sink.write()     # one MERGE commit with the change
        ```
    """

    def __init__(
        self,
        uri: str,
        view: IncrementalView,
        *,
        app_id: str | None = None,
        storage_options: dict[str, str] | None = None,
    ):
        self.uri, self.view, self.storage_options = str(uri), view, storage_options
        self.app_id = app_id or f"sverify:{view.name}"
        self._written: Counter[tuple] | None = None
        if view.stored is not None and view.stored[0] == self.uri:
            self._written = view.stored[1]

    def _table(self) -> DeltaTable | None:
        if not DeltaTable.is_deltatable(self.uri, storage_options=self.storage_options):
            return None
        return DeltaTable(self.uri, storage_options=self.storage_options)

    def write(self) -> SinkWrite:
        """Write the view's current state, unless the table has its epoch.

        Returns:
            What was written.

        Raises:
            ValueError: The view reads a table that is not a source, the
                table has CHECK constraints the view does not guarantee, or
                it has this epoch from other contents of a static table.
        """
        contract = view_contract_record(self.view)
        commit = CommitProperties(
            custom_metadata={METADATA_KEY: contract.to_json()},
            app_transactions=[Transaction(self.app_id, contract.epoch)],
        )
        schema = sink_schema(self.view, contract.not_null)
        dt = self._table()
        done = None if dt is None else dt.transaction_version(self.app_id)
        if dt is not None and done is not None and done >= contract.epoch:
            check_same_state(
                self.uri,
                DeltaSource(self.uri, storage_options=self.storage_options).contract(),
                contract,
            )
            self._written = Counter(self.view.counts)
            return SinkWrite("skipped", dt.version(), contract)
        mode: Literal["created", "overwrite", "merge"]
        if dt is None:
            dt = DeltaTable.create(
                self.uri,
                schema,
                configuration={"delta.enableChangeDataFeed": "true"},
                storage_options=self.storage_options,
            )
            mode = "created"
        else:
            mode = "merge" if self._written is not None else "overwrite"
        constraints = self._constraints(dt, contract)
        counts = self.view.counts
        if mode == "merge":
            assert self._written is not None
            inserted, deleted = self._merge(dt, schema, self._written, counts, commit)
        else:
            rows = self.view._arrow(counts).cast(schema)
            write_deltalake(
                dt,
                rows,
                mode="overwrite",
                commit_properties=commit,
                storage_options=self.storage_options,
            )
            inserted, deleted = rows.num_rows, 0
        self._written = Counter(counts)
        version = DeltaTable(self.uri, storage_options=self.storage_options).version()
        return SinkWrite(mode, version, contract, inserted, deleted, constraints)

    def _constraints(self, dt: DeltaTable, contract: Contract) -> dict[str, str]:
        """Add the contract's CHECK constraints the table lacks. A constraint
        of an earlier contract that this one does not prove is an error: the
        table would promise what the view no longer guarantees."""
        have = {
            k.removeprefix("delta.constraints."): v
            for k, v in dt.metadata().configuration.items()
            if k.startswith("delta.constraints.")
        }
        stale = {k: v for k, v in have.items() if contract.checks.get(k) != v}
        if stale:
            raise ValueError(f"{self.uri} has constraints the view does not guarantee: {stale}")
        missing = {k: v for k, v in contract.checks.items() if k not in have}
        if missing:
            dt.alter.add_constraint(missing)
        return contract.checks

    def _merge(
        self,
        dt: DeltaTable,
        schema: pa.Schema,
        old: Counter[tuple],
        new: Counter[tuple],
        commit: CommitProperties,
    ) -> tuple[int, int]:
        """Replace every row whose multiplicity changed, in one commit."""
        changed = [k for k in old.keys() | new.keys() if old[k] != new[k]]
        examples = self.view.examples
        rows: list[tuple[Row, str]] = [(examples[k], "d") for k in changed if old[k] > 0]
        rows += [(examples[k], "i") for k in changed for _ in range(new[k])]
        if not rows:
            return 0, 0
        names = schema.names
        source = pa.Table.from_pylist(
            [{**dict(zip(names, r, strict=True)), OP: op} for r, op in rows],
            schema=pa.schema([*[f.with_nullable(True) for f in schema], pa.field(OP, pa.string())]),
        )
        same = " AND ".join(f"(t.{q(c)} IS NOT DISTINCT FROM s.{q(c)})" for c in names)
        (
            dt.merge(
                source,
                predicate=f"(s.{q(OP)} = 'd') AND {same}",
                source_alias="s",
                target_alias="t",
                commit_properties=commit,
            )
            .when_matched_delete()
            .when_not_matched_insert_all(predicate=f"s.{q(OP)} = 'i'", except_cols=[OP])
            .execute()
        )
        return sum(new[k] for k in changed), sum(old[k] for k in changed)
