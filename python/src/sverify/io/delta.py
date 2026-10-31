"""Delta Lake tables (delta-rs) as change sources and sinks.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

A `DeltaSource` hands the nodes reading it Arrow tables: the snapshot at a version,
and the change between two versions from the Change Data Feed, where
`insert` and `update_postimage` rows have weight +1 and `delete` and
`update_preimage` rows weight -1. Its metadata gives facts about every row:
schema nullability (enforced by writers), CHECK constraints
(`delta.constraints.*`, enforced by writers) and per-file statistics from the
add actions (trusted).

A `DeltaSink` stores a node (`node.write(DeltaSink(uri))`) in a Delta
table, one commit per state, exactly once (Delta's transaction identifiers),
with the node's proved guarantees as NOT NULL columns and CHECK constraints,
and the contract in the commit metadata. A restarted job resumes from it
(`DeltaSource.stored`), and nodes downstream read it through its Change Data
Feed.
"""

from __future__ import annotations

from collections import Counter
from datetime import timedelta
from pathlib import PurePosixPath
from typing import Literal

import pyarrow as pa
import pyarrow.dataset as ds
import sqlglot as sg

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
    SinkWrite,
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


def _basename(uri: str) -> str:
    return PurePosixPath(uri.rstrip("/")).name or uri


class DeltaSource:
    """A Delta table read by version, as the input of transforms.

    With `where` (a SQL condition on the columns), the source is the rows on
    which it is TRUE: snapshots read only the files whose statistics do not
    rule it out, and changes are filtered. `name` is the table's name in the
    plans that read it (default: the last part of `uri`)."""

    def __init__(
        self,
        uri: str,
        *,
        storage_options: dict[str, str] | None = None,
        where: str | None = None,
        name: str | None = None,
    ):
        self.uri, self.storage_options, self.where = str(uri), storage_options, where
        self.name = name or _basename(self.uri)
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
        dt = DeltaTable(self.uri, storage_options=self.storage_options)
        if version is not None:
            dt.load_as_version(version)
        return dt

    def schema(self) -> pa.Schema:
        return _arrow_schema(self.table())

    def latest(self) -> int:
        return self.table().version()

    def snapshot(self, version: int | None = None) -> Snapshot:
        dt = self.table(version)
        v = dt.version()
        rows, files = self._rows(dt)
        return Snapshot(v, rows, self._facts(dt, files, f"file stats @v{v}"))

    def contract(self, version: int | None = None) -> Contract | None:
        """The contract the last sverify commit up to `version` recorded."""
        dt = self.table(version)
        for commit in dt.history():
            if METADATA_KEY in commit:
                return Contract.from_json(commit[METADATA_KEY])
        return None

    def stored(self) -> Stored | None:
        """The view state the table's last commit stored, if a `DeltaSink`
        made that commit (to resume a pipeline from)."""
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

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        dt = self.table(until)
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


def _same_sql(a: str | None, b: str) -> bool:
    """The same condition, up to parentheses: Delta stores a constraint as
    it reads it (`(x IS NULL) OR (x > 0)` as `x IS NULL OR x > 0`)."""
    if a is None:
        return False

    def tree(sql: str) -> sg.exp.Expression:
        e = sg.parse_one(sql, read="postgres")
        return e.transform(lambda n: n.this if isinstance(n, sg.exp.Paren) else n)

    return a == b or tree(a) == tree(b)


OP = "__sverify_op"


class DeltaSink:
    """Stores a node in a Delta table, exactly once per state:
    `node.write(DeltaSink(uri))`.

    Each commit carries the transaction `(app_id, epoch)`, where the epoch is
    the sum of the node's source versions; a state whose epoch the table has
    already committed is skipped. The first write creates the table with
    Change Data Feed enabled, NOT NULL columns and CHECK constraints for the
    node's proved guarantees; later writes MERGE the change (each changed row
    deleted and re-inserted with its new multiplicity) in one commit. A new
    sink on an existing table first overwrites it, unless it resumes from it.
    `name` is the table's name in the plans that read the stored node
    (default: the last part of `uri`); `app_id` defaults to
    `sverify:<node name>`."""

    def __init__(
        self,
        uri: str,
        view: IncrementalView | None = None,
        *,
        app_id: str | None = None,
        storage_options: dict[str, str] | None = None,
        name: str | None = None,
    ):
        self.uri, self.storage_options = str(uri), storage_options
        self.name = name or _basename(self.uri)
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
        if view.stored is not None and view.stored[0] == self.uri:
            self._written = view.stored[1]

    def _source(self) -> DeltaSource:
        """The table as a source, for the nodes that read the stored node."""
        return DeltaSource(self.uri, storage_options=self.storage_options, name=self.name)

    def _stored(self) -> Stored | None:
        if self._table() is None:
            return None
        return self._source().stored()

    def _table(self) -> DeltaTable | None:
        if not DeltaTable.is_deltatable(self.uri, storage_options=self.storage_options):
            return None
        return DeltaTable(self.uri, storage_options=self.storage_options)

    def _commit(self) -> SinkWrite:
        """Write the attached view's state, unless the table has it."""
        if self.view is None or self.app_id is None:
            raise ValueError(f"no node is stored in {self.uri}: node.write(sink) attaches one")
        view, app_id = self.view, self.app_id
        contract = view_contract_record(view)
        commit = CommitProperties(
            custom_metadata={METADATA_KEY: contract.to_json()},
            app_transactions=[Transaction(app_id, contract.epoch)],
        )
        schema = sink_schema(view, contract.not_null)
        dt = self._table()
        done = None if dt is None else dt.transaction_version(app_id)
        if dt is not None and done is not None and done >= contract.epoch:
            check_same_state(
                self.uri,
                DeltaSource(self.uri, storage_options=self.storage_options).contract(),
                contract,
            )
            self._written = Counter(view.counts)
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
        counts = view.counts
        if mode == "merge":
            assert self._written is not None
            inserted, deleted = self._merge(dt, schema, self._written, counts, commit)
        else:
            rows = view._arrow(counts).cast(schema)
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
        stale = {k: v for k, v in have.items() if not _same_sql(contract.checks.get(k), v)}
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
        assert self.view is not None
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
