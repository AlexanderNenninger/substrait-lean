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

from dataclasses import replace
from datetime import timedelta
from pathlib import PurePosixPath
from typing import Literal

import pyarrow as pa
import pyarrow.compute as pc
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

from sverify._weighted import WEIGHT, concat, expanded, grouped, rows_of
from sverify.contracts import Fact
from sverify.incremental import Snapshot, SourceBatch, Stored, first_line
from sverify.io._common import (
    FILTER,
    ColumnStats,
    Contract,
    SinkWrite,
    filter_rows,
    prune,
    q,
    stats_facts,
)
from sverify.io._sink import Sink, SinkChange
from sverify.io._storage import Options, resolve
from sverify.steps import Pipeable

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


class DeltaSource(Pipeable):
    """A Delta table read by version, as the input of transforms.

    With `where` (a SQL condition on the columns), the source is the rows on
    which it is TRUE: snapshots read only the files whose statistics do not
    rule it out, and changes are filtered. `name` is the table's name in the
    plans that read it (default: the last part of `uri`).

    A refresh reads the Change Data Feed (`delta.enableChangeDataFeed`)
    between the version a node's state was computed from and the latest;
    where the feed is off or its files are gone, the new snapshot is diffed
    instead. Its metadata gives facts about every row, which can establish
    a transform's preconditions without reading the data: NOT NULL columns,
    CHECK constraints and file statistics.

    Args:
        uri: The table's location: a path, or a URI such as `s3://...`.
        storage_options: Options for delta-rs's object store (credentials,
            region): a `Storage` shared with other tables, a mapping, or a
            function returning one, called whenever the table is opened.
            Default: None, delta-rs's default chain (environment, profiles,
            roles).
        where: A SQL condition on the columns. The source is the rows on
            which it is TRUE; files are skipped only where Lean proves from
            their statistics that it is TRUE on none of their rows. Default:
            None, every row.
        name: The table's name in the plans that read it. Default: the last
            part of `uri`.

    Attributes:
        uri: The table's location.
        name: The table's name in the plans that read it.
        where: The SQL condition, or None.

    Examples:
        A node over a Delta table, updated from its Change Data Feed:

        ```python
        import tempfile
        from pathlib import Path

        import pyarrow as pa
        import sverify as sv
        from deltalake import write_deltalake
        from sverify.io import DeltaSource

        lake = Path(tempfile.mkdtemp())
        write_deltalake(lake / "orders", pa.table({"id": [1, 2], "amount": [30, 5]}),
                        configuration={"delta.enableChangeDataFeed": "true"})


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        big = big_orders(DeltaSource(str(lake / "orders")))
        big.refresh()
        write_deltalake(lake / "orders", pa.table({"id": [3], "amount": [50]}), mode="append")
        print(big.refresh())
        # big_orders:
        #   orders@v0→v1: 1 insert(s), 0 delete(s); Δ trusted as coming from Delta CDF v0→v1
        #   view big_orders: orders@v1
        ```
    """

    def __init__(
        self,
        uri: str,
        *,
        storage_options: Options = None,
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
        """The table as delta-rs opens it.

        Args:
            version: The version to load. Default: the latest.

        Returns:
            A `deltalake.DeltaTable`.
        """
        dt = DeltaTable(self.uri, storage_options=resolve(self.storage_options))
        if version is not None:
            dt.load_as_version(version)
        return dt

    def schema(self) -> pa.Schema:
        """The table's schema at its latest version, as Arrow."""
        return _arrow_schema(self.table())

    def latest(self) -> int:
        """The table's latest version."""
        return self.table().version()

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
        """The node state the table's last commit stored, if a `DeltaSink`
        made that commit. A restarted job's first refresh resumes the sink's
        node from it, when it was stored by the same plan from the same
        sources.

        Returns:
            The stored state, or None if another writer made the last commit.
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

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        """The change from version `since` to `until`, as a refresh reads it.

        Args:
            since: The version the node's state was computed from.
            until: The version to read up to. Default: the latest.

        Returns:
            The net change from the Change Data Feed, with facts from the
            statistics of the files added since; or, where the feed is
            unavailable for some commit, the snapshot at `until` and the
            reason.
        """
        dt = self.table(until)
        end = dt.version()
        files = file_stats(dt)
        snapshot_facts = self._facts(dt, files, f"file stats @v{end}")
        schema = _arrow_schema(dt)
        if end == since:
            return SourceBatch.unchanged(since, snapshot_facts, schema)
        try:
            old: DeltaTable | None = self.table(since)
        except Exception:
            old = None  # its log is gone: no statistics for the batch
        try:
            self._check_cdf(dt, since, end)
            cdf = pa.table(dt.load_cdf(starting_version=since + 1, ending_version=end).read_all())
        except Exception as e:
            return SourceBatch.from_snapshot(
                since,
                end,
                self._rows(dt)[0],
                reason=f"Delta CDF v{since}→v{end} unavailable: {first_line(e)}",
                snapshot_facts=snapshot_facts,
                schema=schema,
            )
        if self.where is not None:
            cdf = filter_rows(cdf, self.where)
        kind = cdf.column("_change_type").cast(pa.string())
        rows = cdf.select(schema.names).cast(schema)
        # The net inserts are rows at `end` written after `since`, so they
        # lie in the files `end` has and `since` had not.
        if old is not None:
            before = file_stats(old)
            new_files = {p: s for p, s in files.items() if p not in before}
            facts = self._facts(dt, new_files, f"file stats @v{end} (new files)")
        else:
            facts = self._facts(dt, {}, "")
        return SourceBatch.from_changes(
            since,
            end,
            inserts=rows.filter(_is_in(kind, INSERT)),
            deletes=rows.filter(_is_in(kind, DELETE)),
            trusted=f"Δ trusted as coming from Delta CDF v{since}→v{end}",
            facts=facts,
            snapshot_facts=snapshot_facts,
            schema=schema,
        )


def _is_in(column: pa.ChunkedArray, values: tuple[str, ...]) -> pa.ChunkedArray:
    return pc.call_function("is_in", [column], pc.SetLookupOptions(pa.array(values)))


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


class DeltaSink(Sink):
    """Stores a node in a Delta table, exactly once per state:
    `node.write(DeltaSink(uri))`, written by every `refresh`.

    Each commit carries the transaction `(app_id, epoch)`, where the epoch is
    the sum of the node's source versions; a state whose epoch the table has
    already committed is skipped, unless another plan committed it: then the
    table is overwritten, schema and constraints included. The first write creates the table with
    Change Data Feed enabled, NOT NULL columns and CHECK constraints for the
    node's proved guarantees; later writes MERGE the change (each changed row
    deleted and re-inserted with its new multiplicity) in one commit. A new
    sink on an existing table first overwrites it, unless it resumes from it.
    `name` is the table's name in the plans that read the stored node
    (default: the last part of `uri`); `app_id` defaults to
    `sverify:<name>`.

    The node `write` returns reads the table as a `DeltaSource`, through its
    Change Data Feed, and builds on the contract the stored node proved. A
    restarted job that builds the same nodes resumes from the table on its
    first refresh. The refresh's report includes what each write did
    (`SinkWrite`). It raises `ValueError` if the table has CHECK constraints
    the node does not guarantee, or holds this state's epoch from other
    contents of a `StaticSource`.

    Args:
        uri: The sink table's location: a path, or a URI such as `s3://...`.
        app_id: The transaction's application id. Default:
            `"sverify:<name>"`.
        storage_options: Options for delta-rs's object store, as for
            `DeltaSource`. Default: None.
        name: The table's name in the plans that read the stored node.
            Default: the last part of `uri`.

    Attributes:
        uri: The sink table's location.
        name: The table's name in the plans that read the stored node.

    Examples:
        A node written to a Delta table and refreshed:

        ```python
        import tempfile
        from pathlib import Path

        import pyarrow as pa
        import sverify as sv
        from deltalake import write_deltalake
        from ibis import _
        from sverify.io import DeltaSink, DeltaSource

        lake = Path(tempfile.mkdtemp())
        write_deltalake(lake / "orders", pa.table({"id": [1, 2], "amount": [30, 5]}),
                        configuration={"delta.enableChangeDataFeed": "true"})


        @sv.transform(ensures=[_.amount > 10])
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        orders = DeltaSource(str(lake / "orders"))
        big = big_orders(orders).write(DeltaSink(str(lake / "big_orders")))
        big.refresh()  # creates the table, with a CHECK constraint for `amount > 10`

        write_deltalake(lake / "orders", pa.table({"id": [3], "amount": [50]}), mode="append")
        print(big.refresh())  # reads the Change Data Feed, writes one MERGE commit
        # big_orders:
        #   orders@v0→v1: 1 insert(s), 0 delete(s); Δ trusted as coming from Delta CDF v0→v1
        #   view big_orders: orders@v1
        #   wrote big_orders from orders@v1: merge v3, 1 row(s) written, 0 deleted
        print(DeltaSource(str(lake / "big_orders")).contract().checks)
        # {'sverify_1': 'amount > 10'}
        ```
    """

    def __init__(
        self,
        uri: str,
        *,
        app_id: str | None = None,
        storage_options: Options = None,
        name: str | None = None,
    ):
        self.uri, self.storage_options = str(uri), storage_options
        super().__init__(name or _basename(self.uri), app_id=app_id, location=self.uri)

    def source(self) -> DeltaSource:
        """The table as a source, for the nodes that read the stored node."""
        return DeltaSource(self.uri, storage_options=self.storage_options, name=self.name)

    def _stored(self) -> Stored | None:
        if self._table() is None:
            return None
        return self.source().stored()

    def _table(self) -> DeltaTable | None:
        options = resolve(self.storage_options)
        if not DeltaTable.is_deltatable(self.uri, storage_options=options):
            return None
        return DeltaTable(self.uri, storage_options=options)

    def _version(self) -> int | None:
        dt = self._table()
        return None if dt is None else dt.version()

    def committed(self) -> Contract | None:
        """The contract of the last commit with this sink's transaction
        (`app_id`), with its epoch, or None."""
        dt = self._table()
        done = None if dt is None else dt.transaction_version(self.app_id)
        if done is None:
            return None
        contract = DeltaSource(self.uri, storage_options=self.storage_options).contract()
        return None if contract is None else replace(contract, epoch=done)

    def write(self, change: SinkChange) -> SinkWrite:
        """Create the table, overwrite it, or MERGE the change, in one commit
        that records the contract and the transaction `(app_id, epoch)`."""
        assert self.view is not None
        view, contract, schema = self.view, change.contract, change.schema
        options = resolve(self.storage_options)
        commit = CommitProperties(
            custom_metadata={METADATA_KEY: contract.to_json()},
            app_transactions=[Transaction(self.app_id, contract.epoch)],
        )
        mode: Literal["created", "overwrite", "merge"]
        dt = self._table()
        if dt is None:
            dt = DeltaTable.create(
                self.uri,
                schema,
                configuration={"delta.enableChangeDataFeed": "true"},
                storage_options=options,
            )
            mode = "created"
        else:
            mode = "overwrite" if change.replace else "merge"
        missing = self._constraints(dt, contract, replace=mode != "merge")
        if mode == "merge":
            if missing:
                dt.alter.add_constraint(missing)
            assert self._written is not None
            inserted, deleted = self._merge(dt, schema, self._written, view.state, commit)
        else:
            # The rows may come from another plan, with other columns: the
            # schema becomes the rows'. Its constraints hold only once the
            # rows are in, so the last commit records the epoch: a job that
            # stops in between writes the state again.
            rows = change.table
            write_deltalake(
                dt,
                rows,
                mode="overwrite",
                schema_mode="overwrite",
                commit_properties=None if missing else commit,
                storage_options=options,
            )
            if missing:
                DeltaTable(self.uri, storage_options=options).alter.add_constraint(
                    missing, commit_properties=commit
                )
            inserted, deleted = rows.num_rows, 0
        version = DeltaTable(self.uri, storage_options=options).version()
        return SinkWrite(mode, version, contract, inserted, deleted, contract.checks)

    def _constraints(self, dt: DeltaTable, contract: Contract, *, replace: bool) -> dict[str, str]:
        """The contract's CHECK constraints the table lacks. A constraint of
        an earlier contract that this one does not prove is an error: the
        table would promise what the view no longer guarantees. Unless the
        rows are replaced (`replace`): then the constraints a `DeltaSink`
        added (`sverify_*`) are dropped."""
        have = {
            k.removeprefix("delta.constraints."): v
            for k, v in dt.metadata().configuration.items()
            if k.startswith("delta.constraints.")
        }
        stale = {k: v for k, v in have.items() if not _same_sql(contract.checks.get(k), v)}
        foreign = {k: v for k, v in stale.items() if not (replace and k.startswith("sverify_"))}
        if foreign:
            raise ValueError(f"{self.uri} has constraints the view does not guarantee: {foreign}")
        for k in stale:
            dt.alter.drop_constraint(k)
            del have[k]
        return {k: v for k, v in contract.checks.items() if k not in have}

    def _merge(
        self,
        dt: DeltaTable,
        schema: pa.Schema,
        old: pa.Table,
        new: pa.Table,
        commit: CommitProperties,
    ) -> tuple[int, int]:
        """Replace every row whose multiplicity changed from `old` to `new`
        (weighted tables), in one commit."""
        changed = _multiplicities(old, new)
        if not changed.num_rows:
            return 0, 0
        n_old, n_new = changed.column(_OLD), changed.column(_NEW)
        rows = rows_of(changed.drop_columns([_OLD, _NEW]))
        gone = rows.filter(pc.call_function("greater", [n_old, 0]))
        came = expanded(rows.append_column(WEIGHT, n_new))
        nullable = pa.schema([f.with_nullable(True) for f in schema])
        source = pa.concat_tables(
            [
                t.rename_columns(schema.names)
                .cast(nullable)
                .append_column(OP, pa.repeat(pa.scalar(op), t.num_rows))
                for t, op in ((gone, "d"), (came, "i"))
            ]
        )
        names = schema.names
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
        total = [pc.call_function("sum", [n]).as_py() for n in (n_new, n_old)]
        return total[0], total[1]


_OLD, _NEW = "__sverify_old", "__sverify_new"


def _multiplicities(old: pa.Table, new: pa.Table) -> pa.Table:
    """The rows whose number of copies differs between the weighted tables
    `old` and `new`, with both numbers (`_OLD`, `_NEW`) and the difference
    (`WEIGHT`)."""

    def side(z: pa.Table, o: bool) -> pa.Table:
        w = z.column(WEIGHT)
        zero = pa.repeat(pa.scalar(0, pa.int64()), z.num_rows)
        rows = rows_of(z)
        rows = rows.append_column(_OLD, w if o else zero).append_column(_NEW, zero if o else w)
        return rows.append_column(WEIGHT, pc.call_function("negate", [w]) if o else w)

    return grouped(concat([side(new, False), side(old, True)]), (_OLD, _NEW, WEIGHT))
