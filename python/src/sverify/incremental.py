"""Incrementally maintained views on DataFusion or Polars, with delta plans from Lean.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

The verified part is the delta plan: `substrait-check --delta` compiles the
view's Substrait plan with `Rel.delta`, splits it into union-free terms
(`Rel.terms`) and applies the weight-column encoding (`Rel.weighted`). Lean
proves the concatenated results are the change to the view
(`Rel.incremental_sound`, `Rel.zeval_terms`, `Rel.weighted_eval`). This module
is the trusted glue around it: it keeps the view as rows with multiplicities
(a weighted Arrow table, `sverify._weighted`), builds the change tables, runs
the delta plans on DataFusion or Polars and merges the result. A batch is
computed completely before anything is replaced, so a failing batch changes
nothing.

A view of a contracted transformation (`sverify.transform`, possibly
composed) keeps its proved postconditions in every state: the preconditions
on the base tables are checked once in full, and then only on each batch
(row conditions on the inserted rows, `unique` keys against the kept keys;
`Spec.update`, `Triple.maintained` in `SubstraitLean/Compose.lean`).
Postconditions a transform checks on its output instead of proving them
(`on_unproved="runtime"`) are checked on the view's full state once, and then
on the rows each batch inserts into it, before anything is replaced
(`PostconditionError`).

Users meet this module through nodes (`sverify.nodes`): `Node.pipe` composes
contracted transforms over sources, `.write` stores a node in a sink and ends
a stage, and `Node.refresh` (or `sv.group(...).refresh()` for several nodes)
brings the stages up to date, upstream first. Each stage is one
`IncrementalView`, maintained by a `Pipeline`, the internal engine behind
nodes; a stored node's table is a source of the stages that read it.

A `Pipeline` maintains views that read each other. Each view's change becomes
the change table of the views that read it (the DBSP chain rule,
`Rel.chain_sound`). A view without a delta rule (left join, fetch, window) is
recomputed and diffed, which still yields its change for the views
downstream (`ZSet.diff_correct`).

Sources come from a table format (`sverify.io`): `Pipeline.source` loads a
snapshot and records its version, and a refresh applies the format's change
feed from the recorded version to the latest, advancing the version in the
same commit. The feed is trusted to turn the old snapshot into the new one
(`ChangeFeed`, `Rel.cdf_sound` in `SubstraitLean/TableFormat.lean`), and
every `RefreshReport` says so; where the feed is unavailable, the new
snapshot is diffed against the view's state instead and the views reading it
are recomputed (`ChangeFeed.of_diff`). A source whose schema changed is read
in the schema the views were checked against where its data still fits
(added columns, widened types); otherwise the views reading it are planned
and checked again on the new schema and recomputed (`SchemaChange`).
"""

from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from typing import Any, Literal, Protocol

import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa
import sqlglot as sg

from sverify import _retention
from sverify._retention import RetentionReport
from sverify._scan import Native, Resident, Scan, ScanSnapshot
from sverify._state import DuckDBStore, Merger, State, Store, arrow_of, store_for
from sverify._weighted import (
    WEIGHT,
    concat,
    consolidated,
    deleted_count,
    duplicate_keys,
    expanded,
    inserted_count,
    matching,
    missing,
    negated,
    negative,
    positive,
    rows_of,
    weighted,
)
from sverify.contracts import (
    ON_DATA,
    ArrivesWithin,
    Condition,
    Discharged,
    Fact,
    MaxRows,
    PostconditionError,
    PreconditionError,
    References,
    Unique,
    discharge,
    label,
    register_facts,
    register_view,
    show_duration,
    table_facts,
    view_contract,
    violations,
)
from sverify.engine import (
    Connection,
    Engine,
    plan_json,
    put_table,
    read_tables,
    run_checker,
    run_plan,
    to_arrow,
    written_plan,
)
from sverify.steps import Pipeable

Row = tuple


class NotIncremental(Exception):
    """The plan is outside the fragment with verified delta rules.

    Raised by `sverify.engines.delta_plans` for a plan with an operator
    without a delta rule (a left join, aggregate, window, `DISTINCT` or
    `LIMIT`). A node over such a plan is recomputed and diffed instead, so
    refreshing it does not raise this. The message is the checker's reason.
    """


def delta_plans(plan_json: str) -> list[str]:
    """Ask Lean for the weighted delta plans of a Substrait JSON plan; the
    change to the view is the concatenation of their outputs.

    Each delta plan reads the view's input tables `t` at their old contents
    and their changes as tables `t$delta`, which have the columns of `t` and
    an extra `__weight` column (+1 for an inserted row, -1 for a deleted
    one). Its output has the view's columns and a weight column likewise.

    Args:
        plan_json: A Substrait plan as protobuf JSON, as
            `sverify.engines.substrait_json` or a node's `plan` write it.

    Returns:
        The delta plans, each a Substrait JSON plan in Lean's written form.

    Raises:
        sverify.errors.NotIncremental: The plan has an operator without a
            verified delta rule.
        ValueError: The checker rejects the plan.
    """
    code, out, err = run_checker(("--delta",), plan_json)
    if code == 3:
        raise NotIncremental(err.strip())
    if code != 0:
        raise ValueError(f"substrait-check --delta failed: {err.strip()}")
    return out.splitlines()


def _value_key(x: object) -> object:
    # The model has one NaN, equal to itself (Python's is not), and one zero
    # (`-0.0 + 0.0` is `0.0`).
    if isinstance(x, float):
        return "NaN" if math.isnan(x) else x + 0.0
    return x


def row_key(row: Row) -> tuple:
    """Rows compare as the model compares them (see `_value_key`)."""
    return tuple(_value_key(x) for x in row)


def arrow_rows(table: pa.Table) -> list[Row]:
    return [tuple(r.values()) for r in table.to_pylist()]


@dataclass
class Changes:
    """Rows to insert into and delete from one table (bag semantics: each
    deleted row removes one occurrence).

    Rows are an Arrow table with the table's columns, or tuples in the
    table's column order. An update is a delete of the old row plus an insert
    of the new one. `StaticSource.apply` takes one.

    Attributes:
        inserts: Rows to add. Default: none.
        deletes: Rows to remove, one occurrence each; every one must be in
            the table, or `StaticSource.apply` raises `ValueError`.
            Default: none.
    """

    inserts: pa.Table | Sequence[Row] = field(default_factory=list)
    deletes: pa.Table | Sequence[Row] = field(default_factory=list)


def _as_table(rows: pa.Table | Sequence[Row], schema: pa.Schema) -> pa.Table:
    """Rows in `schema`: an Arrow table's columns by name, or tuples in the
    schema's order."""
    if isinstance(rows, pa.Table):
        return rows.select(schema.names).cast(schema)
    return to_arrow(rows, schema)


def change_table(ch: Changes, schema: pa.Schema) -> pa.Table:
    """`ch` as one weighted table (`sverify._weighted`): each insert with
    weight 1, each delete with -1, in that order and not added up."""
    return concat(
        [weighted(_as_table(ch.inserts, schema), 1), weighted(_as_table(ch.deletes, schema), -1)]
    )


def snapshot_diff(old: pa.Table, new: pa.Table) -> pa.Table:
    """The change turning `old` into `new` (bag difference), as a weighted
    table."""
    return consolidated(weighted(new, 1), weighted(old.cast(new.schema), -1))


@dataclass
class Snapshot:
    """A table at one version, as a source hands it to a pipeline: what
    `VersionedSource.snapshot` returns.

    Attributes:
        version: The version.
        table: The rows at that version.
        facts: What the metadata says about every row (`sverify.contracts.Fact`),
            such as file statistics; empty if nothing is known.
    """

    version: int
    table: pa.Table
    facts: list[Fact]
    """What the metadata says about every row (schema nullability is in
    `table.schema`)."""


@dataclass
class SourceBatch:
    """What a versioned source has between a recorded version and its latest
    one: what `VersionedSource.changes` returns.

    Either `changes` from the format's change feed (the net change, with
    `facts` about the inserted rows and the `trusted` assumption it rests
    on), or the new `snapshot` alone with the reason the feed is unavailable
    (`fallback`). Build one with `unchanged`, `from_changes` or
    `from_snapshot`.

    Attributes:
        start: The version the batch starts from (`since`).
        end: The version it reaches.
        snapshot_facts: What the metadata says about every row at `end`.
        changes: The change, or None with `snapshot`.
        facts: What the metadata says about the inserted rows.
        trusted: What the change rests on, for the refresh report.
        kind: `"change feed"` (trusted) or `"snapshot diff"` (exact).
        snapshot: The table at `end`, when there is no change.
        fallback: Why there is no change, with `snapshot`.
        schema: The table's schema at `end`; None: the one recorded.
    """

    start: int
    end: int
    snapshot_facts: list[Fact]
    """What the metadata says about every row at `end`."""
    changes: Changes | None = None
    """Its rows as given: Arrow tables or tuples."""
    facts: list[Fact] = field(default_factory=list)
    trusted: str = ""
    """E.g. "Δ trusted as coming from Delta CDF v3→v5"."""
    kind: Literal["change feed", "snapshot diff"] = "change feed"
    """A snapshot diff is exact (`ChangeFeed.of_diff`): only the snapshots
    are trusted."""
    snapshot: pa.Table | None = None
    fallback: str | None = None
    schema: pa.Schema | None = None
    """The table's schema at `end`, which `changes` and `snapshot` have;
    None: the schema the pipeline recorded."""

    @classmethod
    def unchanged(
        cls, version: int, facts: Sequence[Fact] = (), schema: pa.Schema | None = None
    ) -> SourceBatch:
        """No change: the table is still at `version`.

        Args:
            version: The version asked for as `since`, and still the latest.
            facts: What the metadata says about every row. Default: none.
            schema: The table's schema. Default: the one recorded.

        Returns:
            A batch from `version` to `version`.
        """
        return cls(version, version, list(facts), schema=schema)

    @classmethod
    def from_changes(
        cls,
        since: int,
        until: int,
        *,
        inserts: pa.Table | Sequence[Row] = (),
        deletes: pa.Table | Sequence[Row] = (),
        trusted: str,
        facts: Sequence[Fact] = (),
        snapshot_facts: Sequence[Fact] = (),
        kind: Literal["change feed", "snapshot diff"] = "change feed",
        schema: pa.Schema | None = None,
    ) -> SourceBatch:
        """The change from `since` to `until`, as rows inserted and deleted.

        Args:
            since: The version the change starts from.
            until: The version it reaches.
            inserts: Rows added: an Arrow table, or tuples in column order.
            deletes: Rows removed, one copy each, in the same forms.
            trusted: What the change rests on, shown in the refresh report,
                such as `"Δ trusted as coming from Delta CDF v3→v5"`.
            facts: What the metadata says about the inserted rows.
                Default: none (preconditions are checked on the rows).
            snapshot_facts: What the metadata says about every row at
                `until`. Default: none.
            kind: `"change feed"` (the change is trusted) or `"snapshot
                diff"` (it was computed from two snapshots, so it is exact).
            schema: The table's schema at `until`, which the rows have.
                Default: the one recorded.

        Returns:
            The batch.
        """
        return cls(
            since,
            until,
            list(snapshot_facts),
            changes=Changes(inserts=inserts, deletes=deletes),
            facts=list(facts),
            trusted=trusted,
            kind=kind,
            schema=schema,
        )

    @classmethod
    def from_snapshot(
        cls,
        since: int,
        until: int,
        table: pa.Table,
        *,
        reason: str,
        snapshot_facts: Sequence[Fact] = (),
        schema: pa.Schema | None = None,
    ) -> SourceBatch:
        """No change is available from `since`: the whole table at `until`
        instead. The refresh diffs it against the state, and recomputes the
        nodes reading it.

        Args:
            since: The version the change would start from.
            until: The version of `table`.
            table: The table at `until`.
            reason: Why there is no change, shown in the refresh report.
            snapshot_facts: What the metadata says about every row of
                `table`. Default: none.
            schema: The table's schema at `until`. Default: `table`'s.

        Returns:
            The batch.
        """
        return cls(
            since,
            until,
            list(snapshot_facts),
            snapshot=table,
            fallback=reason,
            schema=table.schema if schema is None else schema,
        )


class VersionedSource(Protocol):
    """What a pipeline needs of a source: a table with integer versions that
    hands out its snapshot and its change between two versions. Delta and
    Iceberg tables implement it (`sverify.io`).

    Sources you write yourself usually subclass `sverify.io.Source`
    instead, which implements this protocol on top of one `read` method.
    Implement it directly for a table format with metadata facts and a
    change feed; `SourceBatch.from_changes` and `from_snapshot` build what
    `changes` returns.

    Attributes:
        name: The table's name in the plans that read it.
    """

    name: str
    """The table's name in the views that read it."""

    def schema(self) -> pa.Schema:
        """The table's schema at its latest version."""
        ...

    def latest(self) -> int:
        """The table's latest version."""
        ...

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The table at `version`, or at its latest version."""
        ...

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        """The change from version `since` to `until` (default: the latest)."""
        ...


Source = VersionedSource
"""The name the pipeline's internals use for `VersionedSource`."""


class SchemaError(Exception):
    """A source's new schema cannot be read in the old one, and a node
    reading it has a contract that was proved against the old one.

    Raised by `refresh`. A source whose data fits its old schema (added
    columns, widened types) is read in the old schema; otherwise the nodes
    reading it are planned again and recomputed, which a contracted node
    cannot be. Build its nodes again on the new schema, so the contract is
    proved against it. Nothing was applied.
    """


def _plain(t: pa.DataType) -> pa.DataType:
    if pa.types.is_large_string(t) or getattr(pa.types, "is_string_view", lambda _: False)(t):
        return pa.string()
    return t


def _widens(old: pa.DataType, new: pa.DataType) -> bool:
    """Every value of `old` is a value of `new` (the type widenings Delta and
    Iceberg allow: wider integers, float to double)."""
    if pa.types.is_integer(old) and pa.types.is_integer(new):
        if pa.types.is_signed_integer(old) and not pa.types.is_signed_integer(new):
            return False
        extra = 0 if pa.types.is_signed_integer(old) == pa.types.is_signed_integer(new) else 1
        return new.bit_width >= old.bit_width + extra
    return pa.types.is_float32(old) and pa.types.is_float64(new)


@dataclass
class SchemaChange:
    """How a source's schema at a new version differs from the one the
    pipeline's views were checked against."""

    added: list[str] = field(default_factory=list)
    dropped: list[str] = field(default_factory=list)
    widened: dict[str, str] = field(default_factory=dict)
    """Column -> "int32→int64"."""
    nullable: list[str] = field(default_factory=list)
    """NOT NULL columns that may now be NULL."""
    retyped: dict[str, str] = field(default_factory=dict)

    @staticmethod
    def of(old: pa.Schema, new: pa.Schema) -> SchemaChange:
        out = SchemaChange()
        names = set(new.names)
        out.dropped = [n for n in old.names if n not in names]
        out.added = [n for n in new.names if n not in set(old.names)]
        for f in old:
            if f.name not in names:
                continue
            g = new.field(f.name)
            a, b = _plain(f.type), _plain(g.type)
            if a != b:
                kind = out.widened if _widens(a, b) else out.retyped
                kind[f.name] = f"{a}→{b}"
            if not f.nullable and g.nullable:
                out.nullable.append(f.name)
        return out

    def __bool__(self) -> bool:
        return bool(self.added or self.dropped or self.widened or self.nullable or self.retyped)

    @property
    def compatible(self) -> bool:
        """The old schema can hold the new data, if its values fit: nothing
        the views read was dropped or retyped."""
        return not self.dropped and not self.retyped

    def __str__(self) -> str:
        parts = []
        if self.added:
            parts.append(f"added {', '.join(self.added)}")
        if self.dropped:
            parts.append(f"dropped {', '.join(self.dropped)}")
        parts += [f"widened {c} {t}" for c, t in self.widened.items()]
        if self.nullable:
            parts.append(f"{', '.join(self.nullable)} now nullable")
        parts += [f"retyped {c} {t}" for c, t in self.retyped.items()]
        return "; ".join(parts)


def _conform(table: pa.Table, schema: pa.Schema) -> pa.Table:
    """`table` (a new schema) in the old `schema`: added columns left out,
    widened columns cast back. Raises if a value does not fit (a NULL in a NOT
    NULL column, a number out of range)."""
    cols = []
    for f in schema:
        col = table.column(f.name)
        if not f.nullable and col.null_count:
            raise ValueError(f"{col.null_count} NULL(s) in column {f.name}, NOT NULL before")
        cols.append(col.cast(f.type, safe=True))
    return pa.Table.from_arrays(cols, schema=schema)


def _facts_within(facts: Sequence[Fact], names: Sequence[str]) -> list[Fact]:
    """The facts that only mention columns in `names`."""
    keep = set(names)
    out = []
    for f in facts:
        try:
            cols = {
                c.name for c in sg.parse_one(f.condition, read="postgres").find_all(sg.exp.Column)
            }
        except Exception:
            continue
        if cols <= keep:
            out.append(f)
    return out


def plan_digest(plan: str) -> str:
    """sha256 of a plan as Lean wrote it; sinks record it."""
    return hashlib.sha256(plan.encode()).hexdigest()


def table_digest(table: pa.Table) -> str:
    """sha256 of a table's schema and bag of rows (in no particular order)."""
    rows = sorted(repr(row_key(r)) for r in arrow_rows(table))
    return hashlib.sha256(repr((str(table.schema), rows)).encode()).hexdigest()


@dataclass
class Stored:
    """A view's state as a sink stored it, to resume a restarted pipeline
    from (`Pipeline.view(..., resume=...)`). Trusted: the sink's table holds
    exactly the view's rows at `sources`; it does while the sink is the only
    writer, and the sources check that the last commit is the sink's."""

    where: str
    """E.g. "data/big@v7"."""
    where_key: str
    """The table the sink writes (its uri or identifier)."""
    plan: str
    """`plan_digest` of the view's plan."""
    sources: dict[str, int]
    digests: dict[str, str]
    """`table_digest` of each static table the view read."""
    table: pa.Table


class StaticSource(Pipeable):
    """An in-memory Arrow table as a source, such as a small lookup table or
    the rows a test feeds in.

    Its `version` is the caller's (a release number, a batch id), and its
    `digest` is recorded next to it, so a sink can write a node reading it
    exactly once. `apply` changes some rows (the next refresh gets exactly
    that change); `replace` swaps the whole table (the next refresh diffs the
    two). `name` is the table's name in the plans that read it.

    Args:
        table: The table's contents.
        version: The version of these contents. Default: 0.
        name: The table's name in the plans that read it. Default:
            `"table"`.

    Attributes:
        table: The current contents.
        version: Their version.
        digest: sha256 of their schema and bag of rows.
        name: The table's name in the plans that read it.
    """

    def __init__(self, table: pa.Table, version: int = 0, *, name: str = "table"):
        self.name = name
        self._log: list[tuple[int, pa.Table]] = []
        """Each `apply`'s version and change, as a weighted table."""
        self.replace(table, version)

    def replace(self, table: pa.Table, version: int) -> None:
        """Swap in a new table at `version`, above the current one. The
        next `refresh` diffs it against the old one, and recomputes the
        nodes that read the table.

        Use `apply` when you know which rows changed: the refresh then gets
        exactly that change.

        Args:
            table: The new contents.
            version: Their version, above the current one.

        Raises:
            ValueError: `version` is not above the current version.
        """
        if hasattr(self, "version") and version <= self.version:
            raise ValueError(f"a new table needs a version above {self.version}")
        self.table, self.version, self.digest = table, version, table_digest(table)
        self._log, self._exact_since = [], version

    def apply(self, changes: Changes, version: int | None = None) -> None:
        """Insert and delete rows (an Arrow table, or tuples in schema
        order), as `version` (default: one above the current one).

        The next `refresh` of a node reading the source gets exactly this
        change (several `apply` calls in between add up), so the node is
        updated from it rather than recomputed.

        Args:
            changes: The rows to insert and delete.
            version: The new version, above the current one. Default: one
                above the current one.

        Raises:
            ValueError: `version` is not above the current version, or a
                deleted row is not in the table (nothing is changed).

        Examples:
            ```python
            import pyarrow as pa
            import sverify as sv
            from sverify.io import StaticSource

            orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


            @sv.transform()
            def big_orders(orders):
                return orders.filter(orders.amount > 10)


            big = big_orders(orders)
            big.refresh()
            orders.apply(sv.Changes(inserts=[(3, 50)], deletes=[(1, 30)]))  # version 1
            print(big.refresh())
            # big_orders:
            #   orders@v0→v1: 1 insert(s), 1 delete(s); Δ as applied to orders v0→v1
            #   view big_orders: orders@v1
            assert big.to_arrow().to_pylist() == [{"id": 3, "amount": 50}]
            ```
        """
        version = self.version + 1 if version is None else version
        if version <= self.version:
            raise ValueError(f"a new table needs a version above {self.version}")
        change = change_table(changes, self.table.schema)
        table = _apply_change(self.table, change, self.name)
        self.table, self.version, self.digest = table, version, table_digest(table)
        self._log.append((version, change))

    def schema(self) -> pa.Schema:
        """The current table's schema."""
        return self.table.schema

    def latest(self) -> int:
        """The current version."""
        return self.version

    def snapshot(self, version: int | None = None) -> Snapshot:
        """The current table, as a refresh reads it.

        Args:
            version: The current version, or None for it.

        Returns:
            The version and the rows, with no facts from metadata.

        Raises:
            ValueError: `version` is not the current one; a static table
                keeps only its current contents.
        """
        if version not in (None, self.version):
            raise ValueError(f"a static table only has version {self.version}")
        return Snapshot(self.version, self.table, [])

    def changes(self, since: int, until: int | None = None) -> SourceBatch:
        """The change from version `since` to the current one, as a refresh
        reads it.

        Args:
            since: The version the node's state was computed from.
            until: The current version, or None for it.

        Returns:
            The rows `apply` inserted and deleted since `since`; or, if
            `replace` swapped the table since, the current table, to diff.

        Raises:
            ValueError: `until` is not the current version.
        """
        if until not in (None, self.version):
            raise ValueError(f"a static table only has version {self.version}")
        if since == self.version:
            return SourceBatch.unchanged(since)
        if since >= self._exact_since:
            change = consolidated(*[ch for v, ch in self._log if v > since])
            return SourceBatch.from_changes(
                since,
                self.version,
                inserts=expanded(positive(change)),
                deletes=expanded(positive(negated(change))),
                trusted=f"Δ as applied to {self.name} v{since}→v{self.version}",
                schema=self.table.schema,
            )
        return SourceBatch.from_snapshot(
            since, self.version, self.table, reason="static table replaced"
        )


@dataclass
class SourceRefresh:
    table: str
    start: int
    end: int
    mode: Literal["unchanged", "change feed", "snapshot diff", "recomputed"]
    detail: str = ""
    inserts: int = 0
    deletes: int = 0
    schema: str = ""
    """How the source's schema changed in this batch (`SchemaChange`), or ""."""

    def span(self) -> str:
        """The versions, as "orders@v3→v5" ("orders@v5" if unchanged)."""
        if self.mode == "unchanged":
            return f"{self.table}@v{self.start}"
        return f"{self.table}@v{self.start}→v{self.end}"

    def __str__(self) -> str:
        if self.mode == "unchanged":
            return f"{self.table}@v{self.start}: no new version"
        span = f"{self.table}@v{self.start}→v{self.end}"
        counts = f"{self.inserts} insert(s), {self.deletes} delete(s)"
        if self.mode == "recomputed":
            return f"{span}: recomputed from scratch ({self.detail}); {counts}"
        return f"{span}: {counts}; {self.detail}"


@dataclass
class RefreshReport:
    sources: list[SourceRefresh]
    preconditions: list[Discharged]
    """How each precondition on the batch was established."""
    versions: dict[str, dict[str, int]]
    """For each view, the version of every source it reads."""
    audited: bool = False
    """The batch was compared with the new snapshot, and each view with its
    recomputation, and they agreed."""
    retention: list[RetentionReport] = field(default_factory=list)
    """For each view over a source with `arrives_within`: its open buckets,
    those retired in this refresh, and the bound (`sverify._retention`)."""
    postconditions: list[Discharged] = field(default_factory=list)
    """The unproved postconditions (`on_unproved="runtime"`) checked on the
    rows the batch inserts into each view, by view."""

    @property
    def recomputed(self) -> list[str]:
        return [s.table for s in self.sources if s.mode == "recomputed"]

    @property
    def notable(self) -> list[str]:
        """What a log should show in full: sources whose change could not be
        applied incrementally, and schema changes."""
        out = [f"{t} recomputed" for t in self.recomputed]
        out += [f"{s.table} schema: {s.schema}" for s in self.sources if s.schema]
        return out

    def __str__(self) -> str:
        lines = [str(s) for s in self.sources]
        lines += [f"requires {p}" for p in self.preconditions]
        lines += [f"ensures {p}" for p in self.postconditions]
        for v, vs in self.versions.items():
            lines.append(f"view {v}: " + ", ".join(f"{t}@v{n}" for t, n in vs.items()))
        if self.audited:
            lines.append("audit: batch matches the new snapshots; views match recomputation")
        lines += [str(r) for r in self.retention]
        return "\n".join(lines)


class AuditError(Exception):
    """In audit mode, the change feed or a view disagrees with recomputation.

    Raised by `refresh(audit=True)`, which compares each batch with the new
    snapshots and every node with its recomputation before committing
    anything: when this is raised, nothing was applied.
    """


class IncrementalView:
    """A query result kept up to date from table changes instead of recomputed.

    `query` is an Ibis expression or SQL over tables of `con` (`connect()`).
    The view is also registered as table `name`. `engine` (default: the
    connection's) runs the plans: the view's plan as Lean read it
    (`written_plan`) and the delta plans, all over the tables of `con`; with
    an engine named, preconditions are also checked there.

    If `query` is the result of contracted transformations, `guarantees` are
    its proved postconditions; they hold in every state of the view, because
    every batch is checked against the preconditions on the base tables
    (`requires`). A standalone view refuses a query without delta rules
    (`NotIncremental`); in a `Pipeline` such a view is recomputed instead.
    """

    def __init__(
        self,
        con: Connection,
        query: ir.Table | str,
        name: str,
        engine: Engine | None = None,
        *,
        pipeline: Pipeline | None = None,
        resume: Stored | None = None,
    ):
        self.con, self.name = con, name
        self.engine: Engine = engine or con.engine
        self.query = query
        contract = None if isinstance(query, str) else view_contract(query)
        self._plan(query, standalone=pipeline is None)
        self.requires: dict[str, list[Condition]] = contract.requires if contract else {}
        self.guarantees: list[Condition] = contract.guarantees if contract else []
        self.checked: list[Condition] = contract.checked if contract else []
        """Postconditions that were not proved, checked on every state
        instead (`on_unproved="runtime"`): on the first in full, then on the
        rows each batch inserts (`unique` keys against the new state)."""
        self.postconditions: list[Discharged] = []
        """How `checked` was established on the first state."""
        self.pipeline = pipeline or Pipeline(con, engine)
        self.pipeline._check_new_requires(self.requires)
        found = _retention.plan(query, self.requires)
        self.retention: _retention.Retention | None = None if isinstance(found, str) else found
        """How the view drops its final time buckets (`sverify._retention`),
        if it does."""
        self.retention_off: str | None = found if isinstance(found, str) else None
        """Why a view over a source with `arrives_within` keeps every bucket."""
        self.retired_through: object = None
        """The start of the last bucket retired: the state holds every bucket
        after it, and none at or before it. None: nothing retired."""
        self.resumed: str | None = None
        """How the view got its first state from `resume`, or why it could
        not and was computed instead."""
        self.stored: tuple[str, State] | None = None
        """Where the view's state was restored from, and that state."""
        self.store: Store = store_for(self.engine)
        self.serial = 0
        """How many times the view's state has changed: the sinks writing it
        record the serial they wrote."""
        self._log: list[tuple[int, pa.Table | None]] = []
        self._sinks: list = []
        """Where the view keeps its state (`sverify._state`): in DuckDB on
        DuckDB, else in Arrow."""
        reason = None if resume is None else self._mismatch(resume)
        if resume is not None and reason is None:
            # The schema the engine gives the view, from a run on no rows.
            empty = {t: con.schema(t).empty_table() for t in self.tables}
            schema = self._result_on(empty).schema
            result = resume.table.select(schema.names).cast(schema)
            self.resumed = f"resumed from {resume.where}"
        else:
            result = run_plan(con, self.plan, self.engine, keep=self.store.keep)
            if resume is not None:
                self.resumed = f"computed: {reason} (stored at {resume.where})"
        self._set_schema(result.schema)
        self.state: State = self._merge(self.store.weighted(result), keep=self.store.keep)
        """The view's rows, each once with its number of copies (a weighted
        table, `sverify._weighted`): an Arrow table, or one DuckDB holds."""
        if resume is not None and reason is None:
            self.stored = (resume.where_key, self.state)
        self._publish()
        self.table: ir.Table = con.table(name)
        """The view as a table for other queries; contracted transformations
        that read it build on `guarantees`."""
        if self.stored is None:
            # A resumed state was checked by the run that stored it.
            self.postconditions = self._check(self.table, self.checked, "row(s)")
        if contract is not None:
            register_view(self.table, contract)
        self.pipeline._views.append(self)

    def _plan(self, query: ir.Table | str, *, standalone: bool) -> None:
        plan = json.loads(plan_json(self.con, query))
        self.columns: list[str] = plan["relations"][0]["root"]["names"]
        self.tables = read_tables(plan)
        # Publishing the view would replace the table it is computed from.
        if self.name in self.tables:
            raise ValueError(f"view name {self.name!r} is a table the view reads")
        self.fallback: str | None = None
        """Why the view has no delta plans and is recomputed, if it is."""
        try:
            self.deltas = delta_plans(json.dumps(plan))
        except NotIncremental as e:
            if standalone:
                raise
            self.deltas, self.fallback = [], str(e)
        self.plan = written_plan(json.dumps(plan))

    def _mismatch(self, stored: Stored) -> str | None:
        """Why `stored` is not this view's state at the versions the pipeline
        holds its inputs at, or None if it is."""
        if stored.plan != plan_digest(self.plan):
            return "the plan changed"
        lineage: dict[str, int] = {}
        for t in self.tables:
            lineage.update(self.pipeline.lineage(t))
        if stored.sources != lineage:
            have = ", ".join(f"{t}@v{n}" for t, n in lineage.items())
            want = ", ".join(f"{t}@v{n}" for t, n in stored.sources.items())
            return f"stored from {want}, the pipeline holds {have}"
        digests = self.pipeline.digests(self.name)
        if stored.digests != digests:
            return f"static tables changed ({', '.join(sorted(digests))})"
        return None

    @property
    def contracted(self) -> bool:
        # A plain function's view requires nothing of each input: {"orders": []}.
        return any(self.requires.values()) or bool(self.guarantees) or bool(self.checked)

    def _check(self, table: ir.Table, conds: Sequence[Condition], what: str) -> list[Discharged]:
        """Check runtime-checked postconditions on `table` (rows of the view),
        raising `PostconditionError` with "<n> <what> of <view> violate ...".
        """
        out = []
        for c in conds:
            if n := violations(table, c, self.pipeline.engine):
                raise PostconditionError(
                    f"{n} {what} of {self.name} violate {label(c)}; nothing was applied"
                )
            out.append(Discharged(self.name, label(c), ON_DATA))
        return out

    def _check_change(self, delta: pa.Table, new: pa.Table | Native | None) -> list[Discharged]:
        """Check `checked` on a batch: row conditions on the rows `delta`
        inserts, keys on the `new` state (None if no key is checked)."""
        rowwise = [c for c in self.checked if not isinstance(c, Unique)]
        keys = [c for c in self.checked if isinstance(c, Unique)]
        out: list[Discharged] = []
        for conds, rows, what in [
            (rowwise, rows_of(positive(delta)), "inserted row(s)"),
            (keys, new, "row(s)"),
        ]:
            if not conds:
                continue
            assert rows is not None
            name = self.name + "$checked"
            put_table(self.con, name, rows)
            try:
                out += self._check(self.con.table(name), conds, what)
            finally:
                self.con.drop(name)
        return out

    def _replan(self, changed: set[str]) -> None:
        """Plan the view again over the current schemas of the `changed`
        tables it reads, and recompute it."""
        query = self.query
        if not isinstance(query, str):
            old = [op for op in query.op().find(ops.DatabaseTable) if op.name in changed]
            new = {op: self.con.table(op.name).op() for op in old}
            query = query.op().replace(new).to_expr()  # type: ignore[attr-defined]
        self.query = query
        self._plan(query, standalone=False)
        result = run_plan(self.con, self.plan, self.engine, keep=self.store.keep)
        self._set_schema(result.schema)
        self.state = self._merge(self.store.weighted(result), keep=self.store.keep)
        self._record(None)
        self._publish()
        self.table = self.con.table(self.name)

    def _set_schema(self, schema: pa.Schema) -> None:
        self.schema = schema
        weighted_schema = pa.schema([*schema, pa.field(WEIGHT, pa.int64())])
        self._merge = Merger(self.con, weighted_schema)
        """Adds up weighted tables of the view's rows by a plan Lean
        checked."""

    def _record(self, delta: pa.Table | None) -> None:
        """The state changed by `delta` (None: replaced). The change is kept
        for the sinks that have not written it yet."""
        self.serial += 1
        written = [s._written for s in self._sinks if s._written is not None]
        if written:
            self._log.append((self.serial, delta))
            self._log = [(n, d) for n, d in self._log if n > min(written)]
        else:
            self._log = []

    def changes_since(self, serial: int) -> pa.Table | None:
        """The view's change since its state at `serial`, as a weighted
        table; None if it is not known (the state was replaced since)."""
        if serial == self.serial:
            return weighted(self.schema.empty_table(), 1)
        parts = [d for n, d in self._log if n > serial]
        if len(parts) != self.serial - serial or any(d is None for d in parts):
            return None
        total = weighted(self.schema.empty_table(), 1)
        for part in parts:
            assert part is not None
            total = arrow_of(self._merge(total, part))
        return total

    def _publish(self) -> None:
        put_table(self.con, self.name, self.store.expanded(self.state))

    @property
    def versions(self) -> dict[str, int]:
        """The version of every source the view reads, e.g. `{"orders": 41}`
        (shown as `orders@v41`)."""
        return self.pipeline.lineage(self.name)

    def rows(self) -> list[Row]:
        """The view's contents as a bag of rows, in a canonical order. A view
        that retires buckets holds the buckets after `retired_through`."""
        rows = arrow_rows(expanded(arrow_of(self.state)))
        return sorted(rows, key=lambda r: repr(row_key(r)))

    def recompute(self) -> list[Row]:
        """The view computed from scratch, for checking."""
        rows = arrow_rows(run_plan(self.con, self.plan, self.engine))
        return sorted(rows, key=lambda r: repr(row_key(r)))

    def apply(self, changes: Mapping[str, Changes]) -> None:
        """Apply changes to base tables, and to every view of the pipeline."""
        self.pipeline.apply(changes)

    def _weighted(self, result: pa.Table) -> pa.Table:
        """A delta plan's result (the view's columns, then the weight) as a
        weighted table in the view's schema."""
        schema = pa.schema([*self.schema, pa.field(WEIGHT, pa.int64())])
        return result.rename_columns(schema.names).cast(schema)

    def _delta(self, deltas: Mapping[str, pa.Table]) -> pa.Table:
        """The view's change, from its delta plans, as a weighted table. The
        tables hold their old contents; `t$delta` is loaded with each input's
        change."""
        con = self.con
        try:
            for t in self.tables:
                _load_delta_table(con, t, deltas.get(t))
            parts = [self._weighted(run_plan(con, plan, self.engine)) for plan in self.deltas]
        finally:
            for t in self.tables:
                con.drop(t + "$delta")
        total = weighted(self.schema.empty_table(), 1)
        for part in parts:
            total = arrow_of(self._merge(total, part))
        return total

    def _result_on(self, new_tables: Mapping[str, pa.Table | Native]) -> pa.Table:
        """The view computed on the new inputs; nothing is replaced."""
        con = self.con
        old = {t: con.get(t) for t in self.tables if t in new_tables}
        try:
            for t in old:
                put_table(con, t, new_tables[t])
            return run_plan(con, self.plan, self.engine)
        finally:
            for t, table in old.items():
                put_table(con, t, table)

    def _diff(self, new_tables: Mapping[str, pa.Table | Native]) -> pa.Table:
        """The view's change by recomputing it on the new inputs and diffing,
        as a weighted table."""
        new = self._kept(self._result_on(new_tables).cast(self.schema))
        return arrow_of(self._merge(weighted(new, 1), self.store.negated(self.state)))

    def _kept(self, result: pa.Table) -> pa.Table:
        """The rows of a result the state keeps: with retention, the buckets
        after the last one retired. The others are final, so their change is
        empty (`Retention.retention_sound`)."""
        if self.retention is None or self.retired_through is None:
            return result
        return _retention.after(result, self.retention.column, self.retired_through)


def _load_delta_table(con: Connection, t: str, change: pa.Table | None) -> None:
    """Table `t$delta`: `change` (a weighted table, None: no change) in the
    schema of `t` and the weight."""
    base = con.schema(t)
    schema = pa.schema([*base, pa.field(WEIGHT, pa.int64())])
    if change is None:
        change = schema.empty_table()
    put_table(con, t + "$delta", change.rename_columns(schema.names).cast(schema))


class Pipeline:
    """Views that read each other, maintained together.

        pipe = Pipeline(con)
        big = pipe.view("big", doubled(paid(con.table("orders"))))
        pipe.view("by_id", summarize(big.table))
        pipe.apply({"orders": Changes(inserts=[...])})

    A view may read base tables and views added before it, as `view.table`.
    `apply` runs the views in order: each view's change is the change table
    of the views that read it, so every intermediate result is materialized
    once and shared. Views without delta rules are recomputed and diffed
    (`fallbacks`). Preconditions of contracted views are checked per batch.

    Base tables may instead come from a table format (`source`), and then
    change only through `refresh`.
    """

    def __init__(self, con: Connection, engine: Engine | None = None):
        self.con = con
        self.engine: Engine | None = engine
        """The engine for plans and precondition checks; None: the
        connection's for plans, Ibis on the connection for checks."""
        self._views: list[IncrementalView] = []
        self.requires: dict[str, list[Condition]] = {}
        """Preconditions on base tables, of every contracted view."""
        self.preconditions: list[Discharged] = []
        """How each precondition was established on the full base tables."""
        self.sources: dict[str, VersionedSource] = {}
        self.versions: dict[str, int] = {}
        """The version of each source table the pipeline's state reflects."""
        self.latest: dict[tuple[str, str], object] = {}
        """For each `arrives_within(col, …)` on table `t`, the largest `col`
        seen, keyed `(t, col)`: the watermark is it minus the lateness."""

    def source(self, name: str, source: VersionedSource, *, version: int | None = None) -> ir.Table:
        """Load the snapshot of `source` at `version` (default: the latest)
        as base table `name`, record its version and what its metadata says
        about it. On DuckDB, a Delta or Iceberg table is held as the files to
        read (`Scan`), which DuckDB reads itself."""
        if name in self.sources or name in self.views:
            raise ValueError(f"the pipeline already has a table {name!r}")
        native = self._native(source, version)
        if native is not None:
            put_table(self.con, name, native.scan)
            facts, read = native.facts, native.version
        else:
            snap = source.snapshot(version)
            put_table(self.con, name, snap.table)
            facts, read = snap.facts, snap.version
        register_facts(self.con, name, facts)
        self.sources[name] = source
        self.versions[name] = read
        return self.con.table(name)

    def _native(self, source: VersionedSource, version: int | None) -> ScanSnapshot | None:
        """The snapshot of `source` as files DuckDB reads itself, where the
        plans run on DuckDB and the source can give one; else None."""
        native = getattr(source, "_native", None)
        if native is None or (self.engine or self.con.engine) != "duckdb":
            return None
        return native(version)

    def view(
        self, name: str, query: ir.Table | str, *, resume: Stored | None = None
    ) -> IncrementalView:
        """Add a view. With `resume` (what a sink stored, e.g.
        `DeltaSource(uri).stored()`), its first state is the stored one
        instead of a computation, if the plan is the same and the pipeline
        holds the view's sources at the stored versions (`pipe.source(...,
        version=stored.sources[name])`); `view.resumed` says which."""
        if name in self.views or name in self.sources:
            raise ValueError(f"the pipeline already has a view {name!r}")
        return IncrementalView(self.con, query, name, self.engine, pipeline=self, resume=resume)

    @property
    def views(self) -> dict[str, IncrementalView]:
        return {v.name: v for v in self._views}

    @property
    def fallbacks(self) -> dict[str, str]:
        """Views that are recomputed and diffed, with the reason."""
        return {v.name: v.fallback for v in self._views if v.fallback is not None}

    def lineage(self, name: str) -> dict[str, int]:
        """The version of every source table that `name` (a view or table)
        is computed from."""
        if name in self.versions:
            return {name: self.versions[name]}
        out: dict[str, int] = {}
        if (v := self.views.get(name)) is not None:
            for t in v.tables:
                out.update(self.lineage(t))
        return out

    def digests(self, name: str) -> dict[str, str]:
        """The content digest of every source with one (`StaticSource`)
        that `name` is computed from: the tables whose versions the caller
        gives, so a sink can tell other contents at the same version."""
        if (digest := getattr(self.sources.get(name), "digest", None)) is not None:
            return {name: digest}
        out: dict[str, str] = {}
        if (v := self.views.get(name)) is not None:
            for t in v.tables:
                out.update(self.digests(t))
        return out

    def _check_new_requires(self, requires: Mapping[str, Sequence[Condition]]) -> None:
        """Establish a new view's preconditions on the full base tables, once:
        from metadata where possible, else on the data."""
        for t, conds in requires.items():
            if t in self.views:
                raise ValueError(f"preconditions on view {t!r} must be proved, not checked")
            if refs := [label(c) for c in conds if isinstance(c, References)]:
                raise ValueError(f"incremental views do not support foreign keys yet: {refs}")
            if caps := [label(c) for c in conds if isinstance(c, MaxRows)]:
                raise ValueError(f"incremental views do not support row caps: {caps}")
            known = {label(c) for c in self.requires.get(t, [])}
            new = [c for c in conds if label(c) not in known]
            table = self.con.table(t)
            for c in new:
                if isinstance(c, Unique):
                    if dup := duplicate_keys(self.con.get(t), c.cols):
                        raise PreconditionError(f"{dup} row(s) of {t} violate {label(c)}")
                    self.preconditions.append(Discharged(t, label(c), ON_DATA))
                elif isinstance(c, ArrivesWithin):
                    self.preconditions.append(self._first_arrivals(t, table, c))
            rowwise = [c for c in new if not isinstance(c, Unique | ArrivesWithin)]
            self.preconditions += discharge(
                table, t, rowwise, self.engine, table_facts(table), f"row(s) of {t}"
            )
            self.requires.setdefault(t, []).extend(new)

    def _first_arrivals(self, t: str, table: ir.Table, c: ArrivesWithin) -> Discharged:
        """`arrives_within` on the full table: no NULL times; the largest is
        the first watermark's."""
        col: Any = table[c.col]
        if not col.type().is_timestamp():
            raise ValueError(f"{label(c)}: {t}.{c.col} is {col.type()}, not a timestamp")
        stats = table.aggregate(latest=col.max(), nulls=col.isnull().sum()).to_pyarrow()
        if nulls := stats.column("nulls")[0].as_py():
            raise PreconditionError(f"{nulls} row(s) of {t} violate {label(c)}: {c.col} is NULL")
        latest = stats.column("latest")[0].as_py()
        self.latest[(t, c.col)] = latest
        seen = "no rows yet" if latest is None else f"latest {_retention.show_time(latest)}"
        return Discharged(t, label(c), f"no NULLs, {seen}; each batch checked at refresh")

    def _arrivals(self, changes: Mapping[str, pa.Table]) -> tuple[list[Discharged], dict]:
        """Check `arrives_within` on a batch: every changed row at or after
        the watermark. Returns how, and the largest times seen after it."""
        found: list[Discharged] = []
        latest: dict[tuple[str, str], object] = {}
        for t, ch in changes.items():
            for c in self.requires.get(t, []):
                if not isinstance(c, ArrivesWithin) or not ch.num_rows:
                    continue
                before: Any = self.latest.get((t, c.col))
                bad, latest[(t, c.col)] = _retention.check_batch(ch, c, before)
                if bad is not None and bad.nulls:
                    raise PreconditionError(
                        f"{bad.nulls} changed row(s) of {t} violate {label(c)}: {c.col} is "
                        "NULL; the batch was rejected, nothing was applied"
                    )
                if bad is not None:
                    raise PreconditionError(
                        f"{bad.late} changed row(s) of {t} violate {label(c)}: {c.col} before "
                        f"the watermark {_retention.show_time(bad.watermark)} (the latest "
                        f"{c.col} seen, {_retention.show_time(before)}, minus "
                        f"{show_duration(c.lateness)}); the batch was rejected, nothing was applied"
                    )
                wm = (
                    "no watermark yet"
                    if before is None
                    else (f"watermark {_retention.show_time(before - c.lateness)}")
                )
                found.append(Discharged(t, label(c), f"{ON_DATA}, {wm}"))
        return found, latest

    def retire(self) -> list[RetentionReport]:
        """Drop the final buckets from the state of every view that retires
        them (`sverify._retention`), where every sink of the view has written
        them; they stay in the sink. Returns what each such view holds."""
        out: list[RetentionReport] = []
        for v in self._views:
            spec = v.retention
            if spec is None:
                if v.retention_off is not None:
                    out.append(RetentionReport(v.name, "", 0, 0, 0, None, off=v.retention_off))
                continue
            report = RetentionReport(v.name, spec.column, 0, 0, spec.bound, None)
            out.append(report)
            if bad := [s for s in v._sinks if not getattr(s, "keeps_retired", False)]:
                report.off = (
                    f"sink {bad[0].name} may rewrite its whole table, which would drop "
                    "the retired buckets"
                )
                continue
            latest = self.latest.get((spec.table, spec.ts))
            report.watermark = spec.watermark(latest)
            cutoff = spec.cutoff(latest)
            behind = [s.name for s in v._sinks if s._written != v.serial]
            if behind:
                report.waiting = f"sink {behind[0]} writes them"
            elif cutoff is not None and (v.retired_through is None or cutoff > v.retired_through):
                report.retired = v.store.retire(v, spec.column, cutoff)
                v.retired_through = cutoff
                v._publish()
            state = arrow_of(v.state)
            report.open = _retention.buckets(state, spec.column)
            report.rows = state.num_rows
        return out

    def _check_batch(
        self,
        changes: Mapping[str, pa.Table],
        new_tables: Mapping[str, pa.Table | Native],
        facts: Mapping[str, Sequence[Fact]],
    ) -> list[Discharged]:
        """Establish the base-table preconditions on a batch alone: row
        conditions on the inserted rows (from `facts` about them where
        possible), and keys of the inserted rows against the new table."""
        found: list[Discharged] = []
        for t, ch in changes.items():
            conds = self.requires.get(t, [])
            rowwise = [c for c in conds if not isinstance(c, Unique | ArrivesWithin)]
            inserts = rows_of(positive(ch))
            if rowwise and inserts.num_rows:
                name = t + "$inserts"
                put_table(self.con, name, inserts)
                try:
                    found += discharge(
                        self.con.table(name),
                        t,
                        rowwise,
                        self.engine,
                        facts.get(t),
                        f"inserted row(s) of {t}",
                    )
                finally:
                    self.con.drop(name)
            for c in conds:
                if not isinstance(c, Unique):
                    continue
                if inserts.num_rows and (clash := duplicate_keys(new_tables[t], c.cols, inserts)):
                    raise PreconditionError(f"{clash} inserted key(s) of {t} violate {label(c)}")
                found.append(Discharged(t, label(c), ON_DATA))
        return found

    def apply(self, changes: Mapping[str, Changes]) -> None:
        """Apply changes to base tables and bring every view up to date."""
        sourced = set(changes) & set(self.sources)
        if sourced:
            raise ValueError(f"{sorted(sourced)} change through their source; call refresh()")
        self._check_changed(changes)
        self._apply({t: change_table(ch, self.con.schema(t)) for t, ch in changes.items()})
        self.retire()

    def refresh(
        self,
        *,
        audit: bool = False,
        until: Mapping[str, int] | None = None,
        retire: bool = True,
    ) -> RefreshReport:
        """Bring every source table to its latest version (or the version
        `until` names for it), and the views with it.

        Each source's change since the recorded version comes from its change
        feed (trusted, and the report says so) or, where the feed is
        unavailable, from diffing the new snapshot against the current state,
        in which case the views reading it are recomputed. The new versions
        are recorded in the same commit as the new state, so a failed refresh
        changes nothing and a retry does not apply a batch twice.

        A source whose schema changed is read in the old schema if its data
        fits (added columns are left out, widened columns cast back). If not,
        the views reading it are planned again on the new schema and
        recomputed; a view with a contract cannot be (`SchemaError`).

        With `audit`, the batch is compared with the new snapshots and every
        view with its recomputation on the new tables, before anything is
        committed (`AuditError`): a mismatch changes nothing.

        With `retire` (the default), the views that retire time buckets drop
        the final ones afterwards (`retire`); a node passes False and retires
        once its sink has written."""
        changes: dict[str, pa.Table] = {}
        facts: dict[str, list[Fact]] = {}
        versions: dict[str, int] = {}
        snapshot_facts: dict[str, list[Fact]] = {}
        recompute: set[str] = set()
        rebuild: dict[str, tuple[pa.Table, SourceRefresh]] = {}
        whole: dict[str, pa.Table | Native] = {}
        report: list[SourceRefresh] = []
        for t, src in self.sources.items():
            start = self.versions[t]
            pin = (until or {}).get(t)
            batch = src.changes(start) if pin is None else src.changes(start, pin)
            if batch.end == start:
                if audit and hasattr(src, "_reread"):
                    # A source that reads its table itself may have missed
                    # rows its batches assume away: read it again in full.
                    current = _as_arrow(self.con.get(t))
                    _audit_source(t, current, src._reread(start), start, start)
                report.append(SourceRefresh(t, start, start, "unchanged"))
                continue
            schema = self.con.schema(t)
            evolved = SchemaChange.of(schema, batch.schema or schema)
            note = schema_note = ""
            if evolved:
                try:
                    if not evolved.compatible:
                        raise ValueError("the old schema cannot hold the new data")
                    batch = _conform_batch(batch, schema)
                    note = f"; schema: {evolved}, read in the old schema"
                    schema_note = str(evolved)
                except (ValueError, pa.ArrowException) as e:
                    snap = batch.snapshot
                    if snap is None or batch.changes is not None:
                        snap = src.snapshot(batch.end).table
                    entry = SourceRefresh(
                        t,
                        start,
                        batch.end,
                        "recomputed",
                        f"schema: {evolved} ({first_line(e)})",
                        schema=str(evolved),
                    )
                    rebuild[t] = (snap, entry)
                    versions[t] = batch.end
                    snapshot_facts[t] = batch.snapshot_facts
                    report.append(entry)
                    continue
            current = self.con.get(t)
            scanned = isinstance(current, Scan)
            # A table held as files stays so: at `end`, it is the files of `end`.
            native = self._native(src, batch.end) if scanned and not evolved else None
            gone = scanned and not current.readable()
            if batch.changes is None or gone:
                new = batch.snapshot if batch.changes is None else None
                if new is None:
                    new = src.snapshot(batch.end).table
                    new = _conform(new, schema) if evolved else new
                recompute.add(t)
                # The diff's inserts are rows of the new snapshot.
                facts[t] = batch.snapshot_facts
                mode = "recomputed"
                if gone:
                    # The files of the version the pipeline holds were
                    # removed (vacuumed): the views reading it are recomputed
                    # on the new snapshot, all of whose rows are inserts.
                    ch = weighted(new, 1)
                    whole[t] = new if native is None else native.scan
                    reason = f"{batch.fallback}; " if batch.fallback else ""
                    detail = f"{reason}the files of v{start} are gone; Δ = snapshot v{batch.end}"
                else:
                    ch = snapshot_diff(_as_arrow(current), new)
                    if native is not None:
                        whole[t] = native.scan
                    detail = f"{batch.fallback}; Δ = snapshot v{batch.end} − state"
            else:
                ch = consolidated(change_table(batch.changes, schema))
                facts[t] = batch.facts
                mode, detail = batch.kind, batch.trusted
                if native is not None and not audit:
                    if (lost := missing(current, ch)).num_rows:
                        (row,) = arrow_rows(rows_of(lost.slice(0, 1)))
                        raise ValueError(f"cannot delete {row!r} from {t}: no such row")
                    whole[t] = native.scan
            if audit and batch.changes is not None and not gone:
                got = _apply_change(_as_arrow(current), ch, t)
                # A source that reads its table itself reads it again in full.
                reread = getattr(src, "_reread", None)
                want = reread(batch.end) if reread else src.snapshot(batch.end).table
                if evolved:
                    want = _conform(want, schema)
                _audit_source(t, got, want, start, batch.end)
            changes[t], versions[t] = ch, batch.end
            snapshot_facts[t] = batch.snapshot_facts
            report.append(
                SourceRefresh(
                    t,
                    start,
                    batch.end,
                    mode,
                    detail + note,
                    inserted_count(ch),
                    deleted_count(ch),
                    schema_note,
                )
            )
        replan = self._reading(set(rebuild))
        if bad := [v.name for v in replan if v.contracted]:
            raise SchemaError(
                f"the schema of {', '.join(sorted(rebuild))} changed incompatibly; views "
                f"{bad} have contracts proved against the old schema: build the pipeline again"
            )
        incremental = {t: n for t, n in versions.items() if t not in rebuild}
        pending = self._prepare(
            changes,
            facts=facts,
            recompute=recompute,
            versions=incremental,
            whole=whole,
            audit=audit,
        )
        if audit:
            self._audit(pending)
        backup = self._backup() if rebuild else None
        self._commit(pending)
        if rebuild:
            assert backup is not None
            try:
                for t, (snap, _) in rebuild.items():
                    put_table(self.con, t, snap)
                changed = set(rebuild)
                for v in replan:
                    v._replan(changed)
                    changed.add(v.name)
            except BaseException:
                self._restore(backup)
                raise
            for t, (snap, entry) in rebuild.items():
                names = [v.name for v in self._reading({t})]
                entry.detail += (
                    f"; views planned again and recomputed: {', '.join(names) or 'none'}"
                )
                entry.inserts = snap.num_rows
                self.versions[t] = versions[t]
        for t, fs in snapshot_facts.items():
            register_facts(self.con, t, fs)
        return RefreshReport(
            report,
            pending.found,
            {v.name: v.versions for v in self._views},
            audited=audit,
            retention=self.retire() if retire else [],
            postconditions=pending.checked,
        )

    def _reading(self, tables: set[str]) -> list[IncrementalView]:
        """The views that read any of `tables`, directly or through other
        views, in pipeline order."""
        out: list[IncrementalView] = []
        seen = set(tables)
        for v in self._views:
            if seen & set(v.tables):
                out.append(v)
                seen.add(v.name)
        return out

    def _backup(self) -> tuple:
        """What a refresh may change: tables, views and versions."""
        tables = {t: self.con.get(t) for t in [*self.sources, *self.views]}
        views = {}
        for v in self._views:
            saved = dict(v.__dict__)
            saved["_log"] = list(v._log)
            if isinstance(v.state, Resident):
                # A refresh updates the state in place: keep a copy.
                saved["state"] = DuckDBStore().copy(v.state)
                tables[v.name] = v.store.expanded(saved["state"])
            views[v.name] = saved
        return tables, views, dict(self.versions), dict(self.latest)

    def _restore(self, backup: tuple) -> None:
        tables, views, versions, latest = backup
        for t, table in tables.items():
            if self.con.get(t) is not table:
                put_table(self.con, t, table)
        for v in self._views:
            state = views[v.name]
            v.__dict__.clear()
            v.__dict__.update(state)
        self.versions, self.latest = versions, latest

    def _audit(self, pending: _Commit) -> None:
        """Compare every view's new state with its recomputation on the new
        tables, before the commit."""
        for v in self._views:
            want = v._kept(v._result_on(pending.new_tables).cast(v.schema))
            state = pending.states.get(v.name, v.state)
            if arrow_of(v._merge(weighted(want, 1), v.store.negated(state))).num_rows:
                raise AuditError(
                    f"view {v.name} differs from its recomputation; nothing was applied"
                )

    def _check_changed(self, changes: Mapping[str, object]) -> None:
        """Raise unless every table in `changes` is a base table a view reads."""
        bad = set(changes) & set(self.views)
        if bad:
            raise ValueError(f"views change only through their inputs: {sorted(bad)}")
        read = {t for v in self._views for t in v.tables}
        unknown = set(changes) - read
        if unknown:
            raise ValueError(f"no view reads {sorted(unknown)}")

    def _apply(
        self,
        changes: Mapping[str, pa.Table],
        *,
        facts: Mapping[str, Sequence[Fact]] | None = None,
        recompute: set[str] | None = None,
        versions: Mapping[str, int] | None = None,
    ) -> list[Discharged]:
        pending = self._prepare(changes, facts=facts, recompute=recompute, versions=versions)
        self._commit(pending)
        return pending.found

    def _prepare(
        self,
        changes: Mapping[str, pa.Table],
        *,
        facts: Mapping[str, Sequence[Fact]] | None = None,
        recompute: set[str] | None = None,
        versions: Mapping[str, int] | None = None,
        whole: Mapping[str, pa.Table | Native] | None = None,
        audit: bool = False,
    ) -> _Commit:
        """Compute the new state of every table and view after `changes`
        (weighted tables), without replacing anything. Views reading a table
        in `recompute` (directly or through other views) are recomputed and
        diffed; `versions` are recorded with the commit. A table in `whole`
        (its source's snapshot at the new version) becomes that table; the
        caller checked that the change's deletes exist.

        A view whose state DuckDB holds is updated in place at the commit,
        at the cost of its change (`DuckDBStore.apply`), unless its new
        contents are read before then: by a view recomputed on the new
        tables, or by the `audit`. Then its new state is a full merge."""
        self._check_changed(changes)
        # New base tables first: this also checks that every delete exists.
        new_tables: dict[str, pa.Table | Native] = {}
        for t, ch in changes.items():
            given = (whole or {}).get(t)
            if given is None:
                given = _apply_change(_as_arrow(self.con.get(t)), ch, t)
            new_tables[t] = given
        arrived, latest = self._arrivals(changes)
        found = arrived + self._check_batch(changes, new_tables, facts or {})
        deltas: dict[str, pa.Table] = {t: consolidated(ch) for t, ch in changes.items()}
        stale = set(recompute or ())
        checked: list[Discharged] = []
        states: dict[str, State] = {}
        in_place: dict[str, pa.Table] = {}
        # The tables whose new contents a recomputed view reads.
        rerun = set(stale)
        read_new: set[str] = set()
        for v in self._views:
            if v.fallback is not None or rerun & set(v.tables):
                rerun.add(v.name)
                read_new.update(v.tables)
        # Views read the *old* tables (and their inputs' changes), so nothing
        # is replaced until every view has its change.
        for v in self._views:
            if not any(t in deltas and deltas[t].num_rows for t in v.tables):
                continue
            rerun = v.fallback is not None or any(t in stale for t in v.tables)
            if rerun:
                stale.add(v.name)
            delta = v._diff(new_tables) if rerun else v._delta(deltas)
            deltas[v.name] = delta
            # A checked key is checked on the whole new state.
            keyed = any(isinstance(c, Unique) for c in v.checked)
            if isinstance(v.state, Resident) and not audit and v.name not in read_new and not keyed:
                # Only the state rows the change touches, merged with it.
                merged = v._merge(matching(v.state, delta), delta)
                if v.store.has_negative(merged):
                    raise ValueError(f"changes delete rows that are not in the inputs of {v.name}")
                checked += v._check_change(delta, None)
                in_place[v.name] = arrow_of(merged)
                continue
            merged = v._merge(v.state, delta, keep=v.store.keep)
            if v.store.has_negative(merged):
                raise ValueError(f"changes delete rows that are not in the inputs of {v.name}")
            new_tables[v.name] = v.store.expanded(merged)
            checked += v._check_change(delta, new_tables[v.name])
            states[v.name] = merged
        changed = {name: deltas[name] for name in [*states, *in_place]}
        return _Commit(
            changes,
            new_tables,
            dict(versions or {}),
            states,
            found,
            in_place,
            changed,
            latest=latest,
            checked=checked,
        )

    def _commit(self, pending: _Commit) -> None:
        """Replace the tables, views and versions with their new state."""
        views = self.views
        if pending.in_place:
            # One transaction: every view's state changes, or none does.
            updates = []
            for name, merged in pending.in_place.items():
                state = views[name].state
                assert isinstance(state, Resident)
                updates.append((state, pending.deltas[name], merged))
            DuckDBStore().apply(updates)
            for name in pending.in_place:
                views[name]._publish()
        for t in pending.changes:
            put_table(self.con, t, pending.new_tables[t])
        self.versions.update(pending.versions)
        self.latest.update(pending.latest)
        for name, state in pending.states.items():
            views[name].state = state
            put_table(self.con, name, pending.new_tables[name])
        for name, delta in pending.deltas.items():
            views[name]._record(delta)


@dataclass
class _Commit:
    """A pipeline's state after a batch, computed but not yet in place."""

    changes: Mapping[str, pa.Table]
    new_tables: dict[str, pa.Table | Native]
    versions: dict[str, int]
    states: dict[str, State]
    """The new contents of each view that changed, as weighted tables."""
    found: list[Discharged]
    in_place: dict[str, pa.Table] = field(default_factory=dict)
    """Views whose state DuckDB updates in place: the state rows the change
    touches, merged with it."""
    deltas: dict[str, pa.Table] = field(default_factory=dict)
    """Each changed view's change, as a weighted table."""
    latest: dict[tuple[str, str], object] = field(default_factory=dict)
    """The largest time seen after the batch, per `arrives_within`."""
    checked: list[Discharged] = field(default_factory=list)
    """The views' runtime-checked postconditions, checked on the batch."""


def _audit_source(t: str, got: pa.Table, want: pa.Table, start: int, end: int) -> None:
    """Raise unless `got` (the state after the change) has the rows of
    `want` (the source's snapshot at `end`)."""
    if snapshot_diff(got, want).num_rows:
        if start == end:
            raise AuditError(
                f"{t}@v{start} differs from the table read again in full: its batches missed "
                "rows; nothing was applied"
            )
        raise AuditError(
            f"{t}: the change feed v{start}→v{end} does not turn the state into snapshot "
            f"v{end}; nothing was applied"
        )


def _conform_batch(batch: SourceBatch, schema: pa.Schema) -> SourceBatch:
    """A batch read in the new schema, in the old `schema` (`_conform`); facts
    about columns the old schema lacks are left out."""
    new = batch.schema or schema
    changes = batch.changes
    if changes is not None:
        changes = Changes(
            inserts=_conform(_as_table(changes.inserts, new), schema),
            deletes=_conform(_as_table(changes.deletes, new), schema),
        )
    return replace(
        batch,
        changes=changes,
        snapshot=None if batch.snapshot is None else _conform(batch.snapshot, schema),
        facts=_facts_within(batch.facts, schema.names),
        snapshot_facts=_facts_within(batch.snapshot_facts, schema.names),
        schema=schema,
    )


def first_line(e: BaseException) -> str:
    text = str(e).strip().splitlines()
    return f"{type(e).__name__}: {text[0] if text else ''}"


def _as_arrow(table: pa.Table | Native) -> pa.Table:
    return arrow_of(table)


def _apply_change(current: pa.Table, change: pa.Table, t: str) -> pa.Table:
    """`current` with the rows of `change` (a weighted table) deleted (one
    occurrence each) and inserted. Raises `ValueError`, naming a row, if a
    delete is not in `current`, even where the change also inserts it."""
    deletes = negative(change)
    kept = consolidated(weighted(current, 1), deletes)
    missing = negative(kept)
    if missing.num_rows:
        (row,) = arrow_rows(rows_of(missing.slice(0, 1)))
        raise ValueError(f"cannot delete {row!r} from {t}: no such row")
    inserts = positive(change)
    if not deletes.num_rows:
        return concat([current, expanded(inserts)])
    return expanded(consolidated(kept, inserts))
