"""What Delta and Iceberg have in common: file statistics as facts,
contracts as SQL, and the record a sink stores with each commit.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from __future__ import annotations

import copy
import json
import math
import re
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Any, Literal, Self

import duckdb
import ibis
import pyarrow as pa
import sqlglot as sg

from sverify import _deprecated
from sverify._cursor import _TAG, UNRECORDED, cursor_json, cursor_value  # noqa: F401  (re-exported)
from sverify._pipe import Pipeable
from sverify._unsupported import SverifyError
from sverify.contracts import Condition, Fact, TableCondition, Unique, _prove_from, resolve
from sverify.incremental import IncrementalView, Snapshot, SourceBatch, plan_digest


@dataclass(frozen=True)
class ColumnStats:
    """One file's statistics for one column; None is unknown (`ColStats` in
    `SubstraitLean/TableFormat.lean`)."""

    lo: Any
    hi: Any
    nulls: int | None
    rows: int | None = None
    """The file's row count, to tell a file of NULLs."""
    nans: int | None = None
    """NaN count of a double column (Iceberg); writers leave NaN out of the
    minimum and maximum."""


def _bounded(t: pa.DataType) -> bool:
    """Types whose minimum and maximum statistics become bounds: integers,
    doubles, dates and microsecond timestamps without a time zone.

    Not strings (writers truncate their bounds, and the checker has no string
    order: #17), decimals (not modelled: #27), timestamps with a time zone
    (not modelled: #20), nor other units and floats."""
    return (
        pa.types.is_integer(t)
        or pa.types.is_float64(t)
        or pa.types.is_date32(t)
        or (pa.types.is_timestamp(t) and t.unit == "us" and t.tz is None)
    )


def q(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def _literal(t: pa.DataType, v: Any) -> str | None:
    """`v` as a SQL literal of type `t`, or None for a double that is not
    finite (no bound)."""
    if pa.types.is_integer(t):
        return str(int(v))
    if pa.types.is_floating(t):
        return repr(float(v)) if math.isfinite(v) else None
    if pa.types.is_date32(t):
        return f"DATE '{v.isoformat()}'"
    return f"TIMESTAMP '{v.isoformat(sep=' ', timespec='microseconds')}'"


def stats_facts(
    files: Sequence[Mapping[str, ColumnStats]],
    schema: pa.Schema,
    source: str,
    *,
    hi_slack: timedelta = timedelta(0),
) -> list[Fact]:
    """Facts about every row of a table made of `files`, from the join of
    the files' statistics (`stats_table` in `SubstraitLean/TableFormat.lean`):
    a column without NULLs is NOT NULL; a bounded column lies between the
    least minimum and the greatest maximum, or is NULL if some file has NULLs
    (`stats_fact`); a column of files of NULLs is NULL (`stats_all_null`).
    A file missing a NULL count makes the column unknown, one missing a
    minimum or maximum drops that side. A double's maximum is used only if
    every file counts no NaN (NaN is above every bound). `hi_slack` widens
    timestamp maxima that the format truncates."""
    if not files:
        return []
    out = []
    for f in schema:
        stats = [file.get(f.name) for file in files]
        if any(s is None or s.nulls is None for s in stats):
            continue
        known = [s for s in stats if s is not None]
        nulls = sum(s.nulls or 0 for s in known)
        col = q(f.name)
        # A file of NULLs bounds nothing (`ColStats.aval`).
        valued = [s for s in known if s.rows is None or s.nulls != s.rows]
        if not valued:
            out.append(Fact(f"{col} IS NULL", source))
            continue
        sides = []
        if _bounded(f.type):
            sides = _sides(f.type, valued, hi_slack)
        bounds = [f"{col} {op} {v}" for op, v in sides]
        if nulls == 0:
            out.append(Fact(" AND ".join([f"{col} IS NOT NULL", *bounds]), source))
        elif bounds:
            out.append(Fact(f"{col} IS NULL OR ({' AND '.join(bounds)})", source))
    return out


def rows_fact(files: Sequence[Mapping[str, ColumnStats]], source: str) -> list[Fact]:
    """A cap on the rows of a table made of `files`: the sum of their record
    counts, when every file has one (#219). A file's count covers its deleted
    rows too, so it bounds the rows a scan or a filter reads."""
    counts = [next(iter(f.values())).rows if f else None for f in files]
    if any(n is None for n in counts):
        return []
    return [Fact("TRUE", source, rows=sum(n for n in counts if n is not None))]


def _sides(t: pa.DataType, files: Sequence[ColumnStats], hi_slack: timedelta) -> list[tuple]:
    """The bounds of the join of `files`, as (operator, literal) pairs."""
    double = pa.types.is_floating(t)

    def usable(v: Any) -> bool:
        return v is not None and not (double and math.isnan(v))

    out = []
    if all(usable(s.lo) for s in files):
        lo = _literal(t, min(s.lo for s in files))
        if lo is not None:
            out.append((">=", lo))
    if all(usable(s.hi) for s in files) and not (double and any(s.nans != 0 for s in files)):
        hi = max(s.hi for s in files)
        if isinstance(hi, datetime):
            hi += hi_slack
        lit = _literal(t, hi)
        if lit is not None:
            out.append(("<=", lit))
    return out


FILTER = "source filter"


def not_true(where: str) -> str:
    """SQL that is TRUE exactly where `where` is not (FALSE or NULL)."""
    return f"CASE WHEN ({where}) THEN FALSE ELSE TRUE END"


def _is_string(t: pa.DataType) -> bool:
    return pa.types.is_string(t) or pa.types.is_large_string(t)


def _str_literal(e: sg.exp.Expr) -> str | None:
    return e.this if isinstance(e, sg.exp.Literal) and e.is_string else None


def str_may_true(where: sg.exp.Expr, bounds: Mapping[str, tuple[Any, Any]]) -> bool:
    """Whether `where` may be TRUE on a row of a file whose string columns
    lie within `bounds` (column -> (minimum, maximum), either None), where
    either bound may be cut to a prefix (`StrStats.mayTrue` in
    `SubstraitLean/Pruning.lean`, proved by `strPrune_sound`): every value
    is at least the minimum, and every value cut to the maximum's length is
    at most the maximum. `AND` needs both sides, `OR` and `IN` one, and a
    comparison of a string column with a string literal its bounds; anything
    else may be TRUE. Python compares strings by code point, as Lean and the
    Parquet statistics do."""
    e = where.unnest() if isinstance(where, sg.exp.Paren) else where
    if isinstance(e, sg.exp.And):
        return str_may_true(e.left, bounds) and str_may_true(e.right, bounds)
    if isinstance(e, sg.exp.Or):
        return str_may_true(e.left, bounds) or str_may_true(e.right, bounds)
    if isinstance(e, sg.exp.In) and not e.args.get("query"):
        return any(
            str_may_true(sg.exp.EQ(this=e.this, expression=k), bounds) for k in e.expressions
        )
    ops: dict[type, str] = {
        sg.exp.EQ: "=",
        sg.exp.LT: "<",
        sg.exp.LTE: "<=",
        sg.exp.GT: ">",
        sg.exp.GTE: ">=",
    }
    op = ops.get(type(e))
    if op is None or not isinstance(e, sg.exp.Binary):
        return True
    col, k = e.left, _str_literal(e.right)
    if k is None:  # `k < col` is `col > k`
        col, k = e.right, _str_literal(e.left)
        op = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}.get(op, op)
    if k is None or not isinstance(col, sg.exp.Column) or col.name not in bounds:
        return True
    lo, hi = bounds[col.name]

    def may_ge() -> bool:  # some x >= k (`StrStats.mayGe`)
        return hi is None or k[: len(hi)] <= hi

    def may_le() -> bool:  # some x <= k (`StrStats.mayLe`)
        return lo is None or lo <= k

    if op == "=":
        return may_le() and may_ge()
    if op == "<":
        return lo is None or lo < k  # `StrStats.mayLt`
    if op == "<=":
        return may_le()
    return may_ge()  # `>` and `>=`


def _str_bounds(stats: Mapping[str, ColumnStats], schema: pa.Schema) -> dict[str, tuple]:
    """The string bounds of a file's statistics, by column."""
    out = {}
    for f in schema:
        s = stats.get(f.name)
        if s is None or not _is_string(f.type):
            continue
        lo = s.lo if isinstance(s.lo, str) else None
        hi = s.hi if isinstance(s.hi, str) else None
        if lo is not None or hi is not None:
            out[f.name] = (lo, hi)
    return out


def prune(
    files: Mapping[str, Mapping[str, ColumnStats]],
    schema: pa.Schema,
    where: str,
    *,
    hi_slack: timedelta = timedelta(0),
) -> set[str]:
    """The files that may hold rows passing `where`. A file is skipped only
    if its string bounds rule `where` out (`str_may_true`, `strStats_prune`
    in `SubstraitLean/Pruning.lean`), or if Lean proves from the facts its
    statistics give that `where` is not TRUE on any of its rows
    (`contract_sound`, `stats_prune`). Then filtering the table reads the
    same rows as filtering the other files (`prune_sound` in
    `SubstraitLean/TableFormat.lean`), and every plan linear in the source
    gives the same result (`Rel.eval_pruned`)."""
    table = ibis.table(ibis.Schema.from_pyarrow(schema), name="file")
    try:
        tree: sg.exp.Expr | None = sg.parse_one(where, read="duckdb")
    except sg.errors.ParseError:
        tree = None
    keep = set()
    for path, stats in files.items():
        if tree is not None and not str_may_true(tree, _str_bounds(stats, schema)):
            continue
        facts = [f.condition for f in stats_facts([stats], schema, "file", hi_slack=hi_slack)]
        if not facts or not _prove_from(table, facts, [not_true(where)]):
            keep.add(path)
    return keep


def filter_rows(table: pa.Table, where: str) -> pa.Table:
    """The rows of `table` on which `where` is TRUE (DuckDB)."""
    con = duckdb.connect()
    con.register("t", table)
    return con.sql(f"SELECT * FROM t WHERE {where}").fetch_arrow_table().cast(table.schema)


def condition_sql(cond: Condition, schema: ibis.Schema) -> str | None:
    """A row condition as a standalone SQL expression over the columns, or
    None if it has none (`unique`, `references`)."""
    if isinstance(cond, TableCondition):
        return None
    if isinstance(cond, str):
        return cond
    t = ibis.table(schema, name="t")
    sql = ibis.to_sql(t.select(c=resolve(cond, t)), dialect="duckdb")
    select = sg.parse_one(sql, read="duckdb")
    expr = select.expressions[0].this  # type: ignore[attr-defined]
    for col in expr.find_all(sg.exp.Column):
        col.set("table", None)
    for ident in expr.find_all(sg.exp.Identifier):
        if re.fullmatch(r"[a-z_][a-z0-9_]*", ident.name):
            ident.set("quoted", False)
    return expr.sql(dialect="postgres")


def not_null_column(sql: str) -> str | None:
    """The column of a condition that says exactly `col IS NOT NULL`."""
    e = sg.parse_one(sql, read="postgres")
    if isinstance(e, sg.exp.Paren):
        e = e.this
    if isinstance(e, sg.exp.Not):
        e, negated = e.this, True
    else:
        negated = bool(e.args.get("negate"))
    if (
        negated
        and isinstance(e, sg.exp.Is)
        and isinstance(e.this, sg.exp.Column)
        and isinstance(e.expression, sg.exp.Null)
    ):
        return e.this.name
    return None


#: The version of the sink's contract record's format (`Contract.format`).
#: Format 2 (1.0) names the node `node`; format 1 called it `view`.
CONTRACT_FORMAT = 2


@dataclass
class Contract:
    """What a sink records with each commit: which plan produced the data,
    from which source versions, and what it proved about every row.

    `DeltaSource.contract()` and `IcebergSource.contract()` read it back.

    Attributes:
        node: The stored node's name.
        sources: The version of every source table the state was computed
            from.
        not_null: Columns the node proves NOT NULL: stated in `ensures`
            (`_.col.notnull()`), or shown never NULL by its proved report
            (`Report.not_null`).
        unique: Column sets the node proves unique.
        cursors: The cursor of every source that can restore its table from
            one (`Source.restore`), at its version in `sources`.
        table_ids: The id of every source table that has one (a Delta
            table's `metaData.id`), at its version in `sources`.
    """

    node: str
    plan: str
    """sha256 of the plan as Lean wrote it."""
    sources: dict[str, int]
    epoch: int
    """Sum of the source versions: grows with every refresh that changes
    anything, so it identifies the commit for exactly-once writes."""
    not_null: list[str]
    checks: dict[str, str]
    """Constraint name -> SQL."""
    unique: list[list[str]]
    digests: dict[str, str] = field(default_factory=dict)
    """Content digest of each static table (`StaticSource`) the node read,
    and of each source that cannot restore (`Source` without `restore`), at
    its version in `sources`: their versions do not tell contents apart
    across processes (#889, #965)."""
    cursors: dict[str, Any] = field(default_factory=dict)
    """The cursor of each source the node read whose cursors last across
    processes (`sverify.io.Source.restore`), at its version in `sources`, as
    `cursor_json` encodes it."""
    table_ids: dict[str, str] = field(default_factory=dict)
    """The id of each source table that has one (`DeltaSource`: the table's
    `metaData.id`), at its version in `sources`. A table dropped and created
    again at the same location has a new id, and versions that start over:
    a state recorded from the old table is not one of the new table's."""
    format: int = CONTRACT_FORMAT
    """The version of the record's format (`CONTRACT_FORMAT`,
    `sverify/schemas/sink-contract.schema.json`). It changes only with a
    record a reader of the previous format cannot read, which 1.x never
    writes (`docs/stability.md`). A record without it was written before
    0.5 and reads as format 1; format 1 named the node `view`."""

    def to_json(self) -> str:
        """The contract as JSON, as sinks store it.

        Returns:
            A JSON object with the contract's fields, keys sorted, in the
            format of `sverify/schemas/sink-contract.schema.json`.
        """
        return json.dumps(self.__dict__, sort_keys=True)

    @staticmethod
    def from_json(text: str) -> Contract:
        """A contract from what `to_json` wrote, by this version of sverify
        or an earlier one. Keys this version does not know, which a later
        1.x version may add, are left out.

        Args:
            text: The JSON `to_json` wrote.

        Returns:
            The contract.

        Raises:
            ValueError: The record's `format` is newer than this version
                reads. A record of an earlier format reads as this one.
        """
        data = json.loads(text)
        fmt = data.get("format", 1)
        if not isinstance(fmt, int) or fmt > CONTRACT_FORMAT:
            raise ValueError(
                f"the sink's contract record has format {fmt!r}, and this version of "
                f"sverify reads format {CONTRACT_FORMAT} or older: upgrade sverify"
            )
        if fmt < 2 and "view" in data:
            data = {**data, "node": data["view"]}
        known = Contract.__dataclass_fields__
        return Contract(**{k: v for k, v in data.items() if k in known and k != "format"})


class ConcurrentWriteError(SverifyError, RuntimeError):
    """Another writer committed to a sink between the moment this refresh
    read what the sink holds (`Sink.committed`) and its own commit: two
    processes refreshing the same sink (#517). This refresh's write was not
    committed, and the sink keeps the other writer's state; the next refresh
    replaces it with this process's state, or skips if the sink already holds
    it."""

    code = "concurrent_write"


@dataclass
class SinkWrite:
    """What storing a node's state did, in any sink.

    `mode` is how: `created` the table, `overwrite` it, `merge` the change
    (Delta), `append` the new rows or write the change `row_level` (Iceberg),
    `update` it with the change (a sink of your own), or `skipped` a state
    the table already holds. `version` is the table's version afterwards;
    `constraints` are the CHECK constraints the table has for the node's
    guarantees (Delta). `print` it for a one-line summary. A refresh's
    report lists the writes it made.

    Attributes:
        mode: `"created"` (the first write made the table), `"overwrite"`
            (the table's rows were replaced), `"merge"` (the change in one
            MERGE commit, Delta), `"append"` (the change only added rows,
            Iceberg), `"row_level"` (position deletes and new rows in one
            snapshot, Iceberg), `"update"` (the change, written by a sink of
            your own) or `"skipped"` (the table already has this state's
            epoch).
        version: The table's version afterwards (Delta), its snapshot
            sequence number (Iceberg), or None if the sink has no versions.
        contract: What the commit recorded.
        inserted: Rows written.
        deleted: Rows deleted.
        constraints: The table's CHECK constraints from the node's
            guarantees, by name (Delta; empty for Iceberg).
    """

    mode: Literal["created", "overwrite", "merge", "append", "row_level", "update", "skipped"]
    version: int | None
    contract: Contract
    inserted: int = 0
    deleted: int = 0
    constraints: dict[str, str] = field(default_factory=dict)

    def __str__(self) -> str:
        src = ", ".join(f"{t}@v{n}" for t, n in self.contract.sources.items())
        if self.mode == "skipped":
            at = "" if self.version is None else f" (v{self.version})"
            return f"{self.contract.node} from {src}: already committed{at}"
        at = "" if self.version is None else f" v{self.version}"
        return (
            f"{self.contract.node} from {src}: {self.mode.replace('_', ' ')}{at}, "
            f"{self.inserted} row(s) written, {self.deleted} deleted"
        )


def view_contract_record(view: IncrementalView) -> Contract:
    versions = view.versions
    bases = _base_tables(view)
    missing = sorted(bases - set(versions))
    if missing:
        raise ValueError(
            f"view {view.name} reads tables without a source ({missing}): a sink needs "
            "source versions to write exactly once; read a table that is not in a table "
            "format through sverify.io.StaticSource(table, name=..., version=...)"
        )
    schema = ibis.Schema.from_pyarrow(view.schema)
    not_null: list[str] = []
    checks: dict[str, str] = {}
    unique: list[list[str]] = []
    for c in view.guarantees:
        if isinstance(c, Unique):
            unique.append(list(c.cols))
            continue
        sql = condition_sql(c, schema)
        if sql is None:
            continue
        col = not_null_column(sql)
        if col is not None:
            not_null.append(col)
        else:
            checks[f"sverify_{len(checks) + 1}"] = sql
    names = set(view.schema.names)
    not_null += [c for c in view.not_null if c in names and c not in not_null]
    return Contract(
        node=view.name,
        plan=plan_digest(view.plan),
        sources=versions,
        epoch=sum(versions.values()),
        not_null=not_null,
        checks=checks,
        unique=unique,
        digests=view.pipeline.digests(view.name),
        cursors=_cursors(view, versions),
        table_ids=_table_ids(view, versions),
    )


def _cursors(view: IncrementalView, versions: Mapping[str, int]) -> dict[str, Any]:
    """The JSON form of the cursor of every source of `view` whose cursors
    last (`sverify.io.Source._cursor_at`), at the version `view` is at."""
    out = {}
    for t, n in versions.items():
        at = getattr(view.pipeline.sources.get(t), "_cursor_at", None)
        if at is None:
            continue
        value = at(n)
        if value is not UNRECORDED and (data := cursor_json(value)) is not UNRECORDED:
            out[t] = data
    return out


def _table_ids(view: IncrementalView, versions: Mapping[str, int]) -> dict[str, str]:
    """The id of every source table of `view` that has one
    (`_TableSource._table_id`), at the version `view` is at."""
    out: dict[str, str] = {}
    for t, n in versions.items():
        src = view.pipeline.sources.get(t)
        if isinstance(src, _TableSource) and (table_id := src._table_id(n)) is not None:
            out[t] = table_id
    return out


@dataclass(frozen=True)
class LastRecord[C, R]:
    """The newest commit of a table that carries a sverify record, as
    `last_record` finds it walking back from the latest."""

    record: R | None
    """What that commit recorded, or None if no commit walked has one."""
    walked: list[C]
    """The commits walked, newest first, ending with that one."""
    kept: bool
    """Whether every commit newer than it keeps what it recorded."""


def last_record[C, R](
    commits: Iterable[C],
    record: Callable[[C], R | None],
    keeps: Callable[[C], bool],
    *,
    stop: bool = False,
) -> LastRecord[C, R]:
    """Walk `commits`, newest first, back to the first one whose `record`
    is not None, noting whether every commit before it `keeps` the state it
    recorded (changes no rows: a compaction, a vacuum, a property). With
    `stop`, give up at the first commit that does not.

    The one walk of a sink's history: Delta's commit log (`DeltaSource`,
    `DeltaSink.maintain`) and Iceberg's snapshot ancestry (`IcebergSource`,
    `IcebergSink`)."""
    walked: list[C] = []
    kept = True
    for c in commits:
        walked.append(c)
        if (r := record(c)) is not None:
            return LastRecord(r, walked, kept)
        if not keeps(c):
            kept = False
            if stop:
                break
    return LastRecord(None, walked, kept)


def other_tables(committed: Contract, contract: Contract) -> list[str]:
    """The sources of `contract` that are not the tables `committed` was
    computed from: their table id changed, or their version went down (a
    table's versions only grow, so a lower one is another table, dropped
    and created again). Then the sink's rows are not a state of these
    inputs, whatever the epochs say (#516)."""
    out = []
    for t, n in contract.sources.items():
        was, now = committed.table_ids.get(t), contract.table_ids.get(t)
        if (was is not None and now is not None and was != now) or n < committed.sources.get(t, n):
            out.append(t)
    return sorted(out)


def check_same_state(uri: str, committed: Contract | None, contract: Contract) -> None:
    """A sink skips a state whose epoch it has committed; that is only right
    if the static tables were the same then."""
    if committed is not None and committed.epoch == contract.epoch:
        changed = sorted(
            t
            for t in committed.digests.keys() | contract.digests.keys()
            if committed.digests.get(t) != contract.digests.get(t)
        )
        if changed:
            raise ValueError(
                f"{uri} has a commit at epoch {contract.epoch} from other contents of "
                f"{changed}: give the changed static table a new version"
            )


def _base_tables(view: IncrementalView) -> set[str]:
    views = view.pipeline.views
    out: set[str] = set()
    for t in view.tables:
        out |= _base_tables(views[t]) if t in views else {t}
    return out


def sink_schema(view: IncrementalView, not_null: Iterable[str]) -> pa.Schema:
    keep = set(not_null)
    return pa.schema([f.with_nullable(f.name not in keep) for f in view.schema])


IDS_KEPT = 64
"""Versions whose table id a `_TableSource` remembers."""


class _TableSource(Pipeable, ABC):
    """What `DeltaSource` and `IcebergSource` share: the restriction to a
    predicate (`where`, `_restricted`), the files it prunes (`_keep`), the
    facts of the files read (`_facts_of`), the table id at each version read
    (`_table_id`, #516, #533), and the snapshot a refresh reads when no
    change is available (`_full`).

    Subclasses implement `VersionedSource` and `_id_at`, and set `_hi_slack`
    where the format's upper bounds are truncated."""

    _hi_slack = timedelta(0)
    """How far a value may lie above a file's upper bound (`stats_facts`)."""

    def __init__(self, name: str, where: str | None):
        self.name, self.where = name, where
        self.implied: str | None = None
        """The predicate a node's view implies on this table, if the source
        reads only the rows that pass it (`_restricted`)."""
        self.skipped: list[str] = []
        """The files the last snapshot did not read."""
        self._kept: dict[tuple[str, str], bool] = {}
        # Whether `where` may hold in a file, by path and schema: files are
        # immutable, so their statistics are proved about once.
        self._ids: dict[int, str] = {}
        # The table id at each version read: a table dropped and created
        # again at the same place has a new one (#516, #533).

    @abstractmethod
    def schema(self) -> pa.Schema: ...

    @abstractmethod
    def latest(self) -> int: ...

    @abstractmethod
    def snapshot(self, version: int | None = None) -> Snapshot: ...

    @abstractmethod
    def changes(self, since: int, until: int | None = None) -> SourceBatch: ...

    @abstractmethod
    def _id_at(self, version: int | None) -> str | None:
        """The id of the table at `version` (default: the latest), read from
        the table; may raise if there is no table at `version`."""

    def _seen(self, version: int, table_id: str) -> None:
        """Remember the id of the table read at `version`."""
        if len(self._ids) >= IDS_KEPT:
            del self._ids[min(self._ids)]
        self._ids[version] = table_id

    def _table_id(self, version: int | None = None) -> str | None:
        """The id of the table read at `version` (default: the latest), for
        a sink to record with the version (`Contract.table_ids`); None if
        there is no table at `version`."""
        if version is not None and version in self._ids:
            return self._ids[version]
        try:
            return self._id_at(version)
        except Exception:  # noqa: BLE001 - no such table or version
            return None

    def _other_table(self, since: int, now: str) -> str | None:
        """The id of the table read at `since`, if it is not `now`: the
        table was dropped and created again since (#516, #533)."""
        was = self._ids.get(since)
        return was if was is not None and was != now else None

    def _restricted(self, implied: str) -> Self:
        """A copy that reads only the rows that also pass `implied`, a
        predicate a node's view implies on this table (#81): the view gives
        the same result on them (`Rel.need_eval` in
        `SubstraitLean/Implied.lean`), and files whose statistics rule it
        out are skipped."""
        out = copy.copy(self)
        out.where = implied if self.where is None else f"({self.where}) AND ({implied})"
        out.implied = implied
        out.skipped, out._kept = [], {}
        return out

    def _keep(
        self,
        files: Mapping[str, Mapping[str, ColumnStats]],
        schema: pa.Schema,
        *,
        record: bool = True,
    ) -> set[str]:
        """The files (by path, with their statistics) that may hold rows
        passing `where` (`prune`); with `record`, records the others in
        `skipped`."""
        if self.where is None:
            return set(files)
        key = str(schema)
        new = {p: s for p, s in files.items() if (p, key) not in self._kept}
        if new:
            kept = prune(new, schema, self.where, hi_slack=self._hi_slack)
            self._kept.update({(p, key): p in kept for p in new})
        keep = {p for p in files if self._kept[(p, key)]}
        if record:
            self.skipped = sorted(set(files) - keep)
        return keep

    def _facts_of(
        self,
        table_facts: list[Fact],
        files: Sequence[Mapping[str, ColumnStats]],
        schema: pa.Schema,
        source: str,
    ) -> list[Fact]:
        """The facts about every row read: the table's own (`table_facts`),
        those of the statistics of `files`, their row count, and `where`."""
        filtered = [] if self.where is None else [Fact(self.where, FILTER)]
        return (
            table_facts
            + stats_facts(files, schema, source, hi_slack=self._hi_slack)
            + rows_fact(files, source)
            + filtered
        )

    @staticmethod
    def _full(
        since: int, end: int, rows: pa.Table, reason: str, facts: list[Fact], schema: pa.Schema
    ) -> SourceBatch:
        """The snapshot `rows` at `end`, where no change from `since` is
        available (`reason`)."""
        return SourceBatch.from_snapshot(
            since, end, rows, reason=reason, snapshot_facts=facts, schema=schema
        )


_deprecated.add(_TableSource, {"hi_slack": "_hi_slack"})
