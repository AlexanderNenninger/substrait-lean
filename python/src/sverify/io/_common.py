"""What Delta and Iceberg have in common: file statistics as facts,
contracts as SQL, and the record a sink stores with each commit.

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.
"""

from __future__ import annotations

import copy
import json
import math
import re
import urllib.parse
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta
from typing import TYPE_CHECKING, Any, Literal, Self

import ibis
import pyarrow as pa
import sqlglot as sg

from sverify import profiles
from sverify._cursor import _TAG, UNRECORDED, cursor_json, cursor_value  # noqa: F401  (re-exported)
from sverify._pipe import Pipeable
from sverify._unsupported import MemoryLimitError, SverifyError
from sverify.conditions import TableCondition, Unique, resolve
from sverify.contracts import Fact, _prove_from
from sverify.incremental import IncrementalView, Snapshot, SourceBatch, plan_digest
from sverify.plan_json import is_utc
from sverify.report import Condition

if TYPE_CHECKING:
    import duckdb
else:
    from sverify._duckdb import lazy as duckdb


@dataclass(frozen=True)
class ColumnStats:
    """One file's statistics for one column; None is unknown (`ColStats` in
    `analysis/Sverify/Analysis/TableFormat.lean`)."""

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
    doubles, dates and microsecond timestamps, instants (UTC) included (D53).

    Not strings (writers truncate their bounds, and the checker has no string
    order: #17), decimals (not modelled: #27), timestamps in another zone, nor
    other units and floats."""
    return (
        pa.types.is_integer(t)
        or pa.types.is_float64(t)
        or pa.types.is_date32(t)
        or (pa.types.is_timestamp(t) and t.unit == "us" and (t.tz is None or is_utc(t.tz)))
    )


_CONTAINER_SCHEMES = frozenset({"abfs", "abfss", "az", "wasb", "wasbs"})
"""Schemes whose user part names the container
(`abfss://container@account.dfs.core.windows.net/path`): `public_uri` keeps
it and drops a password."""


def public_uri(uri: str) -> str:
    """`uri` as sverify records it: the scheme, host, port and path, without
    userinfo (`user:password@`), query string or fragment. A path, an
    Iceberg identifier or any other text without `://` comes back as it is.

    Every URI that goes into a record, a report, an export or an event goes
    through this: the sink's `location`, `started`, `credentials[].location`,
    the ODCS `physicalName` and the OpenLineage namespace."""
    if "://" not in uri:
        return uri
    parts = urllib.parse.urlsplit(uri)
    user, at, host = parts.netloc.rpartition("@")
    if at and parts.scheme.lower() in _CONTAINER_SCHEMES:
        host = f"{user.partition(':')[0]}@{host}"
    return f"{parts.scheme}://{host}{parts.path}"


def has_userinfo(uri: str) -> bool:
    """Whether `uri` carries credentials in its userinfo: `user:password@`,
    or a bare `user@` outside the container schemes `public_uri` keeps."""
    if "://" not in uri:
        return False
    parts = urllib.parse.urlsplit(uri)
    user, at, _ = parts.netloc.rpartition("@")
    return bool(at) and (":" in user or parts.scheme.lower() not in _CONTAINER_SCHEMES)


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
    if getattr(v, "tzinfo", None) is not None:
        # An instant: its literal carries the offset, so no session zone is read.
        text = v.astimezone(UTC).isoformat(sep=" ", timespec="microseconds")
        return f"TIMESTAMPTZ '{text}'"
    return f"TIMESTAMP '{v.isoformat(sep=' ', timespec='microseconds')}'"


def stats_facts(
    files: Sequence[Mapping[str, ColumnStats]],
    schema: pa.Schema,
    source: str,
    *,
    hi_slack: timedelta = timedelta(0),
) -> list[Fact]:
    """Facts about every row of a table made of `files`, from the join of
    the files' statistics (`stats_table` in `analysis/Sverify/Analysis/TableFormat.lean`):
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
    counts, when every file has one. A file's count covers its deleted
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
    `analysis/Sverify/Analysis/Pruning.lean`, proved by `strPrune_sound`): every value
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
    in `analysis/Sverify/Analysis/Pruning.lean`), or if Lean proves from the facts its
    statistics give that `where` is not TRUE on any of its rows
    (`contract_sound`, `stats_prune`). Then filtering the table reads the
    same rows as filtering the other files (`prune_sound` in
    `analysis/Sverify/Analysis/TableFormat.lean`), and every plan linear in the source
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
#: Format 3 (1.0) names the semantics `semantics`, which format 2 called
#: `profile`; format 2 named the node `node`, which format 1 called `view`.
CONTRACT_FORMAT = 3


@dataclass(kw_only=True)
class Contract:
    """What a sink records with each commit: which plan produced the data,
    from which source versions, and what it proved about every row.

    `DeltaSource.contract()` and `IcebergSource.contract()` read it back.
    sverify builds it, and a sink of your own stores `to_json()` and reads it
    back with `from_json`: user code does not construct one. Its fields are
    keyword-only.

    Attributes:
        node: The stored node's name.
        sources: The version of every source table the state was computed
            from.
        not_null: Columns the node proves NOT NULL: stated in `ensures`
            (`_.col.notnull()`), or shown never NULL by its proved report
            (not nullable in `Report.output`).
        unique: Column sets the node proves unique.
        cursors: The cursor of every source that can restore its table from
            one (`Source.restore`), at its version in `sources`.
        table_ids: The id of every source table that has one (a Delta
            table's `metaData.id`), at its version in `sources`.
        fingerprints: What identifies every source that names its place
            where it has no table id (a Flight server and table), by name.
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
    fingerprints: dict[str, str] = field(default_factory=dict)
    """What identifies each source that names its place and has no table id
    (`Source._fingerprint`: a Flight server and table). Two writers of one
    sink that read different sources under one name show it here; a record
    without it (written before it) names none."""
    engine: str | None = None
    """The engine that computed the state (`sverify.engines`), None where the
    record does not say: one written before these fields."""
    engine_version: str | None = None
    """The version of the engine's library."""
    sverify: str | None = None
    """The version of sverify that wrote the record. Its facts and checker are
    those of the release."""
    semantics: str | None = None
    """The semantics the plan was verified under (`verify(semantics=...)`);
    the plan's digest includes it unless it is `"portable"`."""
    package: str | None = None
    """For an engine that comes from another package than sverify, that package
    as `name==version`: its facts ship with it."""
    format: int = CONTRACT_FORMAT
    """The version of the record's format (`CONTRACT_FORMAT`,
    `sverify/schemas/sink-contract.schema.json`). It changes only with a
    record a reader of the previous format cannot read, which 1.x never
    writes (`docs/stability.md`). A record without it was written before
    0.5 and reads as format 1; format 1 named the node `view`, and formats
    1 and 2 named the semantics `profile`."""

    def to_json(self) -> str:
        """The contract as JSON, as sinks store it.

        Returns:
            A JSON object with the contract's fields, keys sorted, in the
            format of `sverify/schemas/sink-contract.schema.json`.
        """
        return json.dumps({k: v for k, v in self.__dict__.items() if v is not None}, sort_keys=True)

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
        if fmt < 3 and "profile" in data:
            data = {**data, "semantics": data["profile"]}
        known = Contract.__dataclass_fields__
        return Contract(**{k: v for k, v in data.items() if k in known and k != "format"})


class ConcurrentWriteError(SverifyError, RuntimeError):
    """Another writer committed to a sink between the moment this refresh
    read what the sink holds (`Sink.committed`) and its own commit: two
    processes refreshing the same sink. This refresh's write was not
    committed, and the sink keeps the other writer's state; the next refresh
    replaces it with this process's state, or skips if the sink already holds
    it."""

    code = "concurrent_write"


@dataclass(kw_only=True)
class SinkWrite:
    """What storing a node's state did, in any sink.

    Built by keyword: a sink of your own may return one from `write`.

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
        inserts: Rows written.
        deletes: Rows deleted.
        constraints: The table's CHECK constraints from the node's
            guarantees, by name (Delta; empty for Iceberg).
    """

    mode: Literal["created", "overwrite", "merge", "append", "row_level", "update", "skipped"]
    version: int | None
    contract: Contract
    inserts: int = 0
    deletes: int = 0
    constraints: dict[str, str] = field(default_factory=dict)

    def __str__(self) -> str:
        src = ", ".join(f"{t}@v{n}" for t, n in self.contract.sources.items())
        if self.mode == "skipped":
            at = "" if self.version is None else f" (v{self.version})"
            return f"{self.contract.node} from {src}: already committed{at}"
        at = "" if self.version is None else f" v{self.version}"
        return (
            f"{self.contract.node} from {src}: {self.mode.replace('_', ' ')}{at}, "
            f"{self.inserts} row(s) written, {self.deletes} deleted"
        )


def _promises(
    guarantees: Sequence[Condition], proved_not_null: Sequence[str], schema: ibis.Schema
) -> tuple[list[str], dict[str, str], list[list[str]]]:
    """What a sink's contract record promises about every row, from a node's
    guarantees and the columns its proved report shows never NULL: the NOT
    NULL columns, the CHECK constraints by name, and the unique column sets.
    The one builder of the committed record and the fresh one `drift`
    compares it with."""
    not_null: list[str] = []
    checks: dict[str, str] = {}
    unique: list[list[str]] = []
    for c in guarantees:
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
    not_null += [c for c in proved_not_null if c in schema and c not in not_null]
    return not_null, checks, unique


@dataclass
class Drift:
    """How a stored node's contract now compares with the one its sink last
    committed (`sverify check --against-sink`, #769): a committed promise
    the fresh node does not prove is `weakened`; a fresh one the record
    lacks is `added`. Each holds `not_null` columns, `checks` as SQL texts
    and `unique` column sets."""

    weakened: dict[str, list[Any]]
    added: dict[str, list[Any]]
    plan_changed: bool
    profiles: tuple[str | None, str]
    """The committed record's profile and the fresh one."""
    why: dict[str, str] = field(default_factory=dict)
    """For a weakened CHECK, why the fresh node does not prove it."""

    def to_dict(self) -> dict[str, Any]:
        return {"weakened": self.weakened, "added": self.added, "plan_changed": self.plan_changed}


def drift(committed: Contract, node: Any) -> Drift:
    """`committed` against what `node`'s sink would record now (ruling 189):
    a NOT NULL column or a unique set by inclusion (a smaller key implies a
    larger one); a CHECK by its SQL text, and one whose text is gone by a
    proof of it as a postcondition of the node. No promise is kept without
    its text in the fresh record or a proof."""
    from sverify.contracts import verify, view_contract

    expr = node._query()._expr
    vc = view_contract(expr)
    not_null, checks, unique = _promises(vc.guarantees, vc.not_null, expr.schema())
    fresh = set(checks.values())
    why: dict[str, str] = {}
    for text in committed.checks.values():
        if text in fresh or text in why:
            continue
        try:
            got = verify(expr, requires=vc.requires, ensures=[text], semantics=vc.profile)
        except MemoryLimitError:
            raise  # a budget, which the CLI reports as one (exit 4)
        except Exception as e:  # noqa: BLE001 - unreadable now: weakened, with why
            why[text] = f"not proved: sverify cannot read it against the node ({e})"
            continue
        if not got.ensures or not got.ensures[0].proved:
            reason = got.ensures[0].why if got.ensures else "no result"
            why[text] = f"not proved: {reason}"
    weakened = {
        "not_null": [c for c in committed.not_null if c not in not_null],
        "checks": list(why),
        "unique": [u for u in committed.unique if not any(set(k) <= set(u) for k in unique)],
    }
    added = {
        "not_null": [c for c in not_null if c not in committed.not_null],
        "checks": [t for t in checks.values() if t not in committed.checks.values()],
        "unique": [u for u in unique if u not in committed.unique],
    }
    plan = plan_digest(node.internal_plan, profile=vc.profile)
    return Drift(weakened, added, plan != committed.plan, (committed.semantics, vc.profile), why)


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
    not_null, checks, unique = _promises(
        view.guarantees, view.not_null, ibis.Schema.from_pyarrow(view.schema)
    )
    return Contract(
        node=view.name,
        plan=plan_digest(view.plan, profile=view.profile),
        sources=versions,
        epoch=sum(versions.values()),
        not_null=not_null,
        checks=checks,
        unique=unique,
        digests=view.pipeline.digests(view.name),
        cursors=_cursors(view, versions),
        table_ids=_table_ids(view, versions),
        fingerprints=_fingerprints(view, versions),
        semantics=view.profile,
        engine=(rt := profiles.runtime(view.engine))["engine"],
        engine_version=rt["engine_version"],
        sverify=rt["sverify"],
        package=rt["package"],
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


def _fingerprints(view: IncrementalView, versions: Mapping[str, int]) -> dict[str, str]:
    """What identifies every source of `view` without a table id that names
    its place (`Source._fingerprint`)."""
    out: dict[str, str] = {}
    for t in versions:
        src = view.pipeline.sources.get(t)
        fp = None if isinstance(src, _TableSource) else getattr(src, "_fingerprint", None)
        if fp is not None and (value := fp()) is not None:
            out[t] = value
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
    computed from: their table id changed, or, where the ids do not tell
    (one side records none), their version went down (a table's versions
    only grow, so a lower one is another table, dropped and created again).
    Then the sink's rows are not a state of these inputs, whatever the
    epochs say. With the same id on both sides, a lower version is
    the same table: this refresh is behind the record, and the sink holds a
    later state, which is not written over."""
    out = []
    for t, n in contract.sources.items():
        was, now = committed.table_ids.get(t), contract.table_ids.get(t)
        if was is not None and now is not None:
            if was != now:
                out.append(t)
        elif n < committed.sources.get(t, n):
            out.append(t)
    return sorted(out)


def check_same_sources(uri: str, committed: Contract, contract: Contract) -> None:
    """Refuse a commit over a state computed from another source: where both
    records fingerprint a source and the fingerprints differ, the two writers
    read different sources under one name, and versions say nothing about
    which is ahead. A source without a fingerprint on either side is not
    compared."""
    for t in sorted(contract.fingerprints):
        was, now = committed.fingerprints.get(t), contract.fingerprints[t]
        if was is not None and was != now:
            raise ValueError(
                f"{uri} holds a state of `{contract.node}` computed from the source "
                f"`{t}` at {was!r} (as `{committed.node}`, plan {committed.plan[:8]}), and this "
                f"node reads `{t}` at {now!r}. Two writers with one app_id read different "
                "sources under one name; versions cannot tell which is ahead, so nothing is "
                "written. Write to a sink of its own, or give the writers different "
                "app_ids and names."
            )


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

    def __init__(self, name: str, where: str | None, schema: pa.Schema | None = None):
        self.name, self.where = name, where
        self._declared = schema
        """The schema the caller declared: `schema()` answers with it, without
        opening the table; every read checks the table still has it."""
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
    def schema(self) -> pa.Schema:
        """The table's schema: the one declared (`schema=`) without opening the
        table, else the table's current one."""

    def _verify_declared(self, actual: pa.Schema) -> None:
        """Raise `SchemaError` if the table's schema is not the declared one:
        names and types (a table read as `large_string` is `string`), and no
        column declared NOT NULL is nullable in the table."""
        if self._declared is None:
            return
        from sverify.engine import plain_schema
        from sverify.incremental import SchemaError

        want = {f.name: f for f in plain_schema(self._declared)}
        got = {f.name: f for f in plain_schema(actual)}
        diff = [f"missing {c}" for c in want.keys() - got.keys()]
        diff += [f"unexpected {c}" for c in got.keys() - want.keys()]
        for c in want.keys() & got.keys():
            if want[c].type != got[c].type:
                diff.append(f"{c}: declared {want[c].type}, table {got[c].type}")
            elif not want[c].nullable and got[c].nullable:
                # A proof may take "never NULL" from the declaration; a table
                # that allows NULLs does not promise it. (Declared nullable
                # over a NOT NULL column is the weaker claim, and fine.)
                diff.append(f"{c}: declared NOT NULL, table nullable")
        if not diff:
            return
        raise SchemaError(
            f"{self.name}: the table's schema is not the one declared with schema=: "
            + "; ".join(sorted(diff))
            + "; update schema= to the table's schema, or restore the table's columns"
        )

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
        `analysis/Sverify/Analysis/Implied.lean`), and files whose statistics rule it
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
            since, end, rows, why=reason, snapshot_facts=facts, schema=schema
        )
