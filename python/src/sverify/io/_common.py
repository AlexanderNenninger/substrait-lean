"""What Delta and Iceberg have in common: file statistics as facts,
contracts as SQL, and the record a sink stores with each commit.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from __future__ import annotations

import json
import math
import re
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Any, Literal

import duckdb
import ibis
import pyarrow as pa
import sqlglot as sg

from sverify.contracts import Condition, Fact, TableCondition, Unique, _prove_from, resolve
from sverify.engine import to_sql
from sverify.incremental import IncrementalView, plan_digest


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


def prune(
    files: Mapping[str, Mapping[str, ColumnStats]],
    schema: pa.Schema,
    where: str,
    *,
    hi_slack: timedelta = timedelta(0),
) -> set[str]:
    """The files that may hold rows passing `where`. A file is skipped only
    if Lean proves from the facts its statistics give that `where` is not
    TRUE on any of its rows (`contract_sound`); then filtering the table
    reads the same rows as filtering the other files (`prune_sound` in
    `SubstraitLean/TableFormat.lean`)."""
    table = ibis.table(ibis.Schema.from_pyarrow(schema), name="file")
    keep = set()
    for path, stats in files.items():
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
    select = sg.parse_one(to_sql(t.select(c=resolve(cond, t))), read="postgres")
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


@dataclass
class Contract:
    """What a sink records with each commit: which plan produced the data,
    from which source versions, and what it proved about every row.

    `DeltaSource.contract` and `IcebergSource.contract` read it back.

    Attributes:
        view: The stored node's name.
        sources: The version of every source table the state was computed
            from.
        not_null: Columns the node proves NOT NULL.
        unique: Column sets the node proves unique.
    """

    view: str
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
    """Content digest of each static table (`StaticSource`) the node read."""

    def to_json(self) -> str:
        """The contract as JSON, as sinks store it.

        Returns:
            A JSON object with the contract's fields, keys sorted.
        """
        return json.dumps(self.__dict__, sort_keys=True)

    @staticmethod
    def from_json(text: str) -> Contract:
        """A contract from what `to_json` wrote.

        Args:
            text: The JSON `to_json` wrote.

        Returns:
            The contract.
        """
        known = Contract.__dataclass_fields__
        return Contract(**{k: v for k, v in json.loads(text).items() if k in known})


@dataclass
class SinkWrite:
    """What storing a node's state did, in any sink.

    `mode` is how: `created` the table, `overwrite` it, `merge` the change
    (Delta), `append` the new rows or write the change `row-level` (Iceberg),
    `update` it with the change (a sink of your own), or `skipped` a state
    the table already holds. `version` is the table's version afterwards;
    `constraints` are the CHECK constraints the table has for the node's
    guarantees (Delta). `print` it for a one-line summary. A refresh's
    report lists the writes it made.

    Attributes:
        mode: `"created"` (the first write made the table), `"overwrite"`
            (the table's rows were replaced), `"merge"` (the change in one
            MERGE commit, Delta), `"append"` (the change only added rows,
            Iceberg), `"row-level"` (position deletes and new rows in one
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

    mode: Literal["created", "overwrite", "merge", "append", "row-level", "update", "skipped"]
    version: int | None
    contract: Contract
    inserted: int = 0
    deleted: int = 0
    constraints: dict[str, str] = field(default_factory=dict)

    def __str__(self) -> str:
        src = ", ".join(f"{t}@v{n}" for t, n in self.contract.sources.items())
        if self.mode == "skipped":
            at = "" if self.version is None else f" (v{self.version})"
            return f"{self.contract.view} from {src}: already committed{at}"
        at = "" if self.version is None else f" v{self.version}"
        return (
            f"{self.contract.view} from {src}: {self.mode}{at}, "
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
            "format through sverify.io.StaticSource(table, version)"
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
    return Contract(
        view=view.name,
        plan=plan_digest(view.plan),
        sources=versions,
        epoch=sum(versions.values()),
        not_null=not_null,
        checks=checks,
        unique=unique,
        digests=view.pipeline.digests(view.name),
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


def describe_contract(c: Contract) -> str:
    sources = ", ".join(f"{t}@v{n}" for t, n in c.sources.items())
    return f"{c.view} (plan {c.plan[:12]}) from {sources}"
