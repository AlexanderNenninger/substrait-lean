"""What Delta and Iceberg have in common: file statistics as facts,
contracts as SQL, and the record a sink stores with each commit."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Any

import ibis
import pyarrow as pa
import sqlglot as sg

from sverify.contracts import Condition, Fact, Unique, resolve
from sverify.engine import to_sql
from sverify.incremental import IncrementalView


@dataclass(frozen=True)
class ColumnStats:
    """One file's statistics for one column; None is unknown."""

    lo: Any
    hi: Any
    nulls: int | None


def _bounded(t: pa.DataType) -> bool:
    """Types whose min/max statistics become bounds: integers, dates and
    microsecond timestamps without a time zone. Not doubles (minimum and
    maximum leave out NaN) nor strings (writers may truncate them)."""
    return (
        pa.types.is_integer(t)
        or pa.types.is_date32(t)
        or (pa.types.is_timestamp(t) and t.unit == "us" and t.tz is None)
    )


def q(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def _literal(t: pa.DataType, v: Any) -> str:
    if pa.types.is_integer(t):
        return str(int(v))
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
    """Facts about every row of a table made of `files`: a column without
    NULLs in any file is NOT NULL, and a bounded column lies between the least
    minimum and the greatest maximum (the join of the files' bounds,
    `stats_table` in `SubstraitLean/TableFormat.lean`). A file missing a
    statistic makes it unknown for the whole table. `hi_slack` widens
    timestamp maxima that the format truncates."""
    if not files:
        return []
    out = []
    for f in schema:
        stats = [file.get(f.name) for file in files]
        if any(s is None or s.nulls is None for s in stats):
            continue
        known = [s for s in stats if s is not None]
        if sum(s.nulls or 0 for s in known):
            continue
        conds = [f"{q(f.name)} IS NOT NULL"]
        if _bounded(f.type) and all(s.lo is not None and s.hi is not None for s in known):
            lo = min(s.lo for s in known)
            hi = max(s.hi for s in known)
            if isinstance(hi, datetime):
                hi += hi_slack
            conds += [
                f"{q(f.name)} >= {_literal(f.type, lo)}",
                f"{q(f.name)} <= {_literal(f.type, hi)}",
            ]
        out.append(Fact(" AND ".join(conds), source))
    return out


def condition_sql(cond: Condition, schema: ibis.Schema) -> str | None:
    """A row condition as a standalone SQL expression over the columns, or
    None if it has none (`unique`)."""
    if isinstance(cond, Unique):
        return None
    if isinstance(cond, str):
        return cond
    t = ibis.table(schema, name="t")
    select = sg.parse_one(to_sql(t.select(c=resolve(cond, t))), read="postgres")
    expr = select.expressions[0].this  # type: ignore[attr-defined]
    for col in expr.find_all(sg.exp.Column):
        col.set("table", None)
    return expr.sql(dialect="postgres")


def not_null_column(sql: str) -> str | None:
    """The column of a condition that says exactly `col IS NOT NULL`."""
    e = sg.parse_one(sql, read="postgres")
    if isinstance(e, sg.exp.Paren):
        e = e.this
    if (
        isinstance(e, sg.exp.Not)
        and isinstance(e.this, sg.exp.Is)
        and isinstance(e.this.this, sg.exp.Column)
        and isinstance(e.this.expression, sg.exp.Null)
    ):
        return e.this.this.name
    return None


@dataclass
class Contract:
    """What a sink records with each commit: which plan produced the data,
    from which source versions, and what it proved about every row."""

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

    def to_json(self) -> str:
        return json.dumps(self.__dict__, sort_keys=True)

    @staticmethod
    def from_json(text: str) -> Contract:
        return Contract(**json.loads(text))


def plan_hash(view: IncrementalView) -> str:
    return hashlib.sha256(view.plan.encode()).hexdigest()


def view_contract_record(view: IncrementalView) -> Contract:
    versions = view.versions
    bases = _base_tables(view)
    missing = sorted(bases - set(versions))
    if missing:
        raise ValueError(
            f"view {view.name} reads tables without a source ({missing}): a sink needs "
            "source versions to write exactly once"
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
        plan=plan_hash(view),
        sources=versions,
        epoch=sum(versions.values()),
        not_null=not_null,
        checks=checks,
        unique=unique,
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


def first_line(e: BaseException) -> str:
    text = str(e).strip().splitlines()
    return f"{type(e).__name__}: {text[0] if text else ''}"


def describe_contract(c: Contract) -> str:
    sources = ", ".join(f"{t}@v{n}" for t, n in c.sources.items())
    return f"{c.view} (plan {c.plan[:12]}) from {sources}"
