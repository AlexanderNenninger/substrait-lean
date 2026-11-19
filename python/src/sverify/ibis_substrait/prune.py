"""Columns a plan never mentions are not written (#1484, #1485 item 22).

Part of the Ibis producer (`sverify.ibis_substrait`). A column of a type that
blocks a read (a struct, which the DuckDB writer has no SQL form for, or a
`map`, a zoned timestamp, an unsigned integer: `plan_json.type_json`
refuses them) fails every plan over its table. Dropped from the read when no
part of the query mentions it, it blocks nothing; a query that does mention
it reaches the refusal, which names the column.

A column is mentioned where an expression reads it or the plan outputs it. A
verification makes several plans over one table (the transformation and each
condition) and the checker wants one schema for the table, so `mentioning`
sets the names of all of them, and each plan drops the same columns.
"""

from __future__ import annotations

import contextlib
from collections.abc import Collection, Iterator, Mapping
from contextvars import ContextVar
from typing import Any

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify.plan_json import Unsupported, type_json

EVERYTHING = "*"
"""In a set of mentioned names: every column is mentioned (a plan that carries
columns unnamed, `SELECT *`)."""

_MENTIONED: ContextVar[frozenset[str] | None] = ContextVar("mentioned", default=None)

#: The relations whose columns are mentioned by name where they are used.
#: Others (`distinct`, set operations, …) carry all their input's columns.
_NAMED = (
    ops.UnboundTable,
    ops.DatabaseTable,
    ops.Filter,
    ops.Sort,
    ops.Limit,
    ops.Project,
    ops.Aggregate,
    ops.JoinChain,
    ops.JoinLink,
    ops.JoinReference,
)


def blocks(dtype: Any) -> bool:
    """Whether a column of this type fails the plans that write it."""
    if dtype.is_struct():
        return True
    try:
        type_json(dtype)
    except Unsupported:
        return True
    return False


def mentions(expr: ir.Table) -> frozenset[str] | None:
    """The column names `expr` reads or outputs, or None where it has a
    relation that carries columns unnamed."""
    root: Any = expr.op()
    if not all(isinstance(r, _NAMED) for r in root.find(ops.Relation)):
        return None
    return frozenset(f.name for f in root.find(ops.Field)) | frozenset(root.schema.names)


def sql_mentions(sql: str) -> frozenset[str] | None:
    """The column names a SQL query mentions, or None where it has a `*`
    (other than a `count(*)`) or does not parse."""
    import sqlglot
    from sqlglot import exp

    try:
        tree = sqlglot.parse_one(sql, read="duckdb")
    except sqlglot.errors.SqlglotError:
        return None
    if any(not isinstance(s.parent, exp.Count) for s in tree.find_all(exp.Star)):
        return None
    return frozenset(i.name for i in tree.find_all(exp.Identifier))


@contextlib.contextmanager
def mentioning(names: Collection[str]) -> Iterator[None]:
    """Within, every plan keeps the columns called one of `names`, besides the
    ones it mentions itself (`prune_unmentioned`; `EVERYTHING` keeps them all)."""
    token = _MENTIONED.set((_MENTIONED.get() or frozenset()) | frozenset(names))
    try:
        yield
    finally:
        _MENTIONED.reset(token)


def mentioned() -> frozenset[str] | None:
    """The names of the verification being written (`mentioning`), if any."""
    return _MENTIONED.get()


def drop_unmentioned(
    schemas: Mapping[str, ibis.Schema], names: Collection[str] | None
) -> dict[str, ibis.Schema]:
    """`schemas` without the blocking columns not in `names` (all kept for
    None or `EVERYTHING`)."""
    if names is None or EVERYTHING in names:
        return dict(schemas)
    return {
        t: ibis.schema({c: d for c, d in s.items() if c in names or not blocks(d)})
        for t, s in schemas.items()
    }


def prune_unmentioned(expr: ir.Table) -> ir.Table:
    """`expr` with the blocking columns of its tables that no plan of this
    verification mentions dropped from them."""
    own = mentions(expr)
    if own is None:
        return expr
    names = own | (_MENTIONED.get() or frozenset())
    if EVERYTHING in names:
        return expr
    swaps: dict[Any, Any] = {}
    tables: Any = expr.op().find((ops.UnboundTable, ops.DatabaseTable))
    for table in tables:
        kept = drop_unmentioned({"": table.schema}, names)[""]
        if kept.names != table.schema.names:
            swaps[table] = table.copy(schema=kept)
    return expr.op().replace(swaps).to_expr() if swaps else expr
