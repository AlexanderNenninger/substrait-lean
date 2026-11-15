"""The DuckDB column types sverify models, by the type DuckDB declares.

Arrow exports some DuckDB types as another kind (a UUID as `string`, an ENUM
as `dictionary<string>`, a BIT as `binary`), and DuckDB compares and orders
them by their own rules (duckdb-uuid-text-order, duckdb-uuid-string-cast,
duckdb-enum-order). A table read through Arrow would then be checked as text.
`refuse_unmodelled` takes the declared types (`rel.types`, or DESCRIBE) and
refuses every column whose type is not on the allow-list below, whatever Arrow
exports it as, with the exit that works: a cast to a modelled type in the
source query (#1253).
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any

#: The type ids (`DuckDBPyType.id`) sverify reads through Arrow as DuckDB
#: computes them. JSON is a VARCHAR and `tuple` the empty struct; the unsigned integers and the
#: time-zone-aware types have refusals of their own, further on.
MODELLED = frozenset(
    {
        "boolean",
        "tinyint",
        "smallint",
        "integer",
        "bigint",
        "utinyint",
        "usmallint",
        "uinteger",
        "ubigint",
        "hugeint",
        "uhugeint",
        "float",
        "double",
        "decimal",
        "varchar",
        "blob",
        "date",
        "time",
        "time with time zone",
        "timestamp",
        "timestamp_s",
        "timestamp_ms",
        "timestamp_ns",
        "timestamp with time zone",
        "interval",
        "list",
        "array",
        "struct",
        "map",
        "tuple",
        "null",
    }
)

_NESTED = frozenset({"list", "array", "struct", "map"})

#: What to write in the source query in place of each refused type.
_EXIT = {
    "uuid": (
        "read it as text with CAST({col} AS VARCHAR) in the source query, and compare "
        "it with the lower-case hyphenated form"
    ),
    "enum": (
        "read it as text with CAST({col} AS VARCHAR) in the source query; DuckDB orders "
        "an ENUM by declaration position, text by spelling"
    ),
    "bit": "read it as text with CAST({col} AS VARCHAR) in the source query",
    "bignum": (
        "cast it to a DECIMAL(p, 0) that holds its values, CAST({col} AS DECIMAL(p, 0)), "
        "in the source query"
    ),
}


def _unmodelled(t: Any) -> str | None:
    """The id of the first type inside `t` that is not modelled, if any."""
    kind = str(t.id)
    if kind not in MODELLED:
        return kind
    if kind in _NESTED:
        for _, child in t.children:
            if hasattr(child, "id") and (bad := _unmodelled(child)) is not None:
                return bad
    return None


def refuse_unmodelled(columns: Iterable[str], types: Iterable[Any], where: str = "") -> None:
    """Raise `ValueError` for the first column whose declared DuckDB type (a
    `DuckDBPyType`, as `rel.types` gives) is not modelled, naming the exit.
    `where` is appended to the column ("of <table>")."""
    for col, t in zip(columns, types, strict=True):
        bad = _unmodelled(t)
        if bad is None:
            continue
        exit_ = _EXIT.get(
            bad, "cast it to a modelled type in the source query ({col} is not read as {id})"
        )
        what = f"column {col}{where} is {t}"
        if bad != str(t.id):
            what += f" (holding {bad.upper()})"
        raise ValueError(f"{what}; {exit_.format(col=col, id=bad.upper())}")


def refuse_base_table(backend: Any, op: Any) -> None:
    """`ProfilePlugin.refuse_declared_types`: raise `Unsupported` for a base
    table of an Ibis DuckDB `backend` with a column of an unmodelled declared
    type. Ibis types an ENUM as `string` and so hides it from the producer."""
    from sverify._unsupported import Unsupported

    ns = op.namespace
    parts = [p for p in (ns.catalog, ns.database, op.name) if p]
    q = ".".join('"' + p.replace('"', '""') + '"' for p in parts)
    rel = backend.con.sql(f"SELECT * FROM {q} LIMIT 0")
    try:
        refuse_unmodelled(rel.columns, rel.types, f" of {op.name}")
    except ValueError as e:
        raise Unsupported(str(e)) from e
