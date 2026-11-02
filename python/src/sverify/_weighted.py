"""Weighted tables: bags of rows as Arrow tables, for incremental views (#173).

Internal: not part of sverify's public API.

A weighted table is an Arrow table with the rows' columns and a last column
`WEIGHT` (int64): the number of copies of the row, negative for a change that
deletes them. Rows are equal as the model compares them (`row_key`): one NaN,
equal to itself, and `-0.0` equal to `0.0`; lists and structs compare by
their elements. DuckDB groups rows that way, in process and without copying
the Arrow data; pyarrow's `group_by` does not (it keeps `-0.0` apart and
refuses list keys).

The grouping only finds which rows are equal and adds up their weights: each
group keeps its first row's values, taken from the Arrow table itself, so no
value round-trips through DuckDB's types.
"""

from __future__ import annotations

import threading
from collections.abc import Sequence
from typing import Any

import duckdb
import pyarrow as pa
import pyarrow.compute as pc

WEIGHT = "__weight"
_ROW = "__sverify_row"

_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()


def _q(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def _sql(sql: str, **tables: pa.Table) -> pa.Table:
    """Run `sql` over `tables` on the shared in-process DuckDB database."""
    global _DB
    with _LOCK:
        if _DB is None:
            _DB = duckdb.connect()
        db = _DB
        try:
            for name, table in tables.items():
                db.register(name, table)
            return db.sql(sql).to_arrow_table()
        finally:
            for name in tables:
                db.unregister(name)


def _call(name: str, *args: object) -> Any:
    # `pyarrow.compute`'s functions are generated at import, so type
    # checkers do not see them; `call_function` is typed.
    return pc.call_function(name, list(args))


def _indices(n: int) -> pa.Array:
    ones = pa.repeat(pa.scalar(1, pa.int64()), n)
    return _call("subtract", _call("cumulative_sum", ones), 1)


def weighted(rows: pa.Table, weight: int) -> pa.Table:
    """`rows` with the weight `weight` on every row."""
    return rows.append_column(WEIGHT, pa.repeat(pa.scalar(weight, pa.int64()), rows.num_rows))


def rows_of(z: pa.Table) -> pa.Table:
    """The rows of a weighted table, without the weights."""
    return z.drop_columns([WEIGHT])


def negated(z: pa.Table) -> pa.Table:
    return z.set_column(z.num_columns - 1, WEIGHT, _call("negate", z.column(WEIGHT)))


def concat(parts: Sequence[pa.Table]) -> pa.Table:
    """The tables one after the other, in the first one's schema (types and
    nullability may differ in name only, as `string` and `large_string`)."""
    schema = parts[0].schema
    return pa.concat_tables([p.cast(schema) if p.schema != schema else p for p in parts])


def grouped(z: pa.Table, sums: Sequence[str] = (WEIGHT,), *, nonzero: str = WEIGHT) -> pa.Table:
    """The rows of `z`, one per group of equal rows (all columns but `sums`),
    with each of the `sums` columns added up over the group; groups whose
    `nonzero` sum is 0 are left out. Each group keeps its first row's values,
    and the groups are in the order of their first rows."""
    if z.num_rows == 0:
        return z
    keys = [c for c in z.column_names if c not in sums]
    indexed = pa.Table.from_arrays(
        [*(z.column(c) for c in keys), _indices(z.num_rows), *(z.column(c) for c in sums)],
        names=[*keys, _ROW, *sums],
    )
    totals = ", ".join(f"CAST(sum({_q(c)}) AS BIGINT) AS {_q(c)}" for c in sums)
    group = f"GROUP BY {', '.join(map(_q, keys))}" if keys else ""
    out = _sql(
        f"SELECT min({_q(_ROW)}) AS {_q(_ROW)}, {totals} FROM z {group} "
        f"HAVING sum({_q(nonzero)}) <> 0 ORDER BY 1",
        z=indexed,
    )
    first = out.column(_ROW)
    columns = [z.column(c).take(first) for c in keys]
    columns += [out.column(c).cast(z.schema.field(c).type) for c in sums]
    schema = pa.schema([z.schema.field(c) for c in [*keys, *sums]])
    return pa.Table.from_arrays(columns, schema=schema)


def consolidated(*parts: pa.Table) -> pa.Table:
    """The weighted tables added up: the weights of equal rows summed, rows
    of weight 0 left out."""
    return grouped(concat(parts))


def positive(z: pa.Table) -> pa.Table:
    """The rows of positive weight."""
    return z.filter(_call("greater", z.column(WEIGHT), 0))


def negative(z: pa.Table) -> pa.Table:
    """The rows of negative weight."""
    return z.filter(_call("less", z.column(WEIGHT), 0))


def has_negative(z: pa.Table) -> bool:
    return _call("any", _call("less", z.column(WEIGHT), 0)).as_py() is True


def expanded(z: pa.Table) -> pa.Table:
    """The bag of rows of a weighted table without negative weights: each row
    as many times as its weight."""
    w = z.column(WEIGHT)
    rows = rows_of(z)
    if z.num_rows == 0 or _call("all", _call("equal", w, 1)).as_py():
        return rows
    if has_negative(z):
        raise ValueError("a bag of rows cannot hold a negative number of copies")
    idx = pa.table({_ROW: _indices(z.num_rows), WEIGHT: w})
    take = _sql(f"SELECT {_q(_ROW)} FROM idx, range({_q(WEIGHT)}) ORDER BY 1", idx=idx)
    return rows.take(take.column(_ROW))


def total(z: pa.Table) -> int:
    """How many rows `z` adds (positive weights) or removes (negative)."""
    s = _call("sum", z.column(WEIGHT)).as_py()
    return 0 if s is None else s


def inserted_count(z: pa.Table) -> int:
    return total(positive(z))


def deleted_count(z: pa.Table) -> int:
    return -total(negative(z))


def duplicate_keys(table: pa.Table, cols: Sequence[str], among: pa.Table | None = None) -> int:
    """How many copies beyond the first the keys `cols` of `table` have:
    over all keys, or only over the keys of `among` (a table with the
    columns `cols`). Keys are equal as rows are (NULLs equal)."""
    key = ", ".join(map(_q, cols))
    dup = f"SELECT {key}, count(*) AS n FROM t GROUP BY {key} HAVING count(*) > 1"
    if among is None:
        out = _sql(f"SELECT coalesce(sum(n - 1), 0) AS d FROM ({dup})", t=table.select(cols))
    else:
        same = " AND ".join(f"d.{_q(c)} IS NOT DISTINCT FROM a.{_q(c)}" for c in cols)
        out = _sql(
            f"SELECT count(*) AS d FROM ({dup}) d WHERE EXISTS (SELECT 1 FROM a WHERE {same})",
            t=table.select(cols),
            a=among.select(cols),
        )
    return out.column("d")[0].as_py()
