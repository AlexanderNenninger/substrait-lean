"""DuckDB as an engine, through SQL generated from the plan.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

`run` writes the plan as SQL with `sverify.sql.to_sql` (whose semantics are
Lean's `Rel.eval`, see `sverify.sql.core`) and runs it on an in-process
DuckDB database holding the given tables. DuckDB's Substrait extension is not
used.
"""

from __future__ import annotations

import functools
import json
import threading
from collections.abc import Callable, Mapping, Sequence
from typing import Literal, overload

import duckdb
import pyarrow as pa

from sverify import _duckdb
from sverify._scan import Native, Resident
from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB


@functools.lru_cache(maxsize=4096)
def _sql(plan: str, guards: bool = True, finite: bool = True) -> str:
    """`to_sql` of a JSON plan, memoized: an incremental view runs the same
    delta plans on every batch."""
    return to_sql(json.loads(plan), DUCKDB, guards=guards, finite=finite)


_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()


def _forget_cursor() -> None:
    global _DB
    _DB = None


_duckdb.on_reset(_forget_cursor)


def setting(name: str) -> object:
    """The value of DuckDB setting `name` on the engine's cursor, which
    every `run` uses: a session's `SET GLOBAL` shows here, a `SET` on
    another cursor does not."""
    global _DB
    with _LOCK:
        if _DB is None:
            _DB = _duckdb.cursor()
        rows = _DB.execute("SELECT current_setting(?)", [name]).fetchall()
    return rows[0][0] if rows else None


def settings(names: Sequence[str]) -> dict[str, object]:
    """The values of DuckDB settings `names` on the engine's cursor, as
    `setting` reads each, in one query."""
    if not names:
        return {}
    global _DB
    with _LOCK:
        if _DB is None:
            _DB = _duckdb.cursor()
        sql = "SELECT " + ", ".join(["current_setting(?)"] * len(names))
        (row,) = _DB.execute(sql, list(names)).fetchall()
    return dict(zip(names, row, strict=True))


@overload
def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: Literal[False] = False,
    finite: bool = True,
) -> pa.Table: ...


@overload
def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: Literal[True],
    finite: bool = True,
) -> Resident: ...


def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: bool = False,
    finite: bool = True,
) -> pa.Table | Resident:
    """Run a Substrait JSON plan on DuckDB over `tables`: Arrow tables, or
    tables DuckDB reads where they are (`sverify._scan.Native`: Parquet
    files, or tables it holds). With `keep`, the result stays in DuckDB, as
    a `Resident` table.

    The process's database serves every call (`sverify._duckdb`; opening
    one costs ~10 ms), through a cursor of the engine's own; the tables are
    created for the call, as temporary tables, and dropped after it.
    `guards=False`, `finite=False`: see `sverify.sql.to_sql`."""
    global _DB
    sql = (
        _sql(plan, guards, finite)
        if isinstance(plan, str)
        else to_sql(plan, DUCKDB, guards=guards, finite=finite)
    )
    # `to_sql` numbers a table's rows with `rowid` where the plan needs their order.
    ordered = DUCKDB.row_ordinal() in sql
    with _LOCK:
        if _DB is None:
            _DB = _duckdb.cursor()
        db = _DB
        _duckdb.collect(db)
        drops: list[Callable[[], None]] = []
        try:
            for name, table in tables.items():
                if isinstance(table, Native):
                    # A view reads the table where it is; a table holds its
                    # rows in order when the plan needs `rowid`.
                    drops.append(table.attach(db, name, table=ordered))
                    continue
                if not ordered:
                    # A view of the Arrow data, without copying it.
                    db.register(name, table)
                    drops.append(functools.partial(_unregister, db, name))
                    continue
                # A real table (not a view on the Arrow data): `rowid` numbers its
                # rows in insertion order, which `to_sql` uses as the scan order.
                db.register("__sverify_input", table)
                db.execute(
                    f"CREATE TEMP TABLE {DUCKDB.quote(name)} AS SELECT * FROM __sverify_input"
                )
                db.unregister("__sverify_input")
                drops.append(functools.partial(_drop, db, name))
            if not keep:
                return db.sql(sql).to_arrow_table()
            name = Resident.new_name()
            db.execute(f"CREATE TABLE main.{DUCKDB.quote(name)} AS {sql}")
            schema = db.sql(f"SELECT * FROM main.{DUCKDB.quote(name)} LIMIT 0").to_arrow_table()
            return Resident(name, schema.schema)
        finally:
            for drop in drops:
                drop()


def _unregister(db: duckdb.DuckDBPyConnection, name: str) -> None:
    db.unregister(name)


def _drop(db: duckdb.DuckDBPyConnection, name: str) -> None:
    db.execute(f"DROP TABLE IF EXISTS {DUCKDB.quote(name)}")
