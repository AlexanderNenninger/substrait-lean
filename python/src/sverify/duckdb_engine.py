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
from collections.abc import Callable, Mapping
from typing import Literal, overload

import duckdb
import pyarrow as pa

from sverify import _duckdb
from sverify._scan import Native, Resident
from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB


@functools.lru_cache(maxsize=4096)
def _sql(plan: str, guards: bool = True) -> str:
    """`to_sql` of a JSON plan, memoized: an incremental view runs the same
    delta plans on every batch."""
    return to_sql(json.loads(plan), DUCKDB, guards=guards)


_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()


@overload
def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: Literal[False] = False,
) -> pa.Table: ...


@overload
def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: Literal[True],
) -> Resident: ...


def run(
    plan: str | dict,
    tables: Mapping[str, pa.Table | Native],
    *,
    guards: bool = True,
    keep: bool = False,
) -> pa.Table | Resident:
    """Run a Substrait JSON plan on DuckDB over `tables`: Arrow tables, or
    tables DuckDB reads where they are (`sverify._scan.Native`: Parquet
    files, or tables it holds). With `keep`, the result stays in DuckDB, as
    a `Resident` table.

    The process's database serves every call (`sverify._duckdb`; opening
    one costs ~10 ms), through a cursor of the engine's own; the tables are
    created for the call, as temporary tables, and dropped after it.
    `guards=False`: see `sverify.sql.to_sql`."""
    global _DB
    sql = _sql(plan, guards) if isinstance(plan, str) else to_sql(plan, DUCKDB, guards=guards)
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


def _drop(db: duckdb.DuckDBPyConnection, name: str) -> None:
    db.execute(f"DROP TABLE IF EXISTS {DUCKDB.quote(name)}")
