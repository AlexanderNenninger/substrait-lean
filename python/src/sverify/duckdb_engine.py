"""DuckDB as an engine, through SQL generated from the plan.

`run` writes the plan as SQL with `sverify.sql.to_sql` (whose semantics are
Lean's `Rel.eval`, see `sverify.sql.core`) and runs it on an in-process
DuckDB database holding the given tables. DuckDB's Substrait extension is not
used.
"""

from __future__ import annotations

import functools
import json
import threading
from collections.abc import Mapping

import pyarrow as pa

try:
    import duckdb
except ImportError as e:
    raise ImportError("the DuckDB engine needs duckdb: pip install 'sverify[duckdb]'") from e

from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB


@functools.lru_cache(maxsize=4096)
def _sql(plan: str, guards: bool = True) -> str:
    """`to_sql` of a JSON plan, memoized: an incremental view runs the same
    delta plans on every batch."""
    return to_sql(json.loads(plan), DUCKDB, guards=guards)


_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()


def run(plan: str | dict, tables: Mapping[str, pa.Table], *, guards: bool = True) -> pa.Table:
    """Run a Substrait JSON plan on DuckDB over `tables`.

    One in-process database serves every call (opening one costs ~10 ms); the
    tables are created for the call and dropped after it. `guards=False`:
    see `sverify.sql.to_sql`."""
    global _DB
    sql = _sql(plan, guards) if isinstance(plan, str) else to_sql(plan, DUCKDB, guards=guards)
    with _LOCK:
        if _DB is None:
            _DB = duckdb.connect()
        db = _DB
        try:
            for name, table in tables.items():
                # A real table (not a view on the Arrow data): `rowid` numbers its
                # rows in insertion order, which `to_sql` uses as the scan order.
                db.register("__sverify_input", table)
                db.execute(f"CREATE TABLE {DUCKDB.quote(name)} AS SELECT * FROM __sverify_input")
                db.unregister("__sverify_input")
            return db.sql(sql).to_arrow_table()
        finally:
            for name in tables:
                db.execute(f"DROP TABLE IF EXISTS {DUCKDB.quote(name)}")
