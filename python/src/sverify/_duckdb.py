"""The process's DuckDB database (#173).

Internal: not part of sverify's public API.

One in-memory database serves every connection's Ibis backend, the DuckDB
engine and the weighted-table helpers, each through a cursor of its own: a
cursor's registered tables, temporary tables and settings are its own. A
database per connection would start a thread pool per connection, which
lives until the cyclic garbage collector frees the connection (its backend
refers back to it): a few hundred connections reach macOS's per-process
thread limit.

Tables DuckDB holds between calls (`sverify._scan.Resident`, such as a view's
state) live in the database's main schema under names of their own, so every
cursor reads them. A resident's table is dropped once nothing refers to it:
the garbage collector queues it (`forget`), and the next cursor that asks
(`collect`) drops it, since a finalizer may run while a cursor is busy.
"""

from __future__ import annotations

import threading

import duckdb

_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()
_GONE: list[tuple[str, str]] = []


def cursor() -> duckdb.DuckDBPyConnection:
    """A new connection to the process's database."""
    global _DB
    with _LOCK:
        if _DB is None:
            _DB = duckdb.connect()
        return _DB.cursor()


def forget(name: str, kind: str) -> None:
    """Queue resident `name` (a `TABLE` or `VIEW`) to be dropped."""
    with _LOCK:
        _GONE.append((name, kind))


def collect(db: duckdb.DuckDBPyConnection) -> None:
    """Drop the residents nothing refers to any more, through `db`."""
    with _LOCK:
        gone = list(_GONE)
        _GONE.clear()
    # Views first: one may read a table dropped in the same batch.
    for name, kind in sorted(gone, key=lambda g: g[1] != "VIEW"):
        db.execute(f'DROP {kind} IF EXISTS main."{name}"')
