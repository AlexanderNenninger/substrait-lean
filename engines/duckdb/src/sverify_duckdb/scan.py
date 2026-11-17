"""DuckDB reads a `sverify._scan.Scan` (#173): the descriptor's files as a
`read_parquet` view or table in a connection.

`Scan` is plain data. This module is the DuckDB engine's one function from a
descriptor to its scan (the Polars and Spark plugins own theirs), and holds the
SQL that does it. The files are read by column name; a column no file has is
NULL, and every column is cast to the type DuckDB gives the schema's Arrow
type, so a plan sees the types it sees on the Arrow table of the same rows.
"""

from __future__ import annotations

import uuid
from collections.abc import Callable
from typing import TYPE_CHECKING

import duckdb
import pyarrow as pa

from sverify._scan import _q

if TYPE_CHECKING:
    from sverify._scan import Scan

FILE, POS = '"__sverify_file"', '"__sverify_pos"'
"""The columns `attach_scan(..., positions=True)` adds (quoted)."""


def lit(s: str) -> str:
    return "'" + s.replace("'", "''") + "'"


def attach_scan(
    scan: Scan,
    db: duckdb.DuckDBPyConnection,
    name: str,
    *,
    table: bool = False,
    positions: bool = False,
) -> Callable[[], None]:
    """Make `name` a temporary view of the scan's rows in `db`, or with `table`
    a temporary table holding them (whose `rowid` numbers the rows in file
    order). With `positions`, each row also has its file (`FILE`) and its
    position in the file (`POS`). Returns the function that drops it again."""
    tag = uuid.uuid4().hex
    deleted = f"__sverify_deleted_{tag}"
    if scan.deleted is not None:
        db.register(deleted, scan.deleted)
    kind = "TABLE" if table else "VIEW"
    try:
        sql = scan_sql(scan, db, deleted, positions)
        db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS {sql}")
    except BaseException:
        if scan.deleted is not None:
            db.unregister(deleted)
        raise

    def drop() -> None:
        db.execute(f"DROP {kind} IF EXISTS {_q(name)}")
        if scan.deleted is not None:
            db.unregister(deleted)

    return drop


def read_scan(scan: Scan) -> pa.Table:
    """The scan's rows as an Arrow table in its schema."""
    db = duckdb.connect()
    try:
        attach_scan(scan, db, "t")
        return db.sql("SELECT * FROM t").to_arrow_table().cast(scan.schema)
    finally:
        db.close()


def scan_sql(
    scan: Scan, db: duckdb.DuckDBPyConnection, deleted: str, positions: bool = False
) -> str:
    """The SELECT over the scan's files: `deleted` names the registered table of
    deleted positions."""
    types = duckdb_types(db, scan.schema)
    names = scan.schema.names
    if not scan.files:
        cols = ", ".join(f"CAST(NULL AS {t}) AS {_q(c)}" for c, t in zip(names, types, strict=True))
        if positions:
            cols += f", CAST(NULL AS VARCHAR) AS {FILE}, CAST(NULL AS BIGINT) AS {POS}"
        return f"SELECT {cols} WHERE FALSE"
    files = "[" + ", ".join(map(lit, scan.files)) + "]"
    options = "union_by_name = true"
    if scan.deleted is not None or positions:
        options += ", filename = true, file_row_number = true"
    source = f"read_parquet({files}, {options})"
    present = {r[0] for r in db.execute(f"DESCRIBE SELECT * FROM {source}").fetchall()}
    cols = ", ".join(
        f"{_column(f, t, present)} AS {_q(f.name)}" for f, t in zip(scan.schema, types, strict=True)
    )
    if positions:
        cols += f", s.filename AS {FILE}, s.file_row_number AS {POS}"
    sql = f"SELECT {cols} FROM {source} s"
    if scan.deleted is not None:
        sql += (
            f" WHERE NOT EXISTS (SELECT 1 FROM {deleted} d"
            " WHERE d.file = s.filename AND d.pos = s.file_row_number)"
        )
    if scan.where is not None:
        sql = f"SELECT * FROM ({sql}) WHERE {scan.where}"
    return sql


def _column(f: pa.Field, t: str, present: set[str]) -> str:
    """Column `f` of a file as type `t`, NULL where no file has it. Doubles
    as `sverify.engine.canonical` makes them: `-0.0` as `0.0`, and every NaN
    the positive one (files may hold others, which DuckDB orders apart)."""
    if f.name not in present:
        return f"CAST(NULL AS {t})"
    col = f"CAST(s.{_q(f.name)} AS {t})"
    if pa.types.is_floating(f.type):
        col = f"CAST(CASE WHEN isnan({col}) THEN 'NaN' ELSE {col} + 0.0 END AS {t})"
    return col


def duckdb_types(db: duckdb.DuckDBPyConnection, schema: pa.Schema) -> list[str]:
    """The DuckDB type of each column of an Arrow table with `schema`."""
    name = f"__sverify_schema_{uuid.uuid4().hex}"
    db.register(name, schema.empty_table())
    try:
        return [r[1] for r in db.execute(f"DESCRIBE {_q(name)}").fetchall()]
    finally:
        db.unregister(name)
