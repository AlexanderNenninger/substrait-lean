"""Tables as Parquet files DuckDB reads itself (#173).

Internal: not part of sverify's public API.

A `Scan` is a table format's snapshot as sverify chose its rows: the data
files to read, after sverify's own pruning (#81, #108), the positions
deleted in them (Delta deletion vectors, Iceberg position deletes), the
table's schema and the source's filter. DuckDB reads it with `read_parquet`
(`attach`), so the table never passes through Python; any other consumer gets
the same rows as an Arrow table (`to_arrow`).

The files are read by column name. A column no file has is NULL, and every
column is cast to the type DuckDB gives the schema's Arrow type, so a plan
sees the types it sees on the Arrow table of the same rows. Sources build a
scan only where reading by name gives the rows their own reader gives (no
partition values kept outside the files, no renamed columns).
"""

from __future__ import annotations

import os
import uuid
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING
from urllib.parse import unquote, urlparse

import duckdb
import pyarrow as pa

if TYPE_CHECKING:
    from sverify.contracts import Fact


def local_path(uri: str) -> str | None:
    """The local path a table location or file URI names, or None for
    object stores (which `Scan` does not read)."""
    parsed = urlparse(uri)
    if parsed.scheme == "file":
        return os.path.abspath(unquote(parsed.path))
    if parsed.scheme == "" or (len(parsed.scheme) == 1 and os.name == "nt"):
        return os.path.abspath(uri)
    return None


def _q(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def _lit(s: str) -> str:
    return "'" + s.replace("'", "''") + "'"


@dataclass(frozen=True, eq=False)
class Scan:
    """The rows of a table at one version, as files to read.

    Attributes:
        files: The Parquet files, as local paths.
        schema: The table's schema.
        deleted: The deleted rows: a table with a `file` (one of `files`)
            and a `pos` (int64, the row's position in the file) column, or
            None.
        where: A SQL condition on the columns: the rows are those on which
            it is TRUE. None: every row.
        origin: Where the rows come from, such as `orders@v3`.
    """

    files: tuple[str, ...]
    schema: pa.Schema
    deleted: pa.Table | None = None
    where: str | None = None
    origin: str = ""

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        """Make `name` a temporary view of the rows in `db`, or with `table`
        a temporary table holding them (whose `rowid` numbers the rows in
        file order). Returns the function that drops it again."""
        tag = uuid.uuid4().hex
        deleted = f"__sverify_deleted_{tag}"
        if self.deleted is not None:
            db.register(deleted, self.deleted)
        kind = "TABLE" if table else "VIEW"
        try:
            db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS {self._sql(db, deleted)}")
        except BaseException:
            if self.deleted is not None:
                db.unregister(deleted)
            raise

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")
            if self.deleted is not None:
                db.unregister(deleted)

        return drop

    def readable(self) -> bool:
        """Whether every file is still there (a vacuum removes the files of
        old versions)."""
        return all(os.path.exists(f) for f in self.files)

    def to_arrow(self) -> pa.Table:
        """The rows as an Arrow table in the scan's schema."""
        db = duckdb.connect()
        try:
            self.attach(db, "t")
            return db.sql("SELECT * FROM t").to_arrow_table().cast(self.schema)
        finally:
            db.close()

    def _sql(self, db: duckdb.DuckDBPyConnection, deleted: str) -> str:
        types = _duckdb_types(db, self.schema)
        names = self.schema.names
        if not self.files:
            cols = ", ".join(
                f"CAST(NULL AS {t}) AS {_q(c)}" for c, t in zip(names, types, strict=True)
            )
            return f"SELECT {cols} WHERE FALSE"
        files = "[" + ", ".join(map(_lit, self.files)) + "]"
        options = "union_by_name = true"
        if self.deleted is not None:
            options += ", filename = true, file_row_number = true"
        source = f"read_parquet({files}, {options})"
        present = {r[0] for r in db.execute(f"DESCRIBE SELECT * FROM {source}").fetchall()}
        cols = ", ".join(
            f"{_column(f, t, present)} AS {_q(f.name)}"
            for f, t in zip(self.schema, types, strict=True)
        )
        sql = f"SELECT {cols} FROM {source} s"
        if self.deleted is not None:
            sql += (
                f" WHERE NOT EXISTS (SELECT 1 FROM {deleted} d"
                " WHERE d.file = s.filename AND d.pos = s.file_row_number)"
            )
        if self.where is not None:
            sql = f"SELECT * FROM ({sql}) WHERE {self.where}"
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


def _duckdb_types(db: duckdb.DuckDBPyConnection, schema: pa.Schema) -> list[str]:
    """The DuckDB type of each column of an Arrow table with `schema`."""
    name = f"__sverify_schema_{uuid.uuid4().hex}"
    db.register(name, schema.empty_table())
    try:
        return [r[1] for r in db.execute(f"DESCRIBE {_q(name)}").fetchall()]
    finally:
        db.unregister(name)


@dataclass
class ScanSnapshot:
    """A source's snapshot as a scan: what a source's `_native` returns."""

    version: int
    scan: Scan
    facts: list[Fact] = field(default_factory=list)
