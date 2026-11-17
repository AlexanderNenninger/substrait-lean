"""Tables DuckDB reads or holds itself (#173): Parquet files, and tables
it keeps between calls.

Internal: not part of sverify's public API.

A `Native` table is one that DuckDB reads where it is, instead of an Arrow
table handed to it. A connection holds one like an Arrow table
(`sverify.engine.Connection.get`); DuckDB attaches it to the cursor that
runs a plan (`attach`), and every other consumer reads it into Arrow
(`to_arrow`). There are two kinds: a `Scan` of Parquet files, and a
`Resident` table in the process's database (`sverify._duckdb`).

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
import weakref
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING
from urllib.parse import unquote, urlparse

import duckdb
import pyarrow as pa

from sverify import _duckdb

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


class Native:
    """A table DuckDB reads where it is, with its Arrow `schema`."""

    schema: pa.Schema

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        """Make `name` a temporary view of the rows in `db`, or with `table`
        a temporary table holding them (whose `rowid` numbers the rows in
        order). Returns the function that drops it again."""
        raise NotImplementedError

    def to_arrow(self) -> pa.Table:
        """The rows as an Arrow table in the table's schema."""
        raise NotImplementedError

    def readable(self) -> bool:
        """Whether the rows can still be read."""
        return True


class Resident(Native):
    """A table DuckDB holds between calls, in the main schema of the
    process's database (`sverify._duckdb`), such as a view's state. An
    operation on it makes a new one, except that a refresh updates a view's
    state in place (`sverify._state.DuckDBStore.apply`). Its table is dropped
    once nothing refers to the `Resident`.

    Attributes:
        name: The table's (or view's) name in the main schema.
        schema: Its schema, as DuckDB gives it to Arrow.
        kind: `"TABLE"`, or `"VIEW"` for a view of other residents, which
            it keeps alive (`reads`).
    """

    def __init__(
        self,
        name: str,
        schema: pa.Schema,
        kind: str = "TABLE",
        reads: tuple[Resident, ...] = (),
    ):
        self.name, self.schema, self.kind, self.reads = name, schema, kind, reads
        weakref.finalize(self, _duckdb.forget, name, kind)

    @staticmethod
    def new_name() -> str:
        return f"__sverify_resident_{uuid.uuid4().hex}"

    @property
    def ref(self) -> str:
        """The table's qualified name, for SQL."""
        return f"main.{_q(self.name)}"

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        kind = "TABLE" if table else "VIEW"
        db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS SELECT * FROM {self.ref}")

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")

        return drop

    def to_arrow(self) -> pa.Table:
        db = _duckdb.cursor()
        try:
            return db.sql(f"SELECT * FROM {self.ref}").to_arrow_table().cast(self.schema)
        finally:
            db.close()

    def __repr__(self) -> str:
        return f"Resident({self.name!r}, {self.kind})"


@dataclass(eq=False)
class Scan(Native):
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
        self,
        db: duckdb.DuckDBPyConnection,
        name: str,
        *,
        table: bool = False,
        positions: bool = False,
    ) -> Callable[[], None]:
        """DuckDB's view or table of the rows (`sverify_duckdb.scan.attach_scan`)."""
        from sverify_duckdb.scan import attach_scan

        return attach_scan(self, db, name, table=table, positions=positions)

    def readable(self) -> bool:
        """Whether every file is still there (a vacuum removes the files of
        old versions)."""
        return all(os.path.exists(f) for f in self.files)

    def to_arrow(self) -> pa.Table:
        """The rows as an Arrow table in the scan's schema: the reference reader,
        what an engine's scan of this descriptor must equal."""
        from sverify_duckdb.scan import read_scan

        return read_scan(self)


@dataclass
class ScanSnapshot:
    """A source's snapshot as a scan: what a source's `_native` returns."""

    version: int
    scan: Scan
    facts: list[Fact] = field(default_factory=list)
