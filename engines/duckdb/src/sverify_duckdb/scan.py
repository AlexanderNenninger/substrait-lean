"""DuckDB reads a `sverify._scan.Scan` (#173): the descriptor's files as a
`read_parquet` view or table in a connection.

`Scan` is plain data. This module is the DuckDB engine's one function from a
descriptor to its scan (the Polars and Spark plugins own theirs), and holds the
SQL that does it. The files are read by column name, by physical name or by field
id (`Scan.physical`, `Scan.field_ids`); a column no file has is NULL, and every
column is cast to the type DuckDB gives the schema's Arrow type, so a plan sees
the types it sees on the Arrow table of the same rows. The partition columns come
from the descriptor's `partitions`, a small table joined on the file name.
"""

from __future__ import annotations

import functools
import uuid
from collections.abc import Callable
from typing import TYPE_CHECKING
from urllib.parse import urlparse

import pyarrow as pa

from sverify._scan import _q

if TYPE_CHECKING:
    import duckdb
else:
    from sverify._duckdb import lazy as duckdb

if TYPE_CHECKING:
    from sverify._scan import EqualityDelete, Scan

#: The option names of `Storage` (delta-rs's) and the fields of DuckDB's S3 secret: the one
#: table from a storage option to this engine.
S3_SECRET = {
    "AWS_ACCESS_KEY_ID": "KEY_ID",
    "AWS_SECRET_ACCESS_KEY": "SECRET",
    "AWS_SESSION_TOKEN": "SESSION_TOKEN",
    "AWS_REGION": "REGION",
}

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
    deleted, parts = f"__sverify_deleted_{tag}", f"__sverify_partitions_{tag}"
    registered = []
    if scan.deleted is not None:
        registered.append((deleted, scan.deleted))
    if scan.partitions is not None:
        registered.append((parts, scan.partitions))
    for n, t in registered:
        db.register(n, t)
    kind = "TABLE" if table else "VIEW"
    if scan.storage is not None:
        attach_secret(db, scan)

    def unregister() -> None:
        for n, _ in registered:
            db.unregister(n)

    try:
        sql = scan_sql(scan, db, deleted, parts, positions)
        db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS {sql}")
    except BaseException:
        unregister()
        raise

    def drop() -> None:
        db.execute(f"DROP {kind} IF EXISTS {_q(name)}")
        unregister()

    return drop


def _store_scheme(uri: str) -> str:
    return urlparse(uri).scheme


def readable_here(options: dict[str, str]) -> bool:
    """Whether DuckDB can read an S3 table opened with `options`: `httpfs` loads,
    and the default credential chain (no explicit key) has the `aws` extension.
    Sverify installs nothing. The answer is cached for the process: an extension
    installed later in the same process is seen at the next start."""
    return _loadable("httpfs") and ("AWS_ACCESS_KEY_ID" in options or _loadable("aws"))


@functools.cache
def _loadable(extension: str) -> bool:
    db = duckdb.connect()
    try:
        db.execute(f"LOAD {extension}")
        return True
    except duckdb.Error:
        return False
    finally:
        db.close()


def attach_secret(db: duckdb.DuckDBPyConnection, scan: Scan) -> None:
    """A temporary, in-memory DuckDB secret in `db` for the S3 prefix of the scan's
    files, from the scan's `storage` as it is now. The values are bound, never
    written into SQL text, and the secret goes with the connection."""
    assert scan.storage is not None
    schemes = {_store_scheme(f) for f in scan.files} - {"", "file"}
    if not schemes:
        return
    if schemes != {"s3"}:
        raise ValueError(f"DuckDB reads s3:// files here, not {sorted(schemes)}")
    options = scan.storage.options()
    for ext in ("httpfs", *(() if "AWS_ACCESS_KEY_ID" in options else ("aws",))):
        try:
            db.execute(f"LOAD {ext}")
        except duckdb.Error as e:
            raise RuntimeError(
                f"DuckDB needs its `{ext}` extension to read an object store: run "
                f"`INSTALL {ext}` (sverify installs nothing)"
            ) from e
    fields: dict[str, str | bool] = {S3_SECRET[k]: v for k, v in options.items() if k in S3_SECRET}
    endpoint = options.get("AWS_ENDPOINT_URL")
    if endpoint:
        parsed = urlparse(endpoint)
        fields["ENDPOINT"] = parsed.netloc or parsed.path
        fields["USE_SSL"] = parsed.scheme != "http" and not _truthy(options, "AWS_ALLOW_HTTP")
        fields["URL_STYLE"] = "path"
    if "KEY_ID" not in fields:
        db.execute(
            "CREATE OR REPLACE TEMPORARY SECRET sverify_s3 (TYPE s3, PROVIDER credential_chain)"
        )
        return
    prefix = _prefix(scan.files)
    columns = ", ".join(f"{n} ?" for n in fields)
    db.execute(
        f"CREATE OR REPLACE TEMPORARY SECRET sverify_s3 (TYPE s3, SCOPE ?, {columns})",
        [prefix, *fields.values()],
    )


def _truthy(options: dict[str, str], key: str) -> bool:
    return options.get(key, "").lower() == "true"


def _prefix(files: tuple[str, ...]) -> str:
    """The longest directory prefix the files share."""
    parts = [f.split("/") for f in files]
    common = parts[0][:-1]
    for p in parts[1:]:
        while common and p[: len(common)] != common:
            common.pop()
    return "/".join(common) + "/"


def read_scan(scan: Scan) -> pa.Table:
    """The scan's rows as an Arrow table in its schema."""
    db = duckdb.connect()
    try:
        attach_scan(scan, db, "t")
        return db.sql("SELECT * FROM t").to_arrow_table().cast(scan.schema)
    finally:
        db.close()


def scan_sql(
    scan: Scan,
    db: duckdb.DuckDBPyConnection,
    deleted: str,
    partitions: str,
    positions: bool = False,
) -> str:
    """The SELECT over the scan's files: `deleted` names the registered table of
    deleted positions, `partitions` that of the partition values."""
    types = duckdb_types(db, scan.schema)
    names = scan.schema.names
    if not scan.files:
        cols = ", ".join(f"CAST(NULL AS {t}) AS {_q(c)}" for c, t in zip(names, types, strict=True))
        if positions:
            cols += f", CAST(NULL AS VARCHAR) AS {FILE}, CAST(NULL AS BIGINT) AS {POS}"
        return f"SELECT {cols} WHERE FALSE"
    files = "[" + ", ".join(map(lit, scan.files)) + "]"
    constant = set() if scan.partitions is None else set(scan.partitions.column_names) - {"file"}
    if scan.field_ids is None:
        options = "union_by_name = true"
    else:
        # By field id: a column a file lacks is NULL, and a type a file has
        # that DuckDB cannot read as the schema's raises.
        fields = ", ".join(
            f"{i}: {{name: {lit(f.name)}, type: {lit(t)}, default_value: NULL}}"
            for i, f, t in zip(scan.field_ids, scan.schema, types, strict=True)
            if f.name not in constant
        )
        options = f"schema = map {{{fields}}}"
    if scan.deleted is not None or scan.equality or positions or constant:
        options += ", filename = true, file_row_number = true"
    source = f"read_parquet({files}, {options})"
    present = {r[0] for r in db.execute(f"DESCRIBE SELECT * FROM {source}").fetchall()}
    cols = []
    for i, (f, t) in enumerate(zip(scan.schema, types, strict=True)):
        if f.name in constant:
            cols.append(f"{_column(f, t, f'c.{_q(f.name)}', True)} AS {_q(f.name)}")
        else:
            file_name = f.name if scan.physical is None else scan.physical[i]
            cols.append(
                f"{_column(f, t, f's.{_q(file_name)}', file_name in present)} AS {_q(f.name)}"
            )
    select = ", ".join(cols)
    if positions:
        select += f", s.filename AS {FILE}, s.file_row_number AS {POS}"
    sql = f"SELECT {select} FROM {source} s"
    if constant:
        sql += f" LEFT JOIN {partitions} c ON c.file = s.filename"
    conds = []
    if scan.deleted is not None:
        conds.append(
            f"NOT EXISTS (SELECT 1 FROM {deleted} d"
            " WHERE d.file = s.filename AND d.pos = s.file_row_number)"
        )
    for e in scan.equality:
        conds.append(_equality(e, scan.schema, types))
    if conds:
        sql += " WHERE " + " AND ".join(conds)
    if scan.where is not None:
        sql = f"SELECT * FROM ({sql}) WHERE {scan.where}"
    return sql


def _equality(e: EqualityDelete, schema: pa.Schema, types: list[str]) -> str:
    """The condition that a row of the data files `e` applies to matches none
    of the delete file's rows on its columns (NULLs equal)."""
    by_name = dict(zip(schema.names, types, strict=True))
    fields = ", ".join(
        f"{i}: {{name: {lit(c)}, type: {lit(by_name[c])}, default_value: NULL}}"
        for i, c in zip(e.ids, e.columns, strict=True)
    )
    same = " AND ".join(f"d.{_q(c)} IS NOT DISTINCT FROM s.{_q(c)}" for c in e.columns)
    files = ", ".join(map(lit, e.applies_to))
    return (
        f"NOT (s.filename IN ({files}) AND EXISTS (SELECT 1 FROM read_parquet({lit(e.file)}, "
        f"schema = map {{{fields}}}) d WHERE {same}))"
    )


def _column(f: pa.Field, t: str, ref: str, present: bool) -> str:
    """Column `f` as type `t` from the SQL reference `ref`, NULL where no file has
    it. Doubles as `sverify.engine.canonical` makes them: `-0.0` as `0.0`, and
    every NaN the positive one (files may hold others, which DuckDB orders apart)."""
    if not present:
        return f"CAST(NULL AS {t})"
    col = f"CAST({ref} AS {t})"
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
