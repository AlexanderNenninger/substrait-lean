"""Sinks written by DuckDB (#173).

Internal: not part of sverify's public API.

When a view keeps its state in DuckDB (`sverify._state.DuckDBStore`), its
Delta and Iceberg sinks have DuckDB write the Parquet files, and sverify
commits them with the contract and the epoch, as it commits the files the
Arrow path writes. The rows never pass through Python:

* `copy` writes rows to a Parquet file, cast to the sink's schema (with
  Iceberg's field ids where asked);
* `positions` finds where in the table's files the rows a change deletes
  are: one copy per deleted copy, by the model's row equality, skipping rows
  already deleted;
* `delta_stats` computes a Delta add action's statistics from a file, as
  delta-rs writes them.

The change is the sum of the view's changes since the state the sink wrote
(`IncrementalView.changes_since`), which `SinkChange.native` hands to DuckDB.
"""

from __future__ import annotations

import json
import math
import threading
import uuid
from datetime import UTC, date, datetime
from typing import Any

import duckdb
import pyarrow as pa

from sverify import _duckdb
from sverify._scan import FILE, POS, Resident, Scan, _duckdb_types, _lit, _q
from sverify._weighted import WEIGHT

_DB: duckdb.DuckDBPyConnection | None = None
_LOCK = threading.Lock()


def _db() -> duckdb.DuckDBPyConnection:
    global _DB
    if _DB is None:
        _DB = _duckdb.cursor()
    _duckdb.collect(_DB)
    return _DB


def _columns(schema: pa.Schema, prefix: str = "") -> str:
    return ", ".join(f"{prefix}{_q(c)}" for c in schema.names)


def inserts_sql(change: Resident, schema: pa.Schema) -> str:
    """The rows a weighted change inserts, each as many times as its weight,
    with the columns of `schema`."""
    return f"SELECT {_columns(schema, 's.')} FROM {change.ref} s, range(s.{_q(WEIGHT)}) " + (
        f"WHERE s.{_q(WEIGHT)} > 0"
    )


def rows_sql(rows: Resident, schema: pa.Schema) -> str:
    return f"SELECT {_columns(schema)} FROM {rows.ref}"


def counts(change: Resident) -> tuple[int, int]:
    """How many rows a weighted change inserts, and how many it deletes."""
    w = _q(WEIGHT)
    with _LOCK:
        row = (
            _db()
            .execute(
                f"SELECT coalesce(sum({w}) FILTER ({w} > 0), 0), "
                f"coalesce(-sum({w}) FILTER ({w} < 0), 0) FROM {change.ref}"
            )
            .fetchall()[0]
        )
    assert row is not None
    return int(row[0]), int(row[1])


def rows_count(rows: Resident) -> int:
    with _LOCK:
        return int(_db().execute(f"SELECT count(*) FROM {rows.ref}").fetchall()[0][0])


def copy(sql: str, path: str, schema: pa.Schema, field_ids: dict[str, int] | None = None) -> int:
    """Write the rows of `sql` (with the columns of `schema`) to the Parquet
    file `path`, in `schema`'s types. Returns the number of rows."""
    with _LOCK:
        db = _db()
        types = _duckdb_types(db, schema)
        cast = ", ".join(
            f"CAST({_q(c)} AS {t}) AS {_q(c)}" for c, t in zip(schema.names, types, strict=True)
        )
        options = "FORMAT parquet"
        if field_ids is not None:
            ids = ", ".join(f"{_q(c)}: {i}" for c, i in field_ids.items())
            options += f", FIELD_IDS {{{ids}}}"
        row = db.execute(
            f"COPY (SELECT {cast} FROM ({sql})) TO {_lit(path)} ({options})"
        ).fetchall()[0]
    return int(row[0]) if row else 0


def rewrite(path: str, gone: pa.Table, new: str, field_ids: dict[str, int] | None = None) -> int:
    """Copy the Parquet file `path` to `new` without the rows at the
    positions `gone` (a table of `pos`), keeping its columns as they are.
    Returns the number of rows left."""
    with _LOCK:
        db = _db()
        name = f"__sverify_gone_{uuid.uuid4().hex}"
        db.register(name, gone)
        try:
            src = (
                f"SELECT * EXCLUDE (file_row_number) FROM "
                f"read_parquet({_lit(path)}, file_row_number = true) "
                f"WHERE file_row_number NOT IN (SELECT pos FROM {name})"
            )
            options = "FORMAT parquet"
            if field_ids is not None:
                ids = ", ".join(f"{_q(c)}: {i}" for c, i in field_ids.items())
                options += f", FIELD_IDS {{{ids}}}"
            row = db.execute(f"COPY ({src}) TO {_lit(new)} ({options})").fetchall()[0]
        finally:
            db.unregister(name)
    return int(row[0]) if row else 0


def positions(scan: Scan, change: Resident) -> pa.Table | None:
    """Where the rows `change` deletes are in the files of `scan`: a table
    of `file` (the scan's local path) and `pos`, with as many positions per
    row as copies it deletes, the first ones in file order. Rows are equal as
    the model compares them (NULLs equal, one NaN, `-0.0` equal to `0.0`).
    None if the files do not hold them all."""
    names = [c for c in change.schema.names if c != WEIGHT]
    w = _q(WEIGHT)
    same = " AND ".join(f"s.{_q(c)} IS NOT DISTINCT FROM d.{_q(c)}" for c in names)
    view = f"__sverify_scan_{uuid.uuid4().hex}"
    with _LOCK:
        db = _db()
        drop = scan.attach(db, view, positions=True)
        try:
            deletes = (
                f"SELECT {', '.join(_q(c) for c in names)}, -{w} AS n, "
                f"row_number() OVER () AS rid FROM {change.ref} WHERE {w} < 0"
            )
            found = (
                f"SELECT s.{FILE} AS file, s.{POS} AS pos, d.n, row_number() OVER "
                f"(PARTITION BY d.rid ORDER BY s.{FILE}, s.{POS}) AS k "
                f"FROM {_q(view)} s JOIN ({deletes}) d ON {same}"
            )
            out = db.sql(
                f"SELECT file, pos FROM ({found}) WHERE k <= n ORDER BY file, pos"
            ).to_arrow_table()
            want = db.execute(f"SELECT coalesce(-sum({w}), 0) FROM {change.ref} WHERE {w} < 0")
            row = want.fetchall()[0]
        finally:
            drop()
    need = int(row[0]) if row else 0
    if out.num_rows != need:
        return None
    return out.cast(pa.schema([("file", pa.string()), ("pos", pa.int64())]))


# -- Delta statistics ---------------------------------------------------------


def _stat(v: Any, t: pa.DataType) -> Any:
    """A bound in Delta's JSON statistics as delta-rs writes them, or None
    for none (NaN and infinities, which JSON cannot hold)."""
    if v is None:
        return None
    if isinstance(v, float):
        return v if math.isfinite(v) else None
    if isinstance(v, datetime):
        if pa.types.is_timestamp(t) and t.tz is not None:  # type: ignore[attr-defined]
            utc = v.astimezone(UTC) if v.tzinfo else v.replace(tzinfo=UTC)
            return utc.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
        return v.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
    if isinstance(v, date):
        return v.isoformat()
    return v


def _bounded(t: pa.DataType) -> bool:
    """Types whose minima and maxima delta-rs records (and sverify reads)."""
    return (
        pa.types.is_integer(t)
        or pa.types.is_boolean(t)
        or pa.types.is_floating(t)
        or pa.types.is_string(t)
        or pa.types.is_large_string(t)
        or pa.types.is_date(t)
        or pa.types.is_timestamp(t)
    )


def float_bounds(path: str, schema: pa.Schema) -> dict[str, tuple[float, float]]:
    """Each double column's smallest and largest value in the Parquet file
    `path`, without NaN (DuckDB's writer records none when a NaN is there;
    pyiceberg's leaves NaN out)."""
    cols = [f.name for f in schema if pa.types.is_floating(f.type)]
    if not cols:
        return {}
    parts = [
        f"min({_q(c)}) FILTER (WHERE NOT isnan({_q(c)})), "
        f"max({_q(c)}) FILTER (WHERE NOT isnan({_q(c)}))"
        for c in cols
    ]
    with _LOCK:
        row = (
            _db()
            .execute(f"SELECT {', '.join(parts)} FROM read_parquet({_lit(path)})")
            .fetchall()[0]
        )
    out = {}
    for i, c in enumerate(cols):
        lo, hi = row[2 * i], row[2 * i + 1]
        if lo is not None and hi is not None:
            out[c] = (lo, hi)
    return out


def delta_stats(path: str, schema: pa.Schema) -> str:
    """A Delta add action's statistics for the Parquet file `path`: the row
    count, and each top-level column's NULL count and bounds (doubles
    without NaN, timestamps truncated to milliseconds, as delta-rs writes
    them; Delta readers allow for the truncation)."""
    flat = [f for f in schema if not pa.types.is_nested(f.type)]
    parts = ["count(*)"]
    for f in flat:
        c = _q(f.name)
        parts.append(f"count(*) - count({c})")
        if _bounded(f.type):
            keep = f" FILTER (WHERE NOT isnan({c}))" if pa.types.is_floating(f.type) else ""
            parts += [f"min({c}){keep}", f"max({c}){keep}"]
    with _LOCK:
        row = (
            _db()
            .execute(f"SELECT {', '.join(parts)} FROM read_parquet({_lit(path)})")
            .fetchall()[0]
        )
    assert row is not None
    values = iter(row)
    stats: dict[str, Any] = {"numRecords": next(values), "minValues": {}, "maxValues": {}}
    nulls: dict[str, int] = {}
    for f in flat:
        nulls[f.name] = next(values)
        if _bounded(f.type):
            lo, hi = _stat(next(values), f.type), _stat(next(values), f.type)
            if lo is not None:
                stats["minValues"][f.name] = lo
            if hi is not None:
                stats["maxValues"][f.name] = hi
    stats["nullCount"] = nulls
    return json.dumps(stats)
