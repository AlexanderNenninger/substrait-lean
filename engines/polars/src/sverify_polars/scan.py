"""Polars reads a `sverify._scan.Scan` (#173, native scans N4): the descriptor's
Parquet files as a lazy frame, on the streaming engine, without the table
passing through Arrow in the driver.

Route A of the design note (section 3.2), with public Polars API only:
`scan_parquet` over the files (grouped by how their columns are named), the
positions a file lost anti-joined from a scan of that file alone, equality
deletes anti-joined with NULLs equal, and a cast of each column to the type the
Arrow route gives it. A column a file lacks is NULL; a file column whose type
does not widen to the schema's (`sverify._scan.widens`) raises.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import polars as pl
import pyarrow as pa
import pyarrow.parquet as pq

from sverify._scan import widens
from sverify._unsupported import Unsupported

if TYPE_CHECKING:
    from sverify._scan import EqualityDelete, Scan

_FILE, _POS = "__sverify_file", "__sverify_pos"
_FIELD_ID = b"PARQUET:field_id"


def lazy_scan(scan: Scan) -> pl.LazyFrame:
    """The scan's rows as a lazy frame in the dtypes of its Arrow schema."""
    dtypes = pl.from_arrow(scan.schema.empty_table()).schema  # type: ignore[union-attr]
    if not scan.files:
        return pl.LazyFrame(schema=dtypes)
    deleted: dict[str, list[int]] = {}
    if scan.deleted is not None:
        for f, p in zip(
            scan.deleted.column("file").to_pylist(),
            scan.deleted.column("pos").to_pylist(),
            strict=True,
        ):
            deleted.setdefault(f, []).append(p)
    pieces = []
    for names, files in _groups(scan):
        plain = [f for f in files if f not in deleted]
        if plain:
            pieces.append(_read(plain, names, scan, dtypes))
        for f in files:
            if f in deleted:
                pieces.append(_read([f], names, scan, dtypes, deleted[f]))
    lf = pl.concat(pieces, how="vertical")
    for e in scan.equality:
        lf = _equality(lf, e, dtypes)
    lf = lf.drop(_FILE)
    return lf.filter(pl.sql_expr(scan.where)) if scan.where is not None else lf


def _groups(scan: Scan) -> list[tuple[dict[str, str], list[str]]]:
    """The files by the renaming of their columns to the schema's, in file
    order: `{physical name: logical name}` (field ids), identity by name."""
    out: dict[tuple, list[str]] = {}
    maps: dict[tuple, dict[str, str]] = {}
    for f in scan.files:
        names = _renaming(f, scan)
        key = tuple(sorted(names.items()))
        out.setdefault(key, []).append(f)
        maps[key] = names
    return [(maps[k], fs) for k, fs in out.items()]


def _renaming(file: str, scan: Scan) -> dict[str, str]:
    """`{physical: logical}` for the columns of `file` the schema has, and a
    refusal where a type does not widen."""
    schema = pq.read_schema(file)
    by_id = (
        None
        if scan.field_ids is None
        else {i: n for i, n in zip(scan.field_ids, scan.schema.names, strict=True)}
    )
    out = {}
    for f in schema:
        if by_id is None:
            logical = f.name if f.name in scan.schema.names else None
        else:
            raw = (f.metadata or {}).get(_FIELD_ID)
            logical = by_id.get(int(raw)) if raw is not None else None
        if logical is None:
            continue
        want = scan.schema.field(logical).type
        if not widens(f.type, want) and not _same_family(f.type, want):
            raise Unsupported(
                f"{file}: column {logical!r} is {f.type} in the file and {want} in the table"
            )
        out[f.name] = logical
    return out


def _same_family(have: pa.DataType, want: pa.DataType) -> bool:
    """Types `widens` does not cover that Polars reads as the schema's: strings,
    large strings, and the nested and temporal types (cast by Polars)."""
    t = pa.types
    return (
        (t.is_string(have) or t.is_large_string(have))
        and (t.is_string(want) or t.is_large_string(want))
        or (
            not t.is_integer(have)
            and not t.is_floating(have)
            and not t.is_decimal(have)
            and not t.is_integer(want)
            and not t.is_floating(want)
            and not t.is_decimal(want)
        )
    )


def _read(
    files: list[str],
    names: dict[str, str],
    scan: Scan,
    dtypes: pl.Schema,
    positions: list[int] | None = None,
) -> pl.LazyFrame:
    lf = pl.scan_parquet(
        files, include_file_paths=_FILE, row_index_name=_POS if positions is not None else None
    )
    if positions is not None:
        lf = lf.filter(~pl.col(_POS).is_in(positions)).drop(_POS)
    lf = lf.rename(names)
    return lf.select(
        pl.col(_FILE),
        *(
            (pl.col(c) if c in names.values() else pl.lit(None)).cast(dtypes[c]).alias(c)
            for c in scan.schema.names
        ),
    )


def _equality(lf: pl.LazyFrame, e: EqualityDelete, dtypes: pl.Schema) -> pl.LazyFrame:
    """Rows of `e.applies_to` that match a row of the delete file on `e.columns`
    (NULLs equal) leave."""
    delete = (
        pl.scan_parquet(e.file)
        .rename(dict(zip(_physical(e), e.columns, strict=True)))
        .select([pl.col(c).cast(dtypes[c]) for c in e.columns])
    )
    hit = pl.col(_FILE).is_in(list(e.applies_to))
    return pl.concat(
        [
            lf.filter(hit).join(delete, on=list(e.columns), how="anti", nulls_equal=True),
            lf.filter(~hit),
        ],
        how="vertical",
    )


def _physical(e: EqualityDelete) -> list[str]:
    """The delete file's column names, by field id."""
    schema = pq.read_schema(e.file)
    by_id = {
        int(f.metadata[_FIELD_ID]): f.name for f in schema if f.metadata and _FIELD_ID in f.metadata
    }
    return [by_id[i] for i in e.ids]
