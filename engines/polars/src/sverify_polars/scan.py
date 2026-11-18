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

_FILE, _POS, _HIT = "__sverify_file", "__sverify_pos", "__sverify_hit"
_FIELD_ID = b"PARQUET:field_id"


def lazy_scan(scan: Scan) -> pl.LazyFrame:
    """The scan's rows as a lazy frame in the dtypes of its Arrow schema, in
    the descriptor's file order. A scan with a `where` is refused: a source's
    `where` is DuckDB SQL (`sverify.io._common.filter_rows`), which Polars's SQL
    does not read alike. A scan with `partitions` or `physical` names is refused
    too: Polars does not yet read partition values from the log or physical names
    (#173)."""
    if scan.where is not None:
        raise Unsupported(f"{scan.origin}: a `where` is DuckDB SQL, which Polars does not read")
    if scan.partitions is not None or scan.physical is not None:
        raise Unsupported(f"{scan.origin}: Polars does not read partition values or physical names")
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
    for names, files in _runs(scan, deleted):
        if files[0] in deleted:
            pieces.append(_read(files, names, scan, dtypes, deleted[files[0]]))
        else:
            pieces.append(_read(files, names, scan, dtypes))
    lf = pl.concat(pieces, how="vertical")
    for e in scan.equality:
        lf = _equality(lf, e, dtypes)
    return lf.drop(_FILE)


def _runs(scan: Scan, deleted: dict[str, list[int]]) -> list[tuple[dict[str, str], list[str]]]:
    """The files in the descriptor's order, in runs that one scan reads: files
    named alike (`{physical name: logical name}`, by field id for Iceberg),
    none with deleted positions, which are scanned alone."""
    out: list[tuple[dict[str, str], list[str]]] = []
    for f in scan.files:
        names = _renaming(f, scan)
        if out and out[-1][0] == names and f not in deleted and out[-1][1][0] not in deleted:
            out[-1][1].append(f)
        else:
            out.append((names, [f]))
    return out


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
    """The one conversion `widens` leaves out that Polars reads as the schema's:
    between the string types (`string`, `large_string`, `string_view`, which
    delta-rs writes)."""
    t = pa.types

    def string(x: pa.DataType) -> bool:
        return t.is_string(x) or t.is_large_string(x) or t.is_string_view(x)

    return string(have) and string(want)


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
    (NULLs equal) leave; the order of the rows stays."""
    delete = (
        pl.scan_parquet(e.file)
        .rename(dict(zip(_physical(e), e.columns, strict=True)))
        .select([pl.col(c).cast(dtypes[c]) for c in e.columns])
        .unique()
        .with_columns(pl.lit(True).alias(_HIT))
    )
    joined = lf.join(
        delete, on=list(e.columns), how="left", nulls_equal=True, maintain_order="left"
    )
    gone = pl.col(_FILE).is_in(list(e.applies_to)) & pl.col(_HIT).is_not_null()
    return joined.filter(~gone).drop(_HIT)


def _physical(e: EqualityDelete) -> list[str]:
    """The delete file's column names, by field id."""
    schema = pq.read_schema(e.file)
    by_id = {
        int(f.metadata[_FIELD_ID]): f.name for f in schema if f.metadata and _FIELD_ID in f.metadata
    }
    return [by_id[i] for i in e.ids]
