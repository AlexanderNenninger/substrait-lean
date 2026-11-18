"""Spark reads a `sverify._scan.Scan` (#173, native scans N5): the descriptor's
Parquet files as a DataFrame on the session, without the table passing through
Arrow in the driver.

Route A of the design note (section 3.4) with public API that classic and Spark
Connect sessions share: `spark.read.parquet` over the files, grouped by how
their columns are named (Parquet field ids for Iceberg, read from the footers in
the driver), `_metadata.row_index` for the positions a file lost, equality deletes
as a null-safe left join, and a cast of each column to the type the Arrow route
gives it. The session's settings stay the user's. A file column whose type does
not widen to the schema's (`sverify._scan.widens`) raises `Unsupported`.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

import pyarrow as pa
import pyarrow.parquet as pq

from sverify._scan import widens
from sverify._unsupported import Unsupported
from sverify_spark.engine import spark_type

if TYPE_CHECKING:
    from pyspark.sql import DataFrame, SparkSession

    from sverify._scan import EqualityDelete, Scan

_FILE, _POS, _HIT = "__sverify_file", "__sverify_pos", "__sverify_hit"
_FIELD_ID = b"PARQUET:field_id"


def spark_scan(spark: SparkSession, scan: Scan) -> DataFrame:
    """The scan's rows as a DataFrame of `spark_type` columns. A scan with a
    `where` is refused: a source's `where` is DuckDB SQL, not Spark's."""
    from pyspark.sql import functions as F

    if scan.where is not None:
        raise Unsupported(f"{scan.origin}: a `where` is DuckDB SQL, which Spark does not read")
    names = scan.schema.names
    types = {f.name: spark_type(f.type) for f in scan.schema}
    if not scan.files:
        empty = ", ".join(f"`{n}` {types[n]}" for n in names)
        return spark.createDataFrame([], empty)
    deleted: dict[str, list[int]] = {}
    if scan.deleted is not None:
        for f, p in zip(
            scan.deleted.column("file").to_pylist(),
            scan.deleted.column("pos").to_pylist(),
            strict=True,
        ):
            deleted.setdefault(f, []).append(p)
    pieces = []
    for renaming, files in _runs(scan, deleted):
        df = spark.read.parquet(*files).select(
            "*",
            F.regexp_replace(F.col("_metadata.file_path"), "^file:/+", "/").alias(_FILE),
            F.col("_metadata.row_index").alias(_POS),
        )
        if files[0] in deleted:
            df = df.filter(~F.col(_POS).isin(deleted[files[0]]))
        df = df.drop(_POS)
        for physical, logical in renaming.items():
            if physical != logical:
                df = df.withColumnRenamed(physical, logical)
        pieces.append(
            df.select(
                F.col(_FILE),
                *(
                    (F.col(f"`{c}`") if c in renaming.values() else F.lit(None))
                    .cast(types[c])
                    .alias(c)
                    for c in names
                ),
            )
        )
    out = pieces[0]
    for p in pieces[1:]:
        out = out.unionAll(p)
    for e in scan.equality:
        out = _equality(spark, out, e, types)
    out = out.drop(_FILE)
    # The Arrow route reads doubles as the model has them: `-0.0` as `0.0` and one NaN.
    doubles = [f.name for f in scan.schema if pa.types.is_floating(f.type)]
    return out.select(
        *(
            F.when(F.isnan(F.col(f"`{c}`")), F.lit(float("nan")))
            .otherwise(F.col(f"`{c}`") + F.lit(0.0))
            .alias(c)
            if c in doubles
            else F.col(f"`{c}`")
            for c in names
        )
    )


def _runs(scan: Scan, deleted: dict[str, list[int]]) -> list[tuple[dict[str, str], list[str]]]:
    """The files in the descriptor's order, in runs that one read covers: files
    named alike (`{physical name: logical name}`), none with deleted positions."""
    out: list[tuple[dict[str, str], list[str]]] = []
    for f in scan.files:
        names = _renaming(f, scan)
        if out and out[-1][0] == names and f not in deleted and out[-1][1][0] not in deleted:
            out[-1][1].append(f)
        else:
            out.append((names, [f]))
    return out


def _renaming(file: str, scan: Scan) -> dict[str, str]:
    """`{physical: logical}` for the columns of `file` the schema has, refusing a
    type that does not widen."""
    by_id = (
        None
        if scan.field_ids is None
        else dict(zip(scan.field_ids, scan.schema.names, strict=True))
    )
    out = {}
    for f in pq.read_schema(file):
        if by_id is None:
            logical = f.name if f.name in scan.schema.names else None
        else:
            raw = (f.metadata or {}).get(_FIELD_ID)
            logical = by_id.get(int(raw)) if raw is not None else None
        if logical is None:
            continue
        want = scan.schema.field(logical).type
        if not widens(f.type, want) and not _strings(f.type, want):
            raise Unsupported(
                f"{file}: column {logical!r} is {f.type} in the file and {want} in the table"
            )
        out[f.name] = logical
    return out


def _strings(have: pa.DataType, want: pa.DataType) -> bool:
    t = pa.types

    def string(x: pa.DataType) -> bool:
        return t.is_string(x) or t.is_large_string(x) or t.is_string_view(x)

    return string(have) and string(want)


def _equality(
    spark: SparkSession, df: DataFrame, e: EqualityDelete, types: dict[str, str]
) -> DataFrame:
    """Rows of `e.applies_to` that match a row of the delete file on `e.columns`
    (NULLs equal) leave."""
    from pyspark.sql import functions as F

    by_id = {
        int(f.metadata[_FIELD_ID]): f.name
        for f in pq.read_schema(e.file)
        if f.metadata and _FIELD_ID in f.metadata
    }
    keys = spark.read.parquet(e.file)
    keys = keys.select(
        *(
            F.col(f"`{by_id[i]}`").cast(types[c]).alias(f"__d_{c}")
            for i, c in zip(e.ids, e.columns, strict=True)
        )
    ).dropDuplicates()
    keys = keys.withColumn(_HIT, F.lit(True))
    same: Any = None
    for c in e.columns:
        eq = F.col(f"`{c}`").eqNullSafe(F.col(f"__d_{c}"))
        same = eq if same is None else same & eq
    joined = df.join(keys, same, "left")
    gone = F.col(_FILE).isin(list(e.applies_to)) & F.col(_HIT).isNotNull()
    return joined.filter(~gone).drop(_HIT, *(f"__d_{c}" for c in e.columns))
