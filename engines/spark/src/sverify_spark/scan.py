"""Spark reads a `sverify._scan.Scan` (#173, native scans N5): the descriptor's
Parquet files as a DataFrame on the session, without the table passing through
Arrow in the driver.

Route A of the design note (section 3.4) with public API that classic and Spark
Connect sessions share: `spark.read.parquet` over the files, grouped by how
their columns are named (Parquet field ids for Iceberg, the table's physical
names for Delta's column mapping, read from the footers in the driver) and by
their partition values (constants from the log, `Scan.partitions`),
`_metadata.row_index` for the positions a file lost, equality deletes
as a null-safe left join, and a cast of each column to the type the Arrow route
gives it. The session's settings stay the user's. A file column whose type does
not widen to the schema's (`sverify._scan.widens`) raises `Unsupported`.

Limit (an interim until N12, which maps field ids on the server): the driver
opens each file's Parquet footer once, to name its columns and read their
types, so the route covers only a filesystem the driver shares with the
session. A path with a scheme other than `file:` is refused before any open,
and on a Spark Connect client, which does not see the server's filesystem, a
local path the client cannot open is refused with that said.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

import pyarrow as pa
import pyarrow.parquet as pq

from sverify._scan import local_path, widens
from sverify._unsupported import Unsupported
from sverify_spark.engine import spark_type

if TYPE_CHECKING:
    from pyspark.sql import DataFrame, SparkSession

    from sverify._scan import EqualityDelete, Scan

_FILE, _POS, _HIT = "__sverify_file", "__sverify_pos", "__sverify_hit"
_FIELD_ID = b"PARQUET:field_id"

POSITIONS_IN_PLAN = 10_000
"""Deleted positions of one file up to this many go into the plan as a literal
list; above it they are a DataFrame the file's rows are anti-joined with, so a
large deletion vector does not bloat a plan (sent over gRPC on Spark Connect)."""


def is_connect(spark: Any) -> bool:
    """Whether `spark` is a Spark Connect client (it has no JVM and does not see
    the server's filesystem)."""
    return type(spark).__module__.startswith("pyspark.sql.connect")


def shares_filesystem(spark: Any) -> bool:
    """Whether the driver and the session share a filesystem, as far as the
    session says: a classic session with a `local` master. A Connect client
    cannot say, and a cluster master is not local."""
    if is_connect(spark):
        return False
    return str(spark.sparkContext.master).startswith("local")


def _footer(path: str, connect: bool) -> pa.Schema:
    """A Parquet file's schema, read in the driver: one open per file, for a
    local path only (decided from the path before any open)."""
    if local_path(path) is None:
        raise Unsupported(
            f"{path}: the driver reads Parquet footers of local files only; reading the "
            "footers on the server is N12 of #173"
        )
    try:
        return pq.read_schema(path)
    except OSError as e:
        where = (
            "the Spark Connect client does not see the server's filesystem, "
            if connect
            else "the driver cannot open it, "
        )
        raise Unsupported(f"{path}: {where}so its columns cannot be read ({e})") from e


def spark_scan(spark: Any, scan: Scan) -> DataFrame:
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
    connect = is_connect(spark)
    constant = _constant(scan)
    values = _partition_values(scan, constant)
    for renaming, files in _runs(scan, deleted, connect, values):
        # The file is tagged with the descriptor's own string: no match between
        # it and the URI the session reports (`s3a://`, percent-encoding, `file:`
        # with one or three slashes) can fail silently. A file an equality
        # delete applies to is read alone, so the tag names it.
        tag = F.lit(files[0] if len(files) == 1 else None).cast("string")
        df = spark.read.parquet(*files).select(
            tag.alias(_FILE),
            F.col("_metadata.row_index").alias(_POS),
            *(F.col(f"`{p}`").alias(logical) for p, logical in renaming.items()),
        )
        if files[0] in deleted:
            gone = deleted[files[0]]
            if len(gone) <= POSITIONS_IN_PLAN:
                df = df.filter(~F.col(_POS).isin(gone))
            else:
                pos = spark.createDataFrame(pa.table({"p": pa.array(gone, pa.int64())}))
                df = df.join(pos, df[_POS] == pos["p"], "left_anti")
        here = dict(zip(constant, values.get(files[0], ()), strict=False))
        pieces.append(
            df.select(
                F.col(_FILE),
                *(
                    (
                        # nullable, as every column of the Arrow route is
                        F.when(F.col(_POS).isNotNull(), F.lit(here[c]))
                        if c in here
                        else F.col(f"`{c}`")
                        if c in renaming.values()
                        else F.lit(None)
                    )
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
        out = _equality(spark, out, e, types, connect)
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


def _constant(scan: Scan) -> list[str]:
    """The partition columns: their values are the log's, one set per file."""
    return (
        [] if scan.partitions is None else [c for c in scan.partitions.column_names if c != "file"]
    )


def _partition_values(scan: Scan, constant: list[str]) -> dict[str, tuple[Any, ...]]:
    """Each file's partition values, in the order of `constant`."""
    if scan.partitions is None:
        return {}
    cols = [scan.partitions.column(c).to_pylist() for c in constant]
    out = dict(
        zip(scan.partitions.column("file").to_pylist(), zip(*cols, strict=True), strict=True)
    )
    # A file without values would read its partition columns as NULL.
    if missing := [f for f in scan.files if f not in out]:
        raise ValueError(f"{scan.origin}: no partition values for {missing[0]}")
    return out


def _runs(
    scan: Scan, deleted: dict[str, list[int]], connect: bool, values: dict[str, tuple[Any, ...]]
) -> list[tuple[dict[str, str], list[str]]]:
    """The files in the descriptor's order, in runs that one read covers: files
    named alike (`{physical name: logical name}`), typed alike (one read infers
    one schema) and partitioned alike, none with deleted positions or under an
    equality delete, which are read alone."""
    alone = set(deleted).union(*(e.applies_to for e in scan.equality))
    out: list[tuple[dict[str, str], list[str]]] = []
    keys: list[tuple[Any, ...]] = []
    for f in scan.files:
        names, kinds = _renaming(f, scan, connect)
        key = (names, kinds, values.get(f))
        if out and keys[-1] == key and f not in alone and out[-1][1][0] not in alone:
            out[-1][1].append(f)
        else:
            out.append((names, [f]))
            keys.append(key)
    return out


def _renaming(file: str, scan: Scan, connect: bool) -> tuple[dict[str, str], tuple[str, ...]]:
    """`{physical: logical}` for the columns of `file` the schema has, and their
    file types, refusing a type that does not widen."""
    by_id = (
        None
        if scan.field_ids is None
        else dict(zip(scan.field_ids, scan.schema.names, strict=True))
    )
    by_name = dict(zip(scan.physical or scan.schema.names, scan.schema.names, strict=True))
    constant = _constant(scan)
    out = {}
    kinds = []
    for f in _footer(file, connect):
        if by_id is None:
            logical = by_name.get(f.name)
        else:
            raw = (f.metadata or {}).get(_FIELD_ID)
            logical = by_id.get(int(raw)) if raw is not None else None
        if logical is None or logical in constant:
            continue
        want = scan.schema.field(logical).type
        if not widens(f.type, want) and not _strings(f.type, want):
            raise Unsupported(
                f"{file}: column {logical!r} is {f.type} in the file and {want} in the table"
            )
        out[f.name] = logical
        kinds.append(f"{f.name}:{f.type}")
    return out, tuple(kinds)


def _strings(have: pa.DataType, want: pa.DataType) -> bool:
    t = pa.types

    def string(x: pa.DataType) -> bool:
        return t.is_string(x) or t.is_large_string(x) or t.is_string_view(x)

    return string(have) and string(want)


def _equality(
    spark: SparkSession, df: DataFrame, e: EqualityDelete, types: dict[str, str], connect: bool
) -> DataFrame:
    """Rows of `e.applies_to` that match a row of the delete file on `e.columns`
    (NULLs equal) leave."""
    from pyspark.sql import functions as F

    by_id = {
        int(f.metadata[_FIELD_ID]): f.name
        for f in _footer(e.file, connect)
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
