"""Spark's store (#173 N6b, #1329): a view's state as a generation of Parquet
files that Spark writes and reads, never as a table in the Python process.

The design is the Polars store's (`sverify_polars.store`) on Spark: the handle
(`SparkState`) is a directory of Parquet files in the state location and the
Arrow schema of the weighted table. Every operation makes a new generation:
Spark computes it as a `DataFrame` (`SparkLazy` until it is written) and
writes it with `df.write.parquet`, so on a cluster the rows stay on the
cluster. A generation is deleted once nothing refers to its handle. Merges run
the merge plan on Spark (`Store.merge`), whose own guard raises where a weight
sum leaves 64 bits, with ANSI mode on or off.

The state location is a directory the session and the driver both read: a
temporary directory for the local session (`SVERIFY_STATE_LOCATION` names
another). A cluster needs a location it reads and writes, which N6c's
state-location setting brings.
"""

from __future__ import annotations

import atexit
import contextlib
import os
import shutil
import tempfile
import uuid
import weakref
from collections.abc import Callable, Sequence
from typing import Any

import duckdb
import pyarrow as pa

from sverify._arrow_state import ArrowOps
from sverify._scan import Native, _q
from sverify._store import MERGE_A, MERGE_B, State
from sverify._weighted import WEIGHT

_DIR: str | None = None


def _state_dir() -> str:
    """The state location: `SVERIFY_STATE_LOCATION`, else a directory of the
    process removed at exit."""
    global _DIR
    if _DIR is None:
        given = os.environ.get("SVERIFY_STATE_LOCATION")
        if given:
            os.makedirs(given, exist_ok=True)
            _DIR = given
        else:
            _DIR = tempfile.mkdtemp(prefix="sverify-spark-state-")
            atexit.register(shutil.rmtree, _DIR, ignore_errors=True)
    return _DIR


def _session(*handles: Any) -> Any:
    """The session of the first handle that has one, else the local one."""
    for h in handles:
        if isinstance(h, SparkState | SparkLazy):
            return h.spark
    from sverify_spark import engine

    return engine.session()


class SparkLazy:
    """A weighted table Spark has not computed yet (a run's result, weights
    set on one): a `DataFrame` and its Arrow schema."""

    def __init__(self, df: Any, schema: pa.Schema, spark: Any):
        self.df, self.schema, self.spark = df, schema, spark

    def view(self, spark: Any) -> Any:
        return self.df


class SparkState(Native):
    """A weighted table held as a directory of Parquet files.

    Attributes:
        path: The directory.
        schema: The table's Arrow schema, with `WEIGHT` where it has one.
        spark: The session that wrote it.
    """

    def __init__(self, path: str, schema: pa.Schema, spark: Any, owner: SparkState | None = None):
        self.path, self.schema, self.spark, self._owner = path, schema, spark, owner
        if owner is None:
            weakref.finalize(self, _remove, path)

    def view(self, spark: Any) -> Any:
        """The table as a `DataFrame` over its files: its columns, which can
        be fewer than the files' (`owner` holds them)."""
        return spark.read.parquet(self.path).select(*self.schema.names)

    @property
    def df(self) -> Any:
        return self.view(self.spark)

    def columns(self, names: Sequence[str]) -> SparkState:
        """The table's columns `names`, over the same files."""
        schema = pa.schema([self.schema.field(c) for c in names])
        return SparkState(self.path, schema, self.spark, owner=self._owner or self)

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        kind = "TABLE" if table else "VIEW"
        cols = ", ".join(_q(c) for c in self.schema.names)
        glob = os.path.join(self.path, "*.parquet").replace("'", "''")
        db.execute(
            f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS SELECT {cols} FROM read_parquet('{glob}')"
        )

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")

        return drop

    def to_arrow(self) -> pa.Table:
        return _arrow(self.df, self.schema)

    def readable(self) -> bool:
        return os.path.isdir(self.path)


def _remove(path: str) -> None:
    with contextlib.suppress(OSError):
        shutil.rmtree(path)


def _arrow(df: Any, schema: pa.Schema) -> pa.Table:
    """A `DataFrame`'s rows as an Arrow table in `schema`."""
    return df.toArrow().select(schema.names).cast(schema)


def _frame(z: Any, spark: Any) -> Any:
    """A weighted table of any shape the store meets as a `DataFrame`."""
    if isinstance(z, SparkState | SparkLazy):
        return z.view(spark)
    from sverify_spark import engine

    name = f"__sverify_tmp_{uuid.uuid4().hex}"
    engine.put_tables({name: z}, spark)
    return spark.table(name)


def _write(df: Any, schema: pa.Schema, spark: Any) -> SparkState:
    """A new generation: `df` written to a directory of the state location."""
    path = os.path.join(_state_dir(), f"gen-{uuid.uuid4().hex}")
    df.write.mode("overwrite").parquet(path)
    return SparkState(path, schema, spark)


def lazy_plan(df: Any, spark: Any) -> SparkLazy:
    """The result of a plan, to be written by the merge that adds it to the
    state: its Arrow schema from the frame's own (an empty collect)."""
    return SparkLazy(df, df.limit(0).toArrow().schema, spark)


class SparkStore(ArrowOps):
    """A view's state as generations of Parquet files that Spark writes
    (`SparkState`). A weighted table that is an Arrow table (a change, the
    state per group) is handled as the Arrow store does."""

    keep = True

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        import json

        from sverify.engine import _rename_tables
        from sverify_spark import engine

        spark = _session(a, b)
        names = {MERGE_A: "__sverify_a", MERGE_B: "__sverify_b"}
        p = json.loads(plan)
        _rename_tables(p, names)
        df = engine.run_df(p, {"__sverify_a": a, "__sverify_b": b}, spark)
        df = df.toDF(*schema.names)
        if keep:
            return _write(df, schema, spark)
        return _arrow(df, schema)

    def kept(self, table: pa.Table) -> State:
        spark = _session()
        return _write(_frame(table, spark), table.schema, spark)

    def weighted(self, rows: Any, weight: int = 1) -> State:
        if not isinstance(rows, SparkState | SparkLazy):
            return super().weighted(rows, weight)
        from pyspark.sql import functions as F

        out = pa.schema([*rows.schema, pa.field(WEIGHT, pa.int64())])
        df = rows.view(rows.spark).withColumn(WEIGHT, F.lit(weight).cast("bigint"))
        return SparkLazy(df, out, rows.spark)

    def negated(self, z: State) -> State:
        if not isinstance(z, SparkState | SparkLazy):
            return super().negated(z)
        from pyspark.sql import functions as F

        df = z.view(z.spark).withColumn(WEIGHT, -F.col(WEIGHT))
        return SparkLazy(df, z.schema, z.spark)

    def expanded(self, z: State) -> pa.Table | SparkState:
        """Each row as many times as its weight, as a generation of its own
        (without `WEIGHT`)."""
        if not isinstance(z, SparkState):
            return super().expanded(z)
        from pyspark.sql import functions as F

        names = [c for c in z.schema.names if c != WEIGHT]
        schema = pa.schema([z.schema.field(c) for c in names])
        df = z.df
        if df.filter(F.col(WEIGHT) != 1).limit(1).count() == 0:
            return z.columns(names)  # every row once: the state's own files
        copies = F.explode(F.sequence(F.lit(1), F.col(WEIGHT))).alias("__copy")
        return _write(df.select(*names, copies).drop("__copy"), schema, z.spark)

    def has_negative(self, z: State) -> bool:
        if not isinstance(z, SparkState):
            return super().has_negative(z)
        from pyspark.sql import functions as F

        return z.df.filter(F.col(WEIGHT) < 0).limit(1).count() > 0

    def retire(self, view: Any, column: str, cutoff: Any) -> int:
        z = view.state
        if not isinstance(z, SparkState):
            return super().retire(view, column, cutoff)
        from pyspark.sql import functions as F

        df = z.df
        gone = df.filter(F.col(column) <= cutoff).select(column).distinct().count()
        view.state = _write(df.filter(F.col(column) > cutoff), z.schema, z.spark)
        return int(gone)

    def with_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, SparkState):
            return super().with_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, "left_semi")

    def without_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, SparkState):
            return super().without_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, "left_anti")

    def _by_keys(self, z: SparkState, columns: Sequence[str], keys: Any, how: str) -> State:
        # Spark's joins make every NaN one value and `-0.0` equal to `0.0`
        # (`NormalizeFloatingNumbers`), and `<=>` makes NULLs equal.
        right = _frame(keys, z.spark).toDF(*[f"__k{i}" for i in range(len(columns))])
        left, on = z.df, None
        for i, c in enumerate(columns):
            cond = left[c].eqNullSafe(right[f"__k{i}"])
            on = cond if on is None else on & cond
        out = left.join(right.dropDuplicates(), on, how)
        return _write(out, z.schema, z.spark)
