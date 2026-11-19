"""Spark's store (#173 N6b, #1329, N14): a view's state as parts of Parquet
files that Spark writes and reads, never as a table in the Python process.

The parts, their lifetimes, the compaction rule and the exits that add them up
are `sverify._parts`; this module is what Spark supplies to it (`SparkBackend`).
Spark writes a frame with `df.write.parquet`, so on a cluster the rows stay on
the cluster.
"""

from __future__ import annotations

import contextlib
import glob
import json
import os
from collections.abc import Iterator, Sequence
from typing import Any

import pyarrow as pa

from sverify._parts import Backend, Lazy, Part, PartsStore
from sverify._store import MERGE_A, MERGE_B
from sverify._weighted import WEIGHT

#: The bytes of state one shuffle partition of a consolidation holds.
PARTITION_BYTES = 128 * 2**20

#: The most shuffle partitions a consolidation asks for.
MAX_PARTITIONS = 4096


class SparkBackend(Backend):
    """Spark's frames (`DataFrame`) over one session."""

    def __init__(self, spark: Any):
        self.spark = spark

    def remove(self, path: str) -> None:
        if "://" not in path:
            return super().remove(path)
        jvm = self.spark._jvm
        target = jvm.org.apache.hadoop.fs.Path(path)
        fs = target.getFileSystem(self.spark._jsc.hadoopConfiguration())
        with contextlib.suppress(Exception):  # a part that is gone already
            fs.delete(target, True)

    def shuffle_partitions(self, parts: Sequence[Part]) -> int | None:
        """How many shuffle partitions adding `parts` up wants: one per
        `PARTITION_BYTES` of their files, at least the session's parallelism.
        None where the driver cannot see the files."""
        if any("://" in p.path for p in parts):
            return None
        size = sum(
            os.path.getsize(f) for p in parts for f in glob.glob(os.path.join(p.path, "*.parquet"))
        )
        wanted = -(-size // PARTITION_BYTES)
        return int(min(MAX_PARTITIONS, max(self.spark.sparkContext.defaultParallelism, wanted)))

    @contextlib.contextmanager
    def sized(self, parts: Sequence[Part]) -> Iterator[None]:
        key = "spark.sql.shuffle.partitions"
        n = self.shuffle_partitions(parts)
        before = self.spark.conf.get(key, None)
        if n is not None:
            self.spark.conf.set(key, str(n))
        try:
            yield
        finally:
            if n is not None:
                if before is None:
                    self.spark.conf.unset(key)
                else:
                    self.spark.conf.set(key, before)

    def write(self, frame: Any, schema: pa.Schema, path: str, *, merged: bool = False) -> None:
        # `coalesce` keeps the writer to a few files: a change from Arrow has a
        # task per 10,000 rows, and a file each costs more than the rows do.
        # The plan's own guard raises a weight sum that leaves 64 bits.
        out = frame.toDF(*schema.names).coalesce(self.spark.sparkContext.defaultParallelism)
        out.write.mode("overwrite").parquet(path)

    def read(self, parts: Sequence[Part], schema: pa.Schema) -> Any:
        return self.spark.read.parquet(*[p.path for p in parts]).select(*schema.names)

    def run(self, plan: str, schema: pa.Schema, a: Any, b: Any) -> Any:
        from sverify.engine import _rename_tables
        from sverify_spark import engine

        names = {MERGE_A: "__sverify_a", MERGE_B: "__sverify_b"}
        p = json.loads(plan)
        _rename_tables(p, names)
        tables = {names[MERGE_A]: Lazy(a, schema, self), names[MERGE_B]: Lazy(b, schema, self)}
        return engine.run_df(p, tables, self.spark).toDF(*schema.names)

    def arrow(self, frame: Any, schema: pa.Schema, *, merged: bool = False) -> pa.Table:
        return frame.toArrow().select(schema.names).cast(schema)

    def frame(self, table: pa.Table) -> Any:
        from sverify_spark import engine

        return engine.arrow_frame(table, self.spark)

    def measure(self, path: str, weighted: bool) -> tuple[int, int | None, int | None]:
        from pyspark.sql import functions as F

        df = self.spark.read.parquet(path)
        if not weighted:
            return df.count(), None, None
        r = df.agg(F.count(F.lit(1)), F.min(WEIGHT), F.max(WEIGHT)).first()
        return (
            int(r[0]),
            (None if r[1] is None else int(r[1])),
            (None if r[2] is None else int(r[2])),
        )

    def with_weight(self, frame: Any, weight: int) -> Any:
        from pyspark.sql import functions as F

        return frame.withColumn(WEIGHT, F.lit(weight).cast("bigint"))

    def negate(self, frame: Any) -> Any:
        from pyspark.sql import functions as F

        return frame.withColumn(WEIGHT, -F.col(WEIGHT))

    def copies(self, frame: Any, names: Sequence[str]) -> Any:
        from pyspark.sql import functions as F

        # `sequence(1, w)` has w copies for w >= 1.
        copies = F.explode(F.sequence(F.lit(1), F.col(WEIGHT))).alias("__copy")
        return frame.select(*names, copies).drop("__copy")

    def filtered(
        self, left: Any, schema: pa.Schema, columns: Sequence[str], keys: Any, *, anti: bool
    ) -> Any:
        # Spark's joins make every NaN one value and `-0.0` equal to `0.0`
        # (`NormalizeFloatingNumbers`), and `<=>` makes NULLs equal.
        right = keys.toDF(*[f"__k{i}" for i in range(len(columns))])
        on = None
        for i, c in enumerate(columns):
            cond = left[c].eqNullSafe(right[f"__k{i}"])
            on = cond if on is None else on & cond
        return left.join(right.dropDuplicates(), on, "left_anti" if anti else "left_semi")

    def split(self, frame: Any, column: str, cutoff: Any) -> tuple[int, Any]:
        from pyspark.sql import functions as F

        gone = frame.filter(F.col(column) <= cutoff).select(column).distinct().count()
        return int(gone), frame.filter(F.col(column) > cutoff)


def lazy_plan(df: Any, spark: Any) -> Lazy:
    """The result of a plan, to be written by the merge that adds it to the
    state: its Arrow schema from the frame's own (an empty collect)."""
    return Lazy(df, df.limit(0).toArrow().schema, SparkBackend(spark))


class SparkStore(PartsStore):
    """A view's state as parts of Parquet files that Spark writes."""

    def default_backend(self) -> Backend:
        from sverify_spark import engine

        return SparkBackend(engine.session())
