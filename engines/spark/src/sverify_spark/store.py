"""Spark's store (#173 N6b, #1329, N14): a view's state as parts of Parquet
files that Spark writes and reads, never as a table in the Python process.

The parts, their lifetimes, the compaction rule and the exits that add them up
are `sverify._parts`; this module is what Spark supplies to it (`SparkBackend`).
Spark writes a frame with `df.write.parquet`, so on a cluster the rows stay on
the cluster.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from typing import Any

import pyarrow as pa

from sverify._parts import Backend, Lazy, Part, PartsStore, new_part_path
from sverify._store import MERGE_A, MERGE_B
from sverify._weighted import WEIGHT


class SparkBackend(Backend):
    """Spark's frames (`DataFrame`) over one session."""

    def __init__(self, spark: Any):
        self.spark = spark

    def write(self, frame: Any, schema: pa.Schema, *, merged: bool = False) -> Part:
        # `coalesce` keeps the writer to a few files: a change from Arrow has a
        # task per 10,000 rows, and a file each costs more than the rows do.
        # The plan's own guard raises a weight sum that leaves 64 bits.
        path = new_part_path()
        out = frame.toDF(*schema.names).coalesce(self.spark.sparkContext.defaultParallelism)
        out.write.mode("overwrite").parquet(path)
        return Part(path, schema, self)

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
        import uuid

        from sverify_spark import engine

        name = f"__sverify_tmp_{uuid.uuid4().hex}"
        engine.put_tables({name: table}, self.spark)
        return self.spark.table(name)

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
