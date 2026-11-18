"""Spark's store (#173 N6b, #1329): a view's state as Parquet files that Spark
writes and reads, never as a table in the Python process.

A state (`SparkState`) is a list of parts: directories of Parquet files, each
with its own lifetime (a part is deleted once no handle holds it), and the
Arrow schema of the weighted table they hold. The table is the sum of the
parts: their union, with the weights of equal rows added. A merge with `keep`
writes the change as a new part and leaves the others where they are, so a
refresh costs the change and not the state. The Lean merge plan (`Store.merge`:
union, group by every column, add the weights, drop zeros) adds the parts up:

- when something reads the table: `view`, `attach`, `to_arrow`, `retire`, and
  `expanded` or `has_negative` unless the parts alone answer (below). No row
  and no answer leaves a state whose parts are not added up;
- when the parts passed a bound (`needs_compaction`): the rows added since the
  last time hold as many rows as that sum, or there are more than `MAX_PARTS`
  parts. The files on disk then stay within about twice the consolidated
  state.

An operation that is linear in the weights runs on the parts as they are:
`negated`, the key filters of `with_keys` and `without_keys` (a filter of an
added-up state stays added up) and `expanded` where every weight of every part
is positive (a row is as many copies as its weights add up to). A weight sum
that leaves 64 bits is raised by the plan's own guard, at the merge that adds
the parts up, which can be later than the refresh that caused it; no answer
comes from such a state. The plan is the one definition of row equality:
nothing else adds weights.

The state location is a directory the session and the driver both read: a
temporary directory for the local session (`SVERIFY_STATE_LOCATION` names
another). A part's row count and weight range come from its Parquet footers,
which the driver reads where it can see the files; elsewhere a Spark job
measures them. A cluster needs a location it reads and writes, which N6c's
state-location setting brings.
"""

from __future__ import annotations

import atexit
import contextlib
import glob
import json
import os
import shutil
import tempfile
import uuid
import weakref
from collections.abc import Callable, Sequence
from typing import TYPE_CHECKING, Any

import pyarrow as pa
import pyarrow.parquet as pq

from sverify._arrow_state import ArrowOps
from sverify._scan import Native, _q
from sverify._store import MERGE_A, MERGE_B, State
from sverify._weighted import WEIGHT

if TYPE_CHECKING:
    import duckdb

#: More parts than this are added up.
MAX_PARTS = 16

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
    set on one, a state's rows as they lie): a `DataFrame` and its Arrow
    schema. Nothing is added up in it; a merge writes it as a part."""

    def __init__(self, df: Any, schema: pa.Schema, spark: Any):
        self.df, self.schema, self.spark = df, schema, spark

    def view(self, spark: Any) -> Any:
        return self.df


def _remove(path: str) -> None:
    with contextlib.suppress(OSError):
        shutil.rmtree(path)


class Part:
    """A directory of Parquet files, deleted with its last holder.

    Attributes:
        path: The directory.
        rows: How many rows it holds.
        low: The least weight in it, None if it has no weight column.
        high: The greatest weight in it, None if it has none.
    """

    def __init__(self, path: str, schema: pa.Schema, spark: Any):
        self.path = path
        weakref.finalize(self, _remove, path)
        self.rows, self.low, self.high = self._measure(schema, spark)

    def _measure(self, schema: pa.Schema, spark: Any) -> tuple[int, int | None, int | None]:
        weighted = WEIGHT in schema.names
        if "://" not in self.path:
            try:
                return _footers(glob.glob(os.path.join(self.path, "*.parquet")), weighted)
            except (OSError, ValueError, LookupError):
                pass
        from pyspark.sql import functions as F

        df = spark.read.parquet(self.path)
        if not weighted:
            return df.count(), None, None
        r = df.agg(F.count(F.lit(1)), F.min(WEIGHT), F.max(WEIGHT)).first()
        return (
            int(r[0]),
            (None if r[1] is None else int(r[1])),
            (None if r[2] is None else int(r[2])),
        )


def _footers(files: list[str], weighted: bool) -> tuple[int, int | None, int | None]:
    """The rows and the weight range of Parquet files, from their footers."""
    rows, low, high = 0, None, None
    for f in files:
        pf = pq.ParquetFile(f)
        meta = pf.metadata
        rows += meta.num_rows
        if not weighted or meta.num_rows == 0:
            continue
        i = pf.schema_arrow.names.index(WEIGHT)
        for g in range(meta.num_row_groups):
            s = meta.row_group(g).column(i).statistics
            if s is None or not s.has_min_max:
                raise LookupError("no statistics")
            low = s.min if low is None else min(low, s.min)
            high = s.max if high is None else max(high, s.max)
    return rows, low, high


def _part(df: Any, schema: pa.Schema, spark: Any) -> Part:
    """A new part: `df` (the columns of `schema`) written to a directory of
    the state location."""
    path = os.path.join(_state_dir(), f"part-{uuid.uuid4().hex}")
    df.toDF(*schema.names).write.mode("overwrite").parquet(path)
    return Part(path, schema, spark)


def _raw(z: Any, spark: Any) -> Any:
    """A weighted table of any shape the store meets as a `DataFrame`, its
    parts as they lie (not added up)."""
    if isinstance(z, SparkState):
        return z.raw(spark)
    if isinstance(z, SparkLazy):
        return z.df
    from sverify_spark import engine

    name = f"__sverify_tmp_{uuid.uuid4().hex}"
    engine.put_tables({name: z}, spark)
    return spark.table(name)


def _input(z: Any, spark: Any) -> Any:
    """A table for the merge plan: an Arrow table as it is, a state's parts as
    they lie."""
    if isinstance(z, SparkState | SparkLazy):
        return SparkLazy(_raw(z, spark), z.schema, spark)
    return z


def _run(plan: str, schema: pa.Schema, spark: Any, a: Any, b: Any) -> Any:
    """The merge plan over `a` and `b`, as a `DataFrame` with the names of
    `schema`."""
    from sverify.engine import _rename_tables
    from sverify_spark import engine

    names = {MERGE_A: "__sverify_a", MERGE_B: "__sverify_b"}
    p = json.loads(plan)
    _rename_tables(p, names)
    return engine.run_df(p, {names[MERGE_A]: a, names[MERGE_B]: b}, spark).toDF(*schema.names)


class SparkState(Native):
    """A weighted table held as parts of Parquet files.

    Attributes:
        parts: The parts; the table is their sum.
        schema: The table's Arrow schema, with `WEIGHT` where it has one.
        spark: The session that wrote it.
        plan: The merge plan that adds the parts up.
        consolidated: Whether the parts are added up already (one part, equal
            rows once, no zero weight).
        base: Whether the first part is an added-up state that the others
            came after.
    """

    def __init__(
        self,
        parts: Sequence[Part],
        schema: pa.Schema,
        spark: Any,
        *,
        plan: str | None = None,
        consolidated: bool = False,
        base: bool = False,
    ):
        self.parts, self.schema, self.spark = tuple(parts), schema, spark
        self.plan, self.base = plan, base
        # Plain rows (no weight column) have nothing to add up.
        self.consolidated = consolidated or WEIGHT not in schema.names

    def raw(self, spark: Any) -> Any:
        """The union of the parts as they lie, in the state's columns."""
        if not self.parts:
            return _raw(self.schema.empty_table(), spark)
        return spark.read.parquet(*[p.path for p in self.parts]).select(*self.schema.names)

    def needs_compaction(self) -> bool:
        """The parts are added up when they are many, or when the rows added
        since the base are as many as the base holds."""
        if self.consolidated:
            return False
        if len(self.parts) > MAX_PARTS:
            return True
        if not self.base or not self.parts[0].rows:
            return False
        return sum(p.rows for p in self.parts[1:]) >= self.parts[0].rows

    def consolidate(self) -> SparkState:
        """Adds the parts up by the merge plan, into one part (in place)."""
        if self.consolidated:
            return self
        assert self.plan is not None, (
            "parts that are not added up come with the plan that adds them"
        )
        a = SparkLazy(self.raw(self.spark), self.schema, self.spark)
        df = _run(self.plan, self.schema, self.spark, a, self.schema.empty_table())
        self.parts = (_part(df, self.schema, self.spark),)
        self.consolidated = self.base = True
        return self

    def range(self) -> tuple[int | None, int | None]:
        """The least and the greatest weight over the parts."""
        lows = [p.low for p in self.parts if p.low is not None]
        highs = [p.high for p in self.parts if p.high is not None]
        return (min(lows) if lows else None, max(highs) if highs else None)

    def positive(self) -> bool:
        """Every weight of every part is positive, so the weights of equal
        rows add up to a positive weight."""
        low, _ = self.range()
        return low is None or low > 0

    def view(self, spark: Any) -> Any:
        """The table as a `DataFrame` over its files (added up first)."""
        return self.consolidate().raw(spark)

    @property
    def df(self) -> Any:
        return self.view(self.spark)

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        self.consolidate()
        kind = "TABLE" if table else "VIEW"
        if self.parts:
            cols = ", ".join(_q(c) for c in self.schema.names)
            globs = ", ".join(
                "'" + os.path.join(p.path, "*.parquet").replace("'", "''") + "'" for p in self.parts
            )
            body = f"SELECT {cols} FROM read_parquet([{globs}])"
        else:
            body = (
                "SELECT "
                + ", ".join(f"NULL AS {_q(c)}" for c in self.schema.names)
                + " WHERE false"
            )
        db.execute(f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS {body}")

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")

        return drop

    def to_arrow(self) -> pa.Table:
        return _arrow(self.df, self.schema)

    def readable(self) -> bool:
        return all(os.path.isdir(p.path) for p in self.parts)


def _arrow(df: Any, schema: pa.Schema) -> pa.Table:
    """A `DataFrame`'s rows as an Arrow table in `schema`."""
    return df.toArrow().select(schema.names).cast(schema)


def lazy_plan(df: Any, spark: Any) -> SparkLazy:
    """The result of a plan, to be written by the merge that adds it to the
    state: its Arrow schema from the frame's own (an empty collect)."""
    return SparkLazy(df, df.limit(0).toArrow().schema, spark)


def _parts_of(z: Any, schema: pa.Schema, spark: Any) -> tuple[Part, ...]:
    """The parts that make `z`: a state's own, a result or a change written
    as one (none for an empty table)."""
    if isinstance(z, SparkState):
        return z.parts
    if isinstance(z, pa.Table) and z.num_rows == 0:
        return ()
    return (_part(_raw(z, spark), schema, spark),)


class SparkStore(ArrowOps):
    """A view's state as parts of Parquet files that Spark writes
    (`SparkState`). A weighted table that is an Arrow table (a change, the
    state per group) is handled as the Arrow store does."""

    keep = True

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        spark = _session(a, b)
        if keep:
            parts = (*_parts_of(a, schema, spark), *_parts_of(b, schema, spark))
            parts = tuple(p for p in parts if p.rows)
            held = a if isinstance(a, SparkState) else None
            out = SparkState(
                parts,
                schema,
                spark,
                plan=plan,
                consolidated=held is not None and held.consolidated and parts == held.parts,
                base=held is not None and held.base and bool(parts) and parts[0] is held.parts[0],
            )
            return out.consolidate() if out.needs_compaction() else out
        return _arrow(_run(plan, schema, spark, _input(a, spark), _input(b, spark)), schema)

    def kept(self, table: pa.Table) -> State:
        spark = _session()
        parts = tuple(p for p in _parts_of(table, table.schema, spark) if p.rows)
        return SparkState(parts, table.schema, spark, consolidated=True, base=bool(parts))

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

        df = _raw(z, z.spark).withColumn(WEIGHT, -F.col(WEIGHT))
        return SparkLazy(df, z.schema, z.spark)

    def expanded(self, z: State) -> pa.Table | SparkState:
        """Each row as many times as its weight, as parts of its own (without
        `WEIGHT`). Where every weight is positive the parts alone give the
        copies; otherwise the parts are added up first, and a negative weight
        left is an error."""
        if not isinstance(z, SparkState):
            return super().expanded(z)
        from pyspark.sql import functions as F

        names = [c for c in z.schema.names if c != WEIGHT]
        schema = pa.schema([z.schema.field(c) for c in names])
        if not z.positive():
            low, _ = z.consolidate().range()
            if low is not None and low < 0:
                raise ValueError("a bag of rows cannot hold a negative number of copies")
        low, high = z.range()
        if not z.parts or (low == 1 and high == 1):
            return SparkState(z.parts, schema, z.spark)  # every row once: the parts' own files
        # Every weight is positive here, so `sequence(1, w)` has w copies.
        copies = F.explode(F.sequence(F.lit(1), F.col(WEIGHT))).alias("__copy")
        df = z.raw(z.spark).select(*names, copies).drop("__copy")
        return SparkState((_part(df, schema, z.spark),), schema, z.spark)

    def has_negative(self, z: State) -> bool:
        if not isinstance(z, SparkState):
            return super().has_negative(z)
        if z.positive():
            return False  # weights of one sign add up to that sign
        low, _ = z.consolidate().range()
        return low is not None and low < 0

    def retire(self, view: Any, column: str, cutoff: Any) -> int:
        z = view.state
        if not isinstance(z, SparkState):
            return super().retire(view, column, cutoff)
        from pyspark.sql import functions as F

        df = z.df  # added up: a row whose weights cancelled is not a bucket
        gone = df.filter(F.col(column) <= cutoff).select(column).distinct().count()
        part = _part(df.filter(F.col(column) > cutoff), z.schema, z.spark)
        view.state = SparkState(
            (part,), z.schema, z.spark, plan=z.plan, consolidated=True, base=bool(part.rows)
        )
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
        # (`NormalizeFloatingNumbers`), and `<=>` makes NULLs equal. A filter
        # by key is linear: it runs on the parts as they lie, and its result
        # is as added up as they are.
        right = _raw(keys, z.spark).toDF(*[f"__k{i}" for i in range(len(columns))])
        left, on = z.raw(z.spark), None
        for i, c in enumerate(columns):
            cond = left[c].eqNullSafe(right[f"__k{i}"])
            on = cond if on is None else on & cond
        part = _part(left.join(right.dropDuplicates(), on, how), z.schema, z.spark)
        return SparkState(
            (part,),
            z.schema,
            z.spark,
            plan=z.plan,
            consolidated=z.consolidated,
            base=z.consolidated and bool(part.rows),
        )
