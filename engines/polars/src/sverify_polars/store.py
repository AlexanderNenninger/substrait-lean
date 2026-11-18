"""Polars's store (#173 N6, #1329): a view's state as a generation of Parquet
files that Polars writes and scans lazily, never as a table in the Python
process.

The handle (`PolarsState`) is a Parquet file in a state directory and the
Arrow schema of the weighted table it holds. Every operation makes a new
generation: Polars computes it as a lazy frame and streams it into a file
(`sink_parquet`), so a state larger than memory is never held whole. A
generation's file is deleted once nothing refers to its handle, which is how
generation n-1 goes after epoch n has replaced it. DuckDB reads the same file
(`attach`), so the view's rows are a table of the `Connection` like any
other.

Merges run the merge plan on Polars (`Store.merge`). Only answers cross into
Arrow: `to_arrow` reads a generation back.
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
import polars as pl
import pyarrow as pa
import pyarrow.parquet as pq

from sverify._arrow_state import ArrowOps
from sverify._scan import Native, _q
from sverify._store import MERGE_A, MERGE_B, State
from sverify._weighted import WEIGHT
from sverify_polars import engine, shims

_DIR: str | None = None


def _state_dir() -> str:
    """The process's state directory, removed at exit."""
    global _DIR
    if _DIR is None:
        _DIR = tempfile.mkdtemp(prefix="sverify-polars-state-")
        atexit.register(shutil.rmtree, _DIR, ignore_errors=True)
    return _DIR


class PolarsState(Native):
    """A weighted table held as a Parquet file in the state directory.

    Attributes:
        path: The file.
        schema: The table's Arrow schema, with `WEIGHT` where it has one.
    """

    def __init__(self, path: str, schema: pa.Schema, owner: PolarsState | None = None):
        self.path, self.schema, self._owner = path, schema, owner
        if owner is None:
            weakref.finalize(self, _remove, path)

    def lazy(self) -> pl.LazyFrame:
        """The table as a lazy frame over its file: its columns, which can be
        fewer than the file's (`owner` holds the file)."""
        return pl.scan_parquet(self.path).select(self.schema.names)

    def columns(self, names: Sequence[str]) -> PolarsState:
        """The table's columns `names`, over the same file (kept while it is
        read)."""
        schema = pa.schema([self.schema.field(c) for c in names])
        return PolarsState(self.path, schema, owner=self._owner or self)

    def attach(
        self, db: duckdb.DuckDBPyConnection, name: str, *, table: bool = False
    ) -> Callable[[], None]:
        kind = "TABLE" if table else "VIEW"
        cols = ", ".join(_q(c) for c in self.schema.names)
        path = self.path.replace("'", "''")
        db.execute(
            f"CREATE OR REPLACE TEMP {kind} {_q(name)} AS SELECT {cols} FROM read_parquet('{path}')"
        )

        def drop() -> None:
            db.execute(f"DROP {kind} IF EXISTS {_q(name)}")

        return drop

    def to_arrow(self) -> pa.Table:
        return pq.read_table(self.path).select(self.schema.names).cast(self.schema)

    def readable(self) -> bool:
        return os.path.exists(self.path)


def _remove(path: str) -> None:
    with contextlib.suppress(OSError):
        os.unlink(path)


class LazyState:
    """A weighted table Polars has not computed yet: the result of a run, or
    weights set on one. A merge writes it as a generation, once."""

    def __init__(self, lf: pl.LazyFrame, schema: pa.Schema):
        self.lf, self.schema = lf, schema


def _lazy(z: Any) -> pl.LazyFrame:
    """A weighted table of any shape the store meets as a lazy frame."""
    if isinstance(z, PolarsState):
        return z.lazy()
    if isinstance(z, LazyState):
        return z.lf
    if isinstance(z, pl.LazyFrame):
        return z
    return pl.from_arrow(z).lazy()  # type: ignore[union-attr]


def _write(lf: pl.LazyFrame, schema: pa.Schema) -> PolarsState:
    """A new generation: `lf` (the columns of `schema`, in its types) streamed
    into a file."""
    path = os.path.join(_state_dir(), f"gen-{uuid.uuid4().hex}.parquet")
    engine.sink_parquet(lf, path)
    return PolarsState(path, schema)


def lazy_plan(lf: pl.LazyFrame) -> LazyState:
    """The result of a translated plan, to be written by the merge that adds
    it to the state: its Arrow schema from the frame's own (an empty collect)."""
    return LazyState(lf, lf.head(0).collect().to_arrow().schema)


def _key(e: pl.Expr, t: pa.DataType) -> pl.Expr:
    """A key column as the model compares it: `-0.0` as `0.0` (Polars's joins
    already make every NaN one value, polars-nan-equality)."""
    return shims.one_zero(e) if pa.types.is_floating(t) else e


_OVERFLOW = "a row's weight sum leaves 64 bits"


class PolarsStore(ArrowOps):
    """A view's state as generations of Parquet files that Polars scans
    (`PolarsState`). A weighted table that is an Arrow table (a change, the
    state per group) is handled as the Arrow store does."""

    keep = True

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        # The plan's own overflow guard (a callback per batch) is left out: a
        # weight sum that leaves 64 bits comes out NULL, which is checked
        # natively on the result, one `any()` over the written weights.
        lf = engine.to_lazy(
            plan, {MERGE_A: _lazy(a), MERGE_B: _lazy(b)}, guards=False, rows="multiset"
        )
        lf = lf.select([pl.col(f.name).cast(_dtype(f)) for f in schema])
        if keep:
            out = _write(lf, schema)
            if out.lazy().select(pl.col(WEIGHT).is_null().any()).collect().item():
                raise engine.SumOverflow(_OVERFLOW)
            return out
        table = engine.collect(lf).to_arrow().cast(schema)
        if table.column(WEIGHT).null_count:
            raise engine.SumOverflow(_OVERFLOW)
        return table

    def kept(self, table: pa.Table) -> State:
        return _write(_lazy(table), table.schema)

    def weighted(self, rows: Any, weight: int = 1) -> State:
        if not isinstance(rows, PolarsState | LazyState):
            return super().weighted(rows, weight)
        out = pa.schema([*rows.schema, pa.field(WEIGHT, pa.int64())])
        lf = _lazy(rows).with_columns(pl.lit(weight, pl.Int64).alias(WEIGHT))
        return LazyState(lf, out)

    def negated(self, z: State) -> State:
        if not isinstance(z, PolarsState | LazyState):
            return super().negated(z)
        return LazyState(_lazy(z).with_columns(-pl.col(WEIGHT)), z.schema)

    def expanded(self, z: State) -> pa.Table | PolarsState:
        """Each row as many times as its weight, as a generation of its own
        (without `WEIGHT`)."""
        if not isinstance(z, PolarsState):
            return super().expanded(z)
        names = [c for c in z.schema.names if c != WEIGHT]
        schema = pa.schema([z.schema.field(c) for c in names])
        if not z.lazy().select((pl.col(WEIGHT) != 1).any()).collect().item():
            return z.columns(names)  # every row once: the state's own file
        lf = (
            z.lazy()
            .with_columns(pl.int_ranges(0, pl.col(WEIGHT)).alias("__copy"))
            .explode("__copy")
            .select(names)
        )
        return _write(lf, schema)

    def has_negative(self, z: State) -> bool:
        if not isinstance(z, PolarsState):
            return super().has_negative(z)
        return bool(z.lazy().select((pl.col(WEIGHT) < 0).any()).collect().item())

    def retire(self, view: Any, column: str, cutoff: object) -> int:
        z = view.state
        if not isinstance(z, PolarsState):
            return super().retire(view, column, cutoff)
        lf = z.lazy()
        gone = lf.filter(pl.col(column) <= cutoff).select(pl.col(column).n_unique()).collect()
        view.state = _write(lf.filter(pl.col(column) > cutoff), z.schema)
        return int(gone.item())

    def with_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, PolarsState):
            return super().with_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, "semi")

    def without_keys(self, z: State, columns: Sequence[str], keys: Any) -> State:
        if not isinstance(z, PolarsState):
            return super().without_keys(z, columns, keys)
        return self._by_keys(z, columns, keys, "anti")

    def _by_keys(self, z: PolarsState, columns: Sequence[str], keys: Any, how: str) -> State:
        left = z.lazy()
        right = _lazy(keys)
        names = right.collect_schema().names()
        types = [z.schema.field(c).type for c in columns]
        lk = [f"__k{i}" for i in range(len(columns))]
        left_marked = left.with_columns(
            [_key(pl.col(c), t).alias(k) for c, t, k in zip(columns, types, lk, strict=True)]
        )
        right_marked = right.select(
            [
                _key(pl.col(n).cast(_dtype(z.schema.field(c))), t).alias(k)
                for n, c, t, k in zip(names, columns, types, lk, strict=True)
            ]
        ).unique()
        out = left_marked.join(right_marked, on=lk, how=how, nulls_equal=True).drop(lk)
        return _write(out, z.schema)


def _dtype(f: pa.Field) -> pl.DataType:
    return pl.from_arrow(pa.schema([f]).empty_table()).schema[f.name]  # type: ignore[union-attr]
