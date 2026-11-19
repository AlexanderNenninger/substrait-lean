"""Polars's store (#173 N6, #1329, N14): a view's state as parts of Parquet
files that Polars writes and scans lazily, never as a table in the Python
process.

The parts, their lifetimes, the compaction rule and the exits that add them up
are `sverify._parts`; this module is what Polars supplies to it
(`PolarsBackend`). Polars computes a frame lazily and streams it into a file
(`sink_parquet`), so a state larger than memory is never held whole.
"""

from __future__ import annotations

import glob
import os
from collections.abc import Sequence
from typing import Any

import polars as pl
import pyarrow as pa

from sverify._parts import Backend, Lazy, Part, PartsStore, new_part_path
from sverify._store import MERGE_A, MERGE_B
from sverify._weighted import WEIGHT
from sverify_polars import engine, shims

_OVERFLOW = "a row's weight sum leaves 64 bits"


def _dtype(f: pa.Field) -> pl.DataType:
    return pl.from_arrow(pa.schema([f]).empty_table()).schema[f.name]  # type: ignore[union-attr]


def _key(e: pl.Expr, t: pa.DataType) -> pl.Expr:
    """A key column as the model compares it: `-0.0` as `0.0` (Polars's joins
    already make every NaN one value, polars-nan-equality)."""
    return shims.one_zero(e) if pa.types.is_floating(t) else e


def _files(path: str) -> list[str]:
    return sorted(glob.glob(os.path.join(path, "*.parquet")))


class PolarsBackend(Backend):
    """Polars's frames (`LazyFrame`)."""

    def write(self, frame: pl.LazyFrame, schema: pa.Schema, *, merged: bool = False) -> Part:
        names = frame.collect_schema().names()
        frame = frame.select(
            [pl.col(n).cast(_dtype(f)).alias(f.name) for n, f in zip(names, schema, strict=True)]
        )
        path = new_part_path()
        os.makedirs(path)
        file = os.path.join(path, "part.parquet")
        engine.sink_parquet(frame, file)
        # The merge runs with its own guard off: a weight sum that leaves 64
        # bits comes out NULL, which is checked natively on the written
        # weights, one `any()`.
        if merged and pl.scan_parquet(file).select(pl.col(WEIGHT).is_null().any()).collect().item():
            raise engine.SumOverflow(_OVERFLOW)
        return Part(path, schema, self)

    def read(self, parts: Sequence[Part], schema: pa.Schema) -> pl.LazyFrame:
        files = [f for p in parts for f in _files(p.path)]
        return pl.scan_parquet(files).select(schema.names)

    def run(self, plan: str, schema: pa.Schema, a: pl.LazyFrame, b: pl.LazyFrame) -> pl.LazyFrame:
        return engine.to_lazy(plan, {MERGE_A: a, MERGE_B: b}, guards=False, rows="multiset")

    def arrow(self, frame: pl.LazyFrame, schema: pa.Schema, *, merged: bool = False) -> pa.Table:
        table = engine.collect(frame).to_arrow().rename_columns(schema.names).cast(schema)
        if merged and WEIGHT in schema.names and table.column(WEIGHT).null_count:
            raise engine.SumOverflow(_OVERFLOW)
        return table

    def frame(self, table: pa.Table) -> pl.LazyFrame:
        return pl.from_arrow(table).lazy()  # type: ignore[union-attr]

    def measure(self, path: str, weighted: bool) -> tuple[int, int | None, int | None]:
        lf = pl.scan_parquet(_files(path))
        if not weighted:
            return int(lf.select(pl.len()).collect().item()), None, None
        r = lf.select(pl.len(), pl.col(WEIGHT).min(), pl.col(WEIGHT).max()).collect().row(0)
        return int(r[0]), r[1], r[2]

    def with_weight(self, frame: pl.LazyFrame, weight: int) -> pl.LazyFrame:
        return frame.with_columns(pl.lit(weight, pl.Int64).alias(WEIGHT))

    def negate(self, frame: pl.LazyFrame) -> pl.LazyFrame:
        return frame.with_columns(-pl.col(WEIGHT))

    def copies(self, frame: pl.LazyFrame, names: Sequence[str]) -> pl.LazyFrame:
        return (
            frame.with_columns(pl.int_ranges(0, pl.col(WEIGHT)).alias("__copy"))
            .explode("__copy")
            .select(list(names))
        )

    def filtered(
        self,
        left: pl.LazyFrame,
        schema: pa.Schema,
        columns: Sequence[str],
        keys: pl.LazyFrame,
        *,
        anti: bool,
    ) -> pl.LazyFrame:
        names = keys.collect_schema().names()
        types = [schema.field(c).type for c in columns]
        lk = [f"__k{i}" for i in range(len(columns))]
        marked = left.with_columns(
            [_key(pl.col(c), t).alias(k) for c, t, k in zip(columns, types, lk, strict=True)]
        )
        right = keys.select(
            [
                _key(pl.col(n).cast(_dtype(schema.field(c))), t).alias(k)
                for n, c, t, k in zip(names, columns, types, lk, strict=True)
            ]
        ).unique()
        return marked.join(right, on=lk, how="anti" if anti else "semi", nulls_equal=True).drop(lk)

    def split(self, frame: pl.LazyFrame, column: str, cutoff: Any) -> tuple[int, pl.LazyFrame]:
        gone = frame.filter(pl.col(column) <= cutoff).select(pl.col(column).n_unique()).collect()
        return int(gone.item()), frame.filter(pl.col(column) > cutoff)


BACKEND = PolarsBackend()


def lazy_plan(lf: pl.LazyFrame) -> Lazy:
    """The result of a translated plan, to be written by the merge that adds
    it to the state: its Arrow schema from the frame's own (an empty collect)."""
    return Lazy(lf, lf.head(0).collect().to_arrow().schema, BACKEND)


class PolarsStore(PartsStore):
    """A view's state as parts of Parquet files that Polars writes."""

    def default_backend(self) -> Backend:
        return BACKEND
