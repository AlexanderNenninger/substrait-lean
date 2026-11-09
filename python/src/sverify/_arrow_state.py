"""The store operations that still run in Arrow (#1189, interim).

Internal: not part of sverify's public API. `ArrowOps` does a `Store`'s
operations on Arrow tables in the Python process, with `sverify._weighted`.
DuckDB's store takes the ones it does not do natively from it, and Polars's
and Spark's packages use it as their store until their native stores
(`PolarsStore`, `SparkStore`) exist; then each operation moves into its
engine and this module is deleted. sverify picks no store: an engine's
plugin names its own (`ProfilePlugin.store`).
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

import pyarrow as pa

from sverify._scan import Resident
from sverify._state import State, Store, arrow_of, by_keys
from sverify._weighted import expanded, has_negative, negated, weighted


class ArrowOps(Store[Any]):
    """A `Store` whose state is an Arrow table in the Python process."""

    keep = False

    def weighted(self, rows: pa.Table | Resident, weight: int = 1) -> State:
        """`rows` with the weight `weight` on every row."""
        return weighted(arrow_of(rows), weight)

    def negated(self, z: State) -> State:
        return negated(arrow_of(z))

    def expanded(self, z: State) -> pa.Table | Resident:
        """Each row as many times as its weight."""
        return expanded(arrow_of(z))

    def has_negative(self, z: State) -> bool:
        return has_negative(arrow_of(z))

    def retire(self, view, column: str, cutoff: object) -> int:
        """Drop the rows of `view.state` whose bucket `column` starts at or
        before `cutoff` (`sverify._retention`); returns how many buckets."""
        from sverify import _retention

        state = arrow_of(view.state)
        gone = _retention.buckets(_retention.through(state, column, cutoff), column)
        view.state = _retention.after(state, column, cutoff)
        return gone

    def with_keys(self, z: State, columns: Sequence[str], keys: pa.Table) -> State:
        """The rows of `z` whose `columns` equal a row of `keys` (the same
        number of columns, in order), NULLs equal."""
        return by_keys(arrow_of(z), columns, keys)

    def without_keys(self, z: State, columns: Sequence[str], keys: pa.Table) -> pa.Table:
        """The rows of `z` whose `columns` equal no row of `keys`: the rows
        `with_keys` leaves out."""
        return by_keys(arrow_of(z), columns, keys, keep=False)
