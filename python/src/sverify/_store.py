"""The state store: the contract an engine meets to run incremental pipelines
(#1189).

Internal: not part of sverify's public API. An engine's plugin names its
store (`ProfilePlugin.store`); `store_for` finds it. sverify holds no state
of its own and picks no store. `sverify._state` adds up states (`Merger`).
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Sequence
from typing import Any

import pyarrow as pa

from sverify._scan import Native

type State = Any
"""A weighted table as the engine holds it: its store's handle (`Store`'s
`S`), opaque to sverify, which passes it between the engine's store and its
runner."""


def arrow_of(z: pa.Table | Native) -> pa.Table:
    return z.to_arrow() if isinstance(z, Native) else z


class Store[S](ABC):
    """Where a view keeps its state: the contract an engine's plugin meets to
    run incremental pipelines (`ProfilePlugin.store`, #1189). An engine that
    runs only one-shot plans has none.

    `S` is the engine's own handle on a weighted table (`Resident` for a
    table DuckDB holds, an Arrow table for an interim store, a cluster-side
    DataFrame for Spark's), opaque to sverify. The invariant: state stays a
    handle. The operations take and give back handles, so the state stays
    where the engine keeps it; only answers cross into concrete data (a
    count, whether a weight is negative, how many buckets were retired, a
    bounded set of violating keys), and the rows a sink writes at the end.

    `keep`: whether merges leave their result where the engine holds it."""

    keep = False

    @abstractmethod
    def weighted(self, rows: S, weight: int = 1) -> S:
        """`rows` (a batch the engine read) with the weight `weight` on
        every row."""

    @abstractmethod
    def negated(self, z: S) -> S:
        """`z` with every weight negated."""

    @abstractmethod
    def expanded(self, z: S) -> S:
        """Each row as many times as its weight."""

    @abstractmethod
    def has_negative(self, z: S) -> bool:
        """Does a row of `z` have a negative weight?"""

    @abstractmethod
    def retire(self, view, column: str, cutoff: object) -> int:
        """Drop the rows of `view.state` whose bucket `column` starts at or
        before `cutoff` (`sverify._retention`); returns how many buckets."""

    @abstractmethod
    def with_keys(self, z: S, columns: Sequence[str], keys: S) -> S:
        """The rows of `z` whose `columns` equal a row of `keys` (the same
        number of columns, in order), NULLs equal."""

    @abstractmethod
    def without_keys(self, z: S, columns: Sequence[str], keys: S) -> S:
        """The rows of `z` whose `columns` equal no row of `keys`: the rows
        `with_keys` leaves out."""


def by_keys(
    state: pa.Table, columns: Sequence[str], keys: pa.Table, *, keep: bool = True
) -> pa.Table:
    """The rows of `state` whose `columns` equal a row of `keys` (the same
    number of columns, in order), NULLs equal; with `keep=False`, the other
    rows."""
    if not keys.num_rows or not state.num_rows:
        return state.slice(0, 0) if keep else state
    # Each key column as dictionary indices over both tables, NULL its own
    # value, so a hash join matches NULLs.
    left, right = {}, {}
    n = state.num_rows
    for i, c in enumerate(columns):
        both = pa.chunked_array(
            [*state.column(c).chunks, *keys.column(i).cast(state.schema.field(c).type).chunks],
            type=state.schema.field(c).type,
        )
        codes = both.dictionary_encode(null_encoding="encode").combine_chunks().indices
        left[f"__k{i}"], right[f"__k{i}"] = codes[:n], codes[n:]
    marked = state.append_column("__row", pa.array(range(n), pa.int64()))
    for k, v in left.items():
        marked = marked.append_column(k, v)
    hits = marked.join(pa.table(right), list(right), join_type="left semi" if keep else "left anti")
    return state.take(hits.column("__row"))


def store_for(engine: object) -> Store[Any]:
    """The store of the engine a view's plans run on (`ProfilePlugin.store`).

    Raises:
        ValueError: The engine's plugin has no store: it runs one-shot plans
            only, no incremental pipeline.
    """
    from sverify import profiles

    plugin = profiles.find(engine)
    name = plugin.engine if plugin is not None else engine
    if plugin is None or plugin.store is None:
        raise ValueError(
            f"{name!r} keeps no pipeline state (its plugin has no ProfilePlugin.store): "
            "it runs one-shot plans only; refresh the view on an engine that has one"
        )
    return plugin.store()
