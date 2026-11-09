"""Where a view keeps its state, and the plan that adds states up (#173).

Internal: not part of sverify's public API.

A view's state (`IncrementalView.state`) is a weighted table
(`sverify._weighted`): its rows, each once, with its number of copies. The
engine a pipeline runs on keeps it, in its own form: its plugin's `Store`
(`ProfilePlugin.store`; `store_for`). sverify holds no state of its own and
picks no store (#1189, #1288). DuckDB's (`sverify._builtin.duckdb.DuckDBStore`)
is a table DuckDB holds between calls (`Resident`), so the state never passes
through Python; Polars's, Spark's and DataFusion's keep Arrow tables in the
process for now (`sverify._arrow_state`).

Whatever the store, weighted tables are added up by one plan (`Merger`):
the union of two of them, grouped by every column, with the weights summed
and the groups of weight 0 left out. Lean checks it and writes it like any
other plan, so each engine's lowering groups rows as the model compares them
(one NaN, `-0.0` equal to `0.0`, NULLs equal to each other, lists by their
elements), and a store for another engine runs the same plan there. Where a
lowering refuses it (struct columns, #94), the rows are added up in Arrow
with `_weighted.consolidated`, which groups them the same way.

The store's other operations (setting, negating and expanding weights)
compare no values, so each store does them its own way.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Sequence
from typing import Any

import pyarrow as pa

from sverify._scan import Native
from sverify._weighted import WEIGHT, consolidated

type State = Any
"""A weighted table as the engine holds it: its store's handle (`Store`'s
`S`), opaque to sverify, which passes it between the engine's store and its
runner."""

_A, _B = "$merge_a", "$merge_b"


def arrow_of(z: pa.Table | Native) -> pa.Table:
    return z.to_arrow() if isinstance(z, Native) else z


class Merger:
    """Adds up weighted tables with `schema` (the rows' columns, then
    `WEIGHT`) by the plan Lean checked, run on DuckDB over the tables of
    `con`.

    Attributes:
        refused: Why the plan could not be written or run, if it could not:
            the tables are then added up in Arrow.
    """

    def __init__(self, con, schema: pa.Schema):
        self.con, self.schema = con, schema
        self._plan: str | None = None
        self.refused: str | None = None

    def plan(self) -> str | None:
        """The plan, written by Lean on first use; None if it was refused."""
        from sverify.engine import plan_json, written_plan

        if self._plan is None and self.refused is None:
            con = self.con
            try:
                for name in (_A, _B):
                    con.put(name, self.schema.empty_table())
                a, b = con.table(_A), con.table(_B)
                u = a.union(b, distinct=False)
                keys = [c for c in self.schema.names if c != WEIGHT]
                total = u.group_by(keys).aggregate(**{WEIGHT: u[WEIGHT].sum()})
                self._plan = written_plan(plan_json(con, total.filter(total[WEIGHT] != 0)))
            except Exception as e:  # noqa: BLE001 - any refusal: add up in Arrow
                self.refused = f"{type(e).__name__}: {e}"
            finally:
                for name in (_A, _B):
                    con.drop(name)
        return self._plan

    def __call__(self, a: State, b: State | None = None, *, keep: bool = False) -> State:
        """`a` plus `b` (default: nothing), consolidated: as a `Resident`
        table with `keep`, else as an Arrow table."""
        from sverify import duckdb_engine
        from sverify.sql.core import Unsupported

        b = self.schema.empty_table() if b is None else b
        plan = self.plan()
        if plan is not None:
            tables = {_A: a, _B: b}
            try:
                if keep:
                    return duckdb_engine.run(plan, tables, keep=True)
                out = duckdb_engine.run(plan, tables)
            except Unsupported as e:
                self.refused = f"{type(e).__name__}: {e}"
            else:
                return out.rename_columns(self.schema.names).cast(self.schema)
        merged = consolidated(arrow_of(a).cast(self.schema), arrow_of(b).cast(self.schema))
        if keep:
            from sverify._builtin.duckdb import DuckDBStore

            return DuckDBStore().keep_table(merged)
        return merged


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
