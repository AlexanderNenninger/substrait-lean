"""Where a view keeps its state, and the plan that adds states up (#173).

Internal: not part of sverify's public API.

A view's state (`IncrementalView.state`) is a weighted table
(`sverify._weighted`): its rows, each once, with its number of copies. The
engine a pipeline runs on keeps it, in its own form: its plugin's `Store`
(`ProfilePlugin.store`; `store_for`). sverify holds no state of its own and
picks no store (#1189, #1288). DuckDB's (`sverify_duckdb.DuckDBStore`)
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

import pyarrow as pa

from sverify._store import State, Store, arrow_of, by_keys, store_for
from sverify._weighted import WEIGHT, consolidated

__all__ = ["Merger", "State", "Store", "arrow_of", "by_keys", "store_for"]

_A, _B = "$merge_a", "$merge_b"


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
        from sverify.sql.core import Unsupported
        from sverify_duckdb import engine as duckdb_engine

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
            from sverify_duckdb import DuckDBStore

            return DuckDBStore().keep_table(merged)
        return merged
