"""Where a view keeps its state, and the plan that adds states up (#173).

Internal: not part of sverify's public API.

A view's state (`IncrementalView.state`) is a weighted table
(`sverify._weighted`): its rows, each once, with its number of copies. A
`Store` keeps it where an engine reads it:

* `ArrowStore`: an Arrow table in the Python process, which every engine
  reads.
* `DuckDBStore`: a table DuckDB holds between calls (`Resident`), so on
  DuckDB the state never passes through Python.

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

import threading

import duckdb
import pyarrow as pa

from sverify import _duckdb
from sverify._scan import Native, Resident, _q
from sverify._weighted import (
    WEIGHT,
    consolidated,
    expanded,
    has_negative,
    negated,
    weighted,
)

type State = pa.Table | Resident
"""A weighted table: in Arrow, or held by DuckDB."""

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
            tables = {_A: _canonical(a), _B: _canonical(b)}
            try:
                if keep:
                    return duckdb_engine.run(plan, tables, keep=True)
                out = duckdb_engine.run(plan, tables)
            except Unsupported as e:
                self.refused = f"{type(e).__name__}: {e}"
            else:
                return out.rename_columns(self.schema.names).cast(self.schema)
        merged = consolidated(arrow_of(a).cast(self.schema), arrow_of(b).cast(self.schema))
        return DuckDBStore().keep_table(merged) if keep else merged


def _canonical(z: State) -> State:
    """Arrow tables as a connection holds them (`sverify.engine.canonical`):
    the plan was checked over such tables."""
    from sverify.engine import canonical, plain_schema

    return z if isinstance(z, Resident) else canonical(z.cast(plain_schema(z.schema)))


class Store:
    """Where a view keeps its state. `keep`: whether merges leave their
    result in DuckDB."""

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


class ArrowStore(Store):
    """The state as an Arrow table in the Python process."""


class DuckDBStore(Store):
    """The state as a table DuckDB holds (`Resident`): merges leave their
    result in DuckDB, and the view's rows are a DuckDB view of it."""

    keep = True
    _db: duckdb.DuckDBPyConnection | None = None
    _lock = threading.Lock()

    def _sql(self, sql: str, *, kind: str = "TABLE", reads: tuple[Resident, ...] = ()) -> Resident:
        """A new resident holding the result of `sql` (or with `kind`
        "VIEW", a view of it)."""
        with DuckDBStore._lock:
            if DuckDBStore._db is None:
                DuckDBStore._db = _duckdb.cursor()
            db = DuckDBStore._db
            _duckdb.collect(db)
            name = Resident.new_name()
            db.execute(f"CREATE {kind} main.{_q(name)} AS {sql}")
            schema = db.sql(f"SELECT * FROM main.{_q(name)} LIMIT 0").to_arrow_table().schema
        return Resident(name, schema, kind, reads)

    def keep_table(self, table: pa.Table) -> Resident:
        """An Arrow table, held by DuckDB."""
        with DuckDBStore._lock:
            if DuckDBStore._db is None:
                DuckDBStore._db = _duckdb.cursor()
            db = DuckDBStore._db
            _duckdb.collect(db)
            name = Resident.new_name()
            db.register("__sverify_keep", table)
            try:
                db.execute(f"CREATE TABLE main.{_q(name)} AS SELECT * FROM __sverify_keep")
            finally:
                db.unregister("__sverify_keep")
        return Resident(name, table.schema)

    def weighted(self, rows: pa.Table | Resident, weight: int = 1) -> State:
        if not isinstance(rows, Resident):
            return super().weighted(rows, weight)
        w = f"CAST({weight} AS BIGINT) AS {_q(WEIGHT)}"
        return self._sql(f"SELECT *, {w} FROM {rows.ref}")

    def negated(self, z: State) -> State:
        if not isinstance(z, Resident):
            return super().negated(z)
        cols = ", ".join(_q(c) for c in z.schema.names if c != WEIGHT)
        return self._sql(f"SELECT {cols}, -{_q(WEIGHT)} AS {_q(WEIGHT)} FROM {z.ref}")

    def expanded(self, z: State) -> pa.Table | Resident:
        if not isinstance(z, Resident):
            return super().expanded(z)
        cols = ", ".join(f"s.{_q(c)}" for c in z.schema.names if c != WEIGHT)
        sql = f"SELECT {cols} FROM {z.ref} s, range(s.{_q(WEIGHT)})"
        return self._sql(sql, kind="VIEW", reads=(z,))

    def has_negative(self, z: State) -> bool:
        if not isinstance(z, Resident):
            return super().has_negative(z)
        db = _duckdb.cursor()
        try:
            row = db.execute(f"SELECT bool_or({_q(WEIGHT)} < 0) FROM {z.ref}").fetchall()[0]
        finally:
            db.close()
        return bool(row and row[0])


def store_for(engine: object) -> Store:
    """The store for a view whose plans run on `engine`."""
    return DuckDBStore() if engine == "duckdb" else ArrowStore()
