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
from collections.abc import Sequence

import duckdb
import pyarrow as pa

from sverify import _duckdb
from sverify._scan import Native, Resident, _q
from sverify._weighted import (
    WEIGHT,
    _same_rows,
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
        state = arrow_of(z)
        if not keys.num_rows or not state.num_rows:
            return state.slice(0, 0)
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
        hits = marked.join(pa.table(right), list(right), join_type="left semi")
        return state.take(hits.column("__row"))


class ArrowStore(Store):
    """The state as an Arrow table in the Python process."""


class DuckDBStore(Store):
    """The state as a table DuckDB holds (`Resident`): merges leave their
    result in DuckDB, and the view's rows are a DuckDB view of it.

    A refresh changes the state in place, at the cost of the change
    (`apply`): the state rows equal to a row of the change (`matching`) are
    added to the change by the merge plan, and replace those rows, for every
    view in one transaction. The state then holds each row once with its
    weight, as a full merge leaves it."""

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

    def copy(self, z: Resident) -> Resident:
        """A new table with the rows of `z`."""
        return self._sql(f"SELECT * FROM {z.ref}")

    def apply(self, updates: list[tuple[Resident, pa.Table, pa.Table]]) -> None:
        """For each `(state, change, merged)`, in one transaction: delete
        the rows of `state` equal to a row of `change`, and insert `merged`
        (those rows plus the change, by the merge plan)."""
        with DuckDBStore._lock:
            if DuckDBStore._db is None:
                DuckDBStore._db = _duckdb.cursor()
            db = DuckDBStore._db
            _duckdb.collect(db)
            db.execute("BEGIN TRANSACTION")
            try:
                for state, change, merged in updates:
                    keys = [c for c in state.schema.names if c != WEIGHT]
                    db.register("__sverify_change", change)
                    db.register("__sverify_merged", merged)
                    try:
                        same = _same_rows(keys, "s", "c")
                        db.execute(
                            f"DELETE FROM {state.ref} s WHERE EXISTS "
                            f"(SELECT 1 FROM __sverify_change c WHERE {same})"
                        )
                        cols = ", ".join(_q(c) for c in state.schema.names)
                        db.execute(
                            f"INSERT INTO {state.ref} ({cols}) SELECT {cols} FROM __sverify_merged"
                        )
                    finally:
                        db.unregister("__sverify_change")
                        db.unregister("__sverify_merged")
                db.execute("COMMIT")
            except BaseException:
                db.execute("ROLLBACK")
                raise

    def retire(self, view, column: str, cutoff: object) -> int:
        """`Store.retire` in place: one DELETE in DuckDB."""
        z = view.state
        if not isinstance(z, Resident):
            return super().retire(view, column, cutoff)
        with DuckDBStore._lock:
            if DuckDBStore._db is None:
                DuckDBStore._db = _duckdb.cursor()
            db = DuckDBStore._db
            where = f"{_q(column)} <= ?"
            row = db.execute(
                f"SELECT count(DISTINCT {_q(column)}) FROM {z.ref} WHERE {where}", [cutoff]
            ).fetchone()
            gone = row[0] if row else 0
            db.execute(f"DELETE FROM {z.ref} WHERE {where}", [cutoff])
        return int(gone)

    def with_keys(self, z: State, columns: Sequence[str], keys: pa.Table) -> State:
        """`Store.with_keys` in DuckDB: a semi-join with NULLs equal."""
        if not isinstance(z, Resident):
            return super().with_keys(z, columns, keys)
        with DuckDBStore._lock:
            if DuckDBStore._db is None:
                DuckDBStore._db = _duckdb.cursor()
            db = DuckDBStore._db
            on = " AND ".join(
                f"s.{_q(c)} IS NOT DISTINCT FROM k.{_q(k)}"
                for c, k in zip(columns, keys.column_names, strict=True)
            )
            db.register("__sverify_keys", keys)
            try:
                return db.sql(
                    f"SELECT s.* FROM {z.ref} s WHERE EXISTS "
                    f"(SELECT 1 FROM __sverify_keys k WHERE {on})"
                ).to_arrow_table()
            finally:
                db.unregister("__sverify_keys")

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


# A new process database (`_duckdb.reset`) needs a new cursor.
_duckdb.on_reset(lambda: setattr(DuckDBStore, "_db", None))
