"""sverify's DuckDB engine (#1189): its SQL dialect (`sverify_duckdb.dialect`,
`DUCKDB`), its runner on the process's database (`sverify_duckdb.engine`), the
lowering proved for every plan, and the table store (`DuckDBStore`),
registered as the `ProfilePlugin` `PLUGIN` under the entry-point group
`sverify.profiles`. DuckDB is sverify's default engine.

DuckDB's settings: sverify runs each plan on a cursor of its own on the
process's database (`sverify_duckdb.engine`), so a session's `SET` on another
cursor leaves it alone; `SET GLOBAL` reaches it, and that is what the check
sees. Not checked, since no choice depends on them: display settings, threads
(the order of a double `SUM`, `sum_order`, which every route allows within
the plan's bound), and `TimeZone` and `Calendar`, which the written SQL never
reads: an instant (a UTC-zoned timestamp, #1725) is only compared, ordered,
grouped and aggregated, which are zone-free (duckdb-time-zones), and its
conversions and calendar functions are refused.
`dialect_compatibility_mode` and `regex_match_operator_semantics` wait on a
check of DuckDB's source.
"""

from __future__ import annotations

import json
import threading
from collections.abc import Sequence

# An engine built from main beside PyPI's sverify of the same version number
# fails deep inside sverify with a TypeError (#1585): check the interface first.
from importlib.metadata import version as _version
from importlib.util import find_spec
from typing import TYPE_CHECKING, Any, Literal

import pyarrow as pa

from sverify import _meta

if getattr(_meta, "PLUGIN_API", None) != 4:
    raise ImportError(
        f"{__name__.replace('_', '-')} {_version(__name__.replace('_', '-'))} "
        f"needs a sverify of its own build, found sverify {_meta.VERSION}: "
        "install both from the same release (`pip install -U sverify sverify-duckdb`)"
    )

from sverify import _duckdb, black_box
from sverify._scan import Resident, _q
from sverify._store import State, Store
from sverify._unsupported import MIN_MOD_GUARD, RANGE_GUARD
from sverify._weighted import WEIGHT, _same_rows
from sverify.profiles import Finite, ProfilePlugin, Setting, SqlFrontEnd
from sverify_duckdb.declared import refuse_base_table

if TYPE_CHECKING:
    import duckdb

_R15 = tuple(
    f"duckdb-R15-{n}"
    for n in (
        "atan2",
        "digests",
        "double-arith",
        "double-modulus",
        "elementary",
        "int-arith",
        "int-divide",
        "int-modulus",
        "math-domain",
        "regexp",
        "round-digits",
        "round",
        "shift-left",
        "shift-right",
    )
)

#: The settings DuckDB's profile assumes.
SETTINGS: tuple[Setting, ...] = (
    Setting(
        "default_null_order",
        ("nulls_last",),
        "refuse",
        ("duckdb-F2",),
        "where NULLs sort in a key without a placement (null_order), and in "
        "FIRST/LAST(... ORDER BY) and list_sort",
        ("null_order", "list_null_order"),
    ),
    Setting(
        "default_order",
        ("ascending", "asc"),
        "refuse",
        (),
        "the direction of a sort key without one",
        ("null_order", "list_null_order"),
    ),
    Setting(
        "integer_division",
        (False,),
        "refuse",
        ("duckdb-F1",),
        "whether `/` of integers divides as integers (division_type)",
        ("division_type",),
    ),
    Setting(
        "error_on_division_by_zero",
        (True,),
        "refuse",
        ("duckdb-R2", "duckdb-R3", "duckdb-R4", *_R15),
        "what a division by zero gives (on_division_by_zero): `//` and `%` give NULL "
        "instead of raising; deprecated in DuckDB 2.0.0, still read and still in "
        "effect there",
        ("on_division_by_zero",),
    ),
    Setting(
        "ieee_floating_point_ops",
        (True,),
        "refuse",
        ("duckdb-R4", "duckdb-R5", *_R15),
        "NaN and ±inf from double operations (nan_creation)",
        ("nan_creation", "float_overflow"),
    ),
    Setting(
        "default_collation",
        ("",),
        "refuse",
        ("engines/duckdb/replay/collate.json", "duckdb-default-collation-matching"),
        "how strings compare; NOCASE changes `=`, sorting and grouping, and from 2.0.1 `LIKE`, "
        "`contains`, `starts_with` and `strpos` too (`replace` is unchanged)",
    ),
    Setting(
        "scalar_subquery_error_on_multiple_rows",
        (True,),
        "refuse",
        ("engines/duckdb/replay/subquery.json",),
        "whether a scalar subquery with several rows raises or takes one",
    ),
    Setting(
        "enable_optimizer",
        (True,),
        "refuse",
        ("engines/duckdb/replay/settings.json",),
        "which rows a raising expression sees",
    ),
    Setting(
        "disabled_optimizers",
        ("",),
        "refuse",
        ("engines/duckdb/replay/settings.json",),
        "which rows a raising expression sees",
    ),
    Setting(
        "preserve_insertion_order",
        (True,),
        "warn",
        ("engines/duckdb/replay/order.json",),
        "the order of rows without an ORDER BY, which no route relies on",
    ),
)


def _run(
    con: Any,
    plan_json: str,
    session: Any,
    *,
    keep: bool,
    finite: Finite,
    tie_free: bool,
    asof: Sequence[dict] = (),
    unchecked: dict | None = None,
    rows: Literal["sequence", "multiset"] = "sequence",
) -> Any:
    from sverify.engine import read_tables
    from sverify_duckdb import engine as duckdb_engine

    # DuckDB reads `Scan` and `Resident` tables where they are. `unchecked`:
    # the marks `Report.run` passes on a checked run (ruling 223), and
    # `rows="multiset"` where the result needs no ordinal: then the windows
    # need no tiebreak either where the report is exact (`tie_free`).
    tables = {t: con.get(t) for t in read_tables(json.loads(plan_json))}
    return duckdb_engine.run(
        plan_json,
        tables,
        keep=keep,
        finite=finite,
        asof=asof,
        unchecked=unchecked,
        rows=rows,
        deterministic=tie_free and rows == "multiset",
    )


def _run_tables(
    plan_json: str, tables: Any, *, guard_free: bool = False, finite: Finite = True
) -> Any:
    from sverify_duckdb import engine as duckdb_engine

    if guard_free:
        raise ValueError("no theorem covers DuckDB's writer without its guards")
    return duckdb_engine.run(plan_json, tables, finite=finite)


def _version() -> str | None:
    import duckdb

    return duckdb.__version__


def _read_settings(names: Sequence[str], session: Any) -> dict[str, Any]:
    if find_spec("duckdb") is None:
        return {}  # no DuckDB session to read: nothing runs on it either
    from sverify_duckdb import engine as duckdb_engine

    return duckdb_engine.settings(names)


def _restore(setting: Setting) -> str:
    v = setting.expected[0]
    value = f"'{v}'" if isinstance(v, str) else str(v).lower()
    return f"SET GLOBAL {setting.name} = {value}"


def _dialect() -> Any:
    from sverify_duckdb.dialect import DUCKDB

    return DUCKDB


class DuckDBStore(Store[Any]):
    # Its handle: a table DuckDB holds (`Resident`), or an Arrow batch read in.
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

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        from sverify._store import MERGE_A, MERGE_B
        from sverify_duckdb import engine as duckdb_engine

        tables = {MERGE_A: a, MERGE_B: b}
        if keep:
            return duckdb_engine.run(plan, tables, keep=True)
        out = duckdb_engine.run(plan, tables)
        return out.rename_columns(schema.names).cast(schema)

    def kept(self, table: pa.Table) -> State:
        return self.keep_table(table)

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


# A new process database (`_duckdb.reset`) needs a new cursor.
_duckdb.on_reset(lambda: setattr(DuckDBStore, "_db", None))


def _lift(query: str, schemas: Any, semantics: str) -> Any:
    """DuckDB's SQL lifted to a plan (`sverify.sql_lift`), under the profile
    `semantics` names (`"duckdb"` or `"portable"`)."""
    from sverify.sql_lift import lift

    return lift(query, schemas, semantics)


PLUGIN = ProfilePlugin(
    "duckdb",
    sql=SqlFrontEnd("duckdb", _lift),
    title="DuckDB",
    store=DuckDBStore,
    refuse_declared_types=refuse_base_table,
    default=True,
    translation="sverify's DuckDB lowering, proved for every plan, and its SQL writer",
    settings=SETTINGS,
    installed_version=_version,
    restore=_restore,
    runner=_run,
    # The package writes DuckDB SQL without DuckDB; running plans needs it
    # (`pip install sverify[duckdb]`).
    local=find_spec("duckdb") is not None,
    read_settings=_read_settings,
    dialect=_dialect,
    run_tables=_run_tables,
    # The functions only some engines run (#50, #53-#55, #94, #810, #812,
    # #325's black boxes), and the lift's guards (`sverify_raise`: a date of
    # columns outside the calendar, #809).
    functions=frozenset(
        {
            "regexp_extract",
            "regexp_replace",
            "md5",
            "sha256",
            "first",
            "last",
            "string_agg",
            "array_agg",
            "median",
            "quantile_cont",
            "quantile_disc",
            "mode",
            "arg_min",
            "arg_max",
            "covar_samp",
            "covar_pop",
            "corr",
            "sverify_pair",
            "list_prepend",
            "list_concat",
            "list_contains",
            "list_position",
            "flatten",
            "sverify_raise",
            *black_box.NAMES,
        }
    ),
    # The variance over a frame, which only DuckDB's writer computes so far.
    window_functions=frozenset({"variance", "std_dev"}),
    guards=(RANGE_GUARD, MIN_MOD_GUARD),
)
