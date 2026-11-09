"""Substrait producers, and DuckDB or Polars as consumer.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

`connect()` gives a `Connection`: named Arrow tables, the engine that runs
plans over them (DuckDB by default), and Ibis tables bound to them
(`con.table(name)`). `plan_json` compiles Ibis expressions with the vendored
producer (`sverify.ibis_substrait`, typed and engine-neutral) and SQL strings
(DuckDB's SQL) with sverify's lift (`sverify.sql_lift`). `run_plan` runs a plan in Lean's
written form (`substrait-check --write`, `--delta`) on the connection's engine
or the one a call names.
"""

from __future__ import annotations

import json
import warnings
from collections.abc import Iterable, Iterator, MutableMapping
from dataclasses import replace
from pathlib import Path
from typing import Any, Literal, overload

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa
import pyarrow.compute as pc
import sqlglot as sg

from sverify import _duckdb, _engines, _stages
from sverify._checker import (  # noqa: F401  (re-exported: `sverify.engine.checker_path` and others)
    _CHECKER,
    _REBUILD,
    PROTOCOL,
    CheckerVersionError,
    _checker_file,
    _run_checker,
    checker_env,
    checker_path,
    checker_refusal,
    run_checker,
)
from sverify._scan import Native, Resident, Scan
from sverify._unsupported import SverifyError
from sverify.ibis_substrait import to_substrait_json

Engine = str
"""An engine's name, as its plugin registers it (`sverify.profiles`):
`"duckdb"`, `"polars"`, `"spark"`, and any installed one. A `Connection` runs
plans on the local ones (`ENGINES`); `sverify.engines.run` and
`Node.refresh` also run them on Spark."""
ENGINES: tuple[Engine, ...] = _engines.LOCAL
"""The engines a `Connection` runs plans on: `"duckdb"` (the default) and
`"polars"`. Loop over it to run a plan on each, as the tests do.
`sverify.engines.run` also takes `"spark"` or a Spark session."""


def _ibis_backend() -> Any:
    """An Ibis DuckDB backend on a cursor of its own to the process's
    database (`sverify._duckdb`), where the tables DuckDB holds live too."""
    return ibis.duckdb.from_connection(_duckdb.cursor())


class _Arrow(MutableMapping[str, pa.Table]):
    """`Connection.arrow`: the connection's tables as Arrow tables. A table
    DuckDB reads where it is (a `Scan` or `Resident`) is read into Arrow
    when it is first looked up here, and is held as that Arrow table from
    then on."""

    def __init__(self, con: Connection):
        self._con = con

    def __getitem__(self, name: str) -> pa.Table:
        table = self._con._tables[name]
        if isinstance(table, Native):
            self._con.put(name, table.to_arrow())
            table = self._con._tables[name]
        assert isinstance(table, pa.Table)
        return table

    def __setitem__(self, name: str, table: pa.Table) -> None:
        self._con.put(name, table)

    def __delitem__(self, name: str) -> None:
        if name not in self._con._tables:
            raise KeyError(name)
        self._con.drop(name)

    def __iter__(self) -> Iterator[str]:
        return iter(list(self._con._tables))

    def __len__(self) -> int:
        return len(self._con._tables)

    def __contains__(self, name: object) -> bool:
        return name in self._con._tables


class Connection:
    """Named Arrow tables, and the engine that runs plans over them.

    `sverify.connect()` makes one; the class is for type hints.

    * `create(name, schema, rows)` and `put(name, table)` add a table;
      `get(name)` is the table as given, the input of every engine, and
      `rows(name)` its rows. A table may instead be one DuckDB reads where
      it is: a table format's files (`Scan`), or a table DuckDB holds, such
      as a view's state (`Resident`).
    * `table(name)` is an Ibis table bound to it, through an Ibis DuckDB
      backend that views the Arrow tables. Contracts find a table's data
      and metadata through it, and Ibis's own `execute` works on it;
      `con.table(name).get_backend()` is the backend, for SQL of your own.
    * `engine` runs plans (`sverify.engines.run`) unless a call names
      another.

    Args:
        engine: `"duckdb"` or `"polars"`. Default: the installed default engine
            (`ProfilePlugin.default`: DuckDB).

    Attributes:
        engine: The engine that runs plans unless a call names another.
        arrow: Deprecated: the tables by name, as Arrow tables; `get`,
            `rows` and `put` read and write them.
        ibis: Deprecated: the Ibis DuckDB backend the bound tables read
            through; `table(name).get_backend()` is the same backend.

    Raises:
        ValueError: `engine` is unknown.
    """

    def __init__(self, engine: Engine | None = None):
        from sverify import profiles

        plugin = profiles.find(engine if engine is not None else _engines.default())
        if plugin is None or not plugin.local:
            raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")
        self.engine: Engine = plugin.engine  # type: ignore[assignment] - an installed engine's name
        self._tables: dict[str, pa.Table | Native] = {}
        self._views: dict[str, Any] = {}
        self._arrow: MutableMapping[str, pa.Table] = _Arrow(self)
        self._ibis: Any = _ibis_backend()
        # A bound table keeps its backend alive, and the backend its connection.
        self._ibis._sverify_connection = self

    def table(self, name: str) -> ir.Table:
        """Table `name` as an Ibis table bound to the connection. Its schema is
        the Arrow table's, nullability included (DuckDB's view of it drops
        NOT NULL, which contracts read).

        Args:
            name: A table of the connection.

        Returns:
            The bound Ibis table.

        Raises:
            KeyError: The connection has no table `name`.
        """
        schema = ibis.Schema.from_pyarrow(self.schema(name))
        return ops.DatabaseTable(name, schema=schema, source=self._ibis).to_expr()

    @property
    def arrow(self) -> MutableMapping[str, pa.Table]:
        """Deprecated: the tables by name, as Arrow tables."""
        warnings.warn(
            "Connection.arrow is deprecated; read a table with con.get(name) or "
            "con.rows(name), and write one with con.put(name, table)",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._arrow

    @property
    def ibis(self) -> Any:
        """Deprecated: the Ibis DuckDB backend the bound tables read through."""
        warnings.warn(
            "Connection.ibis is deprecated; con.table(name).get_backend() is the same Ibis backend",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._ibis

    def create(
        self, name: str, schema: ibis.Schema | pa.Schema, rows: Iterable[tuple] = ()
    ) -> None:
        """Add table `name` with `schema` (Ibis or Arrow) and `rows` (tuples
        in schema order), replacing any table of that name.

        Args:
            name: The table's name.
            schema: Its schema, as an Ibis or Arrow schema. An Arrow schema
                can mark columns NOT NULL (`nullable=False`), which contracts
                use.
            rows: Tuples in the schema's column order. Default: no rows.
        """
        arrow_schema = schema if isinstance(schema, pa.Schema) else schema.to_pyarrow()
        self.put(name, to_arrow(rows, arrow_schema))

    def rows(self, name: str) -> list[tuple]:
        """The rows of table `name`, as tuples in schema order, in the
        table's order.

        Raises:
            KeyError: The connection has no table `name`.
        """
        return arrow_rows(self._arrow[name])

    def has(self, name: str) -> bool:
        """Whether the connection has a table `name`."""
        return name in self._tables

    def get(self, name: str) -> pa.Table | Native:
        """Table `name` as it is held: an Arrow table, or a table DuckDB
        reads where it is (`Scan`, `Resident`)."""
        return self._tables[name]

    def schema(self, name: str) -> pa.Schema:
        """The Arrow schema of table `name`."""
        return self._tables[name].schema

    def put(self, name: str, table: pa.Table | Native) -> None:
        """Add or replace table `name`, as it is: no copy. The engines read
        `-0.0` as `0.0` and every NaN as one, as the model has them. The
        table is registered with the Ibis backend.

        Args:
            name: The table's name.
            table: Its contents, or a table DuckDB reads where it is (a
                `Scan` of files, a `Resident` table), which the Ibis backend
                views.
        """
        self.drop(name)
        if isinstance(table, Native):
            if isinstance(table, Scan):
                table = replace(table, schema=plain_schema(table.schema))
            self._tables[name] = table
            # A scan whose files were removed is held, but cannot be read.
            if table.readable():
                self._views[name] = table.attach(self._ibis.con, name)
                try:
                    _check_calendar_view(self._ibis.con, name, table)
                except BaseException:
                    self.drop(name)
                    raise
            return
        _check_times(table.schema)
        _check_calendar(table)
        self._tables[name] = table
        self._ibis.con.register(name, table)

    def drop(self, name: str) -> None:
        """Remove table `name`; nothing happens if there is none."""
        if (table := self._tables.pop(name, None)) is None:
            return
        if (drop := self._views.pop(name, None)) is not None:
            drop()
        elif isinstance(table, pa.Table):
            self._ibis.con.unregister(name)


def connect(engine: Engine | None = None) -> Connection:
    """A new, empty connection whose plans run on `engine`.

    Args:
        engine: `"duckdb"` or `"polars"` (see
            `sverify.engines.ENGINES`). Default: the installed default
            engine (`ProfilePlugin.default`: DuckDB).

    Returns:
        A connection with no tables. Add them with
        `Connection.create` or `Connection.put`.

    Raises:
        ValueError: `engine` is unknown.
    """
    return Connection(engine)


def connection_of(table: ir.Table) -> Connection | None:
    """The connection a bound Ibis table reads from, if any."""
    try:
        backend = ibis.get_backend(table)
    except Exception:  # noqa: BLE001 - unbound
        return None
    return getattr(backend, "_sverify_connection", None)


def plan_json(con: Connection, query: ir.Table | str, semantics: str = "reference") -> str:
    """The Substrait plan of a query, as protobuf JSON: an Ibis expression
    through the vendored producer, SQL through sverify's lift
    (`substrait_json`) with `semantics`."""
    with _stages.stage("lift"):
        if isinstance(query, str):
            return substrait_json(con, query, semantics)
        return to_substrait_json(query, semantics)


def substrait_json(con: Connection, sql: str, semantics: str = "reference") -> str:
    """Compile DuckDB's SQL to a Substrait plan with sverify's lift
    (`sverify.sql_lift`, SQLGlot), as protobuf JSON.

    The plan reads the connection's tables by name, and states every choice
    DuckDB's SQL leaves implicit: casts, output types, function options and
    sort directions.

    Args:
        con: The connection whose tables the SQL reads.
        sql: A query in DuckDB's SQL dialect.
        semantics: `"reference"` (the default, as for `sv.verify` and
            `sv.sql`): what sverify's reference model computes; or
            `"duckdb"`: what DuckDB computes where the two differ. Before
            0.6 the default was `"duckdb"`.

    Returns:
        The Substrait plan as protobuf JSON.

    Raises:
        Unsupported: The query is outside what the lift reads (a
            `ValueError`), saying what.
    """

    from sverify.sql_lift import lift

    try:
        read = {t.name.lower() for t in sg.parse_one(sql, read="duckdb").find_all(sg.exp.Table)}
    except sg.errors.ParseError:
        read = set()  # the lift says why
    schemas = {
        name: ibis.Schema.from_pyarrow(con.schema(name))
        for name in con._arrow
        if name.lower() in read
    }
    return json.dumps(lift(sql, schemas, semantics).plan)


def quote(name: str) -> str:
    """A quoted SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


class SqlError(SverifyError, ValueError):
    """A SQL producer refused a query."""

    code = "sql_refused"


def canonical(table: pa.Table) -> pa.Table:
    """Doubles as the model has them: `-0.0` as `0.0` and every NaN as the
    positive one."""
    columns = []
    for c in table.columns:
        if pa.types.is_floating(c.type):
            nan = pa.scalar(float("nan"), c.type)
            zero = pc.call_function("add", [c, pa.scalar(0.0, c.type)])
            c = pc.call_function("if_else", [pc.call_function("is_nan", [c]), nan, zero])
        columns.append(c)
    return pa.Table.from_arrays(columns, schema=table.schema)


class NotIncrementalError(SverifyError):
    """The plan is outside the fragment with verified delta rules.

    Raised by `sverify.engines.delta_plans` for a plan with an operator
    without a delta rule (a left join, aggregate, window, `DISTINCT` or
    `LIMIT`). A node over such a plan is recomputed and diffed instead, so
    refreshing it does not raise this. (A view that ends in `COUNT` and `SUM`
    per group, or in `DISTINCT`, is maintained from a state per group,
    `sverify._linear`.) The message is the checker's reason.
    """

    code = "not_incremental"


def delta_plans(plan_json: str) -> list[str]:
    """Ask Lean for the weighted delta plan of a Substrait JSON plan; its
    output is the change to the view.

    The delta plan reads the view's input tables `t` at their old contents
    and their changes as tables `t$delta`, which have the columns of `t` and
    an extra `__weight` column (+1 for an inserted row, -1 for a deleted
    one). Its output has the view's columns and a weight column likewise.

    Args:
        plan_json: A Substrait plan as protobuf JSON, as
            `sverify.engines.substrait_json` or a node's `plan` write it.

    Returns:
        The delta plan, a Substrait JSON plan in Lean's written form, as a
        one-item list. A checker older than 0.8 printed several plans whose
        outputs add up to the change; callers concatenate the outputs.

    Raises:
        sverify.errors.NotIncrementalError: The plan has an operator without a
            verified delta rule.
        ValueError: The checker rejects the plan.
    """
    code, out, err = run_checker(("--delta",), plan_json)
    if code == 3:
        raise NotIncrementalError(err.strip())
    if code != 0:
        raise checker_failed("--delta", err)
    return out.splitlines()


def stale_checker(path: Path | None = None) -> str | None:
    """Why the checker at `path` is older than this sverify, where it is a
    build in a source checkout (`.lake/build/bin/substrait-check`, an
    editable install or `SVERIFY_CHECKER`) and a Lean source of that checkout
    is newer than it; None otherwise. A checker that speaks this sverify's
    protocol may still lack a feature the Python side asks for (#687)."""
    try:
        path = (path or checker_path()).resolve()
        root = path.parents[3]
        if path.parent.parts[-3:] != (".lake", "build", "bin"):
            return None
        sources = [
            root / "SubstraitLean.lean",
            *(root / "SubstraitLean").rglob("*.lean"),
            *(root / "core").rglob("*.lean"),
            *(root / "analysis").rglob("*.lean"),
            *(root / "engines").rglob("*.lean"),
        ]
        built = path.stat().st_mtime
        newer = [f for f in sources if f.exists() and f.stat().st_mtime > built]
    except (OSError, IndexError):
        return None
    if not newer:
        return None
    return (
        f"the checker at {path} is older than this sverify: {len(newer)} Lean source(s) "
        f"changed since it was built (e.g. {newer[0].relative_to(root)}); {_REBUILD}, "
        "or unset SVERIFY_CHECKER"
    )


def checker_failed(mode: str, err: str) -> Exception:
    """The error for a checker request that failed: `CheckerVersionError`
    where the checker is a stale build (`stale_checker`), else an
    `UnsupportedError` (a `ValueError`) with the checker's message and its
    exit."""
    if (why := stale_checker()) is not None:
        return CheckerVersionError(f"{why}. The checker said: {err.strip()}")
    return checker_refusal(mode, err)


def read_tables(plan: dict) -> list[str]:
    """Named tables a Substrait plan reads."""
    found: list[str] = []

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node["namedTable"]["names"])
                if name not in found:
                    found.append(name)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


def written_plan(plan_json: str) -> str:
    """The plan as Lean parsed it, written back out from its `Rel`
    (`substrait-check --write`; the golden tests check this round trip), once
    the checker has found it well-formed.

    This is the form `sverify.engines.run` and `sverify.engines.to_sql`
    take, and what a node's `plan` holds.

    Args:
        plan_json: A Substrait plan as protobuf JSON.

    Returns:
        The plan in Lean's written form, as protobuf JSON.

    Raises:
        UnsupportedError: The checker rejects the plan (an operator, function
            or type outside the Lean model, or an ill-formed plan).
    """

    def check(*flags: str) -> str:
        code, out, err = run_checker(flags, plan_json)
        if code != 0:
            raise checker_failed(" ".join(flags) or "--check", err or out)
        return out

    check()
    return check("--write")


@overload
def run_plan(
    con: Connection,
    plan_json: str,
    engine: Engine | Any = None,
    *,
    keep: Literal[False] = False,
    finite: bool = True,
    tie_free: bool = False,
) -> pa.Table: ...


@overload
def run_plan(
    con: Connection,
    plan_json: str,
    engine: Engine | Any = None,
    *,
    keep: bool,
    finite: bool = True,
    tie_free: bool = False,
) -> pa.Table | Resident: ...


def run_plan(
    con: Connection,
    plan_json: str,
    engine: Engine | Any = None,
    *,
    keep: bool = False,
    finite: bool = True,
    tie_free: bool = False,
) -> pa.Table | Resident:
    """Run a plan in Lean's written form on `engine` (default: the
    connection's), over the tables of `con`. `"spark"` runs it
    on the local Spark session (`sverify_spark.engine.session`), and a Spark
    session as `engine` runs it there.

    DuckDB runs the SQL `sverify.engines.to_sql` writes for the plan, Polars
    a translation to a lazy frame, Spark the Spark SQL
    `sverify.engines.to_sql` writes in the `SPARK` dialect; each gives the result `Rel.eval` gives.
    This is `sverify.engines.run`.

    Args:
        con: The connection whose tables the plan reads.
        plan_json: A plan in Lean's written form (a node's `plan`, or
            `sverify.engines.written_plan`'s output).
        engine: `"duckdb"`, `"polars"`, `"spark"`, or a Spark session.
            Default: the connection's engine.
        keep: On DuckDB, leave the result in DuckDB, as a `Resident` table.
            Other engines ignore it. Default: False.
        finite: On DuckDB, Polars and Spark, check that no operation on finite
            doubles gives `±∞` (`Issue.infinite`, #575), the reference's
            precondition. Default: True; `Report.run` passes False for a
            plan verified with `semantics="duckdb"`, which allows `±∞`.
        tie_free: On Spark, the plan's windows have no ties on data that
            meets its preconditions (a proved report's `deterministic`), so
            they run without a row-order tiebreak (`to_sql`'s
            `deterministic`). Default: False; `Report.run` and a stored
            node's refresh pass the report's fact.

    Returns:
        The result as an Arrow table, with the plan's output names; with
        `keep` on DuckDB, a `Resident` table.

    Raises:
        ValueError: `engine` is unknown, or the checker rejects the plan.
        ImportError: The engine is an extra that is not installed.
        sverify.engines.UnsupportedError: The plan uses something the engine's
            SQL dialect cannot express (DuckDB, Spark). Polars refuses what
            its translation does not cover with a `ValueError` of its own.

    Examples:
        The plan of a transform, on every engine:

        ```python
        import ibis
        import pyarrow as pa
        import sverify as sv
        from sverify.engines import ENGINES, run
        from sverify.io import StaticSource

        orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        plan = big_orders(orders).internal_plan  # the plan the checker proved

        con = sv.connect()
        con.create("orders", ibis.schema({"id": "int64", "amount": "int64"}), [(1, 30), (2, 5)])
        for engine in ENGINES:
            assert run(con, plan, engine).to_pylist() == [{"id": 1, "amount": 30}]
        ```
    """
    from sverify import profiles

    engine = engine or con.engine
    plugin = profiles.find(engine)
    if plugin is None or plugin.runner is None:
        raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")
    # A session of the caller's (Spark's) runs the plan there; a name, on the
    # engine's own.
    session = None if isinstance(engine, str) else engine
    return plugin.runner(con, plan_json, session, keep=keep, finite=finite, tie_free=tie_free)


def run_guard_free(
    con: Connection, plan_json: str, engine: str, theorem: str | None, *, finite: bool = True
) -> pa.Table:
    """Run a plan whose contract report is `guard_free` on `engine` without
    its other per-row checks, on data that meets its preconditions. The
    assumed issues keep their checks. The engine's plugin names the theorem
    that covers its writer without them (`ProfilePlugin.guard_free_theorem`),
    and the checker names it per engine (`"guard_free_theorem"`,
    `SubstraitLean/Realize.lean`).

    Raises:
        ValueError: No theorem covers the engine's writer without them, or
            `theorem` is not the one that does.
    """
    from sverify import profiles

    plugin = profiles.find(engine)
    run = plugin.run_tables if plugin is not None else None
    covers = plugin.guard_free_theorem if plugin is not None and run is not None else ""
    if run is None or not covers or theorem != covers:
        raise ValueError(
            f"no theorem covers {engine}'s writer without its guards"
            + (f" ({theorem} is not its writer's)" if theorem and covers else "")
        )
    tables = {t: con._arrow[t] for t in read_tables(json.loads(plan_json))}
    return run(plan_json, tables, guard_free=True, finite=finite)


def _rename_tables(node: object, names: dict[str, str]) -> None:
    """Rename the named tables a Substrait plan (as a dict) reads, in place."""
    if isinstance(node, dict):
        if "namedTable" in node:
            name = ".".join(node["namedTable"]["names"])
            node["namedTable"]["names"] = [names.get(name, name)]
        for v in node.values():
            _rename_tables(v, names)
    elif isinstance(node, list):
        for v in node:
            _rename_tables(v, names)


def put_table(con: Connection, name: str, table: pa.Table | Native) -> None:
    """Register (or replace) an in-memory table, or one DuckDB reads where
    it is (`Scan`, `Resident`)."""
    con.put(name, table)


#: The reference's dates and timestamps (D32), 0001-01-01 to 9999-12-31:
#: days and microseconds since 1970-01-01 (`Time.dayMin` … `Time.tsMax`).
_DAY_MIN, _DAY_MAX = -719162, 2932896
_TS_MIN, _TS_MAX = -62135596800000000, 253402300799999999
_PER_UNIT = {"s": 1_000_000, "ms": 1000, "us": 1}


def _calendar_range(t: pa.DataType) -> tuple[pa.DataType, int, int, str] | None:
    """For a DATE or TIMESTAMP column: its physical integer type and the
    reference's range in its unit (D32), and what its values are called.
    None for other types, and for nanosecond timestamps, which reach only
    1677 to 2262."""
    if pa.types.is_date32(t):
        return pa.int32(), _DAY_MIN, _DAY_MAX, "dates"
    if pa.types.is_date64(t):
        ms = 86_400_000
        return pa.int64(), _DAY_MIN * ms, (_DAY_MAX + 1) * ms - 1, "dates"
    if pa.types.is_timestamp(t) and t.unit in _PER_UNIT:
        k = _PER_UNIT[t.unit]
        return pa.int64(), -(-_TS_MIN // k), _TS_MAX // k, "timestamps"
    return None


def _calendar_error(column: str, what: str, count: int, example: str) -> Exception:
    from sverify.plan_json import Unsupported

    return Unsupported(
        f"{column} holds {what} outside 0001–9999 ({count}, e.g. {example}); the reference's "
        "calendar covers 0001–9999. Filter them, or read the column as text."
    )


def _check_calendar(table: pa.Table) -> None:
    """Refuse a DATE or TIMESTAMP column with a value outside the reference's
    0001-01-01 to 9999-12-31 (D32): the checker takes a column read to lie in
    it by its type (`ContractCheck.typeEnv`), so the read checks it, once per
    column, naming the column, the count and one value."""
    for f in table.schema:
        r = _calendar_range(f.type)
        if r is None:
            continue
        phys, lo, hi, what = r
        x = table.column(f.name).cast(phys)
        mm = pc.call_function("min_max", [x]).as_py()
        if mm["min"] is None or (lo <= mm["min"] and mm["max"] <= hi):
            continue
        bad = pc.call_function(
            "or", [pc.call_function("less", [x, lo]), pc.call_function("greater", [x, hi])]
        )
        count = pc.call_function("sum", [bad]).as_py()
        example = table.column(f.name).filter(bad).cast(pa.string())[0].as_py()
        raise _calendar_error(f.name, what, count, example)


def _parquet_in_calendar(files: tuple[str, ...], columns: list[str]) -> bool:
    """Whether the Parquet files' min/max statistics put every value of
    `columns` in the reference's calendar. Python's dates and datetimes span
    exactly 0001 to 9999, so a statistic that reads as one is in range; one
    that is missing, or does not read as one, sends the read to the rows."""
    import datetime as dt

    import pyarrow.parquet as pq

    try:
        for path in files:
            meta = pq.ParquetFile(path).metadata
            names = [meta.schema.column(i).name for i in range(meta.num_columns)]
            for g in range(meta.num_row_groups):
                group = meta.row_group(g)
                for c in columns:
                    if c not in names:
                        return False
                    stats = group.column(names.index(c)).statistics
                    if stats is None or not stats.has_min_max:
                        return False
                    if not all(isinstance(v, dt.date) for v in (stats.min, stats.max)):
                        return False
    except Exception:  # noqa: BLE001 - statistics that do not read: check the rows
        return False
    return True


def _check_calendar_view(db: Any, name: str, table: Native) -> None:
    """`_check_calendar` for a table DuckDB reads where it is: discharged by
    the files' Parquet statistics where they cover every column (Delta and
    Iceberg write them), else one range predicate per column over the view."""
    from sverify._scan import _q

    columns = [(f.name, r) for f in table.schema if (r := _calendar_range(f.type)) is not None]
    if not columns:
        return
    if isinstance(table, Scan) and _parquet_in_calendar(table.files, [c for c, _ in columns]):
        return
    for column, (_, _, _, what) in columns:
        if what == "dates":
            lo, hi = "DATE '0001-01-01'", "DATE '9999-12-31'"
        else:
            lo, hi = "TIMESTAMP '0001-01-01 00:00:00'", "TIMESTAMP '9999-12-31 23:59:59.999999'"
        q = _q(column)
        bad = f"{q} < {lo} OR {q} > {hi}"
        count, example = db.execute(
            f"SELECT count(*), CAST(min({q}) FILTER (WHERE {bad}) AS VARCHAR) "
            f"FROM {_q(name)} WHERE {bad}"
        ).fetchall()[0]
        if count:
            raise _calendar_error(column, what, count, example)


def _check_times(schema: pa.Schema) -> None:
    """Refuse a column of times in nanoseconds (`time64[ns]`, DuckDB's
    `TIME_NS`): the model's times are microseconds, and Ibis's time type has
    no unit, so the plan would read it as microseconds and the engine keep
    the nanoseconds (#627)."""
    from sverify.plan_json import Unsupported

    def walk(t: pa.DataType) -> bool:
        if pa.types.is_time64(t):
            return t.unit == "ns"
        if pa.types.is_struct(t):
            return any(walk(t.field(i).type) for i in range(t.num_fields))
        if pa.types.is_list(t) or pa.types.is_large_list(t) or pa.types.is_fixed_size_list(t):
            return walk(t.value_type)
        if pa.types.is_map(t):
            return walk(t.key_type) or walk(t.item_type)
        return False

    for f in schema:
        if walk(f.type):
            raise Unsupported(
                f"column {f.name}: times in nanoseconds ({f.type}) are not supported; "
                "cast them to microseconds (time64[us])"
            )


def plain_schema(schema: pa.Schema) -> pa.Schema:
    """`schema` with large and view strings as plain `string`: the type the
    plans name (Substrait has one string type). Table formats such as Iceberg read
    strings as `large_string`."""
    plain = (pa.types.is_large_string, getattr(pa.types, "is_string_view", lambda _: False))
    fields = [f.with_type(pa.string()) if any(p(f.type) for p in plain) else f for f in schema]
    return pa.schema(fields, metadata=schema.metadata)


def arrow_rows(table: pa.Table) -> list[tuple]:
    """The rows of an Arrow table, as tuples in schema order, read column by
    column: no dictionary per row."""
    if table.num_columns == 0:
        return [()] * table.num_rows
    return list(zip(*(c.to_pylist() for c in table.columns), strict=True))


def to_arrow(rows, schema: pa.Schema) -> pa.Table:
    """Rows (tuples in schema order) as an Arrow table, built column by
    column: no dictionary per row.

    Raises:
        ValueError: A row's length is not the schema's.
    """
    rows = rows if isinstance(rows, list | tuple) else list(rows)
    n = len(schema)
    if any(len(r) != n for r in rows):
        raise ValueError(f"every row needs {n} values, one per column of {schema.names}")
    columns = list(zip(*rows, strict=True)) if rows else [()] * n
    if n == 0:
        return pa.Table.from_pylist([{} for _ in rows], schema=schema)
    arrays = [pa.array(c, type=f.type) for c, f in zip(columns, schema, strict=True)]
    return pa.Table.from_arrays(arrays, schema=schema)


def create_table(con: Connection, name: str, schema: ibis.Schema | pa.Schema, rows=()) -> None:
    """Deprecated: `con.create(name, schema, rows)`."""
    warnings.warn(
        "sverify.engines.create_table(con, ...) is deprecated; "
        "write con.create(name, schema, rows)",
        DeprecationWarning,
        stacklevel=2,
    )
    con.create(name, schema, rows)


def table_rows(con: Connection, name: str) -> list[tuple]:
    """Deprecated: `con.rows(name)`."""
    warnings.warn(
        "sverify.engines.table_rows(con, name) is deprecated; write con.rows(name)",
        DeprecationWarning,
        stacklevel=2,
    )
    return con.rows(name)
