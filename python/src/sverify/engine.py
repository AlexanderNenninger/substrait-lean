"""Substrait producers, and DuckDB, Polars or DataFusion as consumer.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

`connect()` gives a `Connection`: named Arrow tables, the engine that runs
plans over them (DuckDB by default), and Ibis tables bound to them
(`con.table(name)`). `plan_json` compiles Ibis expressions with the vendored
producer (`sverify.ibis_substrait`, typed and engine-neutral) and SQL strings
(DuckDB's SQL) with sverify's lift (`sverify.sql_lift`). `run_plan` runs a plan in Lean's
written form (`substrait-check --write`, `--delta`) on the connection's engine
or the one a call names.

DataFusion is optional (`pip install 'sverify[datafusion]'`): it is needed
only to run plans with `engine="datafusion"`.
"""

from __future__ import annotations

import atexit
import functools
import json
import os
import subprocess
import threading
from pathlib import Path
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa
import pyarrow.compute as pc
import sqlglot as sg
from google.protobuf import json_format
from substrait.plan_pb2 import Plan

from sverify.ibis_substrait import to_substrait_json
from sverify.sql import core as sql

Engine = Literal["duckdb", "polars", "datafusion"]
ENGINES: tuple[Engine, ...] = ("duckdb", "polars", "datafusion")
"""The engines a `Connection` runs plans on: `"duckdb"` (the default),
`"polars"` and `"datafusion"`. Loop over it to run a plan on each, as the
tests do. `sverify.engines.run` also takes `"spark"` or a Spark session."""


def _datafusion() -> Any:
    """The `datafusion` module, or an error saying how to install it."""
    try:
        import datafusion
        import datafusion.substrait
    except ImportError as e:
        raise ImportError(
            "this needs DataFusion: pip install 'sverify[datafusion]' "
            "(it runs plans with engine='datafusion')"
        ) from e
    return datafusion


def has_datafusion() -> bool:
    try:
        _datafusion()
    except ImportError:
        return False
    return True


def _register(ctx: Any, name: str, table: pa.Table) -> None:
    """Register (or replace) a table in a DataFusion session, as record
    batches rather than a PyArrow dataset: DataFusion pushes filters into
    datasets, where PyArrow compares doubles by IEEE rules instead of
    DataFusion's total order (NaN = NaN)."""
    if ctx.table_exist(name):
        ctx.deregister_table(name)
    batches = table.to_batches() or [pa.RecordBatch.from_pylist([], schema=table.schema)]
    ctx.register_record_batches(name, [batches])


#: The DuckDB database behind every connection's Ibis backend, created on
#: first use. Each connection gets its own DuckDB connection to it (a
#: cursor), whose registered tables and settings are its own. A database
#: per connection would start a thread pool per connection, which lives until
#: the cyclic garbage collector frees the connection (its backend refers back
#: to it): a few hundred connections reach macOS's per-process thread limit.
_IBIS_DB: Any = None
_IBIS_DB_LOCK = threading.Lock()


def _ibis_backend() -> Any:
    global _IBIS_DB
    import duckdb

    with _IBIS_DB_LOCK:
        if _IBIS_DB is None:
            _IBIS_DB = duckdb.connect()
        cursor = _IBIS_DB.cursor()
    return ibis.duckdb.from_connection(cursor)


class Connection:
    """Named Arrow tables, and the engine that runs plans over them.

    * `arrow[name]` is the table as given (`put`), the input of every engine.
    * `table(name)` is an Ibis table bound to it, through an Ibis DuckDB
      backend that views the Arrow tables (`ibis`). Contracts find a table's
      data and metadata through it, and Ibis's own `execute` works on it.
    * `engine` runs plans (`sverify.engines.run`) unless a call names
      another.
    * `datafusion` is a DataFusion session holding the same tables (with the
      functions Ibis's DataFusion SQL calls), created on first use; only the
      DataFusion engine needs it.

    `sverify.connect()` makes one.

    Args:
        engine: `"duckdb"`, `"polars"` or `"datafusion"`. Default:
            `"duckdb"`.

    Attributes:
        engine: The engine that runs plans unless a call names another.
        arrow: The tables by name, as Arrow tables.
        ibis: The Ibis DuckDB backend the bound tables read through.

    Raises:
        ValueError: `engine` is unknown.
    """

    def __init__(self, engine: Engine = "duckdb"):
        if engine not in ENGINES:
            raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")
        self.engine: Engine = engine
        self.arrow: dict[str, pa.Table] = {}
        self.ibis: Any = _ibis_backend()
        # A bound table keeps its backend alive, and the backend its connection.
        self.ibis._sverify_connection = self
        self._datafusion: Any = None

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
        schema = ibis.Schema.from_pyarrow(self.arrow[name].schema)
        return ops.DatabaseTable(name, schema=schema, source=self.ibis).to_expr()

    def has(self, name: str) -> bool:
        """Whether the connection has a table `name`."""
        return name in self.arrow

    def put(self, name: str, table: pa.Table) -> None:
        """Add or replace table `name`, with doubles as the model has them
        (`canonical`: one zero, one NaN).

        Large and view strings become plain strings, the one string type of
        Substrait plans. The table is registered with the Ibis backend and,
        once it exists, the DataFusion session.

        Args:
            name: The table's name.
            table: Its contents.
        """
        table = canonical(table.cast(plain_schema(table.schema)))
        self.drop(name)
        self.arrow[name] = table
        self.ibis.con.register(name, table)
        if self._datafusion is not None:
            _register(self._datafusion, name, table)

    def drop(self, name: str) -> None:
        """Remove table `name`; nothing happens if there is none."""
        if self.arrow.pop(name, None) is None:
            return
        self.ibis.con.unregister(name)
        if self._datafusion is not None and self._datafusion.table_exist(name):
            self._datafusion.deregister_table(name)

    @property
    def datafusion(self) -> Any:
        """A `datafusion.SessionContext` with the connection's tables.

        Raises:
            ImportError: DataFusion is not installed (`pip install
                'sverify[datafusion]'`).
        """
        if self._datafusion is None:
            _datafusion()
            # Ibis's DataFusion backend registers the UDFs its SQL calls
            # (`extract_epoch_seconds_timestamp`, …).
            ctx = ibis.datafusion.connect().con
            for name, table in self.arrow.items():
                _register(ctx, name, table)
            self._datafusion = ctx
        return self._datafusion


def connect(engine: Engine = "duckdb") -> Connection:
    """A new, empty connection whose plans run on `engine`.

    Args:
        engine: `"duckdb"`, `"polars"` or `"datafusion"` (see
            `sverify.engines.ENGINES`). Default: `"duckdb"`.

    Returns:
        A connection with no tables. Add them with
        `sverify.engines.create_table` or `Connection.put`.

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


def plan_json(con: Connection, query: ir.Table | str) -> str:
    """The Substrait plan of a query, as protobuf JSON: an Ibis expression
    through the vendored producer, SQL through sverify's lift
    (`substrait_json`)."""
    if isinstance(query, str):
        return substrait_json(con, query)
    return to_substrait_json(query)


def substrait_json(con: Connection, sql: str, semantics: str = "duckdb") -> str:
    """Compile DuckDB's SQL to a Substrait plan with sverify's lift
    (`sverify.sql_lift`, SQLGlot), as protobuf JSON.

    The plan reads the connection's tables by name, and states every choice
    DuckDB's SQL leaves implicit: casts, output types, function options and
    sort directions.

    Args:
        con: The connection whose tables the SQL reads.
        sql: A query in DuckDB's SQL dialect.
        semantics: `"duckdb"` (the default): what DuckDB computes; or
            `"reference"`: what sverify's reference model computes where the
            two differ.

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
        name: ibis.Schema.from_pyarrow(t.schema)
        for name, t in con.arrow.items()
        if name.lower() in read
    }
    return json.dumps(lift(sql, schemas, semantics).plan)


def quote(name: str) -> str:
    """A quoted SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


class SqlError(ValueError):
    """A SQL producer refused a query."""


def run_substrait_json(con: Connection, plan_json: str) -> pa.Table:
    """Run a Substrait plan on DataFusion.

    The plan runs as given; `sverify.engines.run(con, plan, "datafusion")`
    first rewrites a plan in Lean's written form where DataFusion's
    semantics differ, and is what to use for checked plans.

    Args:
        con: The connection whose tables the plan reads.
        plan_json: A Substrait plan as protobuf JSON.

    Returns:
        The result, with doubles as `canonical` makes them.

    Raises:
        ImportError: DataFusion is not installed.
    """
    ss = _datafusion().substrait
    ctx = con.datafusion
    proto = Plan()
    json_format.Parse(plan_json, proto)
    logical = ss.Consumer.from_substrait_plan(
        ctx, ss.Serde.deserialize_bytes(proto.SerializeToString())
    )
    return canonical(collect(ctx.create_dataframe_from_logical_plan(logical)))


def collect(df: Any) -> pa.Table:
    """A DataFusion DataFrame's result as one Arrow table.

    DataFusion 51 can return record batches whose schemas differ only in
    nullability: the branches of a `UNION ALL` (`SELECT 'x' UNION ALL SELECT
    NULL`, a recursive CTE's anchor and step) each keep their own, and its
    `to_arrow_table()` then fails to concatenate them. A recursive CTE's
    batches can also differ in column names. The result has the first batch's
    names and types, and a column is nullable if it is in any batch."""
    batches = df.collect()
    if not batches:
        return df.to_arrow_table()
    first = batches[0].schema
    nullable = [any(b.schema.field(i).nullable for b in batches) for i in range(len(first))]
    schema = pa.schema(
        [f.with_nullable(n) for f, n in zip(first, nullable, strict=True)], first.metadata
    )
    return pa.Table.from_batches(
        [
            pa.RecordBatch.from_arrays(
                [c.cast(f.type) for c, f in zip(b.columns, schema, strict=True)], schema=schema
            )
            for b in batches
        ],
        schema,
    )


def canonical(table: pa.Table) -> pa.Table:
    """Doubles as the model has them: `-0.0` as `0.0` and every NaN as the
    positive one. Connections store tables this way; DataFusion orders
    doubles by `f64::total_cmp`, where both signs show, so its results go
    through this too, and the plans Lean writes canonicalize what an
    operation computes (`Write.canonical`)."""
    columns = []
    for c in table.columns:
        if pa.types.is_floating(c.type):
            nan = pa.scalar(float("nan"), c.type)
            zero = pc.call_function("add", [c, pa.scalar(0.0, c.type)])
            c = pc.call_function("if_else", [pc.call_function("is_nan", [c]), nan, zero])
        columns.append(c)
    return pa.Table.from_arrays(columns, schema=table.schema)


def checker_path() -> Path:
    """`$SVERIFY_CHECK` if set, else the `substrait-check` the wheel ships with
    (a symlink to the lake build in an editable install)."""
    if env := os.environ.get("SVERIFY_CHECK"):
        return Path(env)
    bundled = Path(__file__).parent / "_bin" / "substrait-check"
    if not bundled.exists():
        raise FileNotFoundError(f"{bundled} is missing; reinstall sverify or set SVERIFY_CHECK")
    return bundled


class _Checker:
    """One `substrait-check --serve` process, started on first use."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.proc: subprocess.Popen[bytes] | None = None
        self.path: str | None = None

    def ask(self, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
        path = str(checker_path())
        flag = " ".join(flags) or "-"
        data = stdin.encode()
        with self.lock:
            if self.proc is None or self.proc.poll() is not None or self.path != path:
                self.close()
                self.proc = subprocess.Popen(
                    [path, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE
                )
                self.path = path
            assert self.proc.stdin is not None and self.proc.stdout is not None
            self.proc.stdin.write(f"{flag} {len(data)}\n".encode() + data)
            self.proc.stdin.flush()
            header = self.proc.stdout.readline()
            if not header:
                self.close()
                raise RuntimeError("substrait-check --serve exited")
            code, m, k = map(int, header.split())
            out, err = self.proc.stdout.read(m), self.proc.stdout.read(k)
        return code, out.decode(), err.decode()

    def close(self) -> None:
        if self.proc is not None:
            self.proc.kill()
            self.proc.wait()
            self.proc = None


_CHECKER = _Checker()
atexit.register(_CHECKER.close)


@functools.lru_cache(maxsize=8192)
def _run_checker(path: str, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
    return _CHECKER.ask(flags, stdin)


def run_checker(flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
    """`substrait-check <flags>` on `stdin`: exit code, stdout, stderr.

    Requests go to one long-lived `substrait-check --serve` process (a process
    start costs ~20 ms, most of it Lean's module initialization; a request
    ~0.04 ms) and are memoized: the checker is a pure function of its input."""
    return _run_checker(str(checker_path()), flags, stdin)


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
        ValueError: The checker rejects the plan (an operator, function or
            type outside the Lean model, or an ill-formed plan).
    """

    def check(*flags: str) -> str:
        code, out, err = run_checker(flags, plan_json)
        if code != 0:
            msg = (err or out).strip().splitlines()[-1:]
            raise ValueError(f"substrait-check {' '.join(flags)} rejects the plan: {msg}")
        return out

    check()
    return check("--write")


def datafusion_plan(plan_json: str) -> str:
    """The plan for DataFusion to run (`substrait-check --write-datafusion`):
    Lean's written form, compensating for where DataFusion's semantics differ
    from `Rel.eval` (an integer `SUM` fails outside 64 bits instead of
    wrapping around)."""
    code, out, err = run_checker(("--write-datafusion",), plan_json)
    if code != 0:
        msg = (err or out).strip().splitlines()[-1:]
        raise ValueError(f"substrait-check --write-datafusion rejects the plan: {msg}")
    plan = json.loads(out)
    _check_datafusion_plan(plan)
    # sverify's own remainder of doubles (#256) is DataFusion's `%` of doubles,
    # C's `fmod` too.
    for e in plan.get("extensions", []):
        f = e.get("extensionFunction", {})
        if f.get("name", "").split(":")[0] == "sverify_fmod":
            f["name"] = "modulus"
    _datafusion_variances(plan)
    return json.dumps(plan)


def _datafusion_variances(plan: dict) -> None:
    """Substrait's `variance` and `std_dev` say sample or population in an
    option; DataFusion has a function for each (#54)."""
    exts = plan.get("extensions", [])
    names = {
        e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"].split(":")[0]
        for e in exts
        if "extensionFunction" in e
    }
    anchors: dict[str, int] = {}

    def anchor(name: str) -> int:
        if name not in anchors:
            a = max([*names, *anchors.values(), 0]) + 1
            anchors[name] = a
            exts.append({"extensionFunction": {"functionAnchor": a, "name": name}})
        return anchors[name]

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            m = node.get("measure")
            if isinstance(m, dict) and names.get(m.get("functionReference")) in (
                "variance",
                "std_dev",
            ):
                pop = any(
                    o.get("name") == "distribution"
                    and o.get("preference", [])[:1] == ["POPULATION"]
                    for o in m.get("options", [])
                )
                base = "var" if names[m["functionReference"]] == "variance" else "stddev"
                m["functionReference"] = anchor(f"{base}_pop" if pop else f"{base}_samp")
                m.pop("options", None)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)


def _check_datafusion_plan(plan: dict) -> None:
    """Refuse what DataFusion computes differently from the reference (#209):
    a `substring` whose start may be negative (DataFusion puts it left of the
    beginning, the reference counts it from the end, `Text.substrWrap`) unless
    the plan asks for `LEFT_OF_BEGINNING`; and an `avg` with an integer result
    (`AggFn.iavg`), which DataFusion computes as a double."""
    names = {
        e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"].split(":")[0]
        for e in plan.get("extensions", [])
        if "extensionFunction" in e
    }

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            for key in ("measure", "windowFunction"):
                a = node.get(key)
                is_avg = isinstance(a, dict) and names.get(a.get("functionReference")) == "avg"
                ints = ("i8", "i16", "i32", "i64")
                if is_avg and any(k in a.get("outputType", {}) for k in ints):
                    raise sql.Unsupported("DataFusion's AVG has no integer result")
            m = node.get("measure")
            if isinstance(m, dict) and names.get(m.get("functionReference")) in ("first", "last"):
                raise sql.Unsupported(
                    "first and last are not yet supported on DataFusion; see #271"
                )
            if isinstance(m, dict) and names.get(m.get("functionReference")) in (
                "covar_samp",
                "covar_pop",
                "corr",
            ):
                raise sql.Unsupported(
                    "covariance and correlation are not yet supported on DataFusion; see #271"
                )
            w = node.get("windowFunction")
            if isinstance(w, dict) and names.get(w.get("functionReference")) == "ntile":
                # DataFusion spreads the larger buckets out (upstream/LEDGER.md).
                raise sql.Unsupported("DataFusion's NTILE does not deal out buckets as SQL does")
            f = node.get("scalarFunction")
            if isinstance(f, dict) and names.get(f.get("functionReference")) == "substring":
                left = any(
                    o.get("name") == "negative_start"
                    and o.get("preference", [])[:1] == ["LEFT_OF_BEGINNING"]
                    for o in f.get("options", [])
                )
                args = f.get("arguments", [])
                lit = args[1].get("value", {}).get("literal", {}) if len(args) > 1 else {}
                start = next((v for k, v in lit.items() if k in ("i8", "i16", "i32", "i64")), None)
                if not left and (start is None or int(start) < 0):
                    raise sql.Unsupported(
                        "DataFusion's substring does not count a negative start from the end"
                    )
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)


def run_plan(con: Connection, plan_json: str, engine: Engine | Any = None) -> pa.Table:
    """Run a plan in Lean's written form on `engine` (default: the
    connection's), over the tables of `con`. DataFusion runs it as
    `datafusion_plan` writes it; `"spark"` runs it on the local Spark session
    (`sverify.spark_engine.session`), and a Spark session as `engine` runs it
    there.

    DuckDB runs the SQL `sverify.engines.to_sql` writes for the plan, Polars
    a translation to a lazy frame, Spark the Spark SQL of
    `sverify.engines.run_spark`; each gives the result `Rel.eval` gives.
    This is `sverify.engines.run`.

    Args:
        con: The connection whose tables the plan reads.
        plan_json: A plan in Lean's written form (a node's `plan`, or
            `sverify.engines.written_plan`'s output).
        engine: `"duckdb"`, `"polars"`, `"datafusion"`, `"spark"`, or a
            Spark session. Default: the connection's engine.

    Returns:
        The result as an Arrow table, with the plan's output names.

    Raises:
        ValueError: `engine` is unknown, or the checker rejects the plan.
        ImportError: The engine is an extra that is not installed.
        sverify.engines.Unsupported: The plan uses something the engine's
            SQL dialect cannot express (DuckDB, Spark). Polars refuses what
            its translation does not cover with a `ValueError` of its own.

    Examples:
        The plan of a transform, on every engine:

        ```python
        import ibis
        import pyarrow as pa
        import sverify as sv
        from sverify.engines import ENGINES, create_table, run
        from sverify.io import StaticSource

        orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


        @sv.transform()
        def big_orders(orders):
            return orders.filter(orders.amount > 10)


        plan = big_orders(orders).plan  # the plan Lean checked

        con = sv.connect()
        create_table(con, "orders", ibis.schema({"id": "int64", "amount": "int64"}),
                     [(1, 30), (2, 5)])
        for engine in ENGINES:
            assert run(con, plan, engine).to_pylist() == [{"id": 1, "amount": 30}]
        ```
    """
    engine = engine or con.engine
    if engine == "spark" or not isinstance(engine, str):
        # Spark: the local session, or the session given as the engine.
        from sverify import spark_engine

        plan = json.loads(plan_json)
        # Spark's temporary views take plain names, not the delta plans' `t$delta`.
        names = {t: f"__sverify_{i}" for i, t in enumerate(read_tables(plan))}
        _rename_tables(plan, names)
        tables = {alias: con.arrow[t] for t, alias in names.items()}
        return spark_engine.run(plan, tables, None if engine == "spark" else engine)
    if engine == "datafusion":
        return run_substrait_json(con, datafusion_plan(plan_json))
    tables = {t: con.arrow[t] for t in read_tables(json.loads(plan_json))}
    if engine == "polars":
        from sverify import polars_engine

        return polars_engine.run(plan_json, tables)
    if engine == "duckdb":
        from sverify import duckdb_engine

        return duckdb_engine.run(plan_json, tables)
    raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")


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


def put_table(con: Connection, name: str, table: pa.Table) -> None:
    """Register (or replace) an in-memory table."""
    con.put(name, table)


def plain_schema(schema: pa.Schema) -> pa.Schema:
    """`schema` with large and view strings as plain `string`: the type the
    plans name (Substrait has one string type), which DataFusion's consumer
    checks against the registered table. Table formats such as Iceberg read
    strings as `large_string`."""
    plain = (pa.types.is_large_string, getattr(pa.types, "is_string_view", lambda _: False))
    fields = [f.with_type(pa.string()) if any(p(f.type) for p in plain) else f for f in schema]
    return pa.schema(fields, metadata=schema.metadata)


def to_arrow(rows, schema: pa.Schema) -> pa.Table:
    """Rows (tuples in schema order) as an Arrow table."""
    names = schema.names
    return pa.Table.from_pylist([dict(zip(names, r, strict=True)) for r in rows], schema=schema)


def create_table(con: Connection, name: str, schema: ibis.Schema | pa.Schema, rows=()) -> None:
    """Add table `name` to `con` with `schema` (Ibis or Arrow) and `rows`
    (tuples in schema order), replacing any table of that name.

    Args:
        con: The connection.
        name: The table's name.
        schema: Its schema, as an Ibis or Arrow schema. An Arrow schema can
            mark columns NOT NULL (`nullable=False`), which contracts use.
        rows (Iterable[tuple]): Tuples in the schema's column order.
            Default: no rows.
    """
    arrow_schema = schema if isinstance(schema, pa.Schema) else schema.to_pyarrow()
    put_table(con, name, to_arrow(rows, arrow_schema))


def table_rows(con: Connection, name: str) -> list[tuple]:
    """The rows of table `name` of `con`, as tuples in schema order.

    Args:
        con: The connection.
        name: A table of the connection.

    Returns:
        The rows, in the table's order.

    Raises:
        KeyError: The connection has no table `name`.
    """
    t = con.arrow[name]
    return [tuple(r.values()) for r in t.to_pylist()]
