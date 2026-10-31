"""Substrait producers, and DuckDB, Polars or DataFusion as consumer.

`connect()` gives a `Connection`: named Arrow tables, the engine that runs
plans over them (DuckDB by default), and Ibis tables bound to them
(`con.table(name)`). `plan_json` compiles Ibis expressions with the vendored
producer (`sverify.ibis_substrait`, typed and engine-neutral) and SQL strings
with the connection's SQL producer: DataFusion's, or Isthmus (substrait-java's
Calcite-based compiler, as its native binary). `run_plan` runs a plan in Lean's
written form (`substrait-check --write`, `--delta`) on the connection's engine
or the one a call names.

DataFusion is optional (`pip install 'sverify[datafusion]'`): it is needed
only to run plans with `engine="datafusion"` and, unless Isthmus compiles them,
SQL strings. sverify does not ship Isthmus: it runs the binary named by
`$SVERIFY_ISTHMUS`, or `isthmus` on `PATH` (`isthmus-<os>-<version>` from
https://github.com/substrait-io/substrait-java/releases).
"""

from __future__ import annotations

import atexit
import functools
import json
import os
import shutil
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
from ibis.backends.sql.compilers.datafusion import DataFusionCompiler
from substrait.plan_pb2 import Plan

from sverify.ibis_substrait import to_substrait_json

Engine = Literal["duckdb", "polars", "datafusion"]
ENGINES: tuple[Engine, ...] = ("duckdb", "polars", "datafusion")
SqlProducer = Literal["datafusion", "isthmus"]
SQL_PRODUCERS: tuple[SqlProducer, ...] = ("datafusion", "isthmus")

_literal = DataFusionCompiler.visit_NonNullLiteral


def _subsecond_literal(self: Any, op: Any, *, value: Any, dtype: Any) -> Any:
    """Ibis refuses sub-second interval literals for DataFusion, which has
    supported them for a long time (`INTERVAL '10 milliseconds'`); sensor
    data at 100 Hz needs them."""
    if dtype.is_interval() and dtype.unit.short in ("ms", "us", "ns"):
        return sg.exp.Interval(
            this=sg.exp.convert(str(value)), unit=sg.exp.var(dtype.unit.plural.lower())
        )
    return _literal(self, op, value=value, dtype=dtype)


DataFusionCompiler.visit_NonNullLiteral = _subsecond_literal

_floor_divide = DataFusionCompiler.visit_FloorDivide


def _int_floor_divide(self: Any, op: Any, *, left: Any, right: Any) -> Any:
    """Ibis compiles integer `a // b` as `CAST(FLOOR(CAST(a AS DOUBLE) / b) AS
    BIGINT)`, which is inexact beyond 2^53 and can't be proved safe (the cast
    of an unbounded double). Floor division in integers instead:
    `a / b - 1` when the truncating quotient is inexact and the signs differ."""
    if not (op.left.dtype.is_integer() and op.right.dtype.is_integer()):
        return _floor_divide(self, op, left=left, right=right)
    e = sg.exp
    zero = e.Literal.number(0)
    quot = e.Div(this=left.copy(), expression=right.copy(), typed=True)
    inexact = e.NEQ(this=e.Mod(this=left.copy(), expression=right.copy()), expression=zero)
    signs = e.NEQ(
        this=e.paren(e.LT(this=left.copy(), expression=zero)),
        expression=e.paren(e.LT(this=right.copy(), expression=zero)),
    )
    down = e.Sub(this=quot.copy(), expression=e.Literal.number(1))
    return e.Case(ifs=[e.If(this=e.and_(inexact, signs), true=down)], default=quot)


DataFusionCompiler.visit_FloorDivide = _int_floor_divide


def _datafusion() -> Any:
    """The `datafusion` module, or an error saying how to install it."""
    try:
        import datafusion
        import datafusion.substrait
    except ImportError as e:
        raise ImportError(
            "this needs DataFusion: pip install 'sverify[datafusion]' "
            "(it runs plans with engine='datafusion' and compiles SQL strings)"
        ) from e
    return datafusion


def has_datafusion() -> bool:
    try:
        _datafusion()
    except ImportError:
        return False
    return True


def isthmus_path() -> str | None:
    """The Isthmus binary: `$SVERIFY_ISTHMUS`, or `isthmus` on `PATH`."""
    return os.environ.get("SVERIFY_ISTHMUS") or shutil.which("isthmus")


def default_sql_producer() -> SqlProducer:
    """DataFusion's producer if DataFusion is installed, else Isthmus."""
    if has_datafusion():
        return "datafusion"
    if isthmus_path() is not None:
        return "isthmus"
    raise ImportError(
        "compiling SQL strings needs a SQL producer: pip install 'sverify[datafusion]', "
        "or put an Isthmus binary (https://github.com/substrait-io/substrait-java/releases) "
        "on PATH as `isthmus` or in $SVERIFY_ISTHMUS"
    )


def _register(ctx: Any, name: str, table: pa.Table) -> None:
    """Register (or replace) a table in a DataFusion session, as record
    batches rather than a PyArrow dataset: DataFusion pushes filters into
    datasets, where PyArrow compares doubles by IEEE rules instead of
    DataFusion's total order (NaN = NaN)."""
    if ctx.table_exist(name):
        ctx.deregister_table(name)
    batches = table.to_batches() or [pa.RecordBatch.from_pylist([], schema=table.schema)]
    ctx.register_record_batches(name, [batches])


class Connection:
    """Named Arrow tables, and the engine that runs plans over them.

    * `arrow[name]` is the table as given (`put`), the input of every engine.
    * `table(name)` is an Ibis table bound to it, through an Ibis DuckDB
      backend that views the Arrow tables (`ibis`). Contracts find a table's
      data and metadata through it, and Ibis's own `execute` works on it.
    * `engine` runs plans (`run_plan`) unless a call names another.
    * `sql_producer` compiles SQL strings: `"datafusion"` or `"isthmus"`;
      `None` picks DataFusion if it is installed, else Isthmus.
    * `datafusion` is a DataFusion session holding the same tables (with the
      functions Ibis's DataFusion SQL calls), created on first use; only the
      DataFusion engine and DataFusion's SQL producer need it.
    """

    def __init__(self, engine: Engine = "duckdb", sql_producer: SqlProducer | None = None):
        if engine not in ENGINES:
            raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")
        if sql_producer is not None and sql_producer not in SQL_PRODUCERS:
            raise ValueError(
                f"unknown SQL producer {sql_producer!r}; expected one of {SQL_PRODUCERS}"
            )
        self.engine: Engine = engine
        self.sql_producer: SqlProducer | None = sql_producer
        self.arrow: dict[str, pa.Table] = {}
        self.ibis: Any = ibis.duckdb.connect()
        # A bound table keeps its backend alive, and the backend its connection.
        self.ibis._sverify_connection = self
        self._datafusion: Any = None

    def table(self, name: str) -> ir.Table:
        """Table `name` as an Ibis table bound to the connection. Its schema is
        the Arrow table's, nullability included (DuckDB's view of it drops
        NOT NULL, which contracts read)."""
        schema = ibis.Schema.from_pyarrow(self.arrow[name].schema)
        return ops.DatabaseTable(name, schema=schema, source=self.ibis).to_expr()

    def has(self, name: str) -> bool:
        return name in self.arrow

    def put(self, name: str, table: pa.Table) -> None:
        """Add or replace table `name`, with doubles as the model has them
        (`canonical`: one zero, one NaN)."""
        table = canonical(table.cast(plain_schema(table.schema)))
        self.drop(name)
        self.arrow[name] = table
        self.ibis.con.register(name, table)
        if self._datafusion is not None:
            _register(self._datafusion, name, table)

    def drop(self, name: str) -> None:
        if self.arrow.pop(name, None) is None:
            return
        self.ibis.con.unregister(name)
        if self._datafusion is not None and self._datafusion.table_exist(name):
            self._datafusion.deregister_table(name)

    @property
    def datafusion(self) -> Any:
        """A `datafusion.SessionContext` with the connection's tables."""
        if self._datafusion is None:
            _datafusion()
            # Ibis's DataFusion backend registers the UDFs its SQL calls
            # (`extract_epoch_seconds_timestamp`, …).
            ctx = ibis.datafusion.connect().con
            for name, table in self.arrow.items():
                _register(ctx, name, table)
            self._datafusion = ctx
        return self._datafusion


def connect(engine: Engine = "duckdb", sql_producer: SqlProducer | None = None) -> Connection:
    """A new, empty connection whose plans run on `engine` and whose SQL
    strings `sql_producer` compiles (default: DataFusion if installed, else
    Isthmus)."""
    return Connection(engine, sql_producer)


def connection_of(table: ir.Table) -> Connection | None:
    """The connection a bound Ibis table reads from, if any."""
    try:
        backend = ibis.get_backend(table)
    except Exception:  # noqa: BLE001 - unbound
        return None
    return getattr(backend, "_sverify_connection", None)


def to_sql(expr: ir.Table) -> str:
    """Ibis's own DataFusion SQL for an expression (needs no DataFusion)."""
    return ibis.to_sql(expr, dialect="datafusion")


def plan_json(con: Connection, query: ir.Table | str) -> str:
    """The Substrait plan of a query, as protobuf JSON: an Ibis expression
    through the vendored producer, SQL through the connection's SQL producer
    (`substrait_json` or `isthmus_json`)."""
    if isinstance(query, str):
        if (con.sql_producer or default_sql_producer()) == "isthmus":
            return isthmus_json(con, query)
        return substrait_json(con, query)
    return to_substrait_json(query)


def substrait_json(con: Connection, sql: str) -> str:
    """Compile SQL to a Substrait plan with DataFusion, as protobuf JSON."""
    ss = _datafusion().substrait
    ctx = con.datafusion
    plan = ss.Producer.to_substrait_plan(ctx.sql(sql).logical_plan(), ctx)
    proto = Plan()
    proto.ParseFromString(plan.encode())
    return json_format.MessageToJson(proto)


def quote(name: str) -> str:
    """A quoted SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


def _sql_type(t: pa.DataType) -> str | None:
    """The SQL type Isthmus should see for an Arrow type; `None` if it has none
    (the plan could not be checked anyway). Timestamps are microseconds, as in
    the Lean model; the engines read any unit."""
    if pa.types.is_timestamp(t):
        return None if t.tz is not None else "TIMESTAMP(6)"
    if pa.types.is_decimal(t):
        return f"DECIMAL({t.precision}, {t.scale})"
    simple = {
        pa.int8(): "TINYINT", pa.int16(): "SMALLINT", pa.int32(): "INTEGER",
        pa.int64(): "BIGINT", pa.float32(): "REAL", pa.float64(): "DOUBLE",
        pa.string(): "VARCHAR", pa.bool_(): "BOOLEAN", pa.date32(): "DATE",
    }  # fmt: skip
    return simple.get(t)


def create_statements(con: Connection) -> tuple[list[str], list[str]]:
    """`CREATE TABLE` statements for the connection's tables, with quoted
    identifiers, and the tables left out for a column type SQL can't name."""
    ddl, skipped = [], []
    for name, table in con.arrow.items():
        cols = []
        for f in table.schema:
            ty = _sql_type(f.type)
            if ty is None:
                skipped.append(f"{name} ({f.name}: {f.type})")
                break
            cols.append(f"{quote(f.name)} {ty}{'' if f.nullable else ' NOT NULL'}")
        else:
            ddl.append(f"CREATE TABLE {quote(name)} ({', '.join(cols)})")
    return ddl, skipped


class SqlError(ValueError):
    """A SQL producer refused a query."""


@functools.lru_cache(maxsize=256)
def _isthmus(binary: str, ddl: tuple[str, ...], sql: str) -> str:
    # Calcite's default conformance; unquoted identifiers keep their case.
    args = [binary, "--unquotedcasing=UNCHANGED"]
    for c in ddl:
        args += ["-c", c]
    p = subprocess.run([*args, sql], capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        lines = [ln.strip() for ln in (p.stderr + p.stdout).splitlines() if ln.strip()]
        msg = next((ln for ln in lines if not ln.startswith("at ")), "Isthmus failed")
        raise SqlError(f"Isthmus: {msg.removeprefix('Error: ')}")
    return p.stdout


def isthmus_json(con: Connection, sql: str) -> str:
    """Compile SQL to a Substrait plan with Isthmus, as protobuf JSON. Isthmus
    reads standard SQL (Calcite's default conformance), not DataFusion's or
    Postgres's dialect: `FLOOR(ts TO DAY)` rather than `DATE_TRUNC`, no
    `GROUP BY` ordinals."""
    binary = isthmus_path()
    if binary is None:
        raise ImportError(
            "sql_producer='isthmus' needs the Isthmus binary "
            "(https://github.com/substrait-io/substrait-java/releases) "
            "on PATH as `isthmus` or in $SVERIFY_ISTHMUS"
        )
    ddl, skipped = create_statements(con)
    try:
        return _isthmus(binary, tuple(ddl), sql)
    except SqlError as e:
        if skipped:
            raise SqlError(f"{e} (tables Isthmus can't see: {', '.join(skipped)})") from None
        raise


def run_substrait_json(con: Connection, plan_json: str) -> pa.Table:
    """Run a Substrait plan on DataFusion."""
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
    the checker has found it well-formed."""

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
    return out


def run_plan(con: Connection, plan_json: str, engine: Engine | None = None) -> pa.Table:
    """Run a plan in Lean's written form on `engine` (default: the
    connection's), over the tables of `con`. DataFusion runs it as
    `datafusion_plan` writes it."""
    engine = engine or con.engine
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


def run_sql(con: Connection, sql: str) -> pa.Table:
    """Run SQL on DataFusion; doubles in the result as `canonical` makes them."""
    return canonical(collect(con.datafusion.sql(sql)))


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
    arrow_schema = schema if isinstance(schema, pa.Schema) else schema.to_pyarrow()
    put_table(con, name, to_arrow(rows, arrow_schema))


def table_rows(con: Connection, name: str) -> list[tuple]:
    t = con.arrow[name]
    return [tuple(r.values()) for r in t.to_pylist()]


def plan_json_obj(plan_json: str) -> dict:
    return json.loads(plan_json)
