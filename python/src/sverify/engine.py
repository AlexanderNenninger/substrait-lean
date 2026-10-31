"""Substrait producers, and DataFusion, Polars or DuckDB as consumer.

`plan_json` compiles Ibis expressions with the vendored producer
(`sverify.ibis_substrait`, typed and engine-neutral) and SQL strings with
DataFusion's. Pipelines are Ibis expressions on an Ibis
DataFusion backend (`connect()`); `con.con` is the underlying
`datafusion.SessionContext`, which also holds the tables. `run_plan` runs a
plan in Lean's written form (`substrait-check --write`, `--delta`) on the
engine a call names, reading the tables from `con`.
"""

import json
import os
import subprocess
from pathlib import Path
from typing import Any, Literal

import ibis
import ibis.expr.types as ir
import pyarrow as pa
import sqlglot as sg
from datafusion import substrait as ss
from google.protobuf import json_format
from ibis.backends.sql.compilers.datafusion import DataFusionCompiler
from substrait.plan_pb2 import Plan

from sverify.ibis_substrait import to_substrait_json

Backend = Any  # ibis.backends.datafusion.Backend
Engine = Literal["datafusion", "polars", "duckdb"]
ENGINES: tuple[Engine, ...] = ("datafusion", "polars", "duckdb")

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


def connect() -> Backend:
    return ibis.datafusion.connect()


def to_sql(expr: ir.Table) -> str:
    return ibis.to_sql(expr, dialect="datafusion")


def plan_json(con: Backend, query: ir.Table | str) -> str:
    """The Substrait plan of a query, as protobuf JSON: an Ibis expression
    through the vendored producer, SQL through DataFusion's (`substrait_json`)."""
    if isinstance(query, str):
        return substrait_json(con, query)
    return to_substrait_json(query)


def substrait_json(con: Backend, sql: str) -> str:
    """Compile SQL to a Substrait plan with DataFusion, as protobuf JSON."""
    plan = ss.Producer.to_substrait_plan(con.con.sql(sql).logical_plan(), con.con)
    proto = Plan()
    proto.ParseFromString(plan.encode())
    return json_format.MessageToJson(proto)


def run_substrait_json(con: Backend, plan_json: str) -> pa.Table:
    proto = Plan()
    json_format.Parse(plan_json, proto)
    logical = ss.Consumer.from_substrait_plan(
        con.con, ss.Serde.deserialize_bytes(proto.SerializeToString())
    )
    return con.con.create_dataframe_from_logical_plan(logical).to_arrow_table()


def checker_path() -> Path:
    """`$SVERIFY_CHECK` if set, else the `substrait-check` the wheel ships with
    (a symlink to the lake build in an editable install)."""
    if env := os.environ.get("SVERIFY_CHECK"):
        return Path(env)
    bundled = Path(__file__).parent / "_bin" / "substrait-check"
    if not bundled.exists():
        raise FileNotFoundError(f"{bundled} is missing; reinstall sverify or set SVERIFY_CHECK")
    return bundled


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
        proc = subprocess.run(
            [str(checker_path()), *flags, "/dev/stdin"],
            input=plan_json,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            msg = (proc.stderr or proc.stdout).strip().splitlines()[-1:]
            raise ValueError(f"substrait-check {' '.join(flags)} rejects the plan: {msg}")
        return proc.stdout

    check()
    return check("--write")


def run_plan(con: Backend, plan_json: str, engine: Engine = "datafusion") -> pa.Table:
    """Run a plan in Lean's written form on `engine`, over the tables of `con`."""
    if engine == "datafusion":
        return run_substrait_json(con, plan_json)
    if engine == "polars":
        from sverify import polars_engine

        names = read_tables(json.loads(plan_json))
        return polars_engine.run(plan_json, {t: con.con.table(t).to_arrow_table() for t in names})
    if engine == "duckdb":
        from sverify import duckdb_engine

        names = read_tables(json.loads(plan_json))
        return duckdb_engine.run(plan_json, {t: con.con.table(t).to_arrow_table() for t in names})
    raise ValueError(f"unknown engine {engine!r}; expected one of {ENGINES}")


def run_sql(con: Backend, sql: str) -> pa.Table:
    return con.con.sql(sql).to_arrow_table()


def put_table(con: Backend, name: str, table: pa.Table) -> None:
    """Register (or replace) an in-memory table.

    Ibis 12's `create_table` is broken on DataFusion (it issues an empty
    `DROP TABLE`). Tables are registered as record batches rather than PyArrow
    datasets: DataFusion pushes filters into datasets, where PyArrow compares
    doubles by IEEE rules instead of DataFusion's total order (NaN = NaN).
    """
    if con.con.table_exist(name):
        con.con.deregister_table(name)
    batches = table.to_batches() or [pa.RecordBatch.from_pylist([], schema=table.schema)]
    con.con.register_record_batches(name, [batches])


def to_arrow(rows, schema: pa.Schema) -> pa.Table:
    """Rows (tuples in schema order) as an Arrow table."""
    names = schema.names
    return pa.Table.from_pylist([dict(zip(names, r, strict=True)) for r in rows], schema=schema)


def create_table(con: Backend, name: str, schema: ibis.Schema | pa.Schema, rows=()) -> None:
    arrow_schema = schema if isinstance(schema, pa.Schema) else schema.to_pyarrow()
    put_table(con, name, to_arrow(rows, arrow_schema))


def table_rows(con: Backend, name: str) -> list[tuple]:
    t = con.con.table(name).to_arrow_table()
    return [tuple(r.values()) for r in t.to_pylist()]


def plan_json_obj(plan_json: str) -> dict:
    return json.loads(plan_json)
