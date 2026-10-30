"""DataFusion as Substrait producer and consumer.

Every plan comes from DataFusion and runs on DataFusion. Pipelines are Ibis
expressions on an Ibis DataFusion backend (`connect()`); `con.con` is the
underlying `datafusion.SessionContext`.
"""

import json
from typing import Any

import ibis
import ibis.expr.types as ir
import pyarrow as pa
import sqlglot as sg
from datafusion import substrait as ss
from google.protobuf import json_format
from ibis.backends.sql.compilers.datafusion import DataFusionCompiler
from substrait.plan_pb2 import Plan

Backend = Any  # ibis.backends.datafusion.Backend

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


def substrait_json(con: Backend, sql: str) -> str:
    """Compile SQL to a Substrait plan, as protobuf JSON."""
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
