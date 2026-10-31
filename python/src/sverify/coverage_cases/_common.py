"""What the coverage cases share: the tables they read and how a case is
written."""

from __future__ import annotations

import datetime as dt
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir

Status = Literal["verified", "rejected", "upstream"]

T = ibis.table(
    {
        "id": "int64",
        "name": "string",
        "amount": "float64",
        "qty": "int64",
        "ts": "timestamp",
        "flag": "boolean",
    },
    name="t",
)
U = ibis.table({"name": "string", "region": "string"}, name="u")
L = ibis.table({"k": "int64", "xs": "array<int64>"}, name="l")
t, u, ls = T, U, L
#: A date constant.
DAY0 = ibis.literal(dt.date(1970, 1, 5))
#: Every table the cases read.
TABLES = (T, U, L)
#: A memtable: its rows are part of the plan.
M = ibis.memtable(
    {"name": ["ada", "bob", None], "score": [1, None, 3]},
    schema={"name": "string", "score": "int64"},
)


def sql_view(table: ir.Table, query: str) -> ir.Table:
    """`table.alias("v").sql(query)` without a backend: `Table.sql` needs one
    to infer the schema, which DataFusion does here. (Ibis 12's DuckDB backend
    cannot: it calls a method DuckDB 2 no longer has.)"""
    from sverify.ibis_substrait import sql_view_schema

    parent: Any = table.alias("v").op()
    schema = sql_view_schema(parent, query)
    return ops.SQLStringView(parent=parent, query=query, schema=schema).to_expr()


class _Tables:
    """The schemas of `t` and `u`, as a backend gives them to `Backend.sql`."""

    def get_schema(self, name: str) -> ibis.Schema:
        return {"t": T, "u": U}[name].schema()


def sql_query(query: str, schema: dict[str, str]) -> ir.Table:
    """`backend.sql(query)` over `t` and `u`."""
    return ops.SQLQueryResult(query, ibis.schema(schema), _Tables()).to_expr()


def exists(table: ir.Table) -> ir.BooleanValue:
    """`EXISTS (table)`; Ibis builds it only from a correlated `.any()`."""
    rel: Any = table.op()
    return ops.ExistsSubquery(rel).to_expr()


@dataclass(frozen=True)
class Case:
    area: str
    label: str
    build: Callable[[], ir.Table]
    expected: Status


def case(area: str, label: str, expected: Status, build: Callable[[], ir.Table]) -> Case:
    return Case(area, label, build, expected)


V, R, X = "verified", "rejected", "upstream"

#: Why engines refuse verified cases (`REFUSED`), as patterns of the reason.
#: These are what cannot be expressed there:
#:
#: * `lt` on strings is undefined in the model (`BinFn.apply` has no case for
#:   it, so it is NULL, where SQL compares), so no engine may run it.
#: * Snowflake and Spark tables have no row order, which FETCH and a stable
#:   sort's or a window's ties follow. Sorts and windows run with
#:   `tie_free=True`. A `SUM` or `AVG` of doubles adds in that order too
#:   (rounding depends on it). So does a window frame's `SUM` or `AVG`.
#: * Spark has no TIME type before 4.1.
NO_ROW_ORDER = {"snowflake": "no row order", "spark": "no row order"}
#: A frame's doubles are added in frame order (`floatSum`), which only DuckDB's
#: and Polars' translations keep.
FRAME_DOUBLES = {"snowflake": "doubles in order", "spark": "doubles in order"}
#: The SQL dialects have no lists yet (#94).
NO_LISTS = {
    "duckdb": "array_agg|unsupported relation|unsupported literal|unsupported column type",
    "snowflake": "array_agg|unsupported relation|unsupported literal|unsupported column type",
    "spark": "array_agg|unsupported relation|unsupported literal|unsupported column type",
}
