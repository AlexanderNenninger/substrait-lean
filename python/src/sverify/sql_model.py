"""SQL models: a transform's body written in SQL, `sv.sql(query, **tables)`.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
public name (`sql`) is re-exported by `sverify`.

    @sv.transform(requires={"orders": ["amount_cents >= 0"]}, ensures=["revenue_cents >= 0"])
    def revenue(orders):
        return sv.sql("SELECT region, sum(amount_cents) AS revenue_cents "
                      "FROM orders GROUP BY region", orders=orders)

The query reads each input by its keyword name. It becomes one relation of
the Ibis expression (`ibis_substrait.SQLModel`), whose plan is the SQL
producer's plan (DataFusion's, or Isthmus's without DataFusion) with each
input's plan spliced in where the query reads it. So a SQL model composes
with Ibis transforms on either side, fuses with them, and is checked like
any other plan; it needs no backend, so it works on the placeholder tables
nodes are built from.
"""

from __future__ import annotations

from typing import Any

import ibis.expr.types as ir
import sqlglot as sg
from ibis.backends.sql.compilers.base import SQLGlotCompiler

from sverify.engine import run_checker
from sverify.ibis_substrait import SQLModel, sql_model_schema, to_substrait_json
from sverify.ibis_substrait import Unsupported as ProducerRefused


def sql(query: str, /, **tables: ir.Table) -> ir.Table:
    """`query` (SQL) over the keyword `tables`, as an Ibis table: the body of
    a transform written in SQL, which reads each table by its keyword name.

    Its schema and plan come from DataFusion's SQL producer, or Isthmus's
    without DataFusion (`pip install 'sverify[datafusion]'`). A query the
    producer cannot plan, or a plan Lean refuses, raises `Unsupported`
    (`sverify.engines`) saying why."""
    from sverify.nodes import Node, is_source
    from sverify.sql import Unsupported

    if not tables:
        raise TypeError("sverify.sql needs its tables as keywords: sql(query, orders=orders)")
    for name, t in tables.items():
        if isinstance(t, Node) or is_source(t):
            raise TypeError(
                f"sverify.sql reads Ibis tables; {name}={t!r} is a node or source: call sql "
                "inside a transform (@sv.transform), which gets its inputs as tables"
            )
        if not isinstance(t, ir.Table):
            raise TypeError(f"sverify.sql: {name} is not a table: {t!r}")
    names = tuple(tables)
    try:
        schema = sql_model_schema(query, {n: t.schema() for n, t in tables.items()})
    except ProducerRefused as e:
        raise Unsupported(str(e)) from e
    inputs: Any = tuple(t.op() for t in tables.values())
    expr = SQLModel(query, inputs, names, schema).to_expr()
    _check(expr)
    return expr


def _check(expr: ir.Table) -> None:
    """Refuse a SQL model Lean cannot read, saying what it refuses."""
    from sverify.sql import Unsupported

    code, out, err = run_checker((), to_substrait_json(expr))
    if code != 0:
        lines = (err or out).strip().splitlines() or ["(no message)"]
        raise Unsupported(f"Lean refuses the SQL: {lines[-1].removeprefix('error: ')}")


def _visit_sql_model(self, op, *, query, inputs, names, schema):  # noqa: ANN001, ANN202
    # The query with each input as a CTE of its name: Ibis's SQL for the
    # expression, which contracts use to tell expressions apart.
    out: Any = sg.parse_one(query, read=self.dialect)
    for name, rel in zip(names, inputs, strict=True):
        if isinstance(rel, sg.exp.Subquery):
            rel = rel.this
        elif isinstance(rel, sg.exp.Table):
            rel = sg.select("*").from_(rel)
        out = out.with_(name, as_=rel)
    return out.subquery(copy=False)


SQLGlotCompiler.visit_SQLModel = _visit_sql_model  # type: ignore[attr-defined]
