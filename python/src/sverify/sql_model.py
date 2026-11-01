"""SQL models: a transform's body written in SQL, `sv.sql(query, **tables)`,
and SQL as a step of `Node.pipe`, `sv.sql(query)`.

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

Without tables, `sv.sql(query)` is a step (`SQLStep`): a transform whose
inputs are the tables the query reads, so that SQL chains like any other
transform.

    regional = paid_orders.pipe(
        sv.sql("SELECT o.*, c.region FROM orders o JOIN customers c ON c.cid = o.cid"),
        customers=customers,
    )
"""

from __future__ import annotations

import inspect
from collections.abc import Mapping
from typing import Any, overload

import ibis.expr.types as ir
import sqlglot as sg
from ibis.backends.sql.compilers.base import SQLGlotCompiler

from sverify.contracts import ContractedTransform
from sverify.engine import run_checker
from sverify.ibis_substrait import SQLModel, sql_model_schema, to_substrait_json
from sverify.ibis_substrait import Unsupported as ProducerRefused


@overload
def sql(query: str, /, *, as_: str | None = None) -> SQLStep: ...
@overload
def sql(query: str, /, **tables: ir.Table) -> ir.Table: ...
def sql(query: str, /, *, as_: str | None = None, **tables: ir.Table) -> ir.Table | SQLStep:
    """SQL as a step of `Node.pipe`, or as the body of a transform.

    Without tables, `sql(query)` is a step: a transform whose inputs are the
    tables the query reads (CTE names don't count, and a table read twice is
    one input). In `node.pipe(sql(query), **inputs)`, the keyword inputs
    bind their own table names, and the chained node binds to the one table
    left over, wherever the query reads it. `as_` names that table, which
    documents it in a long query; it is checked, and doesn't change the
    binding.

    With tables, `sql(query, orders=orders)` is `query` over those Ibis
    tables, as an Ibis table: the body of a transform written in SQL, which
    reads each table by its keyword name.

    Either way, the schema and plan come from DataFusion's SQL producer, or
    Isthmus's without DataFusion (`pip install 'sverify[datafusion]'`), and
    every table the query reads must be an input, so the plan is closed and
    checked.

    Args:
        query: The SQL query.
        as_: For a step: the table the chained node is, checked against the
            one table the keyword inputs of `pipe` leave over. Default None.
        **tables: For the body of a transform: the Ibis tables the query
            reads, by name.

    Returns:
        A `SQLStep` without tables, else the query as an Ibis table.

    Raises:
        sverify.engines.Unsupported: The producer cannot plan the query, or
            Lean refuses the plan, saying why (when the query is applied to
            its inputs); or the query cannot be parsed.
        TypeError: A table is a node or a source (pipe a step instead), or
            `as_` is given with tables or is not a table the query reads.
            In `pipe`: a table of the query has no input, the chained node
            is left unused, a keyword is not a table the query reads, or
            `as_` is not the table left over.

    Examples:
        With `orders`, `paid` and `customers` from the `Node.pipe` example:

        ```python
        regional = orders.pipe(paid).pipe(
            sv.sql(
                "SELECT o.id, c.region FROM customers c JOIN orders o ON o.customer = c.customer",
                as_="orders",
            ),
            customers=customers,
        )
        ```
    """
    from sverify.nodes import Node, is_source
    from sverify.sql import Unsupported

    if not tables:
        return SQLStep(query, as_)
    if as_ is not None:
        raise TypeError(
            "sverify.sql: as_ names the chained node of a step, sql(query, as_=...), "
            "which takes no tables"
        )
    for name, t in tables.items():
        if isinstance(t, Node) or is_source(t):
            raise TypeError(
                f"sverify.sql reads Ibis tables; {name}={t!r} is a node or source: pipe "
                f"the step instead, node.pipe(sv.sql(query), {name}=...), or call sql "
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


def query_tables(query: str) -> list[str]:
    """The tables `query` reads, in the order it first names them: not its
    CTEs, and each once. Unquoted names are lower-cased, as DataFusion
    reads them."""
    from sverify.sql import Unsupported

    try:
        tree = sg.parse_one(query)
    except sg.errors.ParseError as e:
        raise Unsupported(f"cannot parse the SQL: {str(e).splitlines()[0]}") from e
    ctes = {c.alias_or_name for c in tree.find_all(sg.exp.CTE)}
    out: list[str] = []
    for t in tree.find_all(sg.exp.Table, bfs=False):
        ident = t.this
        if not isinstance(ident, sg.exp.Identifier):
            continue  # a table function
        name = ident.name if ident.quoted else ident.name.lower()
        if name not in ctes and name not in out:
            out.append(name)
    return out


class SQLStep(ContractedTransform):
    """`sv.sql(query)`: SQL as a step of `Node.pipe`, a transform with no
    contract whose inputs are the tables the query reads (`tables`).

    In `node.pipe(step, **inputs)`, the keyword inputs bind their own table
    names and the chained node binds to the one table left over; `as_`, if
    given, must be that table. Called directly, it takes every table by
    keyword: `step(orders=orders, customers=customers)`.

    Attributes:
        query: The SQL query.
        tables: The tables the query reads, in the order it names them.
        as_: The table the chained node is, or None.
    """

    def __init__(self, query: str, as_: str | None = None):
        self.query, self.as_ = query, as_
        self.tables = query_tables(query)
        if not self.tables:
            raise TypeError("sverify.sql: the query reads no table, so a step has no input")
        if as_ is not None and as_ not in self.tables:
            raise TypeError(
                f"sverify.sql: as_={as_!r} is not a table the query reads "
                f"({', '.join(self.tables)})"
            )

        def body(**inputs: ir.Table) -> ir.Table:
            return sql(query, **inputs)

        body.__name__ = body.__qualname__ = "sql"
        try:
            params = [inspect.Parameter(n, inspect.Parameter.KEYWORD_ONLY) for n in self.tables]
        except ValueError:  # a name that can't be a parameter, such as "from"
            params = [inspect.Parameter("tables", inspect.Parameter.VAR_KEYWORD)]
        body.__signature__ = inspect.Signature(params)  # type: ignore[attr-defined]
        super().__init__(body, {}, (), "error", True, None)

    def __repr__(self) -> str:
        return f"<sverify.sql step reading {', '.join(self.tables)}>"

    def _pipe_args(self, chained: Any, inputs: Mapping[str, Any]) -> tuple[tuple, dict[str, Any]]:
        """The keyword inputs by their table names, and the chained node as
        the one table left over."""
        reads = ", ".join(self.tables)
        unknown = [n for n in inputs if n not in self.tables]
        if unknown:
            raise TypeError(
                f"sverify.sql: the query reads no table {', '.join(map(repr, unknown))}; "
                f"it reads {reads}"
            )
        left = [n for n in self.tables if n not in inputs]
        if not left:
            raise TypeError(
                f"sverify.sql: every table the query reads ({reads}) has an input by "
                "keyword, so the chained node is unused"
            )
        if len(left) > 1:
            raise TypeError(
                f"sverify.sql: the tables {', '.join(left)} have no input: give all but "
                "one by keyword, and the chained node is the one left over"
            )
        if self.as_ is not None and self.as_ != left[0]:
            raise TypeError(
                f"sverify.sql: as_={self.as_!r}, but the table left over for the "
                f"chained node is {left[0]!r}"
            )
        return (), {left[0]: chained, **inputs}


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
