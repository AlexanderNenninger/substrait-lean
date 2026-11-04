"""Relation rules of the Ibis producer: reads, filters, projections,
aggregations, sorts, limits, joins, set operations, subqueries and SQL strings.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from typing import Any, Optional

import ibis
import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
from ibis.common.collections import FrozenOrderedDict
from ibis.common.typing import VarTuple
from ibis.expr.schema import Schema

from sverify._plan_read import function_names
from sverify.ibis_substrait._base import Exprs, _sort_key, register, register_rels, rel, same_type
from sverify.ibis_substrait.aggregates import measure
from sverify.ibis_substrait.windows import _row_number_from_zero, _window_functions, window
from sverify.plan_json import (
    Json,
    Unsupported,
    call,
    chain,
    distinct_rel,
    emit_rel,
    field_ref,
    literal,
    project_rel,
    read_rel,
    select,
    values_rel,
)
from sverify.plan_json import anchor as _anchor

# Subqueries are uncorrelated here (a column of the outer query is outside
# their input); the checker lifts them into joins. A correlated EXISTS in a
# filter becomes a semi or anti join (`_filter`).


def _scalar_subquery(x: Exprs, op: Any) -> Json:
    return {"subquery": {"scalar": {"input": rel(op.rel)}}}


def _exists_subquery(x: Exprs, op: Any) -> Json:
    tuples = rel(op.rel)
    return {"subquery": {"setPredicate": {"predicateOp": "PREDICATE_OP_EXISTS", "tuples": tuples}}}


def _in_subquery(x: Exprs, op: Any) -> Json:
    (column,) = op.rel.schema.types
    if not same_type(op.needle.dtype, column):
        raise Unsupported(f"IN of {op.needle.dtype} in a subquery of {column}")
    return {"subquery": {"inPredicate": {"needles": [x(op.needle)], "haystack": rel(op.rel)}}}


def _read(op: Any) -> Json:
    return read_rel(op.name, op.schema)


def _exists(p: Any) -> tuple[Any, bool] | None:
    """The subquery of `EXISTS (…)` or `NOT EXISTS (…)`, and whether it is negated."""
    if isinstance(p, ops.ExistsSubquery):
        return p.rel, False
    if isinstance(p, ops.Not) and isinstance(p.arg, ops.ExistsSubquery):
        return p.arg.rel, True
    return None


def _filter(op: Any) -> Json:
    # `[NOT] EXISTS (SELECT … FROM s WHERE c)` conjuncts become semi (anti)
    # joins with `s` on `c`, which may refer to the outer row, as DataFusion
    # decorrelates them.
    x = Exprs({op.parent: 0})
    n = len(op.parent.schema)
    conds: list[Json] = []
    joins: list[tuple[Any, Json, str]] = []
    for p in op.predicates:
        if (found := _exists(p)) is None:
            conds.append(x(p))
            continue
        sub, anti = found
        inner, preds = (sub.parent, sub.predicates) if isinstance(sub, ops.Filter) else (sub, ())
        y = Exprs({op.parent: 0, inner: n})
        on = chain("and", [y(q) for q in preds] or [literal(True, dt.boolean)])
        joins.append((inner, on, "JOIN_TYPE_LEFT_ANTI" if anti else "JOIN_TYPE_LEFT_SEMI"))
    input = rel(op.parent)
    for inner, on, kind in joins:
        input = {"join": {"left": input, "right": rel(inner), "expression": on, "type": kind}}
    if not conds:
        return input
    return {"filter": {"input": input, "condition": chain("and", conds)}}


def _project(op: Any) -> Json:
    input = rel(op.parent)
    values = list(op.values.values())
    wins = _window_functions(values)
    if not wins:
        x = Exprs({op.parent: 0})
        return select(input, len(op.parent.schema), [x(v) for v in values])
    # Window functions first, in a projection of their own (the Lean parser
    # reads them only as whole expressions), then the values over them.
    width = len(op.parent.schema)
    x = Exprs({op.parent: 0})
    windowed = {"project": {"input": input, "expressions": [window(x, w) for w in wins]}}
    cols = {w: width + i for i, w in enumerate(wins)}
    y = Exprs({op.parent: 0}, cols)
    exprs = [_row_number_from_zero(y, v) for v in values]
    return project_rel(windowed, width + len(wins), exprs)


def _aggregate(op: Any) -> Json:
    x = Exprs({op.parent: 0})
    groups = [x(g) for g in op.groups.values()]
    metrics = list(op.metrics.values())
    # Arithmetic over reductions (`a.sum() / b.sum()`, #67): each reduction
    # is a measure of its own, and a projection computes the metrics from them.
    reductions = _reductions(metrics)
    body: Json = {
        "input": rel(op.parent),
        "groupingExpressions": groups,
        "groupings": [{"expressionReferences": list(range(len(groups)))}] if groups else [],
        "measures": [measure(x, m) for m in reductions],
    }
    if reductions == metrics:
        return {"aggregate": body}
    g = len(groups)
    cols = {v: i for i, v in enumerate(op.groups.values())}
    cols |= {r: g + i for i, r in enumerate(reductions)}
    y = Exprs({}, cols)
    exprs = [field_ref(i) for i in range(g)] + [y(m) for m in metrics]
    return project_rel({"aggregate": body}, g + len(reductions), exprs)


def _reductions(metrics: Iterable[Any]) -> list[Any]:
    """The reductions in `metrics`, each once, in order of appearance."""
    found: list[Any] = []

    def walk(node: Any) -> None:
        if isinstance(node, ops.Reduction):
            if node not in found:
                found.append(node)
            return
        if isinstance(node, ops.Value):
            for a in node.__args__:
                for v in a if isinstance(a, tuple) else (a,):
                    walk(v)

    for m in metrics:
        walk(m)
    return found


def _sort(op: Any) -> Json:
    # Sort keys that are expressions are projected first, and dropped after.
    width = len(op.parent.schema)
    x = Exprs({op.parent: 0})
    input = rel(op.parent)
    extra: list[Json] = []
    keys: list[Json] = []
    for k in op.keys:
        if isinstance(k.arg, ops.Field) and k.arg.rel == op.parent:
            keys.append(_sort_key(x, k))
            continue
        extra.append(x(k.arg))
        key = _sort_key(x, k)
        key["expr"] = field_ref(width + len(extra) - 1)
        keys.append(key)
    if extra:
        input = {"project": {"input": input, "expressions": extra}}
    out: Json = {"sort": {"input": input, "sorts": keys}}
    return emit_rel(out, list(range(width))) if extra else out


def _limit(op: Any) -> Json:
    # Ibis writes any other LIMIT as a subquery over the table (one row per
    # row, NULL when it is empty), which DataFusion refuses to run.
    if not isinstance(op.offset, int) or not (op.n is None or isinstance(op.n, int)):
        raise Unsupported("LIMIT and OFFSET must be integers (Ibis writes a subquery otherwise)")
    body: Json = {"input": rel(op.parent), "offsetExpr": literal(op.offset, dt.int64)}
    if op.n is not None:
        body["countExpr"] = literal(op.n, dt.int64)
    return {"fetch": body}


def _distinct(op: Any) -> Json:
    return distinct_rel(rel(op.parent), len(op.schema))


def _drop_null(op: Any) -> Json:
    x = Exprs({op.parent: 0})
    cols = (
        op.subset
        if op.subset is not None
        else [ops.Field(op.parent, n) for n in op.parent.schema.names]
    )
    tests = [call("is_not_null", [x(c)]) for c in cols]
    cond = chain("and" if op.how == "any" else "or", tests)
    return {"filter": {"input": rel(op.parent), "condition": cond}}


def _drop_columns(op: Any) -> Json:
    names = list(op.parent.schema.names)
    keep = [i for i, n in enumerate(names) if n not in op.columns_to_drop]
    return emit_rel(rel(op.parent), keep)


_JOIN_TYPES = {
    "inner": "JOIN_TYPE_INNER",
    "left": "JOIN_TYPE_LEFT",
    "right": "JOIN_TYPE_RIGHT",
    "outer": "JOIN_TYPE_OUTER",
    "semi": "JOIN_TYPE_LEFT_SEMI",
    "anti": "JOIN_TYPE_LEFT_ANTI",
}


def _join_chain(op: Any) -> Json:
    offsets: dict[Any, int] = {op.first: 0}
    width = len(op.first.schema)
    current = rel(op.first.parent)
    for link in op.rest:
        right = rel(link.table.parent)
        if link.how == "cross":
            current = {"cross": {"left": current, "right": right}}
            offsets[link.table] = width
            width += len(link.table.schema)
            continue
        if link.how not in _JOIN_TYPES:
            raise Unsupported(f"{link.how} joins are not supported")
        x = Exprs({**offsets, link.table: width})
        conds = [x(p) for p in link.predicates] or [literal(True, dt.boolean)]
        current = {
            "join": {
                "left": current,
                "right": right,
                "expression": chain("and", conds),
                "type": _JOIN_TYPES[link.how],
            }
        }
        if link.how not in ("semi", "anti"):
            offsets[link.table] = width
            width += len(link.table.schema)
    x = Exprs(offsets)
    return select(current, width, [x(v) for v in op.values.values()])


def numbered(input: Json, width: int) -> Json:
    """`input` with a column numbering the copies of each row from 1:
    `ROW_NUMBER() OVER (PARTITION BY` every column`)`."""
    win = {
        "windowFunction": {
            "functionReference": _anchor("row_number"),
            "partitions": [field_ref(i) for i in range(width)],
            "lowerBound": {"unbounded": {}},
            "upperBound": {"unbounded": {}},
            "boundsType": "BOUNDS_TYPE_ROWS",
        }
    }
    return {"project": {"input": input, "expressions": [win]}}


def _set_op(op: Any) -> Json:
    left, right = rel(op.left), rel(op.right)
    if isinstance(op, ops.Union):
        kind = "SET_OP_UNION_DISTINCT" if op.distinct else "SET_OP_UNION_ALL"
        return {"set": {"inputs": [left, right], "op": kind}}
    # INTERSECT and EXCEPT are a semi or anti join on all columns, NULLs
    # equal: DISTINCT of it, as DataFusion plans them, or with ALL the k-th
    # copy of a row matching the k-th copy on the right, which keeps
    # min(m, n) or max(m - n, 0) copies (SQL's bag semantics, as DuckDB
    # computes them; DataFusion 51 keeps or drops every copy: see
    # `tests/test_datafusion_quirks.py`).
    n = len(op.schema)
    width = n if op.distinct else n + 1
    if not op.distinct:
        left, right = numbered(left, n), numbered(right, n)
    same = [call("is_not_distinct_from", [field_ref(i), field_ref(width + i)]) for i in range(n)]
    if not op.distinct:
        same.append(call("equal", [field_ref(n), field_ref(width + n)]))
    kind = "JOIN_TYPE_LEFT_SEMI" if isinstance(op, ops.Intersection) else "JOIN_TYPE_LEFT_ANTI"
    join = {"join": {"left": left, "right": right, "expression": chain("and", same), "type": kind}}
    return distinct_rel(join, n) if op.distinct else emit_rel(join, list(range(n)))


def _fill_null(op: Any) -> Json:
    # Ibis's rewrite (`fill_null_to_select`): COALESCE each column with its
    # replacement; a scalar replaces in every nullable column.
    if isinstance(op.replacements, Mapping):
        mapping = op.replacements
    else:
        mapping = {n: op.replacements for n, t in op.parent.schema.items() if t.nullable}
    x = Exprs({op.parent: 0})
    exprs = []
    for name in op.parent.schema.names:
        col = ops.Field(op.parent, name)
        value = mapping.get(name)
        exprs.append(x(col if value is None else ops.Coalesce((col, value))))
    return select(rel(op.parent), len(op.parent.schema), exprs)


def _memtable(op: Any) -> Json:
    # A virtual table of literal rows, in the memtable's row order.
    data = op.data.to_pyarrow(op.schema)
    cols = [c.to_pylist() for c in data.columns]
    rows = (
        [
            [literal(v, t) for v, t in zip(row, op.schema.types, strict=True)]
            for row in zip(*cols, strict=True)
        ]
        if cols
        else [[] for _ in range(data.num_rows)]
    )
    return values_rel(op.schema, rows)


def _dummy_table(op: Any) -> Json:
    # `SELECT <values>` without FROM: one row of the values, as literals, or
    # computed over one row of no columns.
    x = Exprs({})
    exprs = [x(v) for v in op.values.values()]
    if all("literal" in e for e in exprs):
        return values_rel(op.schema, [exprs])
    return project_rel(values_rel(ibis.schema({}), [[]]), 0, exprs)


# SQL strings (`sv.sql`, `Table.sql`, `Backend.sql`) are DuckDB's SQL, lifted
# by `sverify.sql_lift` over tables of the right schemas, and the lifted plan
# is spliced in: reads of the inputs (a view's alias) become their plans, and
# function anchors are renumbered into this plan's.


def _physical_tables(op: Any) -> dict[str, Any]:
    """The named tables below `op`, by name, and the views' aliases."""
    found: dict[str, Any] = {}
    for node in op.find((ops.PhysicalTable,)):
        if isinstance(node, ops.InMemoryTable):
            continue
        found[node.name] = node.schema
    return found


def _lift(query: str, tables: Mapping[str, Any], semantics: str = "reference") -> Any:
    from sverify.sql_lift import lift

    return lift(query, tables, semantics)


def sql_view_schema(parent: Any, query: str) -> Any:
    """The schema of `query` over `parent` (an aliased relation)."""
    tables = {**_physical_tables(parent), parent.name: parent.schema}
    return _lift(query, tables).schema


def _splice(plan: Json, views: Mapping[str, Any]) -> Json:
    """The root relation of a lifted plan, with its function anchors in this
    plan's numbering and reads of `views` replaced by their plans."""
    names = function_names(plan, Unsupported)

    def walk(j: Any) -> Any:
        if isinstance(j, list):
            return [walk(v) for v in j]
        if not isinstance(j, dict):
            return j
        if "read" in j and "namedTable" in j["read"]:
            name = ".".join(j["read"]["namedTable"]["names"])
            if name in views:
                return walk_view(j["read"], views[name])
        out = {}
        for k, v in j.items():
            if k in ("scalarFunction", "windowFunction", "measure"):
                # Protobuf JSON leaves out anchor 0.
                v = {**v, "functionReference": _anchor(names[v.get("functionReference", 0)])}
                out[k] = {f: (a if f == "functionReference" else walk(a)) for f, a in v.items()}
            else:
                out[k] = walk(v)
        return out

    def walk_view(read: Json, view: Any) -> Json:
        common = read.get("common", {})
        if set(common) - {"direct", "emit"}:
            raise Unsupported(f"a read of a view with {sorted(common)} is not supported")
        out = rel(view)
        if "filter" in read:
            out = {"filter": {"input": out, "condition": walk(read["filter"])}}
        if "projection" in read:
            items = read["projection"]["select"].get("structItems", [])
            out = emit_rel(out, [i.get("field", 0) for i in items])
        if "emit" in common:
            # A read may map its output columns with an emit.
            out = emit_rel(out, list(common["emit"].get("outputMapping", [])))
        return out

    (root,) = [r["root"] for r in plan["relations"] if "root" in r]
    return walk(root["input"])


class SQLModel(ops.Relation):
    """A SQL query over named input relations (`sverify.sql`): the query reads
    each input by its name in `names`. The SQLGlot lift (`sverify.sql_lift`)
    plans it, as DuckDB's SQL (`dialect`, None meaning DuckDB), with the
    `semantics` profile (None meaning `"reference"`, #411)."""

    query: str
    inputs: VarTuple[ops.Relation]
    names: VarTuple[str]
    schema: Schema
    dialect: Optional[str] = None  # noqa: UP045 - Ibis's annotations need Optional
    semantics: Optional[str] = None  # noqa: UP045
    values = FrozenOrderedDict()


def sql_model_schema(query: str, tables: Mapping[str, Any], semantics: str = "reference") -> Any:
    """The schema of `query` over tables of these (Ibis) schemas."""
    return _lift(query, tables, semantics).schema


def _sql_model(op: Any) -> Json:
    tables = {n: i.schema for n, i in zip(op.names, op.inputs, strict=True)}
    plan = _lift(op.query, tables, op.semantics or "reference").plan
    return _splice(plan, dict(zip(op.names, op.inputs, strict=True)))


def _sql_string_view(op: Any) -> Json:
    if not isinstance(op.parent, ops.AliasedRelation):
        raise Unsupported("SQL over a table needs an alias to refer to it: use t.alias(name).sql")
    parent = op.parent
    tables = {**_physical_tables(parent), parent.name: parent.schema}
    return _splice(_lift(op.query, tables).plan, {parent.name: parent.parent})


def _sql_query_result(op: Any) -> Json:
    import sqlglot as sg
    import sqlglot.expressions as sge

    tables = {}
    for t in sg.parse_one(op.query, read="duckdb").find_all(sge.Table):
        try:
            tables[t.name] = op.source.get_schema(t.name)
        except Exception:  # noqa: BLE001 - a CTE's name, say
            continue
    return _splice(_lift(op.query, tables).plan, {})


register(
    {
        ops.ScalarSubquery: _scalar_subquery,
        ops.ExistsSubquery: _exists_subquery,
        ops.InSubquery: _in_subquery,
    }
)


register_rels(
    {
        ops.UnboundTable: _read,
        ops.DatabaseTable: _read,
        ops.Filter: _filter,
        ops.Project: _project,
        ops.Aggregate: _aggregate,
        ops.Sort: _sort,
        ops.Limit: _limit,
        ops.Distinct: _distinct,
        ops.DropNull: _drop_null,
        ops.DropColumns: _drop_columns,
        ops.JoinChain: _join_chain,
        ops.Union: _set_op,
        ops.Intersection: _set_op,
        ops.Difference: _set_op,
        ops.SelfReference: lambda op: rel(op.parent),
        ops.JoinReference: lambda op: rel(op.parent),
        ops.AliasedRelation: lambda op: rel(op.parent),
        ops.FillNull: _fill_null,
        ops.InMemoryTable: _memtable,
        ops.DummyTable: _dummy_table,
        ops.SQLStringView: _sql_string_view,
        SQLModel: _sql_model,
        ops.SQLQueryResult: _sql_query_result,
    }
)
