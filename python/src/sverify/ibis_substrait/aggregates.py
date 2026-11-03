"""Aggregate measures of the Ibis producer (`measure`), which the
aggregate relation and window aggregates use.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, _sort_key
from sverify.plan_json import Json, Unsupported, call
from sverify.plan_json import anchor as _anchor


def measure(x: Exprs, op: Any) -> Json:
    distinct = False
    args: list[Json]
    options: list[Json] = []
    if isinstance(op, ops.ApproxCountDistinct):
        # A subclass of `CountDistinct`, but its value is each engine's own
        # estimate, so no plan gives the same answer on every engine.
        raise Unsupported(
            "approx_nunique is not supported: its value is each engine's own estimate; "
            "use nunique() for the exact count"
        )
    if isinstance(op, ops.CountStar):
        name, args = "count", []
    elif isinstance(op, ops.Count | ops.CountDistinct):
        name, args = "count", [x(op.arg)]
        distinct = isinstance(op, ops.CountDistinct)
    elif isinstance(op, ops.Sum | ops.Mean):
        name = "sum" if isinstance(op, ops.Sum) else "avg"
        # Ibis sums and averages booleans as integers.
        args = [x(op.arg, dt.int32) if op.arg.dtype.is_boolean() else x(op.arg)]
    elif isinstance(op, ops.Min | ops.Max):
        # On booleans Ibis writes BOOL_AND / BOOL_OR, which are MIN / MAX.
        name, args = ("min" if isinstance(op, ops.Min) else "max"), [x(op.arg)]
    elif isinstance(op, ops.All | ops.Any):
        # `all()` / `any()` are BOOL_AND / BOOL_OR too (#53): FALSE < TRUE,
        # NULLs skipped, and NULL for a group without a non-NULL value.
        name, args = ("min" if isinstance(op, ops.All) else "max"), [x(op.arg)]
    elif isinstance(op, ops.BitAnd | ops.BitOr | ops.BitXor):
        # 64-bit integers (#53); a narrower column is widened first.
        name = {ops.BitAnd: "bit_and", ops.BitOr: "bit_or", ops.BitXor: "bit_xor"}[type(op)]
        args = [x(op.arg, dt.int64)]
    elif isinstance(op, ops.Variance | ops.StandardDev):
        # Of a sample or a population, each engine's own algorithm (#54).
        name = "variance" if isinstance(op, ops.Variance) else "std_dev"
        args = [x(op.arg, dt.float64) if op.arg.dtype.is_boolean() else x(op.arg)]
        options = [
            {"name": "distribution", "preference": ["POPULATION" if op.how == "pop" else "SAMPLE"]}
        ]
    elif isinstance(op, ops.Covariance | ops.Correlation):
        # Of a sample or a population (#54); a correlation is the same for both.
        if isinstance(op, ops.Correlation):
            name = "corr"
        else:
            name = "covar_pop" if op.how == "pop" else "covar_samp"
        args = [x(op.left, dt.float64), x(op.right, dt.float64)]
    elif isinstance(op, ops.ArrayCollect):
        return collect(x, op)
    elif isinstance(op, ops.First | ops.Last):
        return first_last(x, op)
    elif isinstance(op, ops.GroupConcat):
        return group_concat(x, op)
    else:
        raise Unsupported(f"aggregate {type(op).__name__} is not supported")
    agg: Json = {
        "functionReference": _anchor(name),
        "arguments": [{"value": a} for a in args],
        "invocation": (
            "AGGREGATION_INVOCATION_DISTINCT" if distinct else "AGGREGATION_INVOCATION_ALL"
        ),
    }
    if options:
        agg["options"] = options
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out


def collect(x: Exprs, op: Any) -> Json:
    """`ARRAY_AGG(x ORDER BY …) FILTER (WHERE x IS NOT NULL [AND where])`, as
    Ibis's DataFusion compiler writes `collect()`. Without `order_by` the order
    of the elements is the engine's choice."""
    if op.include_null:
        raise Unsupported("collect(include_null=True) is not supported")
    if op.distinct:
        raise Unsupported("collect(distinct=True) is not supported")
    arg = x(op.arg)
    sorts = []
    for k in op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise Unsupported("collect(order_by=) must order by columns")
        sorts.append(key)
    agg: Json = {
        "functionReference": _anchor("array_agg"),
        "arguments": [{"value": arg}],
        "sorts": sorts,
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    keep = call("is_not_null", [arg])
    if op.where is not None:
        keep = call("and", [x(op.where), keep])
    return {"measure": agg, "filter": keep}


def group_concat(x: Exprs, op: Any) -> Json:
    """`STRING_AGG(x, sep ORDER BY …)` of the non-NULL strings (#55), as Ibis's
    `LISTAGG`. Without `order_by` the order is the engine's, which is refused."""
    if not op.order_by:
        raise Unsupported(
            "group_concat() without order_by joins in the engine's order; give it an order_by"
        )
    if not isinstance(op.sep, ops.Literal):
        raise Unsupported("group_concat needs a constant separator")
    if not op.arg.dtype.is_string():
        raise Unsupported(f"group_concat of {op.arg.dtype} is not supported; cast it to string")
    sorts = []
    for k in op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise Unsupported("group_concat(order_by=) must order by columns")
        sorts.append(key)
    agg: Json = {
        "functionReference": _anchor("string_agg"),
        "arguments": [{"value": x(op.arg)}, {"value": x(op.sep)}],
        "sorts": sorts,
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out


def first_last(x: Exprs, op: Any) -> Json:
    """`FIRST(x ORDER BY …)` / `LAST(…)` of the non-NULL values (#55). Without
    `order_by` it is any row's value (Ibis's `distinct(on=)`): verified, but
    reported as the engine's choice unless the group is a key."""
    name = "first" if isinstance(op, ops.First) else "last"
    if op.include_null:
        raise Unsupported(f"{name}(include_null=True) is not supported")
    sorts = []
    for k in op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise Unsupported(f"{name}(order_by=) must order by columns")
        sorts.append(key)
    agg: Json = {
        "functionReference": _anchor(name),
        "arguments": [{"value": x(op.arg)}],
        "sorts": sorts,
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out
