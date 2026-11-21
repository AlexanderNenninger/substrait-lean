"""Aggregate measures of the Ibis producer (`measure`), which the
aggregate relation and window aggregates use.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify._unsupported import QUANTILE_OF_DECIMAL
from sverify.ibis_substrait._base import CONSTANT_FIX, Exprs, _sort_key
from sverify.ibis_substrait._constructs import op_construct
from sverify.plan_json import (
    Json,
    ProducerUnsupported,
    Unsupported,
    call,
    decimal_literal,
    literal,
)
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
            "use nunique() for the exact count",
            construct="function approx_nunique",
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
    elif isinstance(op, ops.First | ops.Last | ops.Arbitrary):
        return first_last(x, op)
    elif isinstance(op, ops.GroupConcat):
        return group_concat(x, op)
    elif isinstance(op, ops.Median | ops.Quantile | ops.MultiQuantile):
        return quantile(x, op)
    elif isinstance(op, ops.Mode):
        return mode(x, op)
    elif isinstance(op, ops.ArgMin | ops.ArgMax):
        return arg_min_max(x, op)
    else:
        raise ProducerUnsupported(
            f"aggregate {type(op).__name__} is not supported",
            construct=op_construct(op),
        )
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
        raise Unsupported(
            "collect(include_null=True) is not supported; use collect(), which skips nulls",
            construct="function collect",
        )
    if op.distinct:
        raise ProducerUnsupported(
            "collect(distinct=True) is not supported", construct="function collect"
        )
    arg = x(op.arg)
    sorts = []
    for k in op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise ProducerUnsupported(
                "collect(order_by=) must order by columns", construct="function collect"
            )
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


def _const_string(op: Any) -> str | None:
    """The string a constant expression of literals and `+` stands for."""
    if isinstance(op, ops.Literal):
        return op.value if isinstance(op.value, str) else None
    if isinstance(op, ops.StringConcat):
        parts = [_const_string(a) for a in op.arg]
        return None if None in parts else "".join(parts)  # type: ignore[arg-type]
    return None


def group_concat(x: Exprs, op: Any) -> Json:
    """`STRING_AGG(x, sep ORDER BY …)` of the non-NULL strings (#55), as Ibis's
    `LISTAGG`. Without `order_by` the order is the engine's: contracts see
    only some string (`Measure.abs`), and `verify` reports the result as not
    deterministic (`Rel.windowsTotal`)."""
    sep = _const_string(op.sep)
    if sep is None:
        raise ProducerUnsupported(
            "group_concat needs a constant separator",
            CONSTANT_FIX,
            construct="function group_concat",
        )
    if not op.arg.dtype.is_string():
        raise Unsupported(
            f"group_concat of {op.arg.dtype} is not supported; cast it to string",
            construct="function group_concat",
        )
    sorts = []
    for k in op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise ProducerUnsupported(
                "group_concat(order_by=) must order by columns", construct="function group_concat"
            )
        sorts.append(key)
    agg: Json = {
        "functionReference": _anchor("string_agg"),
        "arguments": [{"value": x(op.arg)}, {"value": literal(sep, dt.string)}],
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
    reported as the engine's choice unless the group is a key. `arbitrary()`
    is that choice, a non-NULL value of the group (#1920)."""
    name = "last" if isinstance(op, ops.Last) else "first"
    if not isinstance(op, ops.Arbitrary) and op.include_null:
        raise ProducerUnsupported(
            f"{name}(include_null=True) is not supported", construct=f"function {name}"
        )
    sorts = []
    for k in () if isinstance(op, ops.Arbitrary) else op.order_by:
        key = _sort_key(x, k)
        if "selection" not in key["expr"]:
            raise ProducerUnsupported(
                f"{name}(order_by=) must order by columns", construct=f"function {name}"
            )
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


def quantile(x: Exprs, op: Any) -> Json:
    """`median()` and `quantile(q)` (#53), exactly, as Ibis's DuckDB compiler
    writes them: `QUANTILE_CONT(x, q)` of numbers (a double), `QUANTILE_DISC`
    of other ordered values. The fraction is the decimal Python prints for
    it, which DuckDB reads exactly; approximate quantiles are refused."""
    if isinstance(op, ops.ApproxMedian | ops.ApproxQuantile):
        raise Unsupported(
            f"{type(op).__name__} is not supported: its value is each engine's own estimate; "
            "use median() or quantile() for the exact value",
            construct=op_construct(op),
        )
    if isinstance(op, ops.MultiQuantile):
        raise ProducerUnsupported(
            "quantile() of several fractions outside an aggregation is not supported",
            construct="function quantile",
        )
    if isinstance(op, ops.Median):
        q: Any = 0.5
    elif isinstance(op.quantile, ops.Literal) and isinstance(op.quantile.value, int | float):
        q = op.quantile.value
    else:
        raise ProducerUnsupported(
            "quantile() needs a constant fraction",
            CONSTANT_FIX,
            construct="function quantile",
        )
    if not 0 <= q <= 1:
        raise ProducerUnsupported(
            "quantile() needs a fraction between 0 and 1", construct="function quantile"
        )
    t = op.arg.dtype
    cont = t.is_integer() or t.is_floating()
    if t.is_decimal():
        # No engine computes one value for it: DuckDB truncates a double
        # interpolation, Spark and Polars return doubles (D68 is reserved).
        raise ProducerUnsupported(
            f"{type(op).__name__.lower()} of {t} {QUANTILE_OF_DECIMAL}; "
            "cast the column to float64 first: x.cast('float64').quantile(q)",
            construct=op_construct(op),
        )
    if not (cont or t.is_string() or t.is_date()):
        # DuckDB interpolates timestamps in their own type.
        raise ProducerUnsupported(
            f"{type(op).__name__.lower()} of {t} is not supported yet",
            construct=op_construct(op),
        )
    agg: Json = {
        "functionReference": _anchor("quantile_cont" if cont else "quantile_disc"),
        "arguments": [
            {"value": x(op.arg)},
            {"value": decimal_literal(repr(float(q)), dt.Decimal())},
        ],
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out


def split_multi_quantiles(metric: Any) -> Any:
    """`metric` with each `quantile([q1, q2])` as the array of its quantiles,
    `[quantile(q1), quantile(q2)]` (#1910): one measure per fraction, which
    `quantile` reads."""
    swap = {}
    for m in metric.find(ops.MultiQuantile):
        qs = m.quantile
        if not (isinstance(qs, ops.Literal) and isinstance(qs.value, tuple | list)):
            raise ProducerUnsupported(
                "quantile() needs constant fractions",
                CONSTANT_FIX,
                construct="function quantile",
            )
        one = [
            ops.Quantile(m.arg, ops.Literal(q, qs.dtype.value_type), m.where)  # pyrefly: ignore
            for q in qs.value
        ]
        # DuckDB's list is NULL, not a list of NULLs, for a group with no value.
        empty = ops.Equals(ops.Count(m.arg, m.where), ops.Literal(0, dt.int64))
        swap[m] = ops.IfElse(empty, ops.Literal(None, m.dtype), ops.Array(tuple(one)))
    return metric.replace(swap) if swap else metric


def mode(x: Exprs, op: Any) -> Json:
    """`mode()` (#53): the most frequent value, and of the values that tie the
    smallest, `MODE(x ORDER BY x)`. DuckDB's own `MODE(x)` breaks ties in the
    order it reads the rows."""
    arg = x(op.arg)  # a column: `Aggregate` projects an expression first (#1909)
    agg: Json = {
        "functionReference": _anchor("mode"),
        "arguments": [{"value": arg}],
        "sorts": [{"expr": arg, "direction": "SORT_DIRECTION_ASC_NULLS_LAST"}],
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out


def arg_min_max(x: Exprs, op: Any) -> Json:
    """`argmin(key)` / `argmax(key)` (#53): the value at the row with the
    smallest (largest) key, over the rows where neither is NULL, as DuckDB's
    `ARG_MIN`. Ties make it the engine's choice, which `verify` reports
    unless the group and the key contain a unique key."""
    name = "arg_min" if isinstance(op, ops.ArgMin) else "arg_max"
    key = x(op.key)
    if "selection" not in key:
        raise Unsupported(
            f"{name} orders by a column only; select the key as a column first",
            construct=f"function {name}",
        )
    agg: Json = {
        "functionReference": _anchor(name),
        "arguments": [{"value": x(op.arg)}, {"value": key}],
        "invocation": "AGGREGATION_INVOCATION_ALL",
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out
