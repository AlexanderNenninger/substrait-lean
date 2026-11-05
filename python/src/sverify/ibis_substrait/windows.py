"""Window functions of the Ibis producer (`window`), which projections use.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

import datetime as dt_
from collections.abc import Iterable
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, _sort_key
from sverify.ibis_substrait.aggregates import measure
from sverify.ibis_substrait.temporal import _const_interval
from sverify.plan_json import INTERVAL_MICROS, Json, Unsupported, call, literal
from sverify.plan_json import anchor as _anchor


def _window_functions(values: Iterable[Any]) -> list[Any]:
    found: list[Any] = []

    def walk(node: Any) -> None:
        if isinstance(node, ops.WindowFunction):
            if node not in found:
                found.append(node)
            return
        if isinstance(node, ops.Value):
            for a in node.__args__:
                for v in a if isinstance(a, tuple) else (a,):
                    walk(v)

    for v in values:
        walk(v)
    return found


_US_PER_DAY = 86_400_000_000


def _frame_offset(op: Any, b: Any) -> int:
    """A frame bound's offset: rows, or for a RANGE frame the sort key's unit
    (microseconds of a timestamp, days of a date)."""
    v = b.value
    if v.dtype.is_interval():
        micros = _interval_offset(v)
        key = op.order_by[0].arg.dtype if len(op.order_by) == 1 else None
        if key is not None and key.is_date():
            if micros % _US_PER_DAY:
                raise Unsupported("a RANGE frame over a date needs whole days")
            return micros // _US_PER_DAY
        return micros
    if isinstance(v, ops.Cast):
        v = v.arg
    if not isinstance(v, ops.Literal) or not isinstance(v.value, int) or v.value < 0:
        raise Unsupported("frame offsets must be non-negative integer constants")
    return v.value


def _interval_offset(v: Any) -> int:
    """A constant interval of days or less, in microseconds (Ibis writes a
    zero bound as a cast of an integer)."""
    c = _const_interval(v)
    if c is not None and not c[0]:
        return c[1]
    dtype = v.dtype
    if isinstance(v, ops.Cast):
        v = v.arg
    if isinstance(v, ops.Literal) and v.value is not None:
        if isinstance(v.value, dt_.timedelta):
            return v.value // dt_.timedelta(microseconds=1)
        factor = INTERVAL_MICROS.get(dtype.unit.short)
        if factor is not None and isinstance(v.value, int):
            return v.value * factor
    raise Unsupported("frame offsets must be constant intervals of days or less")


def _bound(op: Any, b: Any) -> Json:
    if b is None:
        return {"unbounded": {}}
    k = _frame_offset(op, b)
    if k == 0:
        return {"currentRow": {}}
    side = "preceding" if b.preceding else "following"
    return {side: {"offset": str(k)}}


#: Ibis's ranking functions, by Substrait name.
_RANKS = {
    ops.MinRank: "rank",
    ops.DenseRank: "dense_rank",
    ops.PercentRank: "percent_rank",
    ops.CumeDist: "cume_dist",
}


def window(x: Exprs, op: Any) -> Json:
    func = op.func
    args: list[Json] = []
    if isinstance(func, ops.RowNumber):
        name = "row_number"
    elif type(func) in _RANKS:
        name = _RANKS[type(func)]
    elif isinstance(func, ops.NTile):
        name, args = "ntile", [x(func.buckets, dt.int64)]
    elif isinstance(func, ops.Lag | ops.Lead):
        name = "lag" if isinstance(func, ops.Lag) else "lead"
        if not isinstance(func.arg, ops.Field):
            raise Unsupported(f"{name} of an expression is not supported; use a column")
        args = [x(func.arg)]
        offset = 1 if func.offset is None else func.offset
        if isinstance(offset, ops.Literal):
            offset = offset.value
        args.append(literal(offset, dt.int64))
        if func.default is not None:
            args.append(x(func.default, func.dtype))
    elif isinstance(func, ops.First | ops.Last | ops.NthValue):
        if not isinstance(func.arg, ops.Field):
            raise Unsupported("first/last/nth of an expression is not supported; use a column")
        if isinstance(func, ops.First | ops.Last):
            # Ibis's DataFusion SQL is a plain FIRST_VALUE/LAST_VALUE whatever
            # `include_null` says.
            if func.where is not None or func.order_by:
                raise Unsupported("first/last with where or order_by is not supported")
            name = "first_value" if isinstance(func, ops.First) else "last_value"
            args = [x(func.arg)]
        else:
            nth = func.nth.value if isinstance(func.nth, ops.Literal) else None
            if not isinstance(nth, int) or nth < 0:
                raise Unsupported("nth must be a non-negative integer constant")
            name, args = "nth_value", [x(func.arg), literal(nth + 1, dt.int64)]
    elif isinstance(func, ops.Reduction):
        m = measure(x, func)
        if "filter" in m or m["measure"]["invocation"] != "AGGREGATION_INVOCATION_ALL":
            raise Unsupported("window aggregates with where= or DISTINCT are not supported")
        fn = m["measure"]
        return {
            "windowFunction": {
                "functionReference": fn["functionReference"],
                "partitions": [x(g) for g in op.group_by],
                "sorts": [_sort_key(x, k) for k in op.order_by],
                "arguments": fn["arguments"],
                # A variance's distribution (`Parse.parseWindow`).
                **({"options": fn["options"]} if "options" in fn else {}),
                **_frame(op),
            }
        }
    else:
        raise Unsupported(f"window function {type(func).__name__} is not supported")
    return {
        "windowFunction": {
            "functionReference": _anchor(name),
            "partitions": [x(g) for g in op.group_by],
            "sorts": [_sort_key(x, k) for k in op.order_by],
            "arguments": [{"value": a} for a in args],
            **_frame(op),
        }
    }


def _frame(op: Any) -> Json:
    return {
        "lowerBound": _bound(op, op.start),
        "upperBound": _bound(op, op.end),
        "boundsType": "BOUNDS_TYPE_RANGE" if op.how == "range" else "BOUNDS_TYPE_ROWS",
    }


def _row_number_from_zero(x: Exprs, v: Any) -> Json:
    # Ibis's ROW_NUMBER, RANK, DENSE_RANK and NTILE count from 0: its compiler
    # subtracts 1.
    zero = (ops.RowNumber, ops.MinRank, ops.DenseRank, ops.NTile)
    if isinstance(v, ops.WindowFunction) and isinstance(v.func, zero):
        return call("subtract", [x(v), literal(1, dt.int64)])
    return x(v)
