"""Ibis expressions to Substrait plans (protobuf JSON) for the Lean checker.

Derived from ibis-substrait (Apache License 2.0; see `LICENSE` and
`README.md` in this directory): one translation per Ibis operation, and
field offsets threaded through join chains, follow upstream's
`compiler/translate.py`. Modified by the substrait-lean authors:

* ported from Ibis 9 to the Ibis version `sverify` pins;
* writes plain protobuf JSON with the functions and encodings
  `SubstraitLean/Parse.lean` reads, instead of resolving signatures from
  Substrait's extension YAMLs;
* every operation means what Ibis's DataFusion SQL compiler makes of it
  (`ibis/backends/sql/compilers/{base,datafusion}.py`, plus `sverify.engine`'s
  integer `//`), with Ibis's type promotions written as explicit casts;
* fixes upstream's integer `/` (it divided integers), dropped `where=`
  filters, sort keys that were always NULLS FIRST, promotions that could
  cast a double down to an integer, and timestamp literals read in local
  time;
* raises `Unsupported` for everything outside the Lean model.
"""

from __future__ import annotations

import contextvars
import datetime as dt_
import json
import math
from collections.abc import Callable, Iterable, Mapping
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
import ibis.expr.types as ir

__all__ = ["Unsupported", "to_substrait", "to_substrait_json"]

Json = dict[str, Any]

EPOCH = dt_.datetime(1970, 1, 1)
NULLABLE = {"nullability": "NULLABILITY_NULLABLE"}
REQUIRED = {"nullability": "NULLABILITY_REQUIRED"}


class Unsupported(ValueError):
    """The expression uses something the Lean model does not cover."""


# --------------------------------------------------------------------------
# Types and literals


def type_json(dtype: Any, nullable: bool = True) -> Json:
    """The Substrait type; computed values are typed nullable, as the Lean
    model's values all are, and only table schemas say otherwise."""
    t = _type_json(dtype)
    if not nullable:
        ((name, body),) = t.items()
        t = {name: {**body, **REQUIRED}}
    return t


def _type_json(dtype: Any) -> Json:
    if dtype.is_unsigned_integer():
        raise Unsupported(f"unsigned integers ({dtype}) are not supported")
    if dtype.is_integer():
        return {f"i{dtype.nbytes * 8}": NULLABLE}
    if dtype.is_float64():
        return {"fp64": NULLABLE}
    if dtype.is_floating():
        raise Unsupported(f"{dtype} is not supported; use float64")
    if dtype.is_string():
        return {"string": NULLABLE}
    if dtype.is_boolean():
        return {"bool": NULLABLE}
    if dtype.is_date():
        return {"date": NULLABLE}
    if dtype.is_timestamp():
        if dtype.timezone is not None:
            raise Unsupported("timestamps with a time zone are not supported")
        if dtype.scale not in (None, 6):
            raise Unsupported("only microsecond timestamps are supported")
        return {"precisionTimestamp": {"precision": 6, **NULLABLE}}
    if dtype.is_null():
        return {"i64": NULLABLE}
    raise Unsupported(f"type {dtype} is not supported")


def literal(value: Any, dtype: Any) -> Json:
    if value is None or dtype.is_null():
        return {"literal": {"null": type_json(dtype)}}
    if dtype.is_boolean():
        return {"literal": {"boolean": bool(value)}}
    if dtype.is_integer():
        key = type_json(dtype)
        name = next(iter(key))
        return {"literal": {name: str(value) if name == "i64" else int(value)}}
    if dtype.is_float64():
        x = float(value) + 0.0  # the model's one zero (and one NaN, below)
        text: Any = "NaN" if math.isnan(x) else x
        if math.isinf(x):
            text = "Infinity" if x > 0 else "-Infinity"
        return {"literal": {"fp64": text}}
    if dtype.is_string():
        return {"literal": {"string": str(value)}}
    if dtype.is_timestamp():
        type_json(dtype)
        if value.tzinfo is not None:
            raise Unsupported("timestamps with a time zone are not supported")
        micros = (value - EPOCH) // dt_.timedelta(microseconds=1)
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(micros)}}}
    if dtype.is_date():
        return {"literal": {"date": (value - EPOCH.date()).days}}
    if dtype.is_interval():
        return interval_literal(value, dtype)
    raise Unsupported(f"literal of type {dtype} is not supported")


_INTERVAL_MICROS = {
    "D": 86_400_000_000,
    "h": 3_600_000_000,
    "m": 60_000_000,
    "s": 1_000_000,
    "ms": 1_000,
    "us": 1,
}


def interval_literal(value: Any, dtype: Any) -> Json:
    if isinstance(value, dt_.timedelta):
        micros = value // dt_.timedelta(microseconds=1)
    else:
        factor = _INTERVAL_MICROS.get(dtype.unit.short)
        if factor is None:
            raise Unsupported(f"intervals in {dtype.unit.plural} are not supported")
        micros = int(value) * factor
    days, rest = divmod(micros, 86_400_000_000)
    seconds, sub = divmod(rest, 1_000_000)
    day_to_second = {"days": days, "seconds": seconds, "subseconds": str(sub), "precision": 6}
    return {"literal": {"intervalDayToSecond": day_to_second}}


# --------------------------------------------------------------------------
# Expressions


class Compiler:
    """Holds the function anchors of one plan."""

    def __init__(self) -> None:
        self.functions: dict[str, int] = {}

    def anchor(self, name: str) -> int:
        return self.functions.setdefault(name, len(self.functions) + 1)

    def extensions(self) -> list[Json]:
        return [
            {"extensionFunction": {"functionAnchor": a, "name": n}}
            for n, a in self.functions.items()
        ]


#: The compiler of the plan being built (one per `to_substrait` call).
_COMPILER: contextvars.ContextVar[Compiler] = contextvars.ContextVar("_COMPILER")


def _anchor(name: str) -> int:
    return _COMPILER.get().anchor(name)


def call(name: str, args: Iterable[Json]) -> Json:
    return {
        "scalarFunction": {
            "functionReference": _anchor(name),
            "arguments": [{"value": a} for a in args],
        }
    }


def field_ref(i: int) -> Json:
    return {"selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}}


def if_then(ifs: list[tuple[Json, Json]], default: Json) -> Json:
    return {"ifThen": {"ifs": [{"if": c, "then": t} for c, t in ifs], "else": default}}


def cast_json(e: Json, to: Any) -> Json:
    return {
        "cast": {
            "type": type_json(to),
            "input": e,
            "failureBehavior": "FAILURE_BEHAVIOR_THROW_EXCEPTION",
        }
    }


def same_type(a: Any, b: Any) -> bool:
    return a.copy(nullable=True) == b.copy(nullable=True)


#: Where each relation's columns start in the input of the expression being
#: translated: the input itself at 0, join tables at their join offsets.
Offsets = Mapping[Any, int]


class Exprs:
    """Translates value expressions over one input."""

    def __init__(self, offsets: Offsets, windows: Mapping[Any, int] | None = None):
        self.offsets = offsets
        # Window functions computed beforehand, by column (see `project`).
        self.windows = windows or {}

    def __call__(self, op: Any, to: Any = None) -> Json:
        """`op`, cast to `to` when its type differs."""
        e = self.translate(op)
        if to is not None and not op.dtype.is_null() and not same_type(op.dtype, to):
            return cast_json(e, to)
        return e

    def translate(self, op: Any) -> Json:
        if op in self.windows:
            return field_ref(self.windows[op])
        rule = _RULES.get(type(op))
        if rule is None:
            raise Unsupported(f"{type(op).__name__} is not supported")
        return rule(self, op)


def _common(*types: Any) -> Any:
    return dt.highest_precedence([t for t in types if not t.is_null()] or [dt.null])


def _field(x: Exprs, op: Any) -> Json:
    if op.rel not in x.offsets:
        raise Unsupported(f"column {op.name} refers to a relation outside its input")
    return field_ref(x.offsets[op.rel] + op.rel.schema.names.index(op.name))


def _literal(x: Exprs, op: Any) -> Json:
    return literal(op.value, op.dtype)


def _arith(name: str) -> Callable[[Exprs, Any], Json]:
    """Ibis computes in the operation's type: cast the operands to it."""
    return lambda x, op: call(name, [x(op.left, op.dtype), x(op.right, op.dtype)])


def _compare(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        t = _common(op.left.dtype, op.right.dtype)
        return call(name, [x(op.left, t), x(op.right, t)])

    return rule


def _unary(name: str) -> Callable[[Exprs, Any], Json]:
    return lambda x, op: call(name, [x(op.arg)])


def _power(x: Exprs, op: Any) -> Json:
    # Ibis types integer powers as doubles, but its SQL computes `POW` in
    # integers (which fails on overflow and negative exponents) and converts
    # the result.
    if op.left.dtype.is_integer() and op.right.dtype.is_integer():
        t = _common(op.left.dtype, op.right.dtype)
        return cast_json(call("power", [x(op.left, t), x(op.right, t)]), op.dtype)
    return call("power", [x(op.left, op.dtype), x(op.right, op.dtype)])


def _divide(x: Exprs, op: Any) -> Json:
    # Ibis's `/` is division of doubles (upstream divided integers).
    return call("divide", [x(op.left, dt.float64), x(op.right, dt.float64)])


def _floor_divide(x: Exprs, op: Any) -> Json:
    if op.left.dtype.is_integer() and op.right.dtype.is_integer():
        # Floor division in integers, as `sverify.engine` compiles `//`:
        # one less than the truncating quotient when that is inexact and
        # the signs differ.
        t = op.dtype
        a, b = x(op.left, t), x(op.right, t)
        zero = literal(0, t)
        quot = call("divide", [a, b])
        inexact = call("not_equal", [call("modulus", [a, b]), zero])
        signs = call("not_equal", [call("lt", [a, zero]), call("lt", [b, zero])])
        down = call("subtract", [quot, literal(1, t)])
        return if_then([(call("and", [inexact, signs]), down)], quot)
    q = call("divide", [x(op.left, dt.float64), x(op.right, dt.float64)])
    return cast_json(call("floor", [q]), op.dtype)


def _rounding(name: str) -> Callable[[Exprs, Any], Json]:
    # `CAST(FLOOR(x) AS <type>)` and friends, as Ibis's base compiler writes them.
    def rule(x: Exprs, op: Any) -> Json:
        args = [x(op.arg)]
        if getattr(op, "digits", None) is not None:
            args.append(x(op.digits))
        e = call(name, args)
        return e if same_type(op.arg.dtype, op.dtype) else cast_json(e, op.dtype)

    return rule


def _cast(x: Exprs, op: Any) -> Json:
    if same_type(op.arg.dtype, op.to):
        return x(op.arg)
    return cast_json(x(op.arg), op.to)


def _variadic(name: str) -> Callable[[Exprs, Any], Json]:
    return lambda x, op: call(name, [x(a, op.dtype) for a in op.arg])


def _clip(x: Exprs, op: Any) -> Json:
    arg = x(op.arg, op.dtype)
    if op.upper is not None:
        arg = if_then([(call("is_null", [arg]), arg)], call("least", [x(op.upper, op.dtype), arg]))
    if op.lower is not None:
        arg = if_then(
            [(call("is_null", [arg]), arg)], call("greatest", [x(op.lower, op.dtype), arg])
        )
    return arg


def _between(x: Exprs, op: Any) -> Json:
    t = _common(op.arg.dtype, op.lower_bound.dtype, op.upper_bound.dtype)
    a = x(op.arg, t)
    return call(
        "and", [call("gte", [a, x(op.lower_bound, t)]), call("lte", [a, x(op.upper_bound, t)])]
    )


def _in_values(x: Exprs, op: Any) -> Json:
    t = _common(op.value.dtype, *(o.dtype for o in op.options))
    return {"singularOrList": {"value": x(op.value, t), "options": [x(o, t) for o in op.options]}}


def _if_else(x: Exprs, op: Any) -> Json:
    return if_then([(x(op.bool_expr), x(op.true_expr, op.dtype))], x(op.false_null_expr, op.dtype))


def _searched_case(x: Exprs, op: Any) -> Json:
    ifs = [(x(c), x(r, op.dtype)) for c, r in zip(op.cases, op.results, strict=True)]
    return if_then(ifs, x(op.default, op.dtype))


def _simple_case(x: Exprs, op: Any) -> Json:
    t = _common(op.base.dtype, *(c.dtype for c in op.cases))
    ifs = [
        (call("equal", [x(op.base, t), x(c, t)]), x(r, op.dtype))
        for c, r in zip(op.cases, op.results, strict=True)
    ]
    return if_then(ifs, x(op.default, op.dtype))


def _string_contains(x: Exprs, op: Any) -> Json:
    return call("gt", [call("strpos", [x(op.haystack), x(op.needle)]), literal(0, dt.int64)])


def _like(x: Exprs, op: Any) -> Json:
    if op.escape is not None:
        raise Unsupported("LIKE with an escape character is not supported")
    return call("like", [x(op.arg), x(op.pattern)])


def _trim(name: str) -> Callable[[Exprs, Any], Json]:
    whitespace = " \t\n\r\x0b\x0c"
    return lambda x, op: call(name, [x(op.arg), literal(whitespace, dt.string)])


def _substring(x: Exprs, op: Any) -> Json:
    # Ibis counts from 0, and from the end for negative starts.
    if isinstance(op.length, ops.Literal) and op.length.value < 0:
        raise Unsupported("substring with a negative length")
    start = call("add", [x(op.start, dt.int64), literal(1, dt.int64)])
    start = if_then(
        [(call("gte", [start, literal(1, dt.int64)]), start)],
        call("add", [start, call("character_length", [x(op.arg)])]),
    )
    args = [x(op.arg), start] + ([] if op.length is None else [x(op.length, dt.int64)])
    return call("substring", args)


def _string_concat(x: Exprs, op: Any) -> Json:
    # NULL if any argument is: `str_concat` propagates NULLs.
    return chain("str_concat", [x(a) for a in op.arg])


def _regex_search(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal):
        raise Unsupported("regular expressions must be constants")
    arg, pattern = x(op.arg), x(op.pattern)
    matches = call("array_length", [call("regexp_match", [arg, pattern])])
    found = call(
        "coalesce", [call("gt", [matches, literal(0, dt.int64)]), literal(False, dt.boolean)]
    )
    return if_then([(call("is_null", [arg]), literal(None, dt.boolean))], found)


def _date_part(part: str) -> Callable[[Exprs, Any], Json]:
    return lambda x, op: call("date_part", [literal(part, dt.string), x(op.arg)])


def _date(x: Exprs, op: Any) -> Json:
    # A date, as Ibis types it (its DataFusion SQL truncates to a timestamp).
    return cast_json(x(op.arg), dt.date)


def _truncate(x: Exprs, op: Any) -> Json:
    unit = op.unit.name.lower()
    if unit in ("millisecond", "microsecond", "nanosecond"):
        raise Unsupported(f"truncating to {unit}s is not supported")
    return call("date_trunc", [literal(unit, dt.string), x(op.arg)])


def _is_nan(x: Exprs, op: Any) -> Json:
    # FALSE for NULL, as Ibis's DataFusion SQL writes it.
    arg = x(op.arg)
    return call("and", [call("is_not_null", [arg]), call("is_nan", [arg])])


def _string_find(x: Exprs, op: Any) -> Json:
    # Ibis counts from 0 (-1 when absent): one less than `strpos`.
    if op.start is not None or op.end is not None:
        raise Unsupported("find with start or end is not supported")
    return call("subtract", [call("strpos", [x(op.arg), x(op.substr)]), literal(1, dt.int64)])


_RULES: dict[Any, Callable[[Exprs, Any], Json]] = {
    ops.Field: _field,
    ops.Literal: _literal,
    ops.Add: _arith("add"),
    ops.Subtract: _arith("subtract"),
    ops.Multiply: _arith("multiply"),
    ops.Modulus: _arith("modulus"),
    ops.Power: _power,
    ops.Divide: _divide,
    ops.FloorDivide: _floor_divide,
    ops.Negate: _unary("negate"),
    ops.Abs: _unary("abs"),
    ops.Ceil: _rounding("ceil"),
    ops.Floor: _rounding("floor"),
    ops.Round: _rounding("round"),
    ops.Cast: _cast,
    ops.Equals: _compare("equal"),
    ops.NotEquals: _compare("not_equal"),
    ops.Less: _compare("lt"),
    ops.LessEqual: _compare("lte"),
    ops.Greater: _compare("gt"),
    ops.GreaterEqual: _compare("gte"),
    ops.IdenticalTo: _compare("is_not_distinct_from"),
    ops.And: lambda x, op: call("and", [x(op.left), x(op.right)]),
    ops.Or: lambda x, op: call("or", [x(op.left), x(op.right)]),
    ops.Not: _unary("not"),
    ops.IsNull: _unary("is_null"),
    ops.NotNull: _unary("is_not_null"),
    ops.Between: _between,
    ops.InValues: _in_values,
    ops.IfElse: _if_else,
    ops.SearchedCase: _searched_case,
    ops.SimpleCase: _simple_case,
    ops.Coalesce: _variadic("coalesce"),
    ops.Greatest: _variadic("greatest"),
    ops.Least: _variadic("least"),
    ops.NullIf: lambda x, op: call("nullif", [x(op.arg, op.dtype), x(op.null_if_expr, op.dtype)]),
    ops.Clip: _clip,
    ops.Uppercase: _unary("upper"),
    ops.Lowercase: _unary("lower"),
    ops.StringLength: _unary("character_length"),
    ops.StartsWith: lambda x, op: call("starts_with", [x(op.arg), x(op.start)]),
    ops.EndsWith: lambda x, op: call("ends_with", [x(op.arg), x(op.end)]),
    ops.StringContains: _string_contains,
    ops.StringSQLLike: _like,
    ops.Strip: _trim("btrim"),
    ops.LStrip: _trim("ltrim"),
    ops.RStrip: _trim("rtrim"),
    ops.Substring: _substring,
    ops.StringConcat: _string_concat,
    ops.RegexSearch: _regex_search,
    ops.ExtractYear: _date_part("year"),
    ops.ExtractQuarter: _date_part("quarter"),
    ops.ExtractMonth: _date_part("month"),
    ops.ExtractDay: _date_part("day"),
    ops.ExtractDayOfYear: _date_part("doy"),
    ops.ExtractHour: _date_part("hour"),
    ops.ExtractMinute: _date_part("minute"),
    ops.ExtractSecond: _date_part("second"),
    ops.Date: _date,
    ops.TimestampTruncate: _truncate,
    ops.TimestampAdd: lambda x, op: call("add", [x(op.left), x(op.right)]),
    ops.TimestampSub: lambda x, op: call("subtract", [x(op.left), x(op.right)]),
    ops.TimestampDiff: lambda x, op: call("subtract", [x(op.left), x(op.right)]),
    ops.IsNan: _is_nan,
    ops.StringFind: _string_find,
    ops.ExtractWeekOfYear: _date_part("week"),
}


# --------------------------------------------------------------------------
# Aggregates


def measure(x: Exprs, op: Any) -> Json:
    distinct = False
    args: list[Json]
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
    else:
        raise Unsupported(f"aggregate {type(op).__name__} is not supported")
    agg: Json = {
        "functionReference": _anchor(name),
        "arguments": [{"value": a} for a in args],
        "invocation": (
            "AGGREGATION_INVOCATION_DISTINCT" if distinct else "AGGREGATION_INVOCATION_ALL"
        ),
    }
    out: Json = {"measure": agg}
    if op.where is not None:
        out["filter"] = x(op.where)
    return out


# --------------------------------------------------------------------------
# Relations


def common_emit(mapping: list[int]) -> Json:
    return {"emit": {"outputMapping": mapping}}


def project_rel(input: Json, width: int, exprs: list[Json]) -> Json:
    """Append `exprs` and keep only them."""
    return {
        "project": {
            "common": common_emit(list(range(width, width + len(exprs)))),
            "input": input,
            "expressions": exprs,
        }
    }


def emit_rel(input: Json, mapping: list[int]) -> Json:
    """Keep the columns `mapping` (an empty project carries the emit)."""
    return {"project": {"common": common_emit(mapping), "input": input, "expressions": []}}


def select(input: Json, width: int, exprs: list[Json]) -> Json:
    """`exprs` over the `width` columns of `input`: an emit when all of them
    are columns, a projection otherwise."""
    if not all("selection" in e for e in exprs):
        return project_rel(input, width, exprs)
    cols = [e["selection"]["directReference"]["structField"]["field"] for e in exprs]
    return input if cols == list(range(width)) else emit_rel(input, cols)


def chain(name: str, args: list[Json]) -> Json:
    """`args` combined left to right with the binary function `name`."""
    out = args[0]
    for a in args[1:]:
        out = call(name, [out, a])
    return out


def rel(op: Any) -> Json:
    rule = _RELS.get(type(op))
    if rule is None:
        raise Unsupported(f"{type(op).__name__} is not supported")
    return rule(op)


def _read(op: Any) -> Json:
    schema = {
        "names": list(op.schema.names),
        "struct": {
            "types": [type_json(t, t.nullable) for t in op.schema.types],
            "nullability": "NULLABILITY_REQUIRED",
        },
    }
    return {"read": {"baseSchema": schema, "namedTable": {"names": [op.name]}}}


def _filter(op: Any) -> Json:
    x = Exprs({op.parent: 0})
    conds: list[Json] = []
    for p in op.predicates:
        if isinstance(p, ops.InSubquery):
            inside = {"needles": [x(p.needle)], "haystack": rel(p.rel)}
            conds.append({"subquery": {"inPredicate": inside}})
        else:
            conds.append(x(p))
    return {"filter": {"input": rel(op.parent), "condition": chain("and", conds)}}


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


def window(x: Exprs, op: Any) -> Json:
    if op.start is not None or op.end is not None:
        raise Unsupported("window frames are not supported")
    func = op.func
    args: list[Json] = []
    if isinstance(func, ops.RowNumber):
        name = "row_number"
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
    else:
        raise Unsupported(f"window function {type(func).__name__} is not supported")
    sorts = [_sort_key(x, k) for k in op.order_by]
    return {
        "windowFunction": {
            "functionReference": _anchor(name),
            "partitions": [x(g) for g in op.group_by],
            "sorts": sorts,
            "arguments": [{"value": a} for a in args],
            "lowerBound": {"unbounded": {}},
            "upperBound": {"unbounded": {}},
            "boundsType": "BOUNDS_TYPE_ROWS",
        }
    }


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


def _row_number_from_zero(x: Exprs, v: Any) -> Json:
    # Ibis's ROW_NUMBER counts from 0: its compiler subtracts 1.
    if isinstance(v, ops.WindowFunction) and isinstance(v.func, ops.RowNumber):
        return call("subtract", [x(v), literal(1, dt.int64)])
    return x(v)


def _aggregate(op: Any) -> Json:
    x = Exprs({op.parent: 0})
    groups = [x(g) for g in op.groups.values()]
    body: Json = {
        "input": rel(op.parent),
        "groupingExpressions": groups,
        "groupings": [{"expressionReferences": list(range(len(groups)))}] if groups else [],
        "measures": [measure(x, m) for m in op.metrics.values()],
    }
    return {"aggregate": body}


def _sort_key(x: Exprs, k: Any) -> Json:
    order = "ASC" if k.ascending else "DESC"
    nulls = "FIRST" if k.nulls_first else "LAST"
    return {"expr": x(k.arg), "direction": f"SORT_DIRECTION_{order}_NULLS_{nulls}"}


def _sort(op: Any) -> Json:
    x = Exprs({op.parent: 0})
    for k in op.keys:
        if not isinstance(k.arg, ops.Field):
            raise Unsupported("sorting by an expression is not supported; sort by a column")
    return {"sort": {"input": rel(op.parent), "sorts": [_sort_key(x, k) for k in op.keys]}}


def _limit(op: Any) -> Json:
    if not isinstance(op.offset, int) or not (op.n is None or isinstance(op.n, int)):
        raise Unsupported("LIMIT and OFFSET must be constants")
    body: Json = {"input": rel(op.parent), "offsetExpr": literal(op.offset, dt.int64)}
    if op.n is not None:
        body["countExpr"] = literal(op.n, dt.int64)
    return {"fetch": body}


def distinct_rel(input: Json, width: int) -> Json:
    groups = [field_ref(i) for i in range(width)]
    return {
        "aggregate": {
            "input": input,
            "groupingExpressions": groups,
            "groupings": [{"expressionReferences": list(range(width))}],
        }
    }


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


def _set_op(op: Any) -> Json:
    left, right = rel(op.left), rel(op.right)
    if isinstance(op, ops.Union):
        kind = "SET_OP_UNION_DISTINCT" if op.distinct else "SET_OP_UNION_ALL"
        return {"set": {"inputs": [left, right], "op": kind}}
    if not op.distinct:
        raise Unsupported(f"{type(op).__name__.upper()} ALL is not supported")
    # INTERSECT and EXCEPT are DISTINCT of a semi or anti join on all
    # columns, NULLs equal, as DataFusion plans them.
    n = len(op.schema)
    same = [call("is_not_distinct_from", [field_ref(i), field_ref(n + i)]) for i in range(n)]
    cond = chain("and", same)
    kind = "JOIN_TYPE_LEFT_SEMI" if isinstance(op, ops.Intersection) else "JOIN_TYPE_LEFT_ANTI"
    join = {"join": {"left": left, "right": right, "expression": cond, "type": kind}}
    return distinct_rel(join, n)


_RELS: dict[Any, Callable[[Any], Json]] = {
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
}


# --------------------------------------------------------------------------
# Plans


def to_substrait(expr: ir.Table) -> Json:
    """The Substrait plan of an Ibis table expression, as protobuf JSON."""
    compiler = Compiler()
    token = _COMPILER.set(compiler)
    try:
        op: Any = expr.op()
        root = {"input": rel(op), "names": list(op.schema.names)}
        return {"extensions": compiler.extensions(), "relations": [{"root": root}]}
    finally:
        _COMPILER.reset(token)


def to_substrait_json(expr: ir.Table) -> str:
    return json.dumps(to_substrait(expr))
