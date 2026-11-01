"""Ibis expressions to Substrait plans (protobuf JSON) for the Lean checker.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

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

import ibis
import ibis.expr.datatypes as dt
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.collections import FrozenOrderedDict
from ibis.common.typing import VarTuple
from ibis.expr.schema import Schema

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
    if dtype.is_time():
        return {"precisionTime": {"precision": 6, **NULLABLE}}
    if dtype.is_null():
        return {"i64": NULLABLE}
    if dtype.is_array():
        return {"list": {"type": type_json(dtype.value_type), **NULLABLE}}
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
    if dtype.is_time():
        if value.tzinfo is not None:
            raise Unsupported("times with a time zone are not supported")
        micros = ((value.hour * 60 + value.minute) * 60 + value.second) * 1_000_000
        micros += value.microsecond
        return {"literal": {"precisionTime": {"precision": 6, "value": str(micros)}}}
    if dtype.is_interval():
        return interval_literal(value, dtype)
    if dtype.is_array():
        # The elements of a list literal are literals without the `literal` key.
        if not value:
            return {"literal": {"emptyList": {"type": type_json(dtype.value_type)}}}
        values = [literal(v, dtype.value_type)["literal"] for v in value]
        return {"literal": {"list": {"values": values}}}
    raise Unsupported(f"literal of type {dtype} is not supported")


_INTERVAL_MICROS = {
    "W": 7 * 86_400_000_000,
    "D": 86_400_000_000,
    "h": 3_600_000_000,
    "m": 60_000_000,
    "s": 1_000_000,
    "ms": 1_000,
    "us": 1,
}


#: Months in an interval of each calendar unit.
_INTERVAL_MONTHS = {"Y": 12, "Q": 3, "M": 1}


def interval_parts(value: Any, dtype: Any) -> tuple[int, int]:
    """An interval constant as months and microseconds."""
    if isinstance(value, dt_.timedelta):
        return 0, value // dt_.timedelta(microseconds=1)
    unit = dtype.unit.short
    if unit in _INTERVAL_MONTHS:
        return int(value) * _INTERVAL_MONTHS[unit], 0
    factor = _INTERVAL_MICROS.get(unit)
    if factor is None:
        raise Unsupported(f"intervals in {dtype.unit.plural} are not supported")
    return 0, int(value) * factor


def interval_literal(value: Any, dtype: Any) -> Json:
    months, micros = interval_parts(value, dtype)
    return interval_json(months, micros)


def interval_json(months: int, micros: int) -> Json:
    """`months` and `micros` as one interval literal: a compound one if it
    has months (Lean reads those only added to a date or timestamp). Days are
    written as seconds: DataFusion compares a duration with an interval as
    `(months, days, nanoseconds)`, so only one of seconds compares as a number."""
    seconds, sub = divmod(micros, 1_000_000)
    day_to_second = {"seconds": seconds, "subseconds": str(sub), "precision": 6}
    if months:
        compound = {"intervalYearToMonth": {"months": months}, "intervalDayToSecond": day_to_second}
        return {"literal": {"intervalCompound": compound}}
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


def ieee_divide(a: Json, b: Json) -> Json:
    """`a / b` with `on_division_by_zero` = IEEE: `±inf` or NaN by zero rather
    than an error (#204)."""
    c = call("divide", [a, b])
    c["scalarFunction"]["options"] = [{"name": "on_division_by_zero", "preference": ["IEEE"]}]
    return c


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
        raise Unsupported(
            f"column {op.name} refers to a relation outside its input "
            "(correlated subqueries are only supported in EXISTS)"
        )
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


def _like(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        if op.escape is not None:
            raise Unsupported(f"{name.upper()} with an escape character is not supported")
        return call(name, [x(op.arg), x(op.pattern)])

    return rule


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


def _string_slice(x: Exprs, op: Any) -> Json:
    # Ibis's rewrite: `end - start` characters from `start` (0 if omitted).
    start = ops.Literal(0, dt.int64) if op.start is None else op.start
    if op.end is None:
        length = None
    elif isinstance(start, ops.Literal) and isinstance(op.end, ops.Literal):
        length = ops.Literal(op.end.value - start.value, dt.int64)
    else:
        length = ops.Subtract(op.end, start)
    return _substring(x, ops.Substring(op.arg, start=start, length=length))


def _capitalize(x: Exprs, op: Any) -> Json:
    # Ibis's rewrite: the first character in upper case, the rest in lower case.
    arg, one = x(op.arg), literal(1, dt.int64)
    first = call("upper", [call("substring", [arg, one, one])])
    rest = call("lower", [call("substring", [arg, literal(2, dt.int64)])])
    return call("str_concat", [first, rest])


def _pad(left: bool) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        # Ibis's DataFusion SQL: `s` if it has `length` characters or more,
        # otherwise `pad` repeated `length - length(s)` times on that side (a
        # longer `pad` is not cut to `length`).
        arg, n = x(op.arg), x(op.length, dt.int64)
        size = call("character_length", [arg])
        fill = call("repeat", [x(op.pad), call("subtract", [n, size])])
        padded = call("str_concat", [fill, arg] if left else [arg, fill])
        return if_then([(call("lte", [n, size]), arg)], padded)

    return rule


def _str_right(x: Exprs, op: Any) -> Json:
    # DataFusion's `right(s, n)`: the last `n` characters, or all but the
    # first `-n` for a negative `n`.
    arg, n, one = x(op.arg), x(op.nchars, dt.int64), literal(1, dt.int64)
    last = call("add", [call("subtract", [call("character_length", [arg]), n]), one])
    start = if_then([(call("lt", [n, literal(0, dt.int64)]), call("subtract", [one, n]))], last)
    return call("substring", [arg, start])


def _replace(x: Exprs, op: Any) -> Json:
    if not isinstance(op.pattern, ops.Literal) or not isinstance(op.replacement, ops.Literal):
        raise Unsupported("replace needs a constant pattern and replacement")
    return call("replace", [x(op.arg), x(op.pattern), x(op.replacement)])


def _string_join(x: Exprs, op: Any) -> Json:
    # `concat_ws(sep, …)`: the arguments that are not NULL, joined by `sep`
    # ('' if all are NULL, NULL if `sep` is). Each is `sep || a`, or '' for a
    # NULL `a`; the first `sep` is dropped.
    sep, empty = x(op.sep), literal("", dt.string)
    parts = [call("coalesce", [call("str_concat", [sep, x(a)]), empty]) for a in op.arg]
    start = call("add", [call("character_length", [sep]), literal(1, dt.int64)])
    return call("substring", [chain("str_concat", parts), start])


def _find_in_set(x: Exprs, op: Any) -> Json:
    # Ibis's DataFusion SQL: `array_position(make_array(values), needle) - 1`,
    # -1 if absent; NULL finds a NULL value.
    needle = x(op.needle)
    ifs = [
        (call("is_not_distinct_from", [needle, x(v)]), literal(k, dt.int64))
        for k, v in enumerate(op.values)
    ]
    return if_then(ifs, literal(-1, dt.int64))


def _translate(x: Exprs, op: Any) -> Json:
    raise Unsupported("translate: DataFusion replaces grapheme clusters, not characters")


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


# Dates, timestamps and intervals (`SubstraitLean/Time.lean`): an interval is
# months plus microseconds, and Lean reads month intervals only as constants
# added to a date or timestamp; days added to a date may be a column's count.


def _const_interval(op: Any) -> tuple[int, int] | None:
    """An interval expression of constants, as months and microseconds."""
    match op:
        case ops.Literal(value=v, dtype=t) if v is not None:
            return interval_parts(v, t)
        case ops.IntervalFromInteger(arg=ops.Literal(value=n), unit=u) if n is not None:
            return interval_parts(n, dt.Interval(unit=u))
        case ops.IntervalAdd() | ops.IntervalSubtract():
            a, b = _const_interval(op.left), _const_interval(op.right)
            if a is None or b is None:
                return None
            sign = 1 if isinstance(op, ops.IntervalAdd) else -1
            return a[0] + sign * b[0], a[1] + sign * b[1]
        case ops.IntervalMultiply(left=iv, right=ops.Literal(value=int(n))):
            a = _const_interval(iv)
            return None if a is None else (a[0] * n, a[1] * n)
        case ops.Negate(arg=iv):
            a = _const_interval(iv)
            return None if a is None else (-a[0], -a[1])
    return None


def _interval(x: Exprs, op: Any) -> Json:
    """An interval expression: a constant, or a column's count of a unit of
    days or less (`multiply(n, INTERVAL '1' unit)`)."""
    c = _const_interval(op)
    if c is not None:
        return interval_json(*c)
    if isinstance(op, ops.IntervalFromInteger):
        months, micros = interval_parts(1, dt.Interval(unit=op.unit))
        if months:
            raise Unsupported("a column's count of months or years is not supported")
        return call("multiply", [x(op.arg, dt.int64), interval_json(0, micros)])
    if isinstance(op, ops.IntervalBinary):
        raise Unsupported(f"{type(op).__name__} of non-constant intervals is not supported")
    return x(op)


def _interval_value(x: Exprs, op: Any) -> Json:
    # An interval on its own: microseconds (Lean refuses months there).
    return _interval(x, op)


def _temporal_add(name: str) -> Callable[[Exprs, Any], Json]:
    """`DateAdd`, `DateSub`, `TimestampAdd`, `TimestampSub`."""

    def rule(x: Exprs, op: Any) -> Json:
        if op.left.dtype.is_interval():
            left, right = op.right, op.left
        else:
            left, right = op.left, op.right
        iv = _interval(x, right)
        if op.left.dtype.is_timestamp() and "scalarFunction" in iv:
            raise Unsupported("a timestamp plus a column's interval is not supported")
        return call(name, [x(left), iv])

    return rule


def _date_diff(x: Exprs, op: Any) -> Json:
    # An interval (microseconds) of whole days. Not DataFusion's `d - e`: a
    # duration, which it compares with intervals wrongly.
    days = call("date_diff", [x(op.left), x(op.right)])
    return call("multiply", [days, literal(86_400_000_000, dt.int64)])


def _date_delta(x: Exprs, op: Any) -> Json:
    if op.part.value != "day":
        raise Unsupported(f"delta in {op.part.value}s is not supported; use days")
    return call("date_diff", [x(op.left), x(op.right)])


def _day_of_week_index(x: Exprs, op: Any) -> Json:
    # Monday is 0: `(date_part('dow', x) + 6) % 7`, as Ibis's DataFusion SQL.
    dow = call("date_part", [literal("dow", dt.string), x(op.arg)])
    return call("modulus", [call("add", [dow, literal(6, dt.int64)]), literal(7, dt.int64)])


def _day_of_week_name(x: Exprs, op: Any) -> Json:
    index = _day_of_week_index(x, op)
    names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
    ifs = [(call("equal", [index, literal(i, dt.int64)]), literal(n, dt.string))
           for i, n in enumerate(names)]  # fmt: skip
    return if_then(ifs, literal(None, dt.string))


def _as_date(x: Exprs, arg: Any) -> Json:
    return x(arg) if arg.dtype.is_date() else cast_json(x(arg), dt.date)


def _iso_year(x: Exprs, op: Any) -> Json:
    # The year of the week's Thursday (DataFusion has no `isoyear`).
    d = _as_date(x, op.arg)
    monday_index = _day_of_week_index(x, ops.DayOfWeekIndex(op.arg))
    to_thursday = call("subtract", [literal(3, dt.int64), monday_index])
    day = interval_json(0, 86_400_000_000)
    thursday = call("add", [d, call("multiply", [to_thursday, day])])
    return call("date_part", [literal("year", dt.string), thursday])


def _epoch_seconds(x: Exprs, op: Any) -> Json:
    """Whole seconds since 1970-01-01, rounding toward zero as Ibis's
    DataFusion UDF does (`CAST(ts AS BIGINT) / 1000000`)."""
    i64 = dt.int64

    def part(p: str) -> Json:
        return call("date_part", [literal(p, dt.string), x(op.arg)])

    days = call("date_diff", [_as_date(x, op.arg), literal(dt_.date(1970, 1, 1), dt.date)])
    secs = call("multiply", [days, literal(86400, i64)])
    if op.arg.dtype.is_date():
        return secs
    for p, k in (("hour", 3600), ("minute", 60), ("second", 1)):
        secs = call("add", [secs, call("multiply", [part(p), literal(k, i64)])])
    # Floor to truncation: before 1970, a fraction of a second rounds up.
    frac = call("modulus", [part("microsecond"), literal(1_000_000, i64)])
    before = call("lt", [x(op.arg), literal(EPOCH, dt.timestamp)])
    up = call("and", [before, call("not_equal", [frac, literal(0, i64)])])
    return call("add", [secs, if_then([(up, literal(1, i64))], literal(0, i64))])


def _sub_second(divisor: int) -> Callable[[Exprs, Any], Json]:
    """Ibis's millisecond (0-999) and microsecond (0-999999) of the second;
    DataFusion's `date_part` counts them within the minute."""

    def rule(x: Exprs, op: Any) -> Json:
        us = call("date_part", [literal("microsecond", dt.string), x(op.arg)])
        within = call("modulus", [us, literal(1_000_000, dt.int64)])
        return within if divisor == 1 else call("divide", [within, literal(divisor, dt.int64)])

    return rule


def _date_truncate(x: Exprs, op: Any) -> Json:
    unit = op.unit.name.lower()
    if unit not in ("day", "week", "month", "quarter", "year"):
        raise Unsupported(f"truncating a date to a {unit} is not supported")
    return call("date_trunc", [literal(unit, dt.string), x(op.arg)])


# Constructors, formatting and times of day.


def _constants(*args: Any) -> list[int] | None:
    """The values of integer literals, or None if one is not a constant."""
    values: list[int] = []
    for a in args:
        v = a.value if isinstance(a, ops.Literal) else None
        if not isinstance(v, int) or isinstance(v, bool):
            return None
        values.append(v)
    return values


def _from_parts(build: Callable[..., Any], dtype: Any, what: str) -> Callable[[Exprs, Any], Json]:
    """`DateFromYMD` and friends: constants only (Lean has no functions of
    three arguments); a bad date is an error, as in DataFusion."""

    def rule(x: Exprs, op: Any) -> Json:
        values = _constants(*op.args)
        if values is None:
            raise Unsupported(f"{what} of columns is not supported, only of constants")
        try:
            value = build(*values)
        except (ValueError, OverflowError) as e:
            raise Unsupported(f"{what} of {values}: {e}") from e
        return literal(value, dtype)

    return rule


_UNIX_MICROS = {"s": 1_000_000, "ms": 1_000, "us": 1}


def _from_unix(x: Exprs, op: Any) -> Json:
    k = _UNIX_MICROS.get(op.unit.short)
    if k is None:
        raise Unsupported(f"timestamps from {op.unit.plural} are not supported")
    us = x(op.arg, dt.int64)
    if k != 1:
        us = call("multiply", [us, literal(k, dt.int64)])
    return cast_json(us, dt.timestamp)


def _strftime(x: Exprs, op: Any) -> Json:
    if not op.arg.dtype.is_timestamp():
        raise Unsupported("strftime is only supported of timestamps")
    if not isinstance(op.format_str, ops.Literal):
        raise Unsupported("strftime formats must be constants")
    return call("strftime", [x(op.arg), literal(op.format_str.value, dt.string)])


def _bucket(x: Exprs, op: Any) -> Json:
    """`date_bin`: buckets of a constant interval of days or less, counted
    from 1970-01-01 plus the offset (Ibis's origin)."""
    c = _const_interval(op.interval)
    o = (0, 0) if op.offset is None else _const_interval(op.offset)
    if c is None or c[0] or c[1] <= 0 or o is None or o[0]:
        raise Unsupported("bucket needs constant intervals of days or less")
    origin = {"literal": {"precisionTimestamp": {"precision": 6, "value": str(o[1])}}}
    return call("date_bin", [interval_json(0, c[1]), x(op.arg), origin])


def _between_time(x: Exprs, op: Any) -> Json:
    t = cast_json(x(op.arg), dt.time)
    lo, hi = x(op.lower_bound, dt.time), x(op.upper_bound, dt.time)
    return call("and", [call("gte", [t, lo]), call("lte", [t, hi])])


def _is_nan(x: Exprs, op: Any) -> Json:
    # FALSE for NULL, as Ibis's DataFusion SQL writes it.
    arg = x(op.arg)
    return call("and", [call("is_not_null", [arg]), call("is_nan", [arg])])


def _double_fn(name: str) -> Callable[[Exprs, Any], Json]:
    # `SQRT(x)` and friends of doubles; DataFusion converts integers.
    return lambda x, op: call(name, [x(op.arg, dt.float64)])


def _double(v: float) -> Json:
    return literal(v, dt.float64)


def _log(x: Exprs, op: Any) -> Json:
    # Ibis's SQL: `LN(x)`, `LOG2(x)` or `LOG10(x)` for a constant base 2 or
    # 10, and `LN(x) / LN(b)` otherwise, which is Substrait's `logb(x, b)`.
    arg = x(op.arg, dt.float64)
    if op.base is None:
        return call("ln", [arg])
    if isinstance(op.base, ops.Literal) and op.base.value in (2, 10):
        return call(f"log{op.base.value}", [arg])
    return call("logb", [arg, x(op.base, dt.float64)])


def _sign(x: Exprs, op: Any) -> Json:
    # -1, 0 or 1 in the argument's type; NaN for NaN, which is tested first
    # (NaN is above every number).
    arg, t = x(op.arg), op.arg.dtype
    ifs = [
        (call("lt", [arg, literal(0, t)]), literal(-1, t)),
        (call("gt", [arg, literal(0, t)]), literal(1, t)),
    ]
    if t.is_floating():
        ifs.insert(0, (call("is_nan", [arg]), arg))
    return if_then(ifs, arg)


def _is_inf(x: Exprs, op: Any) -> Json:
    # Ibis's SQL: `NOT isnan(x) AND abs(x) = inf`, which is this.
    arg = x(op.arg, dt.float64)
    inf = [call("equal", [arg, _double(s * math.inf)]) for s in (1, -1)]
    return call("or", inf)


def _bitwise(name: str) -> Callable[[Exprs, Any], Json]:
    def rule(x: Exprs, op: Any) -> Json:
        if "shift" in name and not op.dtype.is_int64():
            # Narrower shifts lose bits at their own width.
            raise Unsupported(f"shifts of {op.dtype} are not supported; cast to int64")
        return call(name, [x(op.left, op.dtype), x(op.right, op.dtype)])

    return rule


def _xor(x: Exprs, op: Any) -> Json:
    # Ibis's DataFusion SQL: `(a AND NOT b) OR (NOT a AND b)`.
    a, b = x(op.left), x(op.right)
    return call("or", [call("and", [a, call("not", [b])]), call("and", [call("not", [a]), b])])


def _string_find(x: Exprs, op: Any) -> Json:
    # Ibis counts from 0 (-1 when absent): one less than `strpos`.
    if op.end is not None:
        raise Unsupported("find with an end is not supported")
    arg, sub, one = x(op.arg), x(op.substr), literal(1, dt.int64)
    if op.start is None:
        return call("subtract", [call("strpos", [arg, sub]), one])
    # Ibis's DataFusion SQL: from `start`, as
    # `COALESCE(NULLIF(strpos(substring(s, start + 1), t) + start, start), 0) - 1`.
    start = x(op.start, dt.int64)
    rest = call("substring", [arg, call("add", [start, one])])
    pos = call("add", [call("strpos", [rest, sub]), start])
    found = call("coalesce", [call("nullif", [pos, start]), literal(0, dt.int64)])
    return call("subtract", [found, one])


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
    ops.StringSQLLike: _like("like"),
    ops.StringSQLILike: _like("ilike"),
    ops.Strip: _trim("btrim"),
    ops.LStrip: _trim("ltrim"),
    ops.RStrip: _trim("rtrim"),
    ops.Substring: _substring,
    ops.StringSlice: _string_slice,
    ops.Capitalize: _capitalize,
    ops.LPad: _pad(left=True),
    ops.RPad: _pad(left=False),
    ops.Repeat: lambda x, op: call("repeat", [x(op.arg), x(op.times, dt.int64)]),
    ops.Reverse: _unary("reverse"),
    ops.StrRight: _str_right,
    ops.StringReplace: _replace,
    ops.StringAscii: _unary("ascii"),
    ops.StringJoin: _string_join,
    ops.FindInSet: _find_in_set,
    ops.Levenshtein: lambda x, op: call("levenshtein", [x(op.left), x(op.right)]),
    ops.Translate: _translate,
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
    ops.TimestampAdd: _temporal_add("add"),
    ops.TimestampSub: _temporal_add("subtract"),
    ops.TimestampDiff: lambda x, op: call("subtract", [x(op.left), x(op.right)]),
    ops.DateAdd: _temporal_add("add"),
    ops.DateSub: _temporal_add("subtract"),
    ops.DateDiff: _date_diff,
    ops.DateDelta: _date_delta,
    ops.DateTruncate: _date_truncate,
    ops.DayOfWeekIndex: _day_of_week_index,
    ops.DayOfWeekName: _day_of_week_name,
    ops.ExtractIsoYear: _iso_year,
    ops.ExtractEpochSeconds: _epoch_seconds,
    ops.ExtractMillisecond: _sub_second(1000),
    ops.ExtractMicrosecond: _sub_second(1),
    ops.IntervalFromInteger: _interval_value,
    ops.IntervalAdd: _interval_value,
    ops.IntervalSubtract: _interval_value,
    ops.IntervalMultiply: _interval_value,
    ops.DateFromYMD: _from_parts(dt_.date, dt.date, "DateFromYMD"),
    ops.TimestampFromYMDHMS: _from_parts(dt_.datetime, dt.timestamp, "TimestampFromYMDHMS"),
    ops.TimeFromHMS: _from_parts(dt_.time, dt.time, "TimeFromHMS"),
    ops.TimestampFromUNIX: _from_unix,
    ops.Strftime: _strftime,
    ops.Time: lambda x, op: cast_json(x(op.arg), dt.time),
    ops.BetweenTime: _between_time,
    ops.TimestampBucket: _bucket,
    ops.IsNan: _is_nan,
    ops.StringFind: _string_find,
    ops.ExtractWeekOfYear: _date_part("week"),
    # Elementary functions and bitwise operations (`SubstraitLean/Numeric.lean`).
    ops.Sqrt: _double_fn("sqrt"),
    ops.Exp: _double_fn("exp"),
    ops.Ln: _double_fn("ln"),
    ops.Log: _log,
    ops.Log10: _double_fn("log10"),
    ops.Log2: _double_fn("log2"),
    ops.Sin: _double_fn("sin"),
    ops.Cos: _double_fn("cos"),
    ops.Tan: _double_fn("tan"),
    ops.Asin: _double_fn("asin"),
    ops.Acos: _double_fn("acos"),
    ops.Atan: _double_fn("atan"),
    ops.Atan2: lambda x, op: call("atan2", [x(op.left, dt.float64), x(op.right, dt.float64)]),
    # DataFusion's `COT(x)` is `1 / tan(x)` in IEEE division, so `cot(0)` is
    # `inf`; `DEGREES` and `RADIANS` multiply by Rust's constants
    # (`f64::to_degrees`, `to_radians`).
    ops.Cot: lambda x, op: ieee_divide(_double(1.0), call("tan", [x(op.arg, dt.float64)])),
    ops.Degrees: lambda x, op: call("multiply", [x(op.arg, dt.float64), _double(180 / math.pi)]),
    ops.Radians: lambda x, op: call("multiply", [x(op.arg, dt.float64), _double(math.pi / 180)]),
    ops.E: lambda x, op: _double(math.e),
    ops.Pi: lambda x, op: _double(math.pi),
    ops.Sign: _sign,
    ops.IsInf: _is_inf,
    ops.BitwiseAnd: _bitwise("bitwise_and"),
    ops.BitwiseOr: _bitwise("bitwise_or"),
    ops.BitwiseXor: _bitwise("bitwise_xor"),
    ops.BitwiseLeftShift: _bitwise("bitwise_shift_left"),
    ops.BitwiseRightShift: _bitwise("bitwise_shift_right"),
    # `~x` is `x XOR -1`, as Ibis's DataFusion SQL writes it.
    ops.BitwiseNot: lambda x, op: call("bitwise_xor", [x(op.arg), literal(-1, op.dtype)]),
    ops.Xor: _xor,
    ops.ScalarSubquery: _scalar_subquery,
    ops.ExistsSubquery: _exists_subquery,
    ops.InSubquery: _in_subquery,
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
    elif isinstance(op, ops.ArrayCollect):
        return collect(x, op)
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
        factor = _INTERVAL_MICROS.get(dtype.unit.short)
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
        if not all(
            "selection" in a["value"] or "cast" in a["value"] for a in m["measure"]["arguments"]
        ):
            raise Unsupported("window aggregates of expressions are not supported; use a column")
        fn = m["measure"]
        return {
            "windowFunction": {
                "functionReference": fn["functionReference"],
                "partitions": [x(g) for g in op.group_by],
                "sorts": [_sort_key(x, k) for k in op.order_by],
                "arguments": fn["arguments"],
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
    # Ibis's ROW_NUMBER, RANK, DENSE_RANK and NTILE count from 0: its compiler
    # subtracts 1.
    zero = (ops.RowNumber, ops.MinRank, ops.DenseRank, ops.NTile)
    if isinstance(v, ops.WindowFunction) and isinstance(v.func, zero):
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


def values_rel(schema: Any, rows: list[list[Json]]) -> Json:
    base = {
        "names": list(schema.names),
        "struct": {
            "types": [type_json(t) for t in schema.types],
            "nullability": "NULLABILITY_REQUIRED",
        },
    }
    table = {"expressions": [{"fields": r} for r in rows]}
    return {"read": {"baseSchema": base, "virtualTable": table}}


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


# SQL strings (`Table.sql`, `Backend.sql`) are compiled by DataFusion's
# Substrait producer, over empty tables of the right schemas, and its plan is
# spliced in: reads of the view's alias become the aliased relation's plan,
# and function anchors are renumbered into this plan's.


def _sql_context(tables: Mapping[str, Any]) -> Any:
    try:
        import datafusion
    except ImportError as e:
        raise Unsupported("SQL strings need DataFusion: pip install 'sverify[datafusion]'") from e
    import pyarrow as pa

    ctx = datafusion.SessionContext()
    for name, schema in tables.items():
        empty = pa.RecordBatch.from_pylist([], schema=schema.to_pyarrow())
        ctx.register_record_batches(name, [[empty]])
    return ctx


def _physical_tables(op: Any) -> dict[str, Any]:
    """The named tables below `op`, by name, and the views' aliases."""
    found: dict[str, Any] = {}
    for node in op.find((ops.PhysicalTable,)):
        if isinstance(node, ops.InMemoryTable):
            continue
        found[node.name] = node.schema
    return found


def _sql_plan(query: str, tables: Mapping[str, Any]) -> Json:
    from datafusion import substrait as ss
    from google.protobuf import json_format
    from substrait.plan_pb2 import Plan

    ctx = _sql_context(tables)
    try:
        logical = ctx.sql(query).logical_plan()
    except Exception as e:  # noqa: BLE001 - DataFusion raises plain exceptions
        raise Unsupported(f"DataFusion cannot plan the SQL: {str(e).splitlines()[0]}") from e
    proto = Plan()
    proto.ParseFromString(ss.Producer.to_substrait_plan(logical, ctx).encode())
    return json_format.MessageToDict(proto)


def sql_view_schema(parent: Any, query: str) -> Any:
    """The schema DataFusion gives `query` over `parent` (an aliased relation)."""
    tables = {**_physical_tables(parent), parent.name: parent.schema}
    ctx = _sql_context(tables)
    return ibis.Schema.from_pyarrow(ctx.sql(query).schema())


def _splice(plan: Json, views: Mapping[str, Any]) -> Json:
    """The root relation of a DataFusion plan, with its function anchors in
    this plan's numbering and reads of `views` replaced by their plans."""
    names = {
        e["extensionFunction"].get("functionAnchor", 0): e["extensionFunction"]["name"]
        for e in plan.get("extensions", [])
        if "extensionFunction" in e
    }

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
            # Isthmus maps a read's output columns with an emit.
            out = emit_rel(out, list(common["emit"].get("outputMapping", [])))
        return out

    (root,) = [r["root"] for r in plan["relations"] if "root" in r]
    return walk(root["input"])


class SQLModel(ops.Relation):
    """A SQL query over named input relations (`sverify.sql`): the query reads
    each input by its name in `names`."""

    query: str
    inputs: VarTuple[ops.Relation]
    names: VarTuple[str]
    schema: Schema
    values = FrozenOrderedDict()


def _isthmus_plan(query: str, tables: Mapping[str, Any]) -> Json:
    """Isthmus's plan of `query` over empty tables with these schemas."""
    import pyarrow as pa

    from sverify.engine import SqlError, connect, isthmus_json

    con = connect(sql_producer="isthmus")
    for name, schema in tables.items():
        con.put(name, pa.schema(schema.to_pyarrow()).empty_table())
    try:
        return json.loads(isthmus_json(con, query))
    except SqlError as e:
        raise Unsupported(f"Isthmus cannot plan the SQL: {e}") from e


def sql_model_plan(query: str, tables: Mapping[str, Any]) -> Json:
    """The plan of `query` over tables of these (Ibis) schemas, from
    DataFusion's SQL producer, or Isthmus's where DataFusion is not installed."""
    from sverify.engine import default_sql_producer

    try:
        producer = default_sql_producer()
    except ImportError as e:
        raise ImportError(
            "sverify.sql needs a SQL producer: pip install 'sverify[datafusion]' "
            "(or put an Isthmus binary on PATH as `isthmus` or in $SVERIFY_ISTHMUS)"
        ) from e
    if producer == "isthmus":
        return _isthmus_plan(query, tables)
    return _sql_plan(query, tables)


def sql_model_schema(query: str, tables: Mapping[str, Any]) -> Any:
    """The schema of `query` over tables of these (Ibis) schemas."""
    from sverify.engine import default_sql_producer

    try:
        producer = default_sql_producer()
    except ImportError:
        producer = None
    if producer == "datafusion":
        try:
            return ibis.Schema.from_pyarrow(_sql_context(tables).sql(query).schema())
        except Exception as e:  # noqa: BLE001 - DataFusion raises plain exceptions
            raise Unsupported(f"DataFusion cannot plan the SQL: {str(e).splitlines()[0]}") from e
    # Isthmus gives types only in the plan: run it, as Lean writes it, on
    # empty tables.
    import pyarrow as pa

    from sverify.engine import connect, run_plan, written_plan

    plan = sql_model_plan(query, tables)
    con = connect()
    for name, schema in tables.items():
        con.put(name, pa.schema(schema.to_pyarrow()).empty_table())
    result = run_plan(con, written_plan(json.dumps(plan)), "duckdb")
    return ibis.Schema.from_pyarrow(result.schema)


def _sql_model(op: Any) -> Json:
    tables = {n: i.schema for n, i in zip(op.names, op.inputs, strict=True)}
    plan = sql_model_plan(op.query, tables)
    return _splice(plan, dict(zip(op.names, op.inputs, strict=True)))


def _sql_string_view(op: Any) -> Json:
    if not isinstance(op.parent, ops.AliasedRelation):
        raise Unsupported("SQL over a table needs an alias to refer to it: use t.alias(name).sql")
    parent = op.parent
    tables = {**_physical_tables(parent), parent.name: parent.schema}
    return _splice(_sql_plan(op.query, tables), {parent.name: parent.parent})


def _sql_query_result(op: Any) -> Json:
    import sqlglot as sg
    import sqlglot.expressions as sge

    tables = {}
    for t in sg.parse_one(op.query, read="datafusion").find_all(sge.Table):
        try:
            tables[t.name] = op.source.get_schema(t.name)
        except Exception:  # noqa: BLE001 - a CTE's name, say
            continue
    return _splice(_sql_plan(op.query, tables), {})


def _table_unnest(op: Any) -> Json:
    # No standard Substrait relation: an `ExtensionSingleRel` with our own
    # detail (`docs/nested-values.md`). The column keeps its place.
    if op.offset is not None:
        raise Unsupported("unnest(offset=) is not supported")
    if op.keep_empty:
        raise Unsupported("unnest(keep_empty=True) is not supported")
    if op.column_name != op.column.name or not isinstance(op.column, ops.Field):
        raise Unsupported("unnest must unnest a column in place")
    col = list(op.parent.schema.names).index(op.column.name)
    detail = {"@type": "type.googleapis.com/sverify.Unnest", "column": col}
    return {"extensionSingle": {"input": rel(op.parent), "detail": detail}}


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
    ops.AliasedRelation: lambda op: rel(op.parent),
    ops.FillNull: _fill_null,
    ops.InMemoryTable: _memtable,
    ops.DummyTable: _dummy_table,
    ops.SQLStringView: _sql_string_view,
    SQLModel: _sql_model,
    ops.SQLQueryResult: _sql_query_result,
    ops.TableUnnest: _table_unnest,
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
