"""Substrait plans as protobuf JSON: the types, literals, calls and
relations that sverify's producers write (the Ibis producer,
`sverify.ibis_substrait`, and the SQL lift, `sverify.sql_lift`), with the
functions and encodings `SubstraitLean/Parse.lean` reads.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Moved here from `sverify.ibis_substrait` (derived from ibis-substrait, Apache
License 2.0; see `ibis_substrait/LICENSE`), so that both producers write
plans the same way. Function anchors are numbered per plan: `call` and
`anchor` use the `Compiler` that `compiling` sets.
"""

from __future__ import annotations

import base64
import contextlib
import contextvars
import datetime as dt_
import math
from collections.abc import Iterable, Iterator
from decimal import Decimal
from typing import Any

import ibis.expr.datatypes as dt

from sverify import black_box
from sverify._unsupported import Unsupported as _Unsupported

Json = dict[str, Any]

EPOCH = dt_.datetime(1970, 1, 1)
NULLABLE = {"nullability": "NULLABILITY_NULLABLE"}
REQUIRED = {"nullability": "NULLABILITY_REQUIRED"}


class Unsupported(_Unsupported):
    """The expression uses something the Lean model does not cover
    (`sverify.errors.UnsupportedError`)."""


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
    if dtype.is_decimal():
        if dtype.precision is None or dtype.scale is None:
            raise Unsupported("decimals of unknown precision are not supported")
        return {"decimal": {"precision": dtype.precision, "scale": dtype.scale, **NULLABLE}}
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
    if dtype.is_struct():
        return {"struct": {"types": [type_json(t) for t in dtype.types], **NULLABLE}}
    raise Unsupported(f"type {dtype} is not supported")


def struct_names(schema: Any) -> list[str]:
    """A `NamedStruct`'s names: each column's, followed by its struct
    fields' names, depth first (Substrait's `NamedStruct`)."""

    def names(name: str, dtype: Any) -> list[str]:
        if dtype.is_struct():
            return [name, *(n for f, t in dtype.items() for n in names(f, t))]
        return [name]

    return [n for name, t in schema.items() for n in names(name, t)]


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
    if dtype.is_decimal():
        return decimal_literal(value, dtype)
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
    if dtype.is_struct():
        fields = [literal(value.get(f), t)["literal"] for f, t in dtype.items()]
        return {"literal": {"struct": {"fields": fields}}}
    raise Unsupported(f"literal of type {dtype} is not supported")


def same_type(a: Any, b: Any) -> bool:
    """Are the Ibis types `a` and `b` the same, nullability aside?"""
    return a.copy(nullable=True) == b.copy(nullable=True)


def decimal_dtype(p: int, s: int) -> Any:
    """`DECIMAL(p, s)`, its precision capped at DuckDB's 38."""
    return dt.Decimal(precision=min(p, 38), scale=s, nullable=True)


def decimal_type_of(value: Any) -> Any:
    """The narrowest `DECIMAL(p, s)` that holds `value` exactly."""
    d = Decimal(value)
    if not d.is_finite():
        raise Unsupported(f"decimal {d} is not supported")
    s = max(0, -int(d.as_tuple().exponent))
    digits = len(str(abs(int(d.scaleb(s)))))
    return dt.Decimal(precision=max(digits, s, 1), scale=s, nullable=True)


def decimal_literal(value: Any, dtype: Any) -> Json:
    """A `DECIMAL(p, s)` literal: its unscaled value as 16 little-endian bytes
    of two's complement. A decimal of unknown precision (Ibis's constants) gets
    the narrowest type that holds it."""
    if dtype.precision is None or dtype.scale is None:
        dtype = decimal_type_of(value)
    unscaled = Decimal(value).scaleb(dtype.scale)
    if unscaled != unscaled.to_integral_value():
        raise Unsupported(f"{value} has more than {dtype.scale} decimal places")
    if len(str(abs(int(unscaled)))) > dtype.precision:
        raise Unsupported(f"{value} does not fit {dtype}")
    raw = int(unscaled).to_bytes(16, "little", signed=True)
    body = {"value": base64.b64encode(raw).decode(), "precision": dtype.precision}
    return {"literal": {"decimal": {**body, "scale": dtype.scale}}}


INTERVAL_MICROS = {
    "W": 7 * 86_400_000_000,
    "D": 86_400_000_000,
    "h": 3_600_000_000,
    "m": 60_000_000,
    "s": 1_000_000,
    "ms": 1_000,
    "us": 1,
}


#: Months in an interval of each calendar unit.
INTERVAL_MONTHS = {"Y": 12, "Q": 3, "M": 1}


def interval_parts(value: Any, dtype: Any) -> tuple[int, int]:
    """An interval constant as months and microseconds."""
    if isinstance(value, dt_.timedelta):
        return 0, value // dt_.timedelta(microseconds=1)
    unit = dtype.unit.short
    if unit in INTERVAL_MONTHS:
        return int(value) * INTERVAL_MONTHS[unit], 0
    factor = INTERVAL_MICROS.get(unit)
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
        # A black box is sverify's own, under its URN (#325).
        return [
            {
                "extensionFunction": {
                    "functionAnchor": a,
                    "name": n,
                    **({"extensionUrnReference": 1} if n in black_box.NAMES else {}),
                }
            }
            for n, a in self.functions.items()
        ]

    def urns(self) -> list[Json]:
        if not black_box.NAMES & self.functions.keys():
            return []
        return [{"extensionUrnAnchor": 1, "urn": black_box.URN}]


#: The compiler of the plan being built (one per `to_substrait` call).
_COMPILER: contextvars.ContextVar[Compiler] = contextvars.ContextVar("_COMPILER")


def anchor(name: str) -> int:
    """The anchor of the function `name` in the plan being built."""
    return _COMPILER.get().anchor(name)


def call(name: str, args: Iterable[Json]) -> Json:
    return {
        "scalarFunction": {
            "functionReference": anchor(name),
            "arguments": [{"value": a} for a in args],
        }
    }


#: The profile the plan being built is read under (`verify(semantics=...)`):
#: under `"polars"`, integer `//` and `%` are Polars's (`floor_call`).
_SEMANTICS: contextvars.ContextVar[str] = contextvars.ContextVar("_SEMANTICS", default="reference")


def semantics() -> str:
    """The profile the plan being built is read under."""
    return _SEMANTICS.get()


def floor_call(name: str, args: Iterable[Json]) -> Json:
    """Integer `divide` or `modulus` with `division_type` = `FLOOR`: Polars's
    `//` and `%` (`Profile.polars`, `SubstraitLean/PolarsProfile.lean`)."""
    j = call(name, args)
    j["scalarFunction"]["options"] = [{"name": "division_type", "preference": ["FLOOR"]}]
    return j


def substring_left(args: list[Json]) -> Json:
    """`substring` whose start may be below 1, which then lies left of the
    first character (`negative_start` = `LEFT_OF_BEGINNING`): the rules below
    compute such starts. A plan that omits the option counts a negative start
    from the end instead (`Text.substrWrap`, #209)."""
    j = call("substring", args)
    j["scalarFunction"]["options"] = [
        {"name": "negative_start", "preference": ["LEFT_OF_BEGINNING"]}
    ]
    return j


def ieee_divide(a: Json, b: Json) -> Json:
    """`a / b` with `on_division_by_zero` = IEEE: `±inf` or NaN by zero rather
    than an error (#204)."""
    c = call("divide", [a, b])
    c["scalarFunction"]["options"] = [{"name": "on_division_by_zero", "preference": ["IEEE"]}]
    return c


def field_ref(i: int) -> Json:
    return {"selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}}


def column_of(e: Json) -> int | None:
    """The input column `e` reads, if it is a plain column reference (not a
    reference into a value, #94)."""
    sel = e.get("selection")
    if sel is None or "rootReference" not in sel:
        return None
    sf = sel.get("directReference", {}).get("structField")
    if sf is None or "child" in sf:
        return None
    return int(sf.get("field", 0))


def int_range(values: Any) -> tuple[int, int] | None:
    """The bounds of `values` if they are two or more integers that fill a
    range without gaps, as `[0, 1]` or `[3, 1, 2]` do; else None."""
    ints = set(values)
    if len(ints) < 2 or not all(type(v) is int for v in ints):
        return None
    lo, hi = min(ints), max(ints)
    return (lo, hi) if hi - lo + 1 == len(ints) else None


def if_then(ifs: list[tuple[Json, Json]], default: Json) -> Json:
    return {"ifThen": {"ifs": [{"if": c, "then": t} for c, t in ifs], "else": default}}


def cast_json(e: Json, to: Any, or_null: bool = False) -> Json:
    """`CAST(e AS to)`, or `TRY_CAST` (`or_null`: NULL where it fails, #58)."""
    behavior = "RETURN_NULL" if or_null else "THROW_EXCEPTION"
    return {
        "cast": {
            "type": type_json(to),
            "input": e,
            "failureBehavior": f"FAILURE_BEHAVIOR_{behavior}",
        }
    }


def _i64(k: int) -> Json:
    return literal(k, dt.int64)


def days_json(date: Json, n: Json) -> Json:
    """The DATE `n` days after `date` (`BinFn.dateAdd`)."""
    return call("add", [date, call("multiply", [n, interval_json(0, 86_400_000_000)])])


def make_date_json(y: Json, m: Json, d: Json) -> Json:
    """`make_date(y, m, d)` of integers (#809): the date by H. Hinnant's
    `days_from_civil`, NULL if an argument is. It raises for a month or day
    the calendar lacks, as DuckDB does, and for a year outside the
    reference's 1 to 9999."""

    def div(a: Json, k: int) -> Json:
        return call("divide", [a, _i64(k)])

    def mul(a: Json, k: int) -> Json:
        return call("multiply", [a, _i64(k)])

    def add(*xs: Json) -> Json:
        return chain("add", list(xs))

    def sub(a: Json, b: Json) -> Json:
        return call("subtract", [a, b])

    def clamp(a: Json, lo: int, hi: int) -> Json:
        return call("greatest", [call("least", [a, _i64(hi)]), _i64(lo)])

    def within(a: Json, lo: int, hi: int) -> Json:
        return call("and", [call("gte", [a, _i64(lo)]), call("lte", [a, _i64(hi)])])

    # The arguments clamped to their ranges, so that the arithmetic below is
    # bounded and its SQL needs no overflow guards; the comparisons after it
    # see the arguments as they are.
    yc, mc, dc = clamp(y, 1, 9999), clamp(m, 1, 12), clamp(d, 1, 31)
    # The year from March (January and February are the previous year's),
    # and the day of that year, without a CASE.
    yy = sub(yc, div(sub(_i64(14), mc), 12))
    doy = add(div(add(mul(call("modulus", [add(mc, _i64(9)), _i64(12)]), 153), _i64(2)), 5), dc)
    days = add(sub(add(mul(yy, 365), div(yy, 4)), div(yy, 100)), div(yy, 400), doy,
               _i64(-719469))  # fmt: skip
    date = days_json(literal(dt_.date(1970, 1, 1), dt.date), days)
    fail = call("sverify_raise", [m, literal("make_date of a date outside the calendar "
                                              "or the years 1 to 9999", dt.string)])  # fmt: skip

    # The month's length: 30 or 31 alternating, with the turn at August
    # (`(m + m / 8) % 2`), and February's 28 or 29.
    def divides(k: int) -> Json:
        return call("equal", [call("modulus", [yc, _i64(k)]), _i64(0)])

    leap = call("or", [call("and", [divides(4), call("not", [divides(100)])]), divides(400)])
    feb = add(_i64(28), if_then([(leap, _i64(1))], _i64(0)))
    long = add(_i64(30), call("modulus", [add(mc, div(mc, 8)), _i64(2)]))
    length = if_then([(call("equal", [mc, _i64(2)]), feb)], long)
    valid = chain("and", [within(y, 1, 9999), within(m, 1, 12), call("gte", [d, _i64(1)]),
                          call("lte", [d, length])])  # fmt: skip
    null = literal(None, dt.date)
    return if_then([(call("is_null", [a]), null) for a in (y, m, d)] + [(valid, date)], fail)


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
    cols = [column_of(e) for e in exprs]
    if any(c is None for c in cols):
        return project_rel(input, width, exprs)
    fields = [c for c in cols if c is not None]
    return input if fields == list(range(width)) else emit_rel(input, fields)


def chain(name: str, args: list[Json]) -> Json:
    """`args` combined left to right with the binary function `name`."""
    out = args[0]
    for a in args[1:]:
        out = call(name, [out, a])
    return out


def distinct_rel(input: Json, width: int) -> Json:
    groups = [field_ref(i) for i in range(width)]
    return {
        "aggregate": {
            "input": input,
            "groupingExpressions": groups,
            "groupings": [{"expressionReferences": list(range(width))}],
        }
    }


def read_rel(name: str, schema: Any) -> Json:
    """A read of the named table `name`, of the Ibis schema `schema`."""
    struct = {
        "types": [type_json(t, t.nullable) for t in schema.types],
        "nullability": "NULLABILITY_REQUIRED",
    }
    return {
        "read": {
            "baseSchema": {"names": struct_names(schema), "struct": struct},
            "namedTable": {"names": [name]},
        }
    }


def values_rel(schema: Any, rows: list[list[Json]]) -> Json:
    base = {
        "names": struct_names(schema),
        "struct": {
            "types": [type_json(t) for t in schema.types],
            "nullability": "NULLABILITY_REQUIRED",
        },
    }
    table = {"expressions": [{"fields": r} for r in rows]}
    return {"read": {"baseSchema": base, "virtualTable": table}}


@contextlib.contextmanager
def compiling(semantics: str = "reference") -> Iterator[Compiler]:
    """A fresh `Compiler` for the plan built inside the block, read under
    `semantics`."""
    compiler = Compiler()
    token = _COMPILER.set(compiler)
    sem = _SEMANTICS.set(semantics)
    try:
        yield compiler
    finally:
        _SEMANTICS.reset(sem)
        _COMPILER.reset(token)


def plan(compiler: Compiler, root: Json, names: list[str]) -> Json:
    """The plan of the relation `root`, with one name per output column
    (sverify reads them as the columns; Substrait would add struct fields'
    names, depth first)."""
    urns = compiler.urns()
    return {
        **({"extensionUrns": urns} if urns else {}),
        "extensions": compiler.extensions(),
        "relations": [{"root": {"input": root, "names": names}}],
    }
