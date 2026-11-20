"""Substrait plans as protobuf JSON: the types, literals, calls and
relations that sverify's producers write (the Ibis producer,
`sverify.ibis_substrait`, and the SQL lift, `sverify.sql_lift`), with the
functions and encodings `frontend/Sverify/Frontend/Parse.lean` reads.

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.

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
import struct
from collections.abc import Iterable, Iterator
from decimal import Decimal
from typing import Any

import ibis.expr.datatypes as dt

from sverify import black_box
from sverify._decimals import scaled
from sverify._unsupported import Unsupported as _Unsupported

Json = dict[str, Any]

EPOCH = dt_.datetime(1970, 1, 1)
NULLABLE = {"nullability": "NULLABILITY_NULLABLE"}
REQUIRED = {"nullability": "NULLABILITY_REQUIRED"}


_ISSUES = "https://github.com/AlexanderNenninger/substrait-lean/issues"


class Unsupported(_Unsupported):
    """The expression uses something the Lean model does not cover
    (`sverify.errors.UnsupportedError`)."""


class SqlUnsupported(Unsupported):
    """The SQL lift does not read a construct (yet). The message ends with what
    the user can do: the `hint` (a rewrite the lift supports) where the site
    has one; otherwise write the step in Ibis, which `sv.sql` replaces
    one-to-one in a transform, and the `issue` that tracks the construct
    where an open one does."""

    def __init__(
        self,
        message: str,
        hint: str | None = None,
        issue: int | None = None,
        *,
        construct: str | None = None,
        sql: str | None = None,
    ):
        if hint:
            message = f"{message}; {hint}"
        elif "#" not in message and "Ibis" not in message:
            where = f" ({_ISSUES}/{issue})" if issue else ""
            tracked = f"tracked in #{issue}{where}; until then, " if issue else ""
            message = f"{message}; {tracked}write this step in Ibis"
        super().__init__(message, construct=construct, sql=sql)


class ProducerUnsupported(Unsupported):
    """The Ibis producer (or the plan writer) does not read a construct (yet).
    The message ends with the `hint` where the site has one, otherwise with
    what the user can do: rewrite the expression with a supported operation
    or a supported column type."""

    def __init__(self, message: str, hint: str | None = None, *, construct: str | None = None):
        if hint:
            message = f"{message}; {hint}"
        elif "#" not in message:
            message = f"{message}; rewrite it with a supported operation or column type"
        super().__init__(message, construct=construct)


# --------------------------------------------------------------------------
# Types and literals


#: What a refusal of a timestamp with a time zone (an instant) says it can do instead
#: (D53, #1725).
INSTANT_NOTE = (
    "(#1725): a timestamp with a time zone can be read, compared with other such columns, "
    "used as a key and written back, and converted to a timestamp at UTC (a cast to a "
    "timestamp, `x AT TIME ZONE 'UTC'` in SQL), which the calendar functions read (D69)"
)

#: The spellings of the time zone UTC the readers produce (Arrow, Delta, Ibis).
UTC_ZONES = frozenset({"UTC", "Etc/UTC", "+00:00", "Z", "utc"})


def is_utc(zone: str | None) -> bool:
    """Is `zone` UTC, in a spelling a reader produces?"""
    return zone in UTC_ZONES


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
        raise Unsupported(
            f"unsigned integers ({dtype}) are not supported yet (#350); cast the column to "
            "a signed integer before sverify reads the table"
        )
    if dtype.is_integer():
        return {f"i{dtype.nbytes * 8}": NULLABLE}
    if dtype.is_float64():
        return {"fp64": NULLABLE}
    # Read and compared as their values, which doubles hold exactly; arithmetic
    # on them rounds to 32 bits, which the checker refuses (#417).
    if dtype.is_float32():
        return {"fp32": NULLABLE}
    if dtype.is_decimal():
        if dtype.precision is None or dtype.scale is None:
            raise Unsupported(
                "decimals of unknown precision are not supported; cast to DECIMAL(p, s)"
            )
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
        if dtype.timezone is not None and not is_utc(dtype.timezone):
            raise Unsupported(
                f"timestamps with the time zone {dtype.timezone} are not supported yet "
                f"{INSTANT_NOTE}; only UTC is read, as an instant"
            )
        # Seconds and milliseconds are encodings of the source: the read widens
        # them to microseconds, exactly (D61).
        if dtype.scale not in (None, 0, 3, 6):
            raise Unsupported(
                "only second, millisecond and microsecond timestamps are supported (#323); "
                "cast the column to microseconds before sverify reads the table"
            )
        if dtype.timezone is not None:
            return {"precisionTimestampTz": {"precision": 6, **NULLABLE}}
        return {"precisionTimestamp": {"precision": 6, **NULLABLE}}
    if dtype.is_time():
        return {"precisionTime": {"precision": 6, **NULLABLE}}
    if dtype.is_null():
        return {"i64": NULLABLE}
    if dtype.is_array():
        return {"list": {"type": type_json(dtype.value_type), **NULLABLE}}
    if dtype.is_struct():
        return {"struct": {"types": [type_json(t) for t in dtype.types], **NULLABLE}}
    if dtype.is_binary():
        raise Unsupported(
            "sverify reads no binary values (#1918): encode them as text at the source "
            "(hex or base64), or leave the column out"
        )
    if dtype.is_uuid():
        raise Unsupported(
            "type uuid is not supported; read it as text with CAST(column AS VARCHAR) in the "
            "source query, and compare it with the lower-case hyphenated form"
        )
    raise Unsupported(
        f"type {dtype} is not supported; cast the column to a supported type in the source query"
    )


def struct_names(schema: Any) -> list[str]:
    """A `NamedStruct`'s names: each column's, followed by its struct
    fields' names, depth first (Substrait's `NamedStruct`)."""

    def names(name: str, dtype: Any) -> list[str]:
        if dtype.is_struct():
            return [name, *(n for f, t in dtype.items() for n in names(f, t))]
        return [name]

    return [n for name, t in schema.items() for n in names(name, t)]


def _instant(value: dt_.datetime) -> str:
    """The microseconds since 1970-01-01 00:00 UTC of an instant literal (D53): a
    datetime with an offset or a zone is the instant it names, a naive one is read
    as UTC. (A named zone in the *text* of a SQL literal is refused by the lift.)"""
    at = value.astimezone(dt_.UTC) if value.tzinfo is not None else value.replace(tzinfo=dt_.UTC)
    return str((at - EPOCH.replace(tzinfo=dt_.UTC)) // dt_.timedelta(microseconds=1))


def literal(value: Any, dtype: Any) -> Json:
    if value is None or dtype.is_null():
        return {"literal": {"null": type_json(dtype)}}
    if dtype.is_boolean():
        return {"literal": {"boolean": bool(value)}}
    if dtype.is_integer():
        key = type_json(dtype)
        name = next(iter(key))
        return {"literal": {name: str(value) if name == "i64" else int(value)}}
    if dtype.is_float64() or dtype.is_float32():
        x = float(value)  # raw (D31): -0.0 as the text "-0.0", a NaN as one below
        if dtype.is_float32():
            # The single's own value, whose round-trip digits the frontend reads
            # without rounding again (ruling 186 P4).
            try:
                x = struct.unpack("<f", struct.pack("<f", x))[0]
            except OverflowError as e:
                raise ProducerUnsupported(f"{value} does not fit {dtype}") from e
        text: Any = "NaN" if math.isnan(x) else "-0.0" if str(x) == "-0.0" else x
        if math.isinf(x):
            text = "Infinity" if x > 0 else "-Infinity"
        return {"literal": {"fp64" if dtype.is_float64() else "fp32": text}}
    if dtype.is_decimal():
        return decimal_literal(value, dtype)
    if dtype.is_string():
        return {"literal": {"string": str(value)}}
    if dtype.is_timestamp():
        type_json(dtype)
        if value.tzinfo is not None or dtype.timezone is not None:
            return {"literal": {"precisionTimestampTz": {"precision": 6, "value": _instant(value)}}}
        micros = (value - EPOCH) // dt_.timedelta(microseconds=1)
        return {"literal": {"precisionTimestamp": {"precision": 6, "value": str(micros)}}}
    if dtype.is_date():
        return {"literal": {"date": (value - EPOCH.date()).days}}
    if dtype.is_time():
        if value.tzinfo is not None:
            raise ProducerUnsupported("times with a time zone are not supported")
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
    if dtype.is_binary():
        type_json(dtype)  # refuses, saying why (#1918)
    raise ProducerUnsupported(f"literal of type {dtype} is not supported")


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
        raise ProducerUnsupported(f"decimal {d} is not supported")
    s = max(0, -int(d.as_tuple().exponent))
    digits = len(str(abs(int(scaled(d, s)))))
    return dt.Decimal(precision=max(digits, s, 1), scale=s, nullable=True)


def decimal_literal(value: Any, dtype: Any) -> Json:
    """A `DECIMAL(p, s)` literal: its unscaled value as 16 little-endian bytes
    of two's complement. A decimal of unknown precision (Ibis's constants) gets
    the narrowest type that holds it."""
    if dtype.precision is None or dtype.scale is None:
        dtype = decimal_type_of(value)
    unscaled = scaled(value, dtype.scale)
    if unscaled != unscaled.to_integral_value():
        raise ProducerUnsupported(f"{value} has more than {dtype.scale} decimal places")
    if len(str(abs(int(unscaled)))) > dtype.precision:
        raise ProducerUnsupported(f"{value} does not fit {dtype}")
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
        raise ProducerUnsupported(f"intervals in {dtype.unit.plural} are not supported")
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
    `//` and `%` (`Profile.polars`, `engines/polars/Sverify/Polars/Profile.lean`)."""
    j = call(name, args)
    j["scalarFunction"]["options"] = [{"name": "division_type", "preference": ["FLOOR"]}]
    return j


def substring_left(args: list[Json]) -> Json:
    """`substring` whose start may be below 1, which then lies left of the
    first character (`negative_start` = `LEFT_OF_BEGINNING`): the rules below
    compute such starts. A plan that omits the option counts a negative start
    from the end instead (`Text.substrWrap`)."""
    j = call("substring", args)
    j["scalarFunction"]["options"] = [
        {"name": "negative_start", "preference": ["LEFT_OF_BEGINNING"]}
    ]
    return j


def ieee_divide(a: Json, b: Json) -> Json:
    """`a / b` with `on_division_by_zero` = IEEE: `±inf` or NaN by zero rather
    than an error."""
    c = call("divide", [a, b])
    c["scalarFunction"]["options"] = [{"name": "on_division_by_zero", "preference": ["IEEE"]}]
    return c


def field_ref(i: int) -> Json:
    return {"selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}}


def column_of(e: Json) -> int | None:
    """The input column `e` reads, if it is a plain column reference (not a
    reference into a value)."""
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


def between(x: Json, lo: Json, hi: Json, typed: bool = False) -> Json:
    """`x BETWEEN lo AND hi`: `x >= lo AND x <= hi`, NULLs as SQL has them.
    `typed` writes each call's boolean output type (as the SQL lift does)."""

    def fn(name: str, args: list[Json]) -> Json:
        c = call(name, args)
        if typed:
            c["scalarFunction"]["outputType"] = type_json(dt.boolean)
        return c

    return fn("and", [fn("gte", [x, lo]), fn("lte", [x, hi])])


def in_values(
    value: Json, options: list[Json], ints: list[Any] | None, typed: bool = False
) -> Json:
    """`value IN (options…)`. With `ints`, the options' integer values (None
    where one is not a constant), a list that fills a range of integers is
    `value BETWEEN lo AND hi`, NULLs included, and the checker reads a range
    as one; otherwise a `singularOrList`."""
    if ints is not None and (span := int_range(ints)) is not None:
        lo, hi = (options[ints.index(v)] for v in span)
        return between(value, lo, hi, typed)
    return {"singularOrList": {"value": value, "options": options}}


def if_then(ifs: list[tuple[Json, Json]], default: Json) -> Json:
    return {"ifThen": {"ifs": [{"if": c, "then": t} for c, t in ifs], "else": default}}


def cast_json(e: Json, to: Any, or_null: bool = False) -> Json:
    """`CAST(e AS to)`, or `TRY_CAST` (`or_null`: NULL where it fails)."""
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


def month_length(y: Json, m: Json) -> Json:
    """The days of month `m` (1 to 12) of year `y`: 30 or 31 alternating, with
    the turn at August (`(m + m / 8) % 2`), and February's 28 or 29."""

    def divides(k: int) -> Json:
        return call("equal", [call("modulus", [y, _i64(k)]), _i64(0)])

    leap = call("or", [call("and", [divides(4), call("not", [divides(100)])]), divides(400)])
    feb = chain("add", [_i64(28), if_then([(leap, _i64(1))], _i64(0))])
    long = chain("add", [_i64(30), call("modulus", [chain("add", [m, call("divide", [m, _i64(8)])]),
                                                    _i64(2)])])  # fmt: skip
    return if_then([(call("equal", [m, _i64(2)]), feb)], long)


def add_months_json(x: Json, n: Json, timestamp: bool) -> Json:
    """`x + n months` of a date or `timestamp` (#1925), `n` an integer: the
    month `n` after, and the day cut to its length (`2024-01-31 + 1 month` is
    `2024-02-29`); a timestamp keeps its time of day. A year outside 1 to 9999
    raises, as `make_date_json` does."""
    day = cast_json(x, dt.date) if timestamp else x

    def part(name: str) -> Json:
        return call("date_part", [literal(name, dt.string), day])

    months = chain("add", [call("multiply", [part("year"), _i64(12)]),
                           call("subtract", [part("month"), _i64(1)]), n])  # fmt: skip
    # The floor of `months / 12`, and `months % 12`, for a negative count too.
    rest = call("modulus", [call("add", [call("modulus", [months, _i64(12)]), _i64(12)]), _i64(12)])
    year = call("divide", [call("subtract", [months, rest]), _i64(12)])
    month = call("add", [rest, _i64(1)])
    moved = make_date_json(year, month, call("least", [part("day"), month_length(year, month)]))
    if not timestamp:
        return moved
    return days_json(x, call("date_diff", [moved, day]))


def make_date_json(y: Json, m: Json, d: Json) -> Json:
    """`make_date(y, m, d)` of integers: the date by H. Hinnant's
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

    length = month_length(yc, mc)
    valid = chain("and", [within(y, 1, 9999), within(m, 1, 12), call("gte", [d, _i64(1)]),
                          call("lte", [d, length])])  # fmt: skip
    null = literal(None, dt.date)
    return if_then([(call("is_null", [a]), null) for a in (y, m, d)] + [(valid, date)], fail)


def make_timestamp_json(y: Json, m: Json, d: Json, h: Json, mi: Json, sec: Json) -> Json:
    """`make_timestamp(y, m, d, h, mi, s)` of integers (#1928): the date at
    midnight plus `h` hours, `mi` minutes and `s` seconds, NULL if an argument
    is. DuckDB accepts `h` from 0 to 24, `mi` from 0 to 59 and `s` from 0 to
    60, in all at most a day, and raises otherwise (`duckdb-make-timestamp-ranges`); the
    date is `make_date_json`'s."""

    def within(a: Json, lo: int, hi: int) -> Json:
        return call("and", [call("gte", [a, _i64(lo)]), call("lte", [a, _i64(hi)])])

    secs = chain("add", [call("multiply", [h, _i64(3600)]), call("multiply", [mi, _i64(60)]), sec])
    valid = chain("and", [within(h, 0, 24), within(mi, 0, 59), within(sec, 0, 60),
                          call("lte", [secs, _i64(86_400)])])  # fmt: skip
    ts = call("add", [cast_json(make_date_json(y, m, d), dt.timestamp),
                      call("multiply", [secs, interval_json(0, 1_000_000)])])  # fmt: skip
    fail = call("sverify_raise", [h, literal("make_timestamp of a time out of range", dt.string)])
    null = literal(None, dt.timestamp)
    nulls = [(call("is_null", [a]), null) for a in (h, mi, sec)]
    return if_then([*nulls, (valid, ts)], fail)


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


#: The functions of a `plain` expression (`Expr.plain`, `Guard.lean`): they
#: raise on no row, so they guard the operands after them.
_PLAIN_FUNCTIONS = frozenset(
    {
        "equal", "not_equal", "lt", "lte", "gt", "gte", "is_null", "is_not_null", "not", "and",
        "or",
    }
)  # fmt: skip


def is_plain(e: Json) -> bool:
    """Is `e` built from columns and literals by `=`, `<`, `IS NULL`, `NOT`, `AND`
    and `OR` (and their spellings), a literal's cast or `IN` over such? Such an
    expression raises on no row, apart from a constant's cast, which D21 gives to
    the whole plan in the eager and in the lifted reading alike. A chain called plain
    is written eager (D19); this table decides only which chains pay for the lift
    (`Expr.plain` in `Guard.lean` is the narrower, proved one)."""
    if "literal" in e or "selection" in e:
        return True
    if (c := e.get("cast")) is not None:  # a constant's cast raises on every row or on none
        return "literal" in c["input"]
    if (ol := e.get("singularOrList")) is not None:  # `x IN (…)` parses to `=` and `OR`
        return is_plain(ol["value"]) and all(is_plain(o) for o in ol.get("options", []))
    fn = e.get("scalarFunction")
    if fn is None:
        return False
    names = {a: n for n, a in _COMPILER.get().functions.items()}
    if names.get(fn["functionReference"]) not in _PLAIN_FUNCTIONS:
        return False
    return all(is_plain(a["value"]) for a in fn["arguments"])


#: How many levels of nested `AND` and `OR` the lift guards (D50, interim): a connective
#: below this many enclosing lifted ones is written eager. Step D50-d removes the cap.
LIFT_LEVELS = 3


def logical(name: str, operands: list[Json], eager: bool = False) -> Json:
    """`AND` or `OR` (`name`) of `operands`, in order (D50). Where every operand
    is plain, or the plan is read as DuckDB reads it (`eager`), the eager connective
    (`chain`); otherwise `sverify_and` or `sverify_or`, which the checker reads as
    a guard: each operand runs only where the earlier ones do not decide the
    result (`Expr.andG`, `Guard.lean`). Only the top `LIFT_LEVELS` levels of a nest
    are lifted."""
    if eager or len(operands) == 1 or semantics() == "duckdb" or all(is_plain(o) for o in operands):
        return chain(name, operands)
    names = {a: n for n, a in _COMPILER.get().functions.items()}
    spliced: list[Json] = []
    for o in operands:
        fn = o.get("scalarFunction")
        if fn is not None and names.get(fn["functionReference"]) == f"sverify_{name}":
            spliced += [a["value"] for a in fn["arguments"]]  # a guard chain inside is one chain
        else:
            spliced.append(o)
    return _cap_lift(call(f"sverify_{name}", spliced), names, 0)


def _cap_lift(e: Any, names: dict[int, str], level: int) -> Any:
    """`e` with every `sverify_and` and `sverify_or` at `LIFT_LEVELS` or more lifted
    ones above it written as the eager `and` and `or`."""
    if isinstance(e, list):
        return [_cap_lift(x, names, level) for x in e]
    if not isinstance(e, dict):
        return e
    fn = e.get("scalarFunction")
    n = names.get(fn["functionReference"]) if fn is not None else None
    if fn is not None and n in ("sverify_and", "sverify_or"):
        below = level + 1
        args = [_cap_lift(a["value"], names, below) for a in fn["arguments"]]
        return chain(n.removeprefix("sverify_"), args) if level >= LIFT_LEVELS else call(n, args)
    return {k: _cap_lift(v, names, level) for k, v in e.items()}


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
    types = []
    for column, t in schema.items():
        try:
            types.append(type_json(t, t.nullable))
        except Unsupported as e:
            raise Unsupported(
                f"column {column!r} of {name!r}: {e}; "
                "only a column the query never reads is left out"
            ) from e
    struct = {"types": types, "nullability": "NULLABILITY_REQUIRED"}
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
