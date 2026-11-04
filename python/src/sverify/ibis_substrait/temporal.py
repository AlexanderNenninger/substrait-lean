"""Temporal rules of the Ibis producer: dates, timestamps, times and intervals.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

import datetime as dt_
from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, register, register_refusals
from sverify.plan_json import (
    EPOCH,
    Json,
    Unsupported,
    call,
    cast_json,
    if_then,
    interval_json,
    interval_parts,
    literal,
)


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


def _time_add(name: str) -> Callable[[Exprs, Any], Json]:
    """`TimeAdd`, `TimeSub`: a time of day plus a constant interval, which
    wraps around midnight (`duckdb-time-plus-interval`)."""

    def rule(x: Exprs, op: Any) -> Json:
        c = _const_interval(op.right)
        if c is None:
            raise Unsupported("a time of day plus an interval needs a constant interval")
        if c[0]:
            raise Unsupported("a time of day plus months or years is not supported")
        return call(name, [x(op.left), interval_json(0, c[1])])

    return rule


def _time_truncate(x: Exprs, op: Any) -> Json:
    unit = op.unit.name.lower()
    if unit not in ("hour", "minute", "second", "millisecond", "microsecond"):
        raise Unsupported(f"truncating a time of day to a {unit} is not supported")
    return call("date_trunc", [literal(unit, dt.string), x(op.arg)])


def _between_time(x: Exprs, op: Any) -> Json:
    t = cast_json(x(op.arg), dt.time)
    lo, hi = x(op.lower_bound, dt.time), x(op.upper_bound, dt.time)
    return call("and", [call("gte", [t, lo]), call("lte", [t, hi])])


register(
    {
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
        ops.TimeAdd: _time_add("add"),
        ops.TimeSub: _time_add("subtract"),
        ops.TimeTruncate: _time_truncate,
        ops.TimestampBucket: _bucket,
        ops.ExtractWeekOfYear: _date_part("week"),
    }
)


register_refusals(
    {
        "TimestampNow": "the time differs between runs; pass the time in as a column or constant",
        "DateNow": "the date differs between runs; pass the date in as a column or constant",
    }
)
