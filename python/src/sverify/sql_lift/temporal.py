"""The lift's rules of dates, timestamps, intervals and date parts."""

from __future__ import annotations

import datetime as dt_
import re
from collections.abc import Callable
from typing import Any

import ibis.expr.datatypes as dt
import sqlglot.expressions as sge
from ibis.common.temporal import IntervalUnit

from sverify.plan_json import Unsupported, interval_json, literal
from sverify.sql_lift._base import Column, E, Sub, _fn, _Lift, _shown, register
from sverify.sql_lift.strings import _ANONYMOUS_STRINGS


def _temporal_literals(es: list[E]) -> list[E]:
    """String constants next to a date, timestamp or time of day read as one,
    as DuckDB casts them."""
    temporal = [e.type for e in es if e.type.is_date() or e.type.is_timestamp() or e.type.is_time()]
    if not temporal:
        return es
    es = [_temporal(e, temporal[0]) if e.type.is_string() and e.constant else e for e in es]
    # Next to a DATE column, a timestamp constant at midnight compares as its
    # date (exactly); Lean cannot cast the column to a timestamp (#240).
    if any(e.type.is_date() and not e.constant for e in es):
        es = [_as_date(e) if e.type.is_timestamp() and e.constant else e for e in es]
    return es


def _as_date(e: E) -> E:
    v = e.value
    if v is None:
        return E(literal(None, dt.date), dt.date, None)
    if v.time() != dt_.time():
        raise Unsupported(
            f"comparing a DATE column with the timestamp {v} is not supported yet: Lean has "
            "no cast of a DATE column to a timestamp (#240)"
        )
    return E(literal(v.date(), dt.date), dt.date, v.date())


#: A time of day as DuckDB reads one: `H:MM`, `H:MM:SS` or `H:MM:SS.ffffff`.
_TIME = re.compile(r"\s*(\d{1,2}):(\d{2})(?::(\d{2})(?:\.(\d{1,6}))?)?\s*")


def _time(e: E) -> E:
    """A string constant as a TIME literal, in microseconds since midnight
    (#386). What DuckDB raises on, and what it reads that the model has no
    value for (`24:00:00`, an offset, digits past microseconds), is refused."""
    m = _TIME.fullmatch(e.value) if isinstance(e.value, str) else None
    if m is None:
        raise Unsupported(f"cannot read {e.value!r} as a TIME; write it as HH:MM:SS[.ffffff]")
    h, mi, sec = int(m[1]), int(m[2]), int(m[3] or 0)
    if h > 23 or mi > 59 or sec > 59:
        raise Unsupported(
            f"cannot read {e.value!r} as a TIME: out of range (00:00:00 to 23:59:59.999999)"
        )
    v = dt_.time(h, mi, sec, int((m[4] or "0").ljust(6, "0")))
    return E(literal(v, dt.time), dt.time, v)


def _temporal(e: E, t: Any) -> E:
    if t.is_time():
        return _time(e)
    # DuckDB reads a date with spaces around it, and a timestamp with spaces
    # before it, or after it if it has a time of day.
    text = e.value
    if isinstance(text, str):
        if t.is_date() or re.search(r"\d[ T]\d", text.strip()):
            text = text.strip()
        elif text != text.rstrip():
            raise Unsupported(f"DuckDB cannot read {text!r} as a {t}")
        text = text.lstrip()
    try:
        if t.is_date():
            v: Any = dt_.date.fromisoformat(text)
            return E(literal(v, dt.date), dt.date, v)
        v = dt_.datetime.fromisoformat(text)
    except (TypeError, ValueError) as err:
        raise Unsupported(f"cannot read {text!r} as a {t}") from err
    if v.tzinfo is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    ts = dt.timestamp(scale=6)
    return E(literal(v, ts), ts, v)


#: The units `date_trunc` truncates a timestamp to (`SubstraitLean/Time.lean`).
_TRUNC_UNITS = ("second", "minute", "hour", "day", "week", "month", "quarter", "year")


def _date_trunc(lf: _Lift, node: sge.TimestampTrunc, sub: Sub, scope: list[Column]) -> E:
    # DuckDB returns a timestamp, of a date too (the timestamp at its
    # midnight); weeks start on Monday.
    unit = node.args.get("unit")
    name = unit.name.lower() if isinstance(unit, sge.Var | sge.Literal) else None
    if name not in _TRUNC_UNITS:
        raise Unsupported(
            f"date_trunc to {_shown(unit) if unit is not None else '?'} is not supported; "
            f"the unit must be one of {', '.join(_TRUNC_UNITS)}"
        )
    a = sub(node.this)
    ts = dt.timestamp(scale=6)
    if a.type.is_date():
        # A DATE truncates to a date: to a day or less it is itself.
        if name in ("second", "minute", "hour", "day"):
            return E(a.json, dt.date, a.value, midnight=True)
        out = _fn("date_trunc", [literal(name, dt.string), a.json], dt.date)
        return E(out, dt.date, midnight=True)
    if not (a.type.is_timestamp() or a.type.is_null()):
        raise Unsupported(f"date_trunc of a {a.type} is not supported")
    if a.type.is_timestamp() and a.type.timezone is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    return E(_fn("date_trunc", [literal(name, dt.string), lf.to(a, ts).json], ts), ts)


#: An interval unit as (months, microseconds) per unit.
_INTERVAL_UNITS = {
    "microsecond": (0, 1),
    "millisecond": (0, 1_000),
    "second": (0, 1_000_000),
    "minute": (0, 60_000_000),
    "hour": (0, 3_600_000_000),
    "day": (0, 86_400_000_000),
    "week": (0, 7 * 86_400_000_000),
    "month": (1, 0),
    "quarter": (3, 0),
    "year": (12, 0),
}


def _interval(lf: _Lift, node: sge.Interval, sub: Sub, scope: list[Column]) -> E:
    """A constant interval: `INTERVAL '10' MILLISECONDS`, `INTERVAL 1 DAY`,
    `INTERVAL '1 month 2 days'`."""
    unit, value = node.args.get("unit"), node.this
    text = value.this if isinstance(value, sge.Literal) else None
    if isinstance(unit, sge.Var) and text is not None:
        text = f"{text} {unit.name}"
    # `INTERVAL '1 month 2 days'`: integers, each with a unit.
    pairs = re.findall(r"(-?\d+)\s*([a-z]+)", (text or "").lower())
    rest = re.sub(r"(-?\d+)\s*([a-z]+)", "", (text or "").lower()).strip()
    units = [u.removesuffix("s") for _, u in pairs]
    if not pairs or rest or any(u not in _INTERVAL_UNITS for u in units):
        raise Unsupported(
            f"{_shown(node)} is not supported yet; an interval is integers, each with a "
            f"unit ({', '.join(_INTERVAL_UNITS)})"
        )
    parts = (0, 0)
    for (n, _), u in zip(pairs, units, strict=True):
        months, micros = _INTERVAL_UNITS[u]
        parts = (parts[0] + int(n) * months, parts[1] + int(n) * micros)
    return E(interval_json(*parts), dt.Interval(unit=IntervalUnit.MICROSECOND), parts)


_DAY = 86_400_000_000


def _add_months(d: dt_.date, months: int) -> dt_.date:
    """`d` plus `months`, clamped to the month's last day, as DuckDB adds
    (`DATE '2024-01-31' + INTERVAL 1 MONTH` is February 29)."""
    y, m = divmod(d.year * 12 + d.month - 1 + months, 12)
    last = (dt_.date(y + (m + 1) // 12, (m + 1) % 12 + 1, 1) - dt_.timedelta(days=1)).day
    return dt_.date(y, m + 1, min(d.day, last))


def _temporal_plus(name: str, a: E, b: E) -> E:
    """A timestamp or date plus or minus a constant interval. DuckDB's
    `DATE ± INTERVAL` is a TIMESTAMP; of whole days or months it is the date
    at midnight, which the plan holds as a date (`E.midnight`)."""
    if name == "add" and a.type.is_interval():
        a, b = b, a
    if name == "multiply" or not b.type.is_interval() or not b.constant:
        raise Unsupported(f"{name} of {a.type} and {b.type} is not supported yet")
    months, micros = b.value
    if name == "subtract":
        months, micros = -months, -micros
    ts = dt.timestamp(scale=6)
    if a.type.is_date():
        if a.constant:
            if a.value is None:
                return E(literal(None, ts), ts, None)
            d = _add_months(a.value, months)
            if micros % _DAY == 0:
                d += dt_.timedelta(days=micros // _DAY)
                return E(literal(d, dt.date), dt.date, d, midnight=True)
            v = dt_.datetime.combine(d, dt_.time()) + dt_.timedelta(microseconds=micros)
            return E(literal(v, ts), ts, v)
        if micros % _DAY != 0:
            raise Unsupported(
                "a DATE column plus an interval of hours or less is a TIMESTAMP, which needs a "
                "cast Lean lacks (#240)"
            )
        return E(_fn(name, [a.json, b.json], dt.date), dt.date, midnight=True)
    if not a.type.is_timestamp() or a.type.timezone is not None:
        raise Unsupported(f"{name} of {a.type} and an interval is not supported yet")
    return E(_fn(name, [a.json, b.json], ts), ts)


#: Date parts, by the names DuckDB's SQL gives them, as `Time.DatePart`'s.
_DATE_PARTS = {
    "year": "year",
    "quarter": "quarter",
    "month": "month",
    "week": "week",
    "weekofyear": "week",
    "day": "day",
    "dayofmonth": "day",
    "dow": "dow",
    "dayofweek": "dow",
    "doy": "doy",
    "dayofyear": "doy",
    "hour": "hour",
    "minute": "minute",
    "second": "second",
    "millisecond": "millisecond",
    "milliseconds": "millisecond",
    "microsecond": "microsecond",
    "microseconds": "microsecond",
}
_TIME_PARTS = ("hour", "minute", "second", "millisecond", "microsecond")


def _date_part(lf: _Lift, part: str, a: E) -> E:
    """`date_part(part, a)`, a BIGINT: DuckDB's parts, which Lean's are
    (ISO weeks, Sunday as day 0 of the week)."""
    p = _DATE_PARTS.get(part.lower())
    if p is None:
        raise Unsupported(f"the date part {part} is not supported yet")
    if a.type.is_date() and not a.midnight and p in _TIME_PARTS:
        raise Unsupported(f"the {p} of a DATE is not supported")
    if not (a.type.is_date() or a.type.is_timestamp() or a.type.is_null()):
        raise Unsupported(f"date parts of a {a.type} are not supported")
    if a.type.is_timestamp() and a.type.timezone is not None:
        raise Unsupported("timestamps with a time zone are not supported")
    if a.type.is_date() and p in _TIME_PARTS:
        return E(literal(0, dt.int64), dt.int64, 0)  # a DATE at midnight
    return E(_fn("date_part", [literal(p, dt.string), a.json], dt.int64), dt.int64)


def _extract(lf: _Lift, node: sge.Extract, sub: Sub, scope: list[Column]) -> E:
    return _date_part(lf, node.this.name, sub(node.expression))


def _part_fn(part: str) -> Callable[..., E]:
    """`year(d)`, `month(d)`, …"""
    return lambda lf, node, sub, scope: _date_part(lf, part, sub(node.this))


def _anonymous(lf: _Lift, node: sge.Anonymous, sub: Sub, scope: list[Column]) -> E:
    """The functions SQLGlot does not know but DuckDB has (`_KNOWN`)."""
    name = node.name.lower()
    args = node.expressions
    if name in _ANONYMOUS_STRINGS and len(args) == 2:
        return _ANONYMOUS_STRINGS[name](lf, [sub(a) for a in args])
    if name in ("date_part", "datepart") and len(args) == 2:
        part = args[0]
        if not (isinstance(part, sge.Literal) and part.is_string):
            raise Unsupported(f"{name} needs a constant part")
        return _date_part(lf, part.this, sub(args[1]))
    raise Unsupported(f"unknown function {node.name}(): DuckDB SQL here has no such function")


def _date_diff(lf: _Lift, node: sge.DateDiff, sub: Sub, scope: list[Column]) -> E:
    # DuckDB's `datediff('day', a, b)` is `b - a` in days.
    unit = node.args.get("unit")
    name = unit.name.lower() if unit is not None else "day"
    if name not in ("day", "days"):
        raise Unsupported(f"datediff in {name} is not supported yet")
    later, earlier = sub(node.this), sub(node.expression)
    for e in (later, earlier):
        if not e.type.is_date() or e.midnight:
            raise Unsupported(f"datediff of a {e.type} is not supported yet")
    return E(_fn("date_diff", [later.json, earlier.json], dt.int64), dt.int64)


register(
    {
        sge.TimestampTrunc: _date_trunc,
        sge.Interval: _interval,
        sge.Extract: _extract,
        sge.Anonymous: _anonymous,
        sge.DateDiff: _date_diff,
        **{
            cls: _part_fn(part)
            for cls, part in (
                (getattr(sge, n, None), part)
                for n, part in (
                    ("Year", "year"),
                    ("Quarter", "quarter"),
                    ("Month", "month"),
                    ("Week", "week"),
                    ("WeekOfYear", "week"),
                    ("Day", "day"),
                    ("DayOfMonth", "day"),
                    ("DayOfWeek", "dow"),
                    ("DayOfYear", "doy"),
                    ("Hour", "hour"),
                    ("Minute", "minute"),
                    ("Second", "second"),
                )
            )
            if cls is not None
        },
    }
)
