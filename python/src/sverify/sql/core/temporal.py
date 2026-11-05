"""Timestamps, dates, times of day and intervals (`SubstraitLean/Time.lean`).

The date and time functions of `mkCall`, their SQL and their kinds. A new one
goes here, its `Dialect` hook in the timestamps section of `_base.Dialect`.
"""

from __future__ import annotations

import calendar
from collections.abc import Callable
from datetime import date, timedelta

from sverify.sql.core._base import (
    CHRONO_DAY_MAX,
    CHRONO_DAY_MIN,
    DAY_MAX,
    DAY_MIN,
    NS_DAY_MAX,
    NS_DAY_MIN,
    NS_MAX,
    NS_MIN,
    OUTSIDE_DATES,
    PART_MAX,
    PART_MIN,
    Bin,
    Expr,
    FixedKind,
    Kind,
    Lit,
    Un,
    Unsupported,
    _Writer,
    expr_kind,
    parse_format,
    register,
)

#: `Time.DatePart.name` and `Time.TimeUnit.name`.
DATE_PARTS = (
    "year", "quarter", "month", "week", "day", "hour", "minute", "second", "millisecond",
    "microsecond", "dow", "doy",
)  # fmt: skip
TIME_UNITS = (
    "microsecond", "millisecond", "second", "minute", "hour", "day", "week", "month", "quarter",
    "year",
)  # fmt: skip


def _const_days(e: Expr) -> int | None:
    """The days of a constant DATE."""
    return e.value if isinstance(e, Lit) and e.kind == "date" and isinstance(e.value, int) else None


def _in_dates(*days: int) -> bool:
    return all(DAY_MIN <= x <= DAY_MAX for x in days)


def _add_months(m: int, days: int) -> int:
    """`Time.addMonths`: the same day `m` months later, or that month's last
    day; for dates within the reference's (`_in_dates`)."""
    if not _in_dates(days):
        return DAY_MAX + 1
    start = date(1970, 1, 1)
    day = start + timedelta(days=days)
    y, mo = divmod(day.month - 1 + m, 12)
    year, month = day.year + y, mo + 1
    if not 1 <= year <= 9999:
        return DAY_MAX + 1
    last = calendar.monthrange(year, month)[1]
    return (date(year, month, min(day.day, last)) - start).days


def call(name: str, args: list[Expr]) -> Expr | None:
    """`mkCall`'s temporal functions."""
    match name, args:
        # Timestamps (`SubstraitLean/Time.lean`).
        case (("date_part" | "datepart"), [Lit(value=str(part)), a]):
            if part.lower() not in DATE_PARTS:
                raise Unsupported(f"unsupported date part '{part}'")
            return Un("date_part", a, param=part.lower())
        case (("date_trunc" | "datetrunc"), [Lit(value=str(unit)), a]):
            if unit.lower() not in TIME_UNITS:
                raise Unsupported(f"unsupported date_trunc unit '{unit}'")
            return Un("date_trunc", a, param=unit.lower())
        case (("strftime" | "to_char" | "date_format"), [a, Lit(value=str(fmt))]):
            if parse_format(fmt) is None:
                raise Unsupported(f"strftime format '{fmt}' is not supported")
            return Un("strftime", a, param=fmt)
        # sverify's own: the days from `e` to `d`.
        case "date_diff", [d, e]:
            return Bin("date_diff", d, e)
    return None


def expr(
    self: _Writer, e: Expr, ref: Callable[[int], str], cols: list[Kind | None], ctx: Kind | None
) -> str | None:
    """`_Writer.expr` of the temporal operations."""
    d = self.d

    def kind(x: Expr) -> Kind | None:
        return expr_kind(x, cols)

    match e:
        case Un(op="date_part", arg=a, param=part) if kind(a) == "tod":
            return d.time_part(part, self.operand(a, "tod", ref, cols, "date_part"))
        case Un(op="date_part", arg=a, param=part):
            return d.date_part(part, self.operand(a, "time", ref, cols, "date_part"))
        case Un(op="time_of_day", arg=a):
            x = self.operand(a, "time", ref, cols, "CAST to TIME")
            return self.chrono_only(x, d.time_of_day(x), "CAST to TIME", "tod")
        case Un(op="bucket", arg=a, digits=k, origin=origin):
            # `Time.bucket`, in integer microseconds; DataFusion's nanoseconds
            # wrap outside ±2⁶³, where it is an error here.
            x = self.operand(a, "time", ref, cols, "date_bin")
            us = d.time_micros(x)
            rel = f"({us} - {d.int_lit(origin)})"
            k_ = d.int_lit(k)
            floor = f"(({d.trunc_mod(rel, k_)} + {k_}) % {k_})"
            r = d.as_time(f"({us} - {floor})")
            if not d.guards:
                return r
            lo, hi = d.int_lit(NS_MIN), d.int_lit(NS_MAX)
            fail = d.raise_("date_bin outside ±2^63 ns", x, "time")
            ru = d.time_micros(r)
            bad = f"({us} NOT BETWEEN {lo} AND {hi} OR {ru} NOT BETWEEN {lo} AND {hi})"
            return d.case_when(bad, fail, r)
        case Un(op="time_add", arg=a, digits=us):
            return d.time_add(self.operand(a, "tod", ref, cols, "time + interval"), us)
        case Un(op="time_trunc", arg=a, param=unit):
            return d.time_trunc(unit, self.operand(a, "tod", ref, cols, "date_trunc"))
        case Un(op="as_time", arg=a):
            return d.as_time(self.int_operand(a, ref, cols, "CAST to TIMESTAMP"))
        case Un(op="date_time", arg=a):
            # The reference's dates (`UnFn.dateTime`); DuckDB's are wider.
            x = self.operand(a, "date", ref, cols, "CAST to TIMESTAMP")
            if not d.guards:
                return d.date_time(x)
            lo, hi = d.int_lit(DAY_MIN), d.int_lit(DAY_MAX)
            bad = f"({d.date_days(x)} NOT BETWEEN {lo} AND {hi})"
            fail = d.raise_(f"a DATE as a TIMESTAMP {OUTSIDE_DATES}", x, "time")
            return d.case_when(bad, fail, d.date_time(f"(CASE WHEN NOT {bad} THEN {x} END)"))
        case Un(op="epoch_us", arg=a):
            return d.epoch_us(self.operand(a, "time", ref, cols, "epoch_us"))
        case Un(op="strftime", arg=a, param=fmt):
            x = self.operand(a, "time", ref, cols, "strftime")
            return self.chrono_only(x, self.strftime(x, fmt), "strftime", "str")
        case Un(op="date_trunc", arg=a, param=unit):
            return self.date_trunc(unit, self.operand(a, "time", ref, cols, "date_trunc"))
        case Un(op="to_date", arg=a):
            return d.to_date(self.operand(a, "time", ref, cols, "CAST to DATE"))
        case Un(op="day_part", arg=a, param=part):
            x = self.operand(a, "date", ref, cols, "date_part")
            lo, hi = d.int_lit(CHRONO_DAY_MIN), d.int_lit(CHRONO_DAY_MAX)
            inside = f"{d.date_days(x)} BETWEEN {lo} AND {hi}"
            return f"(CASE WHEN {inside} THEN {d.day_part(part, x)} END)"
        case Un(op="day_trunc", arg=a, param=unit):
            x = self.operand(a, "date", ref, cols, "date_trunc")
            return self.date_range(
                x,
                lambda y: d.to_date(d.date_trunc(unit, d.date_to_time(y))),
                NS_DAY_MIN,
                NS_DAY_MAX,
                f"date_trunc to a {unit}",
            )
        case Un(op="add_months", arg=a, digits=months, param=k):
            kind: Kind = "time" if k == "time" else "date"
            x = self.operand(a, kind, ref, cols, "adding months")
            if kind == "date":
                if (c := _const_days(a)) is not None and _in_dates(c, _add_months(months, c)):
                    # Decided when the plan is written (TPC-H Q6).
                    return d.add_months(x, months, kind)
                return self.date_range(
                    x, lambda y: d.add_months(y, months, kind), DAY_MIN, DAY_MAX,
                    "adding months",
                )  # fmt: skip
            if not d.guards:
                return d.add_months(x, months, kind)
            lo, hi = d.int_lit(PART_MIN), d.int_lit(PART_MAX)
            us = d.time_micros(x)
            fail = d.raise_("adding months outside the years chrono represents", x, "time")
            safe = d.add_months(
                f"(CASE WHEN {us} BETWEEN {lo} AND {hi} THEN {x} END)", months, kind
            )
            return d.case_when(
                f"({us} NOT BETWEEN {lo} AND {hi} "
                f"OR {d.time_micros(safe)} NOT BETWEEN {lo} AND {hi})",
                fail,
                safe,
            )
        case Bin(op="date_add", left=a, right=b):
            x = self.operand(a, "date", ref, cols, "date + days")
            n = self.int_operand(b, ref, cols, "date + days")
            c, k = _const_days(a), b.value if isinstance(b, Lit) else None
            if c is not None and isinstance(k, int) and _in_dates(c, c + k):
                return d.date_add_days(x, n)
            return self.date_range(
                x, lambda y: d.date_add_days(y, n), DAY_MIN, DAY_MAX, "date + days"
            )
        case Bin(op="date_diff", left=a, right=b):
            x = self.operand(a, "date", ref, cols, "date_diff")
            y = self.operand(b, "date", ref, cols, "date_diff")
            return d.date_diff_days(x, y)
    return None


#: The result kinds of this area's `Un` and `Bin` operations (`Expr.kind`).
UN_KINDS: dict[str, FixedKind] = {
    "date_part": "int", "day_part": "int", "date_trunc": "time", "to_date": "date",
    "day_trunc": "date", "time_of_day": "tod", "as_time": "time", "bucket": "time",
    "strftime": "str", "time_add": "tod", "time_trunc": "tod", "date_time": "time",
    "epoch_us": "int",
}  # fmt: skip
BIN_KINDS: dict[str, FixedKind] = {"date_diff": "int", "date_add": "date"}

register(call, expr, un_kinds=UN_KINDS, bin_kinds=BIN_KINDS)
