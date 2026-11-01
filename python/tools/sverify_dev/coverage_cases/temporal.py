"""Coverage cases: dates and times."""

from __future__ import annotations

import datetime as dt

import ibis
from ibis import _

from sverify_dev.coverage_cases._common import (
    DAY0,
    NO_ROW_ORDER,
    Case,
    R,
    V,
    X,
    case,
    t,
)

CASES: list[Case] = [
    case("time", "timestamp + interval", V, lambda: t.select(x=t.ts + ibis.interval(hours=1))),
    case(
        "time",
        "compare with literal",
        V,
        lambda: t.filter(t.ts > ibis.timestamp("2024-01-01 00:00:00")),
    ),
    case("time", "year", V, lambda: t.select(x=t.ts.year())),
    case("time", "date", V, lambda: t.select(x=t.ts.date())),
    case("time", "truncate", V, lambda: t.select(x=t.ts.truncate("h"))),
    case("time", "date + days", V, lambda: t.select(x=t.ts.date() + ibis.interval(days=3))),
    case("time", "date - months", V, lambda: t.select(x=t.ts.date() - ibis.interval(months=1))),
    case("time", "date + years", V, lambda: t.select(x=t.ts.date() + ibis.interval(years=1))),
    case(
        "time",
        "date - column days",
        V,
        lambda: t.select(x=t.ts.date() - t.qty.as_interval("D")),
    ),
    case("time", "timestamp + months", V, lambda: t.select(x=t.ts + ibis.interval(months=13))),
    case(
        "time",
        "constant interval arithmetic",
        V,
        lambda: t.select(x=t.ts + (ibis.interval(days=1) + ibis.interval(hours=2))),
    ),
    case(
        "time",
        "date - date",
        V,
        lambda: t.filter(t.ts.date() - DAY0 > ibis.interval(days=3)),
    ),
    case("time", "date delta", V, lambda: t.select(x=t.ts.date().delta(DAY0, unit="day"))),
    case("time", "date parts", V, lambda: t.select(y=t.ts.date().year(), m=t.ts.date().month())),
    case("time", "date truncate", V, lambda: t.select(x=t.ts.date().truncate("M"))),
    case("time", "day_of_week", V, lambda: t.select(x=t.ts.day_of_week.index())),
    case("time", "day_of_week name", V, lambda: t.select(x=t.ts.date().day_of_week.full_name())),
    case("time", "iso_year", V, lambda: t.select(x=t.ts.iso_year())),
    case("time", "epoch_seconds", V, lambda: t.select(x=t.ts.epoch_seconds())),
    case(
        "time",
        "millisecond, microsecond",
        V,
        lambda: t.select(x=t.ts.millisecond(), y=t.ts.microsecond()),
    ),
    case(
        "time",
        "timestamp + column interval",
        R,
        lambda: t.select(x=t.ts + t.qty.as_interval("h")),
    ),
    case(
        "time",
        "date + column months",
        R,
        lambda: t.select(x=t.ts.date() + t.qty.as_interval("M")),
    ),
    case("time", "timestamp delta", R, lambda: t.select(x=t.ts.delta(t.ts, unit="hour"))),
    case("time", "bucket", V, lambda: t.select(x=t.ts.bucket(minutes=15))),
    case(
        "time",
        "group_by_dynamic (no overlap)",
        V,
        lambda: t.mutate(b=t.ts.bucket(minutes=15)).group_by("b").aggregate(n=_.count()),
    ),
    case(
        "time",
        "rolling sum by time",
        V,
        lambda: t.mutate(
            s=t.qty.sum().over(
                ibis.range_window(
                    order_by="ts",
                    preceding=ibis.interval(days=7) - ibis.interval(microseconds=1),
                    following=0,
                )
            )
        ),
    ),
    case(
        "time",
        "offset_by months and days",
        V,
        lambda: t.select(x=t.ts + ibis.interval(months=1) + ibis.interval(days=2)),
    ),
    case(
        "time",
        "month end",
        V,
        lambda: t.select(
            x=t.ts.date().truncate("M") + ibis.interval(months=1) - ibis.interval(days=1)
        ),
    ),
    case(
        "time",
        "group_by_dynamic (overlapping)",
        R,
        lambda: t.mutate(
            start=ibis.range(
                t.ts.bucket(minutes=15) - ibis.interval(minutes=15), t.ts, ibis.interval(minutes=15)
            ).unnest()
        ),
    ),
    case("time", "time of day", V, lambda: t.select(x=t.ts.time())),
    case("time", "time parts", V, lambda: t.select(h=t.ts.time().hour(), m=t.ts.time().minute())),
    case("time", "compare times", V, lambda: t.filter(t.ts.time() > dt.time(9, 30))),
    case("time", "strftime", V, lambda: t.select(x=t.ts.strftime("%Y-%m-%d %H:%M:%S"))),
    case("time", "timestamp from unix", V, lambda: t.select(x=t.qty.as_timestamp("ms"))),
    case(
        "time", "date from constants", V, lambda: t.select(x=t.ts.date() < ibis.date(2024, 2, 29))
    ),
    case(
        "time",
        "timestamp from constants",
        V,
        lambda: t.filter(t.ts < ibis.timestamp(2024, 1, 2, 3, 4, 5)),
    ),
    case("time", "date from columns", R, lambda: t.select(x=ibis.date(t.qty, 1, 1))),
    case("time", "string to timestamp", R, lambda: t.select(x=t.name.as_timestamp("%Y-%m-%d"))),
    case("time", "time + interval", R, lambda: t.select(x=t.ts.time() + ibis.interval(hours=1))),
    case("time", "time truncate", R, lambda: t.select(x=t.ts.time().truncate("h"))),
    case("time", "strftime other directives", R, lambda: t.select(x=t.ts.strftime("%A"))),
    case(
        "time",
        "between_time",
        X,
        lambda: t.filter(t.ts.time().between(dt.time(9), dt.time(17))),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "time of day": {"spark": "no tod type"},
    "time parts": {"spark": "no tod type"},
    "compare times": {"spark": "no tod type"},
    "rolling sum by time": NO_ROW_ORDER,
}

TIE_FREE = {"rolling sum by time"}

NO_DATAFUSION_SQL = {
    # `CAST(n || ' day' AS INTERVAL)` fails on a NULL count.
    "date - column days": "fails on NULL",
    # Python UDFs of Ibis's DataFusion backend.
    "epoch_seconds": "Ibis UDF",
    "millisecond, microsecond": "Ibis UDF",
    # No compilation rule.
    "iso_year": "no rule",
    "date delta": "no rule",
    # A duration is compared with `INTERVAL '3 DAYS'` as (months, days, ns).
    "date - date": "compares durations with days wrongly",
    # "frame offsets for RANGE must be …": Ibis writes the bound as a cast.
    "rolling sum by time": "refuses Ibis's interval frame",
    # No compilation rule.
    "bucket": "no rule",
    "group_by_dynamic (no overlap)": "no rule",
}
