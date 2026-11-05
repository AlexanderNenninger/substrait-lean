"""Dates, timestamps, intervals (`sql_lift/temporal.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "temporal"

TARGETS = [
    target(
        AREA,
        "date_trunc and date parts of a timestamp",
        "in",
        "catalogue: date_trunc 11, date_part 4",
        True,
        sql="SELECT date_trunc('month', ts), extract(year FROM d), date_part('dow', ts), "
        "quarter(d), week(d) FROM t",
    ),
    target(
        AREA,
        "constant intervals on timestamps, date literals",
        "in",
        "catalogue: interval_day_time 17, date_literal 18, interval_month 8",
        True,
        sql="SELECT ts + INTERVAL 1 MONTH, ts - INTERVAL 30 MINUTE FROM t "
        "WHERE d BETWEEN DATE '2024-01-01' AND DATE '2024-01-31' - INTERVAL 1 DAY",
    ),
    target(
        AREA,
        "date_diff in days, date - date",
        "in",
        "catalogue date_diff 6; retention pattern",
        True,
        sql="SELECT date_diff('day', d, d), d - d FROM t",
    ),
    target(
        AREA,
        "DATE ± INTEGER",
        "in",
        "dbt.dateadd on DuckDB; replay 57",
        False,
        sql="SELECT d + 1, d - 7 FROM t",
        issue=319,
    ),
    target(
        AREA,
        "date_diff in hours, minutes, months; epoch",
        "in",
        "sessionization, time-weighted averages, cohorts (#749, #765); catalogue epoch 2",
        True,
        sql="SELECT date_diff('minute', ts, ts), date_diff('month', d, d), epoch(ts) FROM t",
        issue=809,
    ),
    target(
        AREA,
        "make_date, last_day, dayname, monthname",
        "in",
        "Ibis date from columns; calendar dimensions",
        True,
        sql="SELECT make_date(2024, qty, 1), last_day(d), dayname(d) FROM t",
        ibis="date from columns",
        issue=809,
    ),
    target(
        AREA,
        "timestamp - timestamp, and intervals from columns",
        "in",
        "sessionization gaps (ts - lag(ts) > INTERVAL 30 MINUTE); Ibis timestamp delta, "
        "column intervals; replay 307",
        False,
        sql="SELECT ts - ts FROM t",
        ibis="timestamp delta",
        issue=342,
    ),
    target(
        AREA,
        "strptime, try_strptime, strftime",
        "in",
        "dates as text in raw data; Eurostat periods (#771); Ibis string to timestamp; replay 243",
        False,
        sql="SELECT try_strptime(name, '%Y-%m-%d'), strftime(ts, '%Y-%m') FROM t",
        ibis="string to timestamp",
        issue=347,
    ),
    target(
        AREA,
        "time_bucket",
        "in",
        "catalogue time_bucket 1; metrics rollups; replay 74",
        False,
        sql="SELECT time_bucket(INTERVAL 15 MINUTE, ts) FROM t",
        issue=347,
    ),
    target(
        AREA,
        "timestamps at s, ms and ns precision",
        "in",
        "Parquet and Arrow sources (the homelab cycling demo); replay 137",
        False,
        sql="SELECT CAST(ts AS TIMESTAMP_MS) FROM t",
        issue=323,
    ),
    target(
        AREA,
        "time zones: AT TIME ZONE, TIMESTAMPTZ",
        "skipped",
        "catalogue ts-local-day-revenue; replay 46",
        False,
        sql="SELECT ts AT TIME ZONE 'Europe/Berlin' FROM t",
        why="needs the time zone database in the model; store UTC and convert at the edge",
    ),
    target(
        AREA,
        "INTERVAL output columns as months, days and microseconds",
        "after",
        "DuckDB's types/interval tests",
        False,
        sql="SELECT INTERVAL 2 DAYS AS i FROM t",
        issue=342,
    ),
    target(
        AREA,
        "overlapping group_by_dynamic, rolling windows over time",
        "after",
        "Ibis group_by_dynamic (overlapping)",
        False,
        ibis="group_by_dynamic (overlapping)",
        issue=294,
    ),
]
