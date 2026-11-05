"""Window functions (`sql_lift/_base.py`'s `_RANKING`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "windows"

TARGETS = [
    target(
        AREA,
        "row_number, rank, dense_rank, ntile",
        "in",
        "catalogue: row_number 8, ntile 3, rank 2; dedup pattern",
        True,
        sql="SELECT row_number() OVER (PARTITION BY name ORDER BY ts DESC), "
        "rank() OVER (ORDER BY qty), "
        "ntile(4) OVER (ORDER BY amount) FROM t",
    ),
    target(
        AREA,
        "lag and lead",
        "in",
        "catalogue lag_lead 15; sessionization, counter resets",
        True,
        sql="SELECT lag(amount) OVER (PARTITION BY name ORDER BY ts), "
        "lead(ts, 2) OVER (PARTITION BY name ORDER BY ts) FROM t",
    ),
    target(
        AREA,
        "running and ROWS-frame aggregates",
        "in",
        "catalogue: running_agg 11, rows_frame 4; running balance pattern",
        True,
        sql="SELECT sum(amount) OVER (PARTITION BY name ORDER BY ts ROWS UNBOUNDED PRECEDING), "
        "avg(amount) OVER (PARTITION BY name ORDER BY ts ROWS BETWEEN 6 PRECEDING AND CURRENT ROW) "
        "FROM t",
    ),
    target(
        AREA,
        "aggregates over windows and over aggregates",
        "in",
        "catalogue: window_over_aggregate 8, window_partition_agg 4",
        True,
        sql="SELECT name, sum(qty) / sum(sum(qty)) OVER (), count(*) OVER () FROM t GROUP BY name",
    ),
    target(
        AREA,
        "first_value, last_value",
        "in",
        "catalogue first_last_value 2",
        True,
        sql="SELECT first_value(amount) OVER (PARTITION BY name ORDER BY ts), "
        "last_value(amount) OVER (PARTITION BY name ORDER BY ts "
        "ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) FROM t",
    ),
    target(
        AREA,
        "QUALIFY",
        "in",
        "catalogue qualify 7 (written as subqueries); dedup pattern; replay 62",
        False,
        sql="SELECT * FROM t QUALIFY row_number() OVER (PARTITION BY name ORDER BY ts DESC) = 1",
        issue=319,
    ),
    target(
        AREA,
        "named WINDOW",
        "in",
        "replay 71",
        False,
        sql="SELECT sum(qty) OVER w FROM t WINDOW w AS (PARTITION BY name ORDER BY ts)",
        issue=319,
    ),
    target(
        AREA,
        "RANGE frames with an INTERVAL offset",
        "in",
        "rolling 7 days (catalogue range_frame 1); Ibis rolling sum (interval) verifies",
        False,
        sql="SELECT sum(qty) OVER (PARTITION BY name ORDER BY ts "
        "RANGE BETWEEN INTERVAL 7 DAY PRECEDING AND CURRENT ROW) FROM t",
        issue=811,
    ),
    target(
        AREA,
        "IGNORE NULLS",
        "in",
        "gap filling, last observation carried forward (#749, #765)",
        False,
        sql="SELECT last_value(amount IGNORE NULLS) OVER (PARTITION BY name ORDER BY ts "
        "ROWS BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW) FROM t",
        issue=811,
    ),
]
