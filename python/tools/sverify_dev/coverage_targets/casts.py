"""Casts (`sql_lift/casts.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "casts"

TARGETS = [
    target(
        AREA,
        "numeric casts: integer, double, decimal",
        "in",
        "catalogue: cast_numeric 8",
        True,
        sql="SELECT CAST(qty AS DOUBLE) AS a, CAST(qty AS DECIMAL(18, 2)) AS b, "
        "CAST(amount AS DECIMAL(18, 2)) AS c, CAST(price AS DOUBLE) AS e FROM t",
    ),
    target(
        AREA,
        "CAST(DOUBLE AS INTEGER), which DuckDB rounds",
        "in",
        "CAST(amount * 100 AS BIGINT) for cents; catalogue cast_numeric 8; replay 76",
        False,
        sql="SELECT CAST(amount AS BIGINT) FROM t",
        issue=322,
    ),
    target(
        AREA,
        "decimal to a smaller scale",
        "in",
        "CAST(x AS DECIMAL(10, 2)) after arithmetic; replay 25",
        False,
        sql="SELECT CAST(price AS DECIMAL(10, 1)) FROM t",
        issue=27,
    ),
    target(
        AREA,
        "casts to VARCHAR",
        "in",
        "dbt surrogate keys and hash diffs (md5 of casts), dbt_utils.unpivot, labels; replay 184",
        False,
        sql="SELECT CAST(price AS VARCHAR), CAST(d AS VARCHAR), CAST(ts AS VARCHAR), "
        "CAST(flag AS VARCHAR) FROM t",
        issue=346,
    ),
    target(
        AREA,
        "casts from VARCHAR, and TRY_CAST",
        "in",
        "Eurostat values (#771); CSV sources; Ibis try_cast string",
        False,
        sql="SELECT TRY_CAST(name AS DOUBLE), CAST(name AS DATE) FROM t",
        ibis="try_cast string",
        issue=806,
    ),
    target(
        AREA,
        "DATE as TIMESTAMP: the cast, date_trunc and DATE ± INTERVAL of a date column",
        "in",
        "monthly rollups over DATE columns (catalogue date_trunc 11); dbt.dateadd",
        True,
        sql="SELECT date_trunc('month', d), d + INTERVAL 1 DAY, CAST(d AS TIMESTAMP) FROM t",
        issue=807,
    ),
    target(
        AREA,
        "casts of a double to VARCHAR",
        "after",
        "labels; replay (part of 184)",
        False,
        sql="SELECT CAST(amount AS VARCHAR) FROM t",
        issue=346,
        why="DuckDB's shortest round-trip form; a black box until then (#325)",
    ),
]
