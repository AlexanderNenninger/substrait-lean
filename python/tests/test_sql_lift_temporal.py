"""Dates, timestamps and intervals in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`): oracles A and C, and the refusals."""

import datetime as dt_
import json

import pyarrow as pa
import pytest

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    "SELECT id FROM orders WHERE day >= DATE '2024-01-01' AND day < '2024-02-01'",
    "SELECT id, date_trunc('day', placed) AS d, date_trunc('week', placed) AS w,"
    " date_trunc('quarter', placed) AS q, date_trunc('hour', placed) AS h FROM orders",
    "SELECT id, placed + INTERVAL 1 DAY AS tomorrow, placed - INTERVAL '90' MINUTES AS before,"
    " INTERVAL 2 MONTHS + placed AS later FROM orders"
    " WHERE placed >= TIMESTAMP '2024-01-08' - INTERVAL 1 WEEK",
    "SELECT date_trunc('month', placed) AS m, count(*) AS n FROM orders GROUP BY 1 ORDER BY 1",
    # DuckDB's DATE ± INTERVAL and date_trunc of a DATE are TIMESTAMPs at
    # midnight: held as dates, compared exactly.
    "SELECT id FROM orders WHERE day <= DATE '2024-03-31' - INTERVAL 90 DAY",
    "SELECT id FROM orders WHERE day >= DATE '2023-12-31' AND day < DATE '2023-12-31'"
    " + INTERVAL 1 MONTH",
    "SELECT id FROM orders WHERE day + INTERVAL 1 MONTH > DATE '2024-02-15'",
    "SELECT DATE '2024-01-31' + INTERVAL 1 MONTH AS m, DATE '2024-01-01' + INTERVAL 1 HOUR AS h",
    "SELECT id FROM orders WHERE date_trunc('month', day) = DATE '2024-01-01'",
    "SELECT id, extract(year FROM day) AS y, extract(quarter FROM day) AS q, month(day) AS m,"
    " day(day) AS d, dayofweek(day) AS dw, dayofyear(day) AS dy, week(day) AS w FROM orders",
    "SELECT id, date_part('hour', placed) AS h, minute(placed) AS mi, second(placed) AS s,"
    " extract(dow FROM placed) AS dw FROM orders",
    "SELECT id, day - DATE '2024-01-01' AS since, datediff('day', DATE '2024-01-01', day) AS dd"
    " FROM orders",
    "SELECT extract(year FROM day) AS y, count(*) AS n FROM orders GROUP BY 1 ORDER BY 1",
    "SELECT id, placed + INTERVAL '1 month 2 days 3 hours' AS later FROM orders"
    " WHERE day >= ' 2024-01-01'",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "reference").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT INTERVAL 2 DAYS AS x", "INTERVAL output column"),
        # A DATE at midnight that DuckDB types a TIMESTAMP needs a cast Lean
        # lacks where it is one: an output column, next to a timestamp column.
        ("SELECT date_trunc('day', day) AS d FROM orders", "is a TIMESTAMP in DuckDB"),
        ("SELECT day + INTERVAL 1 DAY AS d FROM orders", "is a TIMESTAMP in DuckDB"),
        ("SELECT id FROM orders WHERE day < placed", "DATE column as a TIMESTAMP"),
        ("SELECT day + INTERVAL 1 HOUR AS d FROM orders", "hours or less"),
        ("SELECT extract(epoch FROM placed) FROM orders", "date part EPOCH"),
        ("SELECT placed + INTERVAL 'a while' FROM orders", "integers, each with a unit"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


@pytest.mark.parametrize(
    "query",
    [
        "SELECT LEAST(DATE '1992-01-01', DATE '1994-02-02', DATE '1991-01-01') AS x",
        "SELECT LEAST(DATE '1992-01-01', NULL, DATE '1991-01-01') AS x",
        "SELECT GREATEST(TIMESTAMP '1992-01-01 13:45:21.890123', TIMESTAMP '1991-01-01 01:23:45')"
        " AS x",
        "SELECT id, GREATEST(day, DATE '2024-01-15') AS d, LEAST(placed, TIMESTAMP"
        " '2024-01-02 00:00:00') AS t FROM orders",
    ],
)
def test_greatest_and_least_keep_dates_and_timestamps(query):
    # #381: of constants alone, the written plan held the dates' and
    # timestamps' integer codes, and DuckDB gave 7670 for 1991-01-01.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


def test_greatest_and_least_of_times_run_on_polars_as_on_duckdb():
    import datetime as dt

    import ibis
    import pyarrow as pa

    from sverify.engine import connect, put_table, run_plan, written_plan

    table = pa.table(
        {
            "d": pa.array([dt.date(1992, 1, 1), None, dt.date(1980, 5, 5)], pa.date32()),
            "ts": pa.array([dt.datetime(1992, 1, 1, 13, 45), None, dt.datetime(2001, 1, 1)]),
            "tm": pa.array([dt.time(13, 45), None, dt.time(1, 2)], pa.time64("us")),
            "tn": pa.array([dt.time(2, 0), dt.time(3, 0), None], pa.time64("us")),
        }
    )
    con = connect()
    put_table(con, "t", table)
    sql = (
        "SELECT LEAST(DATE '1992-01-01', DATE '1991-01-01') AS c, GREATEST(d, DATE '1985-01-01')"
        " AS d, LEAST(ts, TIMESTAMP '1995-01-01 00:00:00') AS ts, GREATEST(tm, tn) AS tm FROM t"
    )
    plan = written_plan(json.dumps(lift(sql, {"t": ibis.Schema.from_pyarrow(table.schema)}).plan))
    assert run_plan(con, plan, "polars").to_pylist() == run_plan(con, plan, "duckdb").to_pylist()


#: A table with TIME columns (#386).
TIMES = {
    "t": pa.table(
        {
            "tm": pa.array(
                [dt_.time(4), dt_.time(6, 30, 1, 5), None, dt_.time(23, 59, 59, 999999)],
                pa.time64("us"),
            ),
            "tn": pa.array([dt_.time(1), dt_.time(7), dt_.time(2), None], pa.time64("us")),
        }
    )
}


@pytest.mark.parametrize(
    "query",
    [
        "SELECT TIME '13:45:21' AS x",
        "SELECT CAST('13:45:21' AS TIME) AS x",
        "SELECT TIME '1:02' AS x, TIME ' 13:45:21.5 ' AS y, TIME '00:00:00.000001' AS z",
        "SELECT LEAST(tm, TIME '05:00:00') AS x FROM t",
        "SELECT tm FROM t WHERE tm > TIME '05:00:00'",
        "SELECT tm FROM t WHERE tm > '05:00' AND tm <= '23:59:59.999999'",
        "SELECT GREATEST(tm, tn) AS x FROM t",
    ],
)
def test_time_constants(query):
    # #386: a TIME constant is a `precisionTime` literal, in microseconds
    # since midnight; Lean has no cast of a string to a time of day.
    result = check(query, TIMES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize(
    ("query", "message"),
    [
        # DuckDB raises on these.
        ("SELECT TIME '25:00:00' AS x", "out of range"),
        ("SELECT TIME '13' AS x", "HH:MM:SS"),
        # DuckDB reads these, as values the model has no literal for.
        ("SELECT TIME '24:00:00' AS x", "out of range"),
        ("SELECT TIME '13:45:21+02' AS x", "HH:MM:SS"),
    ],
)
def test_time_constants_outside_the_model_are_refused(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, {})
