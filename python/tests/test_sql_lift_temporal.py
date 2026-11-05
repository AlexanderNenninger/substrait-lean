"""Dates, timestamps and intervals in DuckDB SQL through sverify's own lift
(`sverify.sql_lift`): oracles A and C, and the refusals."""

import datetime as dt_
import json

import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

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
    # A DATE as a TIMESTAMP is its midnight (#807): the cast, and where DuckDB
    # types a date's arithmetic or truncation as a TIMESTAMP.
    "SELECT id, CAST(day AS TIMESTAMP) AS t, date_trunc('day', day) AS d,"
    " date_trunc('month', day) AS m, day + INTERVAL 1 DAY AS n, day - INTERVAL 1 MONTH AS p,"
    " day + INTERVAL 1 HOUR AS h, day - INTERVAL '1 day 90 minutes' AS q FROM orders",
    "SELECT id FROM orders WHERE day < placed OR day >= TIMESTAMP '2024-02-01 12:00'",
    "SELECT max(date_trunc('month', day)) AS m, min(day + INTERVAL 1 DAY) AS n FROM orders",
    # date_diff in every unit (#809): the boundaries crossed, weeks from Monday.
    "SELECT id, date_diff('microsecond', placed, TIMESTAMP '2024-01-01') AS us,"
    " date_diff('millisecond', placed, TIMESTAMP '2024-01-01 00:00:00.0005') AS ms,"
    " date_diff('second', placed, day) AS s, date_diff('minute', placed, day) AS mi,"
    " date_diff('hour', day, placed) AS h, date_diff('day', placed, day) AS d,"
    " date_diff('week', placed, day) AS w, date_diff('month', DATE '2023-11-30', placed) AS mo,"
    " date_diff('quarter', placed, day) AS q, datediff('year', day, placed) AS y FROM orders",
    "SELECT id, date_diff('hour', day, DATE '2024-03-01') AS h, date_diff('weeks', day,"
    " DATE '2024-03-01') AS w, date_diff('mins', day, DATE '1969-12-31') AS m FROM orders",
    # epoch, a DOUBLE of seconds; parts and names (#809).
    "SELECT id, epoch(placed) AS e, extract(epoch FROM day) AS f, epoch_us(placed) AS u,"
    " date_part('epoch', placed) AS g FROM orders",
    "SELECT id, dayname(day) AS dn, monthname(placed) AS mn, isodow(day) AS i,"
    " isoyear(placed) AS y, extract(isoyear FROM day) AS z, last_day(day) AS l,"
    " last_day(placed) AS lp FROM orders",
    "SELECT id, make_date(2024, amount, 1) AS a, make_date(2023 + id // 3, 2, 28 + id // 4) AS b,"
    " make_date(2024, 2, 29) = DATE '2024-02-29' AS c FROM orders WHERE amount BETWEEN 1 AND 12",
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
        ("SELECT date_diff('decade', day, day) FROM orders", "datediff in decade"),
        ("SELECT dayname(customer) FROM orders", "not a date or a timestamp"),
        ("SELECT make_date(2024, 2, 30) AS d", "DuckDB raises"),
        ("SELECT make_date(2024, price, 1) AS d FROM orders", "make_date of a float64"),
        ("SELECT placed + INTERVAL 'a while' FROM orders", "integers, each with a unit"),
        # `ago` negates; SQLGlot drops it from one unit (#626, SG-8).
        ("SELECT placed + INTERVAL '1 day ago' AS p FROM orders", "ago"),
        ("SELECT placed + INTERVAL '-3 microseconds ago' AS p FROM orders", "ago"),
        ("SELECT placed + INTERVAL '1 day 2 hours ago' AS p FROM orders", "ago"),
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
    "query",
    [
        "SELECT tm + INTERVAL 1 HOUR AS x, tm - INTERVAL 1 HOUR AS y FROM t",
        "SELECT INTERVAL '90 minutes' + tm AS x, tm + INTERVAL '-49 hours' AS y FROM t",
        "SELECT tm + INTERVAL 1 MICROSECOND AS x, tm - INTERVAL 25 HOUR AS y FROM t",
        # DuckDB drops the days and months of the interval.
        "SELECT tm + INTERVAL '1 month 2 days 3 hours' AS x FROM t",
        "SELECT TIME '23:30' + INTERVAL 1 HOUR AS x",
        "SELECT tm FROM t WHERE tm + INTERVAL 1 HOUR < TIME '05:00'",
    ],
)
def test_time_plus_interval_wraps_around_midnight(query):
    # #507: TIME ± INTERVAL wraps around midnight (`duckdb-time-plus-interval`).
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
        # DuckDB negates the interval of TIME - INTERVAL, which overflows here (#507).
        (
            "SELECT TIME '12:00:00' - INTERVAL '-4611686018427387904 microseconds"
            " -4611686018427387904 microseconds' AS x",
            "DuckDB raises",
        ),
    ],
)
def test_time_constants_outside_the_model_are_refused(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, {})


#: Timestamps from 1900 to 2100, in microseconds since 1970-01-01.
_US = st.integers(-2_208_988_800_000_000, 4_102_444_800_000_000)


@settings(max_examples=40, deadline=None)
@given(rows=st.lists(st.tuples(st.one_of(st.none(), _US), _US), max_size=8))
def test_date_diff_and_epoch_on_random_timestamps(rows):
    # Boundaries crossed, flooring before 1970 too; epoch as a double (#809).
    t = pa.table(
        {"a": pa.array([a for a, _ in rows], pa.timestamp("us")),
         "b": pa.array([b for _, b in rows], pa.timestamp("us"))}
    )  # fmt: skip
    units = ("microsecond", "millisecond", "second", "minute", "hour", "day", "week", "month",
             "quarter", "year")  # fmt: skip
    cols = ", ".join(f"date_diff('{u}', a, b) AS {u}" for u in units)
    query = f"SELECT {cols}, epoch(a) AS e, CAST(CAST(b AS DATE) AS TIMESTAMP) AS d FROM t"
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


@settings(max_examples=30, deadline=None)
@given(rows=st.lists(st.tuples(st.integers(1, 9999), st.integers(1, 12), st.integers(1, 28)),
                     max_size=6))  # fmt: skip
def test_make_date_on_random_dates(rows):
    # H. Hinnant's days_from_civil, as DuckDB's (#809).
    t = pa.table({k: pa.array([r[i] for r in rows], pa.int64()) for i, k in enumerate("ymd")})
    result = check("SELECT make_date(y, m, d) AS x, isoyear(make_date(y, m, d)) AS i FROM t",
                   {"t": t})  # fmt: skip
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT make_date(2024, amount, 1) AS d FROM orders",
        "SELECT make_date(2024, 2, amount + 26) AS d FROM orders",
    ],
)
def test_make_date_outside_the_calendar_raises(sql):
    """DuckDB raises for a month or day outside the calendar; `verify`
    reports it unless `requires` bounds them."""
    import sverify as sv

    report = sv.verify(sql, tables=SCHEMAS, counterexamples=0, on_inferred="off")
    assert report.errors, report
