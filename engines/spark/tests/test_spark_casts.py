"""TRY_CAST, dates as timestamps, interval arithmetic with columns and
ordering comparisons of strings on Spark (#2540), against DuckDB, the oracle."""

import datetime as dt
import math

import ibis
import pyarrow as pa
import pytest

from sverify.engine import connect, plan_json, put_table, run_plan, written_plan

pytestmark = pytest.mark.backend("spark")

T = ibis.table(
    {"i": "!int64", "x": "float64", "q": "int64", "ts": "timestamp", "s": "string"}, name="t"
)
U = ibis.table({"v": "string"}, name="u")
TS = [dt.datetime(2024, 1, 2, 3, 4, 5, 6), dt.datetime(1, 1, 1), dt.datetime(9999, 12, 31, 23)]
ROWS = pa.table(
    {
        "i": list(range(9)),
        "x": [2.0**63, -(2.0**63), math.nan, math.inf, -math.inf, -2.5, 1e19, 127.9, None],
        "q": [127, 128, -128, -129, 0, None, 2**31, -(2**31) - 1, 5],
        "ts": [*TS, None, *TS, None, TS[0]],
        "s": ["a", "B", "é", "￿", "\U00010000", "", None, "ab", "Z"],
    },
    schema=pa.schema(
        [("i", pa.int64()), ("x", pa.float64()), ("q", pa.int64()),
         ("ts", pa.timestamp("us")), ("s", pa.string())]
    ),
)  # fmt: skip
#: Rows whose results stay in years Python's datetime holds.
INNER = T.ts.between(ibis.timestamp("0002-01-01 00:00:00"), ibis.timestamp("9998-01-01 00:00:00"))
UROWS = pa.table({"v": ["a", "é", "\U00010000", None]})


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def both(spark, expr) -> tuple[list[tuple], list[tuple]]:
    con = connect()
    put_table(con, "t", ROWS)
    put_table(con, "u", UROWS)
    plan = written_plan(plan_json(con, expr))

    def rows(engine) -> list[tuple]:
        out = run_plan(con, plan, engine, tie_free=False).to_pylist()
        return sorted((tuple(r.values()) for r in out), key=repr)

    return rows("duckdb"), rows(spark)


@pytest.mark.parametrize(
    "build",
    [lambda: T.select("i", o=T.x.try_cast("int64")),
     lambda: T.select("i", o=T.q.try_cast("int8")),
     lambda: T.select("i", o=T.q.try_cast("int32")),
     lambda: T.select("i", o=T.ts.date().cast("string")),
     lambda: T.filter(INNER).select("i", o=T.ts.delta(T.ts - ibis.interval(days=1), unit="hour")),
     lambda: T.select("i", o=T.ts.delta(ibis.timestamp("2000-01-01 00:00:00"), unit="second")),
     lambda: T.filter(T.q.abs() < 1000).select("i", o=T.ts + T.q.as_interval("h")),
     lambda: T.filter(INNER & (T.q.abs() < 1000)).select("i", o=T.ts - T.q.as_interval("m"))],
)  # fmt: skip
def test_spark_is_duckdb(spark, build):
    duck, got = both(spark, build())
    assert got == duck


def test_a_join_on_string_order_is_duckdbs(spark):
    """Code point order (spark-string-order): U+10000 above U+FFFF."""
    duck, got = both(spark, T.join(U, T.s < U.v).select("i", "s", "v"))
    assert got == duck
    assert ("￿", "\U00010000") in {(r[1], r[2]) for r in got}
