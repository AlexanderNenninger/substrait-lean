"""The Spark SQL dialect.

* Snapshots: the SQL for every accepted golden fixture and for the plans of
  the incremental pipelines (`SVERIFY_UPDATE_SNAPSHOTS=1` rewrites them);
  each parses as Spark SQL (sqlglot).
* Spark itself: the queries of `test_sql_snowflake` run on
  a local Spark session (`spark_session`) and are compared with Lean's own
  evaluation (`Rel.eval` through `substrait-check`), as are `date_part` and
  `date_trunc` at the edges of the calendar; the hooks whose Spark behaviour
  the model depends on are checked one by one.
"""

from __future__ import annotations

import json
import math
from decimal import Decimal
from pathlib import Path

import pyarrow as pa
import pytest
import sqlglot
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan
from sverify.sql import Unsupported, to_sql
from sverify.sql.spark import SPARK
from sverify.testing import canonical
from test_sql_snowflake import (
    ALL_PLANS,
    NAMED_ORDERED,
    SCHEMAS,
    TABLES,
    TIE_FREE,
    accepted_fixtures,
    check_snapshot,
    run_differential,
)
from test_time import DAY, MAX, MIN, NS_MAX, NS_MIN, PARTS, UNITS, anywhere

pytestmark = pytest.mark.backend("spark")


def spark_sql(plan: dict, tie_free: bool = False) -> str:
    """The query, or the reason it is refused, for snapshots."""
    try:
        return to_sql(plan, SPARK, tie_free=tie_free)
    except Unsupported as e:
        return f"-- Unsupported: {e}"


@pytest.mark.parametrize("path", accepted_fixtures(), ids=lambda p: p.stem)
def test_fixture_snapshot(path: Path):
    check_snapshot(path.stem, spark_sql(json.loads(path.read_text())), "spark")


@pytest.mark.parametrize("name", sorted(ALL_PLANS))
def test_pipeline_snapshot(name: str):
    sql = spark_sql(ALL_PLANS[name], tie_free=name in TIE_FREE)
    assert not sql.startswith("-- Unsupported"), sql
    check_snapshot(f"pipeline_{name}", sql, "spark")


# ------------------------------------------------------------ hooks on their own


def parses(sql: str) -> str:
    sqlglot.parse_one(f"SELECT {sql}", read="spark")
    return sql


def test_literals():
    assert parses(SPARK.float_lit(math.nan)) == "CAST('NaN' AS DOUBLE)"
    assert parses(SPARK.float_lit(-0.0)) == "(- CAST('0' AS DOUBLE))"
    with pytest.raises(Unsupported, match="single NaN"):
        SPARK.float_lit(-math.nan)
    assert parses(SPARK.str_lit("it's a\\b\n")) == "'it\\'s a\\\\b\\u000a'"
    assert parses(SPARK.timestamp_lit(1_500)) == "TIMESTAMP_NTZ '1970-01-01 00:00:00.001500'"
    assert SPARK.int_lit(-(2**63)) == "CAST(-9223372036854775808 AS BIGINT)"
    assert SPARK.quote("a`b") == "`a``b`"


def test_refusals():
    with pytest.raises(Unsupported, match="Math.pow"):
        SPARK.float_pow("a", "b")
    with pytest.raises(Unsupported, match="ORDER BY"):
        SPARK.over(["`c0`"], [])
    with pytest.raises(Unsupported, match="no row order"):
        to_sql(NAMED_ORDERED["window"], SPARK)
    with pytest.raises(Unsupported, match="no row order"):
        to_sql(NAMED_ORDERED["fetch"], SPARK, tie_free=True)


# ------------------------------------------------------------ on Spark


@pytest.fixture(scope="module")
def spark():
    from spark_session import session

    return session()


def query(sql: str) -> list[tuple]:
    from spark_session import query

    return query(sql)


def one(*exprs: str) -> tuple:
    return query(f"SELECT {', '.join(exprs)}")[0]


def test_matches_lean(spark):
    """The queries of the Snowflake tests, against `Rel.eval`."""
    # View names cannot hold `$`.
    views = {name: name.replace("$", "__") for name in SCHEMAS}
    for name, cols in SCHEMAS.items():
        schema = ", ".join(f"{SPARK.quote(c)} {SPARK.type_name(k)}" for c, k in cols)  # type: ignore[arg-type]
        spark.createDataFrame(TABLES[name], schema).createOrReplaceTempView(views[name])

    def retarget(sql: str) -> str:
        for name, view in views.items():
            sql = sql.replace(f"FROM {SPARK.quote(name)}", f"FROM {SPARK.quote(view)}")
        return sql

    def run(sql: str) -> list[tuple]:
        return [tuple(int(v) if isinstance(v, Decimal) else v for v in r) for r in query(sql)]

    run_differential(run, retarget, SPARK)


def test_floats(spark):
    d = SPARK
    nan, inf, ninf = d.float_lit(math.nan), d.float_lit(math.inf), d.float_lit(-math.inf)
    zero, neg0, one_ = d.float_lit(0.0), d.float_lit(-0.0), d.float_lit(1.0)
    # The total order: NaN largest and equal to itself, -0.0 < +0.0.
    assert one(
        d.float_eq(nan, nan),
        d.float_lt(inf, nan),
        d.float_lt(neg0, zero),
        d.float_eq(neg0, zero),
        d.float_lt(ninf, neg0),
        d.sign_bit(neg0),
        d.sign_bit(nan),
        d.sign_bit(d.null("float")),
    ) == (True, True, True, False, True, True, False, None)
    # Division by a zero of either sign is IEEE, not an error.
    got = one(*(d.float_div(a, b) for a, b in [(one_, zero), (one_, neg0), (neg0, zero)]))
    assert got[:2] == (math.inf, -math.inf) and math.isnan(got[2])
    assert one(d.float_div(d.null("float"), zero)) == (None,)
    # FLOOR, CEIL and ROUND keep the sign of a zero, NaN, ±inf and big values.
    x = [d.float_lit(v) for v in (-0.4, 0.3, -0.0, 2.5, 1e300)]
    got = one(
        d.float_round(x[0]),
        d.float_floor(x[1]),
        d.float_ceil(x[0]),
        d.float_floor(x[2]),
        d.float_round(x[3]),
        d.float_floor(x[4]),
        d.float_ceil(ninf),
    )
    assert repr(got) == repr((-0.0, 0.0, -0.0, -0.0, 3.0, 1e300, -math.inf))
    assert math.isnan(one(d.float_round(nan))[0])
    assert one(d.float_to_int(d.float_lit(-2.9))) == (-2,)
    for bad in (2.0**63, math.nan, -math.inf):
        with pytest.raises(Exception, match="sverify"):
            one(d.float_to_int(d.float_lit(bad)))
    with pytest.raises(Exception, match="sverify"):
        one(d.float_neg(nan))
    # The optimizer takes the literals -0.0 and +0.0 for equal; a CASE
    # between them must keep the sign (on a table: VALUES are evaluated
    # without the optimizer).
    spark.range(3).selectExpr("CAST(id AS DOUBLE) - 1 AS x").createOrReplaceTempView("signs")
    pick = d.case_when("(x > 0)", neg0, zero)
    got = query(f"SELECT x, {pick}, {d.float_round('(x * 0.25D)')} FROM signs ORDER BY x")
    assert repr(got) == repr([(-1.0, 0.0, -0.0), (0.0, 0.0, 0.0), (1.0, -0.0, 0.0)])


def test_groups_keep_the_sign_of_zero(spark):
    con = connect()
    put_table(con, "z", pa.table({"x": pa.array([-0.0, 0.0, -0.0, None, math.nan], pa.float64())}))
    plan = written_plan(substrait_json(con, "SELECT x, count(*) AS n FROM z GROUP BY x"))
    from spark_session import put_tables

    put_tables({"z": con.con.table("z").to_arrow_table()})
    got = query(to_sql(json.loads(plan), SPARK))
    assert canonical(got) == canonical(
        [tuple(r.values()) for r in run_plan(con, plan, "duckdb").to_pylist()]
    )
    assert {repr(x) for x, _ in got} == {"-0.0", "0.0", "None", "nan"}


def test_integers(spark):
    d = SPARK
    big, lo = d.int_lit(2**62), d.int_lit(-(2**63))
    for sql in (d.int_add(big, big), d.int_div(lo, d.int_lit(-1)), d.int_pow(big, 2)):
        with pytest.raises(Exception, match="(?i)overflow"):
            one(sql)
    assert one(d.int_div(d.int_lit(-7), d.int_lit(2)), d.int_mod(d.int_lit(-7), d.int_lit(2))) == (
        -3,
        -1,
    )
    with pytest.raises(Exception, match="sverify: division by zero"):
        one(d.int_div(d.int_lit(1), d.int_lit(0)))
    assert one(d.int_pow_var(d.int_lit(3), d.int_lit(5))) == (243,)
    # SUM is the true total: a partial sum may leave 64 bits.
    values = "(VALUES (CAST(9223372036854775807 AS BIGINT)), (1), (-1)) AS v(x)"
    assert query(f"SELECT {d.int_sum('x')} FROM {values}") == [(2**63 - 1,)]
    with pytest.raises(Exception, match="sverify: integer overflow in SUM"):
        query(f"SELECT {d.int_sum('x')} FROM {values} WHERE x > 0")
    # Doubles add in the ordinal's order: 1 + 1e16 + 1 rounds twice.
    rows = "(VALUES (2, 1e16D), (1, 1.0D), (3, 1.0D), (4, NULL)) AS v(o, x)"
    assert query(f"SELECT {d.float_sum('x', 'o')} FROM {rows}") == [(1e16,)]


def test_strings(spark):
    d = SPARK
    tricky = "it's a\\b\n😀 %_"
    assert one(d.str_lit(tricky)) == (tricky,)
    # Code point order (no collation), and characters, not bytes or UTF-16 units.
    assert one(d.lt(d.str_lit("￿"), d.str_lit("😀")), d.char_length(d.str_lit("é😀"))) == (
        True,
        2,
    )
    assert one(d.strpos(d.str_lit("abc"), d.str_lit("")), d.strpos(d.str_lit("abc"), "'c'")) == (
        1,
        3,
    )
    pattern = d.like_pattern(d.str_lit("a\\"))
    assert one(pattern, d.like(d.str_lit("a\\"), pattern)) == ("a\\\\", True)


def ntz(micros: int | None) -> str:
    if micros is None:
        return SPARK.null("time")
    return (
        f"timestampadd(MICROSECOND, {SPARK.int_lit(micros)}, TIMESTAMP_NTZ '1970-01-01 00:00:00')"
    )


def as_micros(ts: str) -> str:
    return f"timestampdiff(MICROSECOND, TIMESTAMP_NTZ '1970-01-01 00:00:00', {ts})"


def polars_rows(sql: str, values: list[int | None]) -> list[tuple]:
    """Polars runs the plan Lean writes, and agrees with Lean (`test_time`)."""
    con = connect()
    put_table(con, "r", pa.table({"ts": pa.array(values, pa.timestamp("us"))}))
    out = run_plan(con, written_plan(substrait_json(con, sql)), "polars")
    cols = [c.cast(pa.int64()) if pa.types.is_timestamp(c.type) else c for c in out.columns]
    return [tuple(r.values()) for r in pa.table(cols, names=out.column_names).to_pylist()]


def spark_rows(exprs: list[str], values: list[int | None]) -> list[tuple]:
    rows = ", ".join(f"({ntz(v)})" for v in values)
    return query(f"SELECT {', '.join(exprs)} FROM (VALUES {rows}) AS r(ts)")


@settings(max_examples=15, deadline=None, suppress_health_check=list(HealthCheck))
@given(values=st.lists(st.one_of(st.none(), anywhere), min_size=1, max_size=8))
def test_date_part_matches_lean(spark, values):
    sql = "SELECT " + ", ".join(f"date_part('{p}', ts) AS {p}" for p in PARTS) + " FROM r"
    got = spark_rows([SPARK.date_part(p, "ts") for p in PARTS], values)
    assert canonical(got) == canonical(polars_rows(sql, values))


@settings(max_examples=15, deadline=None, suppress_health_check=list(HealthCheck))
@given(values=st.lists(st.one_of(st.none(), anywhere), min_size=1, max_size=8))
def test_date_trunc_matches_lean(spark, values):
    # Where Lean reports no issue (as in `test_time`).
    for unit in UNITS:
        calendar = unit in ("week", "month", "quarter", "year")
        lo, hi = (NS_MIN + 400 * DAY, NS_MAX) if calendar else (MIN + DAY, MAX)
        vs = [v for v in values if v is None or lo <= v <= hi] or [None]
        sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
        got = spark_rows([as_micros(SPARK.date_trunc(unit, "ts"))], vs)
        assert canonical(got) == canonical(polars_rows(sql, vs)), unit
