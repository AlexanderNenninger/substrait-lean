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

import math
import re
from decimal import Decimal
from pathlib import Path

import pyarrow as pa
import pytest
import sqlglot
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan
from sverify.sql import Unsupported, to_sql
from sverify.testing import canonical
from sverify_duckdb.dialect import DUCKDB
from sverify_spark.dialect import SPARK
from test_sql_snowflake import (
    ALL_PLANS,
    NAMED_ORDERED,
    SCHEMAS,
    TABLES,
    TIE_FREE,
    accepted_fixtures,
    check_snapshot,
    fixture_plan,
    run_differential,
)
from test_time import D32_POINTS, DAY, MAX, MIN, PARTS, TS_MAX, TS_MIN, UNITS, anywhere

pytestmark = pytest.mark.backend("spark")


def spark_sql(plan: dict, tie_free: bool = False) -> str:
    """The query, or the reason it is refused, for snapshots."""
    try:
        return to_sql(plan, SPARK, deterministic=tie_free)
    except Unsupported as e:
        return f"-- Unsupported: {e}"


@pytest.mark.parametrize("path", accepted_fixtures(), ids=lambda p: p.stem)
def test_fixture_snapshot(path: Path):
    check_snapshot(path.stem, spark_sql(fixture_plan(path)), "spark")


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
    # The model's one zero and one NaN.
    assert parses(SPARK.float_lit(-0.0)) == "-0.0D"
    assert SPARK.float_lit(-math.nan) == SPARK.float_lit(math.nan)
    assert parses(SPARK.str_lit("it's a\\b\n")) == "'it\\'s a\\\\b\\u000a'"
    assert parses(SPARK.timestamp_lit(1_500)) == "TIMESTAMP_NTZ '1970-01-01 00:00:00.001500'"
    assert SPARK.int_lit(-(2**63)) == "CAST(-9223372036854775808 AS BIGINT)"
    assert SPARK.quote("a`b") == "`a``b`"


def test_refusals():
    with pytest.raises(Unsupported, match="Math.pow"):
        SPARK.float_pow("a", "b")
    with pytest.raises(Unsupported, match="ORDER BY"):
        SPARK.over(["`c0`"], [])
    # A time of day, as a column's type or a literal: TIME is off by default.
    for refuse in (lambda: SPARK.type_name("tod"), lambda: SPARK.time_of_day_lit(0)):
        with pytest.raises(Unsupported, match=r"^a time of day \(TIME\) on Spark.*spark-time-type"):
            refuse()
    for name in ("window", "fetch"):
        with pytest.raises(Unsupported, match=r'no row order.*rows="multiset"'):
            to_sql(NAMED_ORDERED[name], SPARK, rows="sequence")
        # Ties and a LIMIT's rows are open under the default observation (#1608), which
        # is what `to_sql` writes for Spark when it is not told (`ProfilePlugin.rows`).
        multiset = to_sql(NAMED_ORDERED[name], SPARK, rows="multiset")
        assert multiset and to_sql(NAMED_ORDERED[name], SPARK) == multiset


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


def _reads(node) -> list:
    """The `Read`s of a parsed plan, in any relation."""
    import dataclasses

    from sverify.sql.core import _base

    if isinstance(node, _base.Read):
        return [node]
    if isinstance(node, tuple | list):
        return [r for n in node for r in _reads(n)]
    if dataclasses.is_dataclass(node) and not isinstance(node, type):
        return [r for f in dataclasses.fields(node) for r in _reads(getattr(node, f.name))]
    return []


@pytest.mark.parametrize(
    "name", ["df_asof", "df_order_by", "df_order_by_limit", "df_window", "union_fetch"]
)
def test_the_fixtures_that_became_queries_analyze_on_spark(spark, name):
    """These Spark snapshots were refusals before `to_sql`'s `rows` followed the
    engine: over empty tables of the plan's schemas, Spark accepts each query."""
    from sverify.sql import parse_plan

    path = next(p for p in accepted_fixtures() if p.stem == name)
    plan = fixture_plan(path)
    sql = to_sql(plan, SPARK)
    assert not sql.startswith("-- Unsupported")
    for i, read in enumerate(_reads(parse_plan(plan).root)):
        schema = ", ".join(
            f"{SPARK.quote(c)} {SPARK.type_name(k)}"  # type: ignore[arg-type]
            for c, k in zip(read.columns, read.kinds, strict=True)
        )
        view = f"snap_{i}_{'_'.join(read.name)}".replace("$", "__").replace(".", "_")
        spark.createDataFrame([], schema).createOrReplaceTempView(view)
        sql = sql.replace(f"FROM {SPARK.quote('.'.join(read.name))}", f"FROM {SPARK.quote(view)}")
    query(sql)  # analyzed and run: no exception


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
    zero, one_ = d.float_lit(0.0), d.float_lit(1.0)
    neg0 = f"(- {zero})"
    # One zero and one NaN: NaN largest and equal to itself, -0.0 = 0.0.
    assert one(
        d.float_eq(nan, nan),
        d.float_lt(inf, nan),
        d.float_lt(neg0, zero),
        d.float_eq(neg0, zero),
        d.float_lt(ninf, neg0),
    ) == (True, True, False, True, True)
    # IEEE division by a zero of either sign raises, as ANSI `/` does and
    # `sparkBin .fdivIeee` states (ruling 161); a non-zero divisor divides.
    for a in (one_, f"(- {one_})", zero):
        for z in (zero, neg0):
            with pytest.raises(Exception, match="(?i)DIVIDE_BY_ZERO|division by zero"):
                one(d.float_div(a, z))
    assert one(
        d.float_div(one_, d.float_lit(4.0)), d.float_div(f"(- {one_})", f"({neg0} + 4.0)")
    ) == (
        0.25,
        -0.25,
    )
    # The remainder is C's `fmod`; by zero sverify's error (#203).
    m = [d.float_lit(v) for v in (7.5, -7.5, 2.0, -2.0)]
    got = one(
        d.float_mod(m[0], m[2]),
        d.float_mod(m[1], m[2]),
        d.float_mod(m[0], m[3]),
        d.float_mod(m[0], inf),
        d.float_mod(inf, m[2]),
        d.float_mod(d.null("float"), zero),
    )
    assert got[:4] == (1.5, -1.5, 1.5, 7.5) and math.isnan(got[4]) and got[5] is None
    with pytest.raises(Exception, match="division by zero"):
        one(d.float_mod(m[0], zero))
    # FLOOR, CEIL and ROUND keep NaN, ±inf and big values; zeros are zero.
    x = [d.float_lit(v) for v in (-0.4, 0.3, 2.5, 1e300)]
    got = one(
        d.float_round(x[0]),
        d.float_floor(x[1]),
        d.float_ceil(x[0]),
        d.float_round(x[2]),
        d.float_floor(x[3]),
        d.float_ceil(ninf),
    )
    assert repr(got) == repr((0.0, 0.0, 0.0, 3.0, 1e300, -math.inf))
    assert math.isnan(one(d.float_round(nan))[0])
    assert one(d.float_to_int(d.float_lit(-2.9))) == (-2,)
    for bad in (2.0**63, math.nan, -math.inf):
        with pytest.raises(Exception, match="sverify"):
            one(d.float_to_int(d.float_lit(bad)))
    # Values stay raw (D31): a computed -0.0 comes out as Spark gives it.
    spark.range(3).selectExpr("CAST(id AS DOUBLE) - 1 AS x").createOrReplaceTempView("signs")
    got = query("SELECT x, (x * -0.0D) FROM signs ORDER BY x")
    assert [(a, math.copysign(1.0, b)) for a, b in got] == [(-1.0, 1.0), (0.0, -1.0), (1.0, -1.0)]


def test_the_parser_cache_is_flushed(spark):
    """The local session bounds the parser's ANTLR DFA cache, which deeply
    nested SQL grew to most of a 1 GB heap (`spark_engine.LOCAL_CONF`)."""
    assert spark.conf.get("spark.sql.parser.manageParserCaches") == "true"
    assert float(spark.conf.get("spark.sql.parser.parserDfaCacheFlushRatio")) > 0


def test_driver_memory_from_the_memory_limit():
    from sverify_spark.engine import driver_memory

    assert driver_memory("2GB") == "2g"
    assert driver_memory(" 512 mb ") == "512m"
    assert driver_memory("4GiB") == "4g"
    with pytest.raises(ValueError, match="memory limit"):
        driver_memory("lots")


def test_groups_have_one_zero_and_one_nan(spark):
    """Through `sverify_spark.engine.run`, Arrow in and out."""
    from sverify_spark import engine as spark_engine

    con = connect()
    z = pa.table({"x": pa.array([-0.0, 0.0, -0.0, None, math.nan], pa.float64())})
    put_table(con, "z", z)
    plan = written_plan(
        substrait_json(con, "SELECT x, count(*) AS n FROM z GROUP BY x", semantics="duckdb")
    )
    got = [tuple(r.values()) for r in spark_engine.run(plan, {"z": z}, spark).to_pylist()]
    duck = [tuple(r.values()) for r in run_plan(con, plan, "duckdb").to_pylist()]
    assert canonical(got) == canonical(duck)
    assert sorted(repr(r) for r in got) == ["(0.0, 3)", "(None, 1)", "(nan, 1)"]


def test_variance_of_one_nan(spark):
    """Spark's `var_pop` and `stddev_pop` of one NaN are NaN
    (spark-var-pop-one-nan), and its profile's `agg.var` row names no shim,
    so its plan has no NaN guard (`Dialect.var_nan`); DuckDB's keeps it."""
    from sverify_spark import engine as spark_engine

    assert SPARK.var_nan("x", "", "body") == "body"
    assert DUCKDB.var_nan("x", "", "body") != "body"
    con = connect()
    t = pa.table({"g": pa.array([1, 2, 2], pa.int64()), "x": pa.array([math.nan, math.nan, 1.0])})
    put_table(con, "t", t)
    sql = "SELECT g, var_pop(x) AS v, stddev_pop(x) AS s FROM t GROUP BY g"
    plan = written_plan(substrait_json(con, sql))
    got = sorted(tuple(r.values()) for r in spark_engine.run(plan, {"t": t}, spark).to_pylist())
    assert [g for g, *_ in got] == [1, 2]
    assert all(math.isnan(v) and math.isnan(s) for _, v, s in got)


def test_ieee_division_by_zero_raises(spark):
    """DuckDB SQL lifted with `semantics="duckdb"` divides doubles under
    `on_division_by_zero` = `IEEE` (D39). Written for Spark it is the plain
    `/`, so a zero divisor raises, `-0.0` as `0.0`, whichever the dividend's
    sign (ruling 161); a non-zero divisor gives the quotient."""
    import json

    from sverify_spark import engine as spark_engine

    con = connect()
    put_table(con, "t", pa.table({"a": [1.0], "b": [2.0]}))
    plan = written_plan(substrait_json(con, "SELECT a / b AS q FROM t", semantics="duckdb"))
    assert '"IEEE"' in plan
    sql = to_sql(json.loads(plan), SPARK)
    # The guards around it read the divisor; the division itself is `/`.
    assert re.search(r"ELSE \(s\d+\.`c0` / s\d+\.`c1`\)", sql)
    assert "'Infinity' AS DOUBLE) ELSE" not in sql and "division by zero" not in sql

    def run(rows: list[tuple[float, float]]) -> list[tuple]:
        a, b = zip(*rows, strict=True)
        t = pa.table({"a": pa.array(a, pa.float64()), "b": pa.array(b, pa.float64())})
        return [tuple(r.values()) for r in spark_engine.run(plan, {"t": t}, spark).to_pylist()]

    assert sorted(run([(3.0, 2.0), (-1.0, 4.0)])) == [(-0.25,), (1.5,)]
    for a in (1.0, -1.0):
        for b in (0.0, -0.0):
            # Beside a row with a non-zero divisor, so the column varies.
            with pytest.raises(Exception, match="(?i)DIVIDE_BY_ZERO|division by zero"):
                run([(a, b), (1.0, 2.0)])


def test_floor_division(spark):
    """A plan that states `division_type: FLOOR` (`semantics="polars"`): the
    SQL writer computes it from Spark's truncating `div` and `%`, so negative
    operands floor, and a zero divisor and `MIN // -1` raise."""
    import json

    from ibis import _

    import sverify as sv
    from sverify_spark import engine as spark_engine

    vcon = sv.connect()
    vcon.put("t", pa.table({"i": pa.array([1], pa.int64()), "j": pa.array([1], pa.int64())}))
    t = vcon.table("t")
    report = sv.verify(
        t.select(m=t.i % t.j, q=t.i // t.j),
        requires={"t": [_.i >= -9 * 10**18, _.j != 0]},
        semantics="polars",
    )
    plan = written_plan(report.internal_plan or "")
    assert '"FLOOR"' in plan
    assert "Unsupported" not in to_sql(json.loads(plan), SPARK)
    lo, hi = -(2**63), 2**63 - 1

    def run(rows: list[tuple[int, int]]) -> list[tuple]:
        i, j = zip(*rows, strict=True)
        t = pa.table({"i": pa.array(i, pa.int64()), "j": pa.array(j, pa.int64())})
        return [tuple(r.values()) for r in spark_engine.run(plan, {"t": t}, spark).to_pylist()]

    edges = [(-7, 2), (7, -2), (-7, -2), (0, -3), (lo, 1), (lo, 2), (hi, -1), (hi, lo)]
    assert sorted(run(edges)) == sorted((a % b, a // b) for a, b in edges)
    for bad in ([(1, 0)], [(lo, -1)]):
        with pytest.raises(Exception, match="(?i)zero|overflow"):
            run(bad)


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
    assert one(
        d.fn("strpos", d.str_lit("abc"), d.str_lit("")), d.fn("strpos", d.str_lit("abc"), "'c'")
    ) == (
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
    out = run_plan(con, written_plan(substrait_json(con, sql, semantics="duckdb")), "polars")
    cols = [c.cast(pa.int64()) if pa.types.is_timestamp(c.type) else c for c in out.columns]
    return [tuple(r.values()) for r in pa.table(cols, names=out.column_names).to_pylist()]


def spark_rows(exprs: list[str], values: list[int | None]) -> list[tuple]:
    rows = ", ".join(f"({ntz(v)})" for v in values)
    return query(f"SELECT {', '.join(exprs)} FROM (VALUES {rows}) AS r(ts)")


@settings(max_examples=15, deadline=None, suppress_health_check=list(HealthCheck))
@given(values=st.lists(st.one_of(st.none(), anywhere), min_size=1, max_size=8))
def test_date_part_matches_lean(spark, values):
    # Within the reference's timestamps: outside them the plan raises (D32).
    values = [v for v in values if v is None or TS_MIN <= v <= TS_MAX] or [None]
    sql = "SELECT " + ", ".join(f"date_part('{p}', ts) AS {p}" for p in PARTS) + " FROM r"
    got = spark_rows([SPARK.date_part(p, "ts") for p in PARTS], values)
    assert canonical(got) == canonical(polars_rows(sql, values))


def test_d32_probe_points(spark):
    """D32's probe points (`test_time.D32_POINTS`): Spark's parts and
    truncations are Lean's, as `spark-calendar-range` records."""
    values = list(D32_POINTS.values())
    for unit in ("week", "month", "quarter", "year"):
        sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
        got = spark_rows([as_micros(SPARK.date_trunc(unit, "ts"))], values)
        assert canonical(got) == canonical(polars_rows(sql, values)), unit
    parts = ["year", "quarter", "month", "week", "day", "dow", "doy"]
    sql = "SELECT " + ", ".join(f"date_part('{p}', ts) AS {p}" for p in parts) + " FROM r"
    got = spark_rows([SPARK.date_part(p, "ts") for p in parts], values)
    assert canonical(got) == canonical(polars_rows(sql, values))


@settings(max_examples=15, deadline=None, suppress_health_check=list(HealthCheck))
@given(values=st.lists(st.one_of(st.none(), anywhere), min_size=1, max_size=8))
def test_date_trunc_matches_lean(spark, values):
    # Where Lean reports no issue (as in `test_time`).
    for unit in UNITS:
        calendar = unit in ("week", "month", "quarter", "year")
        lo, hi = (TS_MIN, TS_MAX) if calendar else (MIN + DAY, MAX)
        vs = [v for v in values if v is None or lo <= v <= hi] or [None]
        sql = f"SELECT date_trunc('{unit}', ts) AS x FROM r"
        got = spark_rows([as_micros(SPARK.date_trunc(unit, "ts"))], vs)
        assert canonical(got) == canonical(polars_rows(sql, vs)), unit


def test_nested_bound_operations_resolve_on_spark(spark):
    """`(x * x + x) / y` binds `x * x`, then `x * x + x`, one layer higher
    each (#1608): the layers are told apart by the dialect's own quoting
    (backticks here), or Spark cannot resolve a column defined beside its use."""
    import json

    import ibis

    from sverify.ibis_substrait import to_substrait_json
    from sverify_spark.engine import put_tables

    t = ibis.table({"x": "float64", "y": "float64"}, name="t")
    plan = json.loads(to_substrait_json(t.select(r=(t.x * t.x + t.x) / t.y)))
    sql = to_sql(plan, SPARK, rows="multiset")
    assert "`b1`" in sql
    xs, ys = [1.5, -7.25, 0.0, 3.0], [2.0, 4.0, 0.5, 8.0]
    put_tables({"t": pa.table({"x": xs, "y": ys})}, spark)
    got = [r[0] for r in spark.sql(sql).collect()]
    assert got == pytest.approx([(x * x + x) / y for x, y in zip(xs, ys, strict=True)])
