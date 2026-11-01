"""Every Ibis operation the checker verifies runs on every engine.

Each `verified` case of the coverage harness (`sverify_dev.coverage`) runs on
random tables: on DataFusion as Ibis compiles it to SQL, and on Polars and
DuckDB as the plan Lean writes back out (`written_plan`) from the Ibis
producer's plan. The results agree as bags with
DataFusion's, and Polars and DuckDB, which both follow `Rel.eval`'s list
order, agree row for row where the order is part of the result (below a
FETCH, a window or a sort). Where a FETCH takes "the first rows" of an unsorted
input DataFusion may take others, and it adds the doubles of a SUM or AVG in
an order of its own, so there only Polars and DuckDB are compared. The
Snowflake SQL is generated for every case too (and parsed).

The Spark SQL of every case runs on a local Spark session (`spark_session`,
one JVM for the whole test) and agrees with DuckDB, row for row where the
order is part of the result. Spark refuses what needs a table's row order;
the cases of `TIE_FREE` run with `tie_free=True` on the tables drawn here,
whose timestamps are distinct.
"""

import datetime as dt
import json
import math
from decimal import Decimal

import duckdb
import ibis
import pyarrow as pa
import pytest
import sqlglot
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify import polars_engine
from sverify.engine import canonical as canonical_table
from sverify.engine import (
    connect,
    create_table,
    put_table,
    run_plan,
    run_sql,
    to_sql,
    written_plan,
)
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import Unsupported, parse_plan
from sverify.sql import to_sql as plan_sql
from sverify.sql.core import Aggregate, Fetch, Rel, order_matters
from sverify.sql.snowflake import SNOWFLAKE
from sverify.sql.spark import SPARK
from sverify.testing import canonical
from sverify_dev import coverage

VERIFIED = [c for c in coverage.CASES if c.expected == "verified"]

#: Cases an engine refuses, with the reason (`sverify_dev.coverage` says why).
REFUSED, TIE_FREE = coverage.REFUSED, coverage.TIE_FREE

T0 = dt.datetime(2024, 2, 28, 23, 0)
STAMPS = [
    T0 + dt.timedelta(hours=h, minutes=m, microseconds=u)
    for h, m, u in [(0, 0, 0), (1, 30, 5), (49, 0, 999_999), (-24 * 400, 7, 1), (24 * 365, 59, 0)]
] + [dt.datetime(1969, 12, 31, 23, 59, 59, 999_999), dt.datetime(2021, 1, 3, 12)]

ints = st.one_of(st.none(), st.integers(-3, 6))
names = st.sampled_from([None, "ada", "bob", "", "a%b", "Émile", " cy "])
doubles = st.sampled_from([None, 0.0, -0.0, 0.5, 1.5, -2.25, 1e300, math.inf, -math.inf, math.nan])


@st.composite
def tables(draw) -> dict[str, pa.Table]:
    """Rows for `t` and `u`. Timestamps are distinct within `t`, so the window
    cases (ordered by `ts`) have no ties."""
    n = draw(st.integers(0, len(STAMPS)))
    ts = draw(st.lists(st.sampled_from(STAMPS), min_size=n, max_size=n, unique=True))
    t = {
        "id": draw(st.lists(ints, min_size=n, max_size=n)),
        "name": draw(st.lists(names, min_size=n, max_size=n)),
        "amount": draw(st.lists(doubles, min_size=n, max_size=n)),
        "qty": draw(st.lists(ints, min_size=n, max_size=n)),
        "ts": ts,
        "flag": draw(st.lists(st.sampled_from([None, True, False]), min_size=n, max_size=n)),
    }
    m = draw(st.integers(0, 4))
    u = {
        "name": draw(st.lists(names, min_size=m, max_size=m)),
        "region": draw(st.lists(st.sampled_from([None, "eu", "us"]), min_size=m, max_size=m)),
    }
    schema = {name: s.to_pyarrow() for name, s in coverage.T.schema().items()}
    nl = draw(st.integers(0, 4))
    lists = st.one_of(st.none(), st.lists(ints, max_size=3))
    return {
        "t": pa.table({k: pa.array(v, schema[k]) for k, v in t.items()}),
        "u": pa.table({k: pa.array(v, pa.string()) for k, v in u.items()}),
        "l": pa.table(
            {
                "k": pa.array(draw(st.lists(ints, min_size=nl, max_size=nl)), pa.int64()),
                "xs": pa.array(
                    draw(st.lists(lists, min_size=nl, max_size=nl)), pa.list_(pa.int64())
                ),
            }
        ),
    }


def rows(table: pa.Table) -> list[tuple]:
    """DataFusion types `ROW_NUMBER()` as a decimal; the model has one integer type."""
    return [
        tuple(int(v) if isinstance(v, Decimal) else v for v in r.values())
        for r in table.to_pylist()
    ]


def bags(rs: list[tuple]) -> list[tuple]:
    """Lists compared as bags: a list built from rows in no fixed order."""
    return [tuple(sorted(v, key=repr) if isinstance(v, list) else v for v in r) for r in rs]


def same(a: list[tuple], b: list[tuple]) -> bool:
    """Equal row for row; NaN equals NaN and -0.0 is not 0.0."""
    return repr(a) == repr(b)


def order_dependent(r: Rel) -> bool:
    """A FETCH of "the first rows", or a SUM or AVG of doubles, whose rounding
    depends on the order of the additions: there DataFusion, with an order of
    its own, may give other values."""
    if isinstance(r, Fetch):
        return True
    if isinstance(r, Aggregate) and any(m.fn in ("fsum", "avg") for m in r.measures):
        return True
    return any(order_dependent(getattr(r, k)) for k in ("input", "left", "right") if hasattr(r, k))


@pytest.fixture(scope="module")
def con():
    con = connect()
    for table in coverage.TABLES:
        create_table(con, table.get_name(), table.schema())
    for name, table in coverage.MEMTABLES.items():
        put_table(con, name, table)
    return con


@pytest.mark.parametrize("case", VERIFIED, ids=lambda c: c.label)
@settings(max_examples=25, deadline=None, suppress_health_check=list(HealthCheck))
@given(data=tables())
def test_engines_agree(con, case, data):
    for name, table in data.items():
        put_table(con, name, table)
    expr = case.build()
    plan = written_plan(to_substrait_json(expr))
    refused = REFUSED.get(case.label, {})
    results, failed = {}, set()
    for engine in ("polars", "duckdb"):
        if engine in refused:
            error = polars_engine.Unsupported if engine == "polars" else Unsupported
            with pytest.raises(error, match=refused[engine]):
                run_plan(con, plan, engine)
            continue
        try:
            results[engine] = rows(run_plan(con, plan, engine))
        except duckdb.Error as e:
            if "non-ASCII text differs between engines" in str(e):
                # UPPER, LOWER, regex classes: DuckDB raises where its
                # Unicode tables could differ from Rust's (#70).
                continue
            failed.add(engine)
        except polars_engine.RuntimeIssue:
            # A runtime error of `SubstraitLean/Safety.lean` (the data has
            # NaN and ±inf to cast): both engines raise it.
            failed.add(engine)
    if failed:
        assert failed | set(refused) == {"polars", "duckdb"}
        return
    if not results:
        return
    if case.label in coverage.UNORDERED_LISTS:
        results = {e: bags(r) for e, r in results.items()}
    try:
        root = parse_plan(json.loads(plan)).root
    except Unsupported:
        # The SQL dialects cannot read it (lists); only Polars ran it.
        root = None
    if "polars" in results and "duckdb" in results:
        assert root is not None
        pl_rows, duck = results["polars"], results["duckdb"]
        assert same(pl_rows, duck) if order_matters(root) else canonical(pl_rows) == canonical(duck)
    no_reference = case.label in coverage.NO_DATAFUSION_SQL
    if (root is None or not order_dependent(root)) and not no_reference:
        # As Ibis returns it: DataFusion's SQL result in the expression's
        # types (`POW` of integers is an integer there, a double in Ibis),
        # or DuckDB's where DataFusion means something else.
        if case.label in coverage.DATAFUSION_SQL:
            duck_sql = ibis.to_sql(expr, dialect="duckdb")
            out = canonical_table(con.ibis.con.sql(duck_sql).to_arrow_table())
        else:
            out = run_sql(con, to_sql(expr))
        expected = rows(out.cast(expr.schema().to_pyarrow()))
        if case.label in coverage.UNORDERED_LISTS:
            expected = bags(expected)
        df = canonical(expected)
        for got in results.values():
            assert canonical(got) == df


def engine_sql(case, engine: str, dialect, read: str) -> str | None:
    """The SQL of a case for a dialect that refuses what needs row order: the
    query, None where it is refused, or the `tie_free` query of `TIE_FREE`.
    It parses as `read` SQL (sqlglot)."""
    plan = json.loads(written_plan(to_substrait_json(case.build())))
    if engine in REFUSED.get(case.label, {}):
        with pytest.raises(Unsupported, match=REFUSED[case.label][engine]):
            plan_sql(plan, dialect)
        if case.label not in TIE_FREE:
            return None
        sql = plan_sql(plan, dialect, tie_free=True)
    else:
        sql = plan_sql(plan, dialect)
    sqlglot.parse_one(sql, read=read)
    return sql


@pytest.mark.backend("snowflake")
@pytest.mark.parametrize("case", VERIFIED, ids=lambda c: c.label)
def test_snowflake_sql(case):
    engine_sql(case, "snowflake", SNOWFLAKE, "snowflake")


@pytest.mark.backend("spark")
@pytest.mark.parametrize("case", VERIFIED, ids=lambda c: c.label)
def test_spark_sql(case):
    engine_sql(case, "spark", SPARK, "spark")


@pytest.mark.backend("spark")
@settings(max_examples=6, deadline=None, suppress_health_check=list(HealthCheck))
@given(data=tables())
def test_spark_agrees_with_duckdb(con, data):
    """Every case on one drawn pair of tables: one test, so one JVM."""
    from spark_session import put_tables, query

    put_tables(data)
    for name, table in data.items():
        put_table(con, name, table)
    for case in VERIFIED:
        sql = engine_sql(case, "spark", SPARK, "spark")
        if sql is None:
            continue
        plan = written_plan(to_substrait_json(case.build()))
        try:
            duck = rows(run_plan(con, plan, "duckdb"))
        except duckdb.Error:
            # A runtime error of `SubstraitLean/Safety.lean`: Spark raises too.
            with pytest.raises(Exception, match="(?i)sverify|overflow|cast"):
                query(sql)
            continue
        got = query(sql)
        root = parse_plan(json.loads(plan)).root
        ordered = order_matters(root) and case.label not in TIE_FREE
        assert same(got, duck) if ordered else canonical(got) == canonical(duck), case.label


def test_connections_share_one_duckdb_database():
    """Connections keep their own tables but start no threads of their own:
    a connection is freed only by the cyclic garbage collector, and a DuckDB
    database per connection left one thread pool each until then."""
    psutil = pytest.importorskip("psutil")
    from sverify import connect
    from sverify.engines import table_rows
    from sverify_dev.examples import create_tables

    a, b = connect(), connect()
    create_tables(a, [(1, "ada", 3)])
    create_tables(b, [(2, "bob", 5)])
    assert table_rows(a, "orders") == [(1, "ada", 3)]
    assert table_rows(b, "orders") == [(2, "bob", 5)]
    before = psutil.Process().num_threads()
    cons = [connect() for _ in range(20)]
    for con in cons:
        create_tables(con, [(1, "ada", 3)])
        con.table("orders").count().execute()
    assert psutil.Process().num_threads() - before < 10
