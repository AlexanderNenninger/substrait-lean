"""Rewrites from contracts (`SubstraitLean/Semantic.lean`): the report's
`optimized` plan gives the same rows as the transformation on data that meets
the preconditions (`Rel.optimize_sound`), and is simpler."""

import json

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import duckdb_engine, polars_engine
from sverify.contracts import violations
from sverify.engine import connect, plan_json, run_checker
from sverify.examples import orders
from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB
from sverify.testing import canonical

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"a": "int64", "b": "int64"}, name="t")
KEYED = {"t": [sv.unique("a")]}

SETTINGS = settings(
    max_examples=25,
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)

# Each query, and the rewrite the key `a` allows.
REWRITTEN = [
    (T.distinct(), "DISTINCT on a key"),
    (T.select("a").distinct(), "DISTINCT on a key"),
    (T.filter(T.b > 0).select("b", "a").distinct(), "DISTINCT on a key"),
    (T.group_by("b").agg(n=T.a.nunique()), "DISTINCT aggregate of a key"),
    (T.group_by(["a", (T.b + 1).name("c")]).agg(), "GROUP BY a key"),
]


def has_aggregate(plan: dict) -> bool:
    return '"aggregate":' in json.dumps(plan)


@pytest.mark.parametrize(("expr", "rewrite"), REWRITTEN)
def test_keys_rewrite(expr, rewrite):
    report = sv.verify(expr, requires=KEYED)
    assert rewrite in report.rewrites


@pytest.mark.parametrize(("expr", "rewrite"), REWRITTEN)
def test_without_keys_nothing_is_rewritten(expr, rewrite):
    report = sv.verify(expr)
    assert report.rewrites == []


@pytest.mark.parametrize("expr", [T.distinct(), T.select("a").distinct(), REWRITTEN[4][0]])
def test_rewritten_plan_has_no_aggregate(expr):
    report = sv.verify(expr, requires=KEYED)
    assert has_aggregate(json.loads(plan_json(connect(), expr)))
    assert report.optimized is not None and not has_aggregate(report.optimized)
    assert "DISTINCT" not in to_sql(report.optimized, DUCKDB).upper()


def test_count_distinct_becomes_count():
    report = sv.verify(T.group_by("b").agg(n=T.a.nunique()), requires=KEYED)
    assert report.optimized is not None
    assert "DISTINCT" not in to_sql(report.optimized, DUCKDB).upper()


def test_key_on_another_column_does_not_rewrite():
    report = sv.verify(T.select("b").distinct(), requires=KEYED)
    assert report.rewrites == []


keyed_rows = st.lists(st.integers(-5, 5), max_size=20).flatmap(
    lambda bs: st.permutations(range(len(bs))).map(lambda a: list(zip(a, bs, strict=True)))
)


@pytest.mark.parametrize(("expr", "rewrite"), REWRITTEN)
@SETTINGS
@given(rows=keyed_rows)
def test_optimized_runs_agree(expr, rewrite, rows):
    tables = {
        "t": pa.table(
            {"a": [r[0] for r in rows], "b": [r[1] for r in rows]},
            schema=pa.schema([("a", pa.int64()), ("b", pa.int64())]),
        )
    }
    report = sv.verify(expr, requires=KEYED)
    want = canonical(
        tuple(r.values()) for r in duckdb_engine.run(plan_json(connect(), expr), tables).to_pylist()
    )
    assert report.optimized is not None
    for run in (duckdb_engine.run, polars_engine.run):
        got = run(report.optimized, tables)
        assert canonical(tuple(r.values()) for r in got.to_pylist()) == want


# Filters the contract implies (#78).

BOUNDED = {"t": [_.a >= 1, _.b.notnull()]}


@pytest.mark.parametrize(
    "expr",
    [
        T.filter(T.a >= 0),
        T.filter(T.b.notnull(), T.a > 0).select("b"),
        T.filter((T.a + 1) > 1),
    ],
)
def test_implied_filter_goes(expr):
    report = sv.verify(expr, requires=BOUNDED)
    assert report.rewrites == ["filter implied by the contract"]
    assert report.optimized is not None
    assert "WHERE" not in to_sql(report.optimized, DUCKDB).upper()


def test_filter_the_contract_rules_out_is_empty():
    report = sv.verify(T.filter(T.a < 0).select("b"), requires=BOUNDED)
    assert report.rewrites == ["filter the contract rules out"]
    tables = {"t": pa.table({"a": [1, 2], "b": [3, 4]})}
    assert report.optimized is not None
    assert duckdb_engine.run(report.optimized, tables).num_rows == 0


def test_filter_on_other_rows_stays():
    report = sv.verify(T.filter(T.a >= 2), requires=BOUNDED)
    assert report.rewrites == []


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount >= 0, _.amount.notnull()])
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(requires={"t": [_.amount.notnull()]}, ensures=[_.amount.notnull()])
def recheck(t):
    # A defensive re-check of what `paid` guarantees.
    return t.filter(t.amount.notnull(), t.amount >= 0)


def test_composed_pipeline_drops_the_downstream_check():
    recheck(paid(orders))
    report = recheck.last_report
    assert report is not None and report.proved
    assert report.rewrites == ["filter implied by the contract"]


# Left joins that are inner joins (#77).

ORDERS = ibis.table({"id": "int64", "cust": "int64", "amount": "int64"}, name="o")
CUSTOMERS = ibis.table({"cid": "int64", "name": "string"}, name="c")
LEFT = ORDERS.left_join(CUSTOMERS, ORDERS.cust == CUSTOMERS.cid).select(
    ORDERS.id, ORDERS.amount, CUSTOMERS.name
)
FK = {"o": [_.cust.notnull(), sv.references("cust", "c", "cid")]}


def test_left_join_on_a_foreign_key_is_inner():
    report = sv.verify(LEFT, requires=FK)
    assert report.rewrites == ["left join on a foreign key"]
    assert report.optimized is not None
    assert "LEFT" not in to_sql(report.optimized, DUCKDB).upper()


@pytest.mark.parametrize(
    "requires",
    [
        {"o": [sv.references("cust", "c", "cid")]},
        {"o": [_.cust.notnull()]},
        {"o": [_.cust.notnull(), sv.references("amount", "c", "cid")]},
    ],
)
def test_left_join_stays_without_a_not_null_foreign_key(requires):
    assert sv.verify(LEFT, requires=requires).rewrites == []


def test_left_join_under_a_null_rejecting_filter_is_inner():
    expr = (
        ORDERS.left_join(CUSTOMERS, ORDERS.cust == CUSTOMERS.cid)
        .filter(CUSTOMERS.name.notnull())
        .select(ORDERS.id, CUSTOMERS.name)
    )
    report = sv.verify(expr)
    assert report.rewrites == ["left join under a filter rejecting NULLs"]


def test_left_join_under_another_filter_stays():
    expr = (
        ORDERS.left_join(CUSTOMERS, ORDERS.cust == CUSTOMERS.cid)
        .filter(CUSTOMERS.name.isnull())
        .select(ORDERS.id)
    )
    assert sv.verify(expr).rewrites == []


def test_rewritten_left_join_is_incremental():
    """`Rel.Incremental` excludes left joins; the inner join is maintainable."""
    report = sv.verify(LEFT, requires=FK)
    assert run_checker(("--delta",), plan_json(connect(), LEFT))[0] == 3
    assert run_checker(("--delta",), json.dumps(report.optimized))[0] == 0


fk_tables = st.lists(st.text("ab", max_size=2), min_size=1, max_size=5).flatmap(
    lambda names: st.lists(
        st.tuples(st.integers(-3, 3), st.integers(0, len(names) - 1)), max_size=15
    ).map(lambda orders: (names, orders))
)


@SETTINGS
@given(data=fk_tables)
def test_left_join_on_a_foreign_key_runs_agree(data):
    names, rows = data
    tables = {
        "o": pa.table(
            {
                "id": list(range(len(rows))),
                "cust": [r[1] for r in rows],
                "amount": [r[0] for r in rows],
            },
            schema=pa.schema([("id", pa.int64()), ("cust", pa.int64()), ("amount", pa.int64())]),
        ),
        "c": pa.table(
            {"cid": list(range(len(names))), "name": names},
            schema=pa.schema([("cid", pa.int64()), ("name", pa.string())]),
        ),
    }
    report = sv.verify(LEFT, requires=FK)
    assert report.optimized is not None
    want = canonical(
        tuple(r.values()) for r in duckdb_engine.run(plan_json(connect(), LEFT), tables).to_pylist()
    )
    for run in (duckdb_engine.run, polars_engine.run):
        got = run(report.optimized, tables)
        assert canonical(tuple(r.values()) for r in got.to_pylist()) == want


def test_foreign_keys_are_checked_on_the_data():
    con = sv.connect()
    sv.create_table(con, "c", CUSTOMERS.schema(), [(1, "x")])
    sv.create_table(con, "o", ORDERS.schema(), [(1, 1, 5), (2, None, 6), (3, 2, 7)])
    assert violations(con.table("o"), sv.references("cust", "c", "cid")) == 1
