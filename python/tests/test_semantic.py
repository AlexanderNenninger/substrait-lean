"""Rewrites from contracts (`SubstraitLean/Semantic.lean`): the report's
`optimized` plan gives the same rows as the transformation on data that meets
the preconditions (`Rel.optimize_sound`), and is simpler."""

import json

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify import duckdb_engine, polars_engine
from sverify.engine import connect, plan_json
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
