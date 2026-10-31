"""Sharded evaluation (`sverify.partition`, `SubstraitLean/Partition.lean`):
the combined result of a plan run shard by shard equals its result on all
the data, and plans whose result would depend on the split are refused."""

import json

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify import polars_engine
from sverify.engine import connect, create_table, run_plan, substrait_json, written_plan
from sverify.partition import NotShardable, run_sharded, split
from sverify.testing import canonical

pytestmark = pytest.mark.backend("polars")

R = ibis.schema({"a": "int64", "b": "int64", "c": "int64"})
S = ibis.schema({"b": "int64", "d": "string"})
S_ROWS = [(0, "zero"), (1, "one"), (2, "two"), (2, "deux")]

LINEAR = [
    "SELECT a, b + 1 AS x FROM r WHERE a > 0",
    "SELECT r.a, s.d FROM r JOIN s ON r.b = s.b",
    "SELECT r.a, s.d FROM r LEFT JOIN s ON r.b = s.b",
    "SELECT a FROM r WHERE b IN (SELECT b FROM s)",
]
TWO_PHASE = [
    "SELECT b, COUNT(*) AS n, SUM(a) AS s, MIN(c) AS lo, MAX(c) AS hi FROM r GROUP BY b",
    "SELECT COUNT(a) AS n, SUM(a) AS s, MAX(c) AS hi FROM r",
    "SELECT b, SUM(a) * 2 AS s2 FROM r WHERE c > 0 GROUP BY b HAVING SUM(a) > 3",
    "SELECT s.d, COUNT(*) AS n, MIN(r.a) AS lo FROM r JOIN s ON r.b = s.b GROUP BY s.d",
]
REFUSED = [
    ("SELECT AVG(CAST(a AS DOUBLE)) AS m FROM r", "not associative"),
    ("SELECT COUNT(DISTINCT a) AS n FROM r", "DISTINCT values"),
    ("SELECT x.a FROM r AS x JOIN r AS y ON x.b = y.b", "co-partitioning"),
    ("SELECT a FROM r ORDER BY a LIMIT 3", "FETCH"),
    ("SELECT a, ROW_NUMBER() OVER (PARTITION BY b ORDER BY a) AS k FROM r", "window"),
]

SETTINGS = settings(
    max_examples=20,
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)


def plan_of(sql: str) -> str:
    con = connect()
    create_table(con, "r", R)
    create_table(con, "s", S)
    return substrait_json(con, sql)


def reference(plan: str, rows: list[tuple]) -> list[str]:
    """The plan on all the data, on Polars."""
    con = connect()
    create_table(con, "r", R, rows)
    create_table(con, "s", S, S_ROWS)
    got = run_plan(con, written_plan(plan), "polars")
    return canonical(tuple(r.values()) for r in got.to_pylist())


def arrow(rows: list[tuple]) -> pa.Table:
    return pa.table({n: pa.array([r[i] for r in rows], pa.int64()) for i, n in enumerate("abc")})


small = st.integers(-3, 3)
r_rows = st.lists(st.tuples(small, st.integers(0, 3), small | st.none()), max_size=12)
#: Rows of `r`, and the shard (of 4) each one goes to.
rows_and_shards = r_rows.flatmap(
    lambda rows: st.tuples(
        st.just(rows), st.lists(st.integers(0, 3), min_size=len(rows), max_size=len(rows))
    )
)


@pytest.mark.parametrize("sql", LINEAR + TWO_PHASE)
@SETTINGS
@given(data=rows_and_shards)
def test_sharded_equals_whole(sql: str, data):
    rows, where = data
    plan = plan_of(sql)
    pairs = list(zip(rows, where, strict=True))
    shards = [{"r": arrow([row for row, k in pairs if k == i])} for i in range(4)]
    s_table = pa.table({"b": [b for b, _ in S_ROWS], "d": [d for _, d in S_ROWS]})
    got = run_sharded(plan, shards, sharded=["r"], broadcast={"s": s_table})
    assert canonical(tuple(r.values()) for r in got.to_pylist()) == reference(plan, rows)


@pytest.mark.parametrize("sql", LINEAR)
def test_linear_plans_are_concatenated(sql: str):
    s = split(plan_of(sql), ["r"])
    assert s.mode == "linear"
    assert "__partials" in json.dumps(s.combine)


@pytest.mark.parametrize("sql", TWO_PHASE)
def test_aggregates_run_in_two_phases(sql: str):
    assert split(plan_of(sql), ["r"]).mode == "two_phase"


@pytest.mark.parametrize(("sql", "why"), REFUSED)
def test_refused_with_a_reason(sql: str, why: str):
    with pytest.raises(NotShardable, match=why):
        split(plan_of(sql), ["r"])


def test_broadcast_tables_are_not_split():
    """A plan that reads only broadcast tables would be repeated on every shard."""
    with pytest.raises(NotShardable, match="no sharded table"):
        split(plan_of("SELECT b FROM s"), ["r"])


def test_partial_sum_may_overflow_where_the_total_does_not():
    """Integer sums are checked in each phase: shards of large values of
    opposite signs fail instead of giving a wrong result."""
    plan = plan_of("SELECT SUM(a) AS s FROM r")
    big = 2**62
    rows = [(big, 0, 0), (big, 0, 0), (-big, 0, 0), (-big, 0, 0)]
    assert reference(plan, rows) == canonical([(0,)])
    shards = [{"r": arrow(rows[:2])}, {"r": arrow(rows[2:])}]
    with pytest.raises(polars_engine.IntegerOverflow):
        run_sharded(plan, shards, sharded=["r"])
    # Interleaved, every partial sum fits.
    shards = [{"r": arrow(rows[::2])}, {"r": arrow(rows[1::2])}]
    got = run_sharded(plan, shards, sharded=["r"])
    assert got.to_pylist() == [{"s": 0}]
