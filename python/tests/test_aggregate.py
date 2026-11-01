"""Aggregation: `GROUP BY` with `COUNT`, `SUM`, `MIN`, `MAX`, `AVG`.

* Lean's semantics (`aggregateEval`) agrees with DataFusion on random tables,
  including NULLs, empty tables (a global aggregate still gives one row),
  `DISTINCT` and `FILTER (WHERE …)` measures, and `HAVING`.
* Polars and DuckDB, which run the plan Lean writes, give Lean's rows, with
  doubles added in Lean's list order, so the same bits.
* Integer `SUM` wraps around in DataFusion, so it comes with a warning; the
  engines raise instead.
* The grouping columns are a key of the result, and contracts see through
  `COUNT`, `MIN`/`MAX` and the sign of a `SUM`.
"""

import json
import math

import duckdb
import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify import polars_engine
from sverify.contracts import decode_double
from sverify.engine import (
    connect,
    create_table,
    run_plan,
    run_sql,
    substrait_json,
    written_plan,
)
from sverify_dev.examples import orders
from sverify.testing import canonical, inline_tables, lean_values

T = ibis.schema({"a": "int64", "b": "int64", "s": "string"})
F = ibis.schema({"k": "int64", "x": "float64"})

small = st.one_of(st.none(), st.integers(-2, 3))
t_rows = st.lists(st.tuples(small, small, st.sampled_from(["x", "y", "é", None])), max_size=7)
doubles = st.one_of(
    st.none(),
    st.sampled_from([0.5, 1.0, 2.25, -3.0, math.inf, -math.inf, math.nan]),
)
f_rows = st.lists(st.tuples(st.one_of(st.none(), st.integers(0, 2)), doubles), max_size=7)

EXACT = [
    "SELECT a, COUNT(*), SUM(b), MIN(b), MAX(b) FROM t GROUP BY a",
    "SELECT COUNT(*), COUNT(b), SUM(b), MIN(a), MAX(s) FROM t",
    "SELECT a, COUNT(DISTINCT b), SUM(DISTINCT b) FROM t GROUP BY a",
    "SELECT a, SUM(b) FILTER (WHERE b > 0), COUNT(*) FILTER (WHERE s = 'x') FROM t GROUP BY a",
    "SELECT a, COUNT(*) AS n FROM t GROUP BY a HAVING COUNT(*) > 1",
    "SELECT a + b, COUNT(*) FROM t GROUP BY a + b",
    "SELECT s, a, MIN(b) FROM t GROUP BY s, a",
    "SELECT s, MIN(s), MAX(s), COUNT(DISTINCT a) FROM t GROUP BY s",
    "SELECT a, MAX(b > 0), MIN(b > 0) FROM t GROUP BY a",
    "SELECT DISTINCT a + 1 FROM t",
]


def datafusion_rows(sql: str, schema: ibis.Schema, rows: list) -> list[tuple]:
    con = connect()
    create_table(con, "t", schema, rows)
    out = run_sql(con, sql)
    return list(zip(*(c.to_pylist() for c in out.columns), strict=True))


def run(sql: str, schema: ibis.Schema, rows: list) -> tuple[list[tuple], list[tuple]]:
    expected = datafusion_rows(sql, schema, rows)
    con = connect()
    create_table(con, "t", schema, rows)
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"t": rows})
    return lean_values(json.dumps(plan)), expected


@pytest.mark.parametrize("sql", EXACT)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows)
def test_aggregates_match_datafusion(sql, t):
    got, expected = run(sql, T, t)
    assert canonical(got) == canonical(expected)


def engine_rows(sql: str, schema: ibis.Schema, rows: list) -> dict[str, list[tuple]]:
    con = connect()
    create_table(con, "t", schema, rows)
    plan = written_plan(substrait_json(con, sql))
    return {
        e: [tuple(r.values()) for r in run_plan(con, plan, e).to_pylist()]
        for e in ("polars", "duckdb")
    }


@pytest.mark.parametrize("sql", EXACT)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows)
def test_engines_match_datafusion(sql, t):
    out = engine_rows(sql, T, t)
    assert canonical(out["polars"]) == canonical(out["duckdb"])
    assert canonical(out["polars"]) == canonical(datafusion_rows(sql, T, t))


def test_engines_raise_where_sum_wraps():
    rows = [(1, 2**62, "x"), (1, 2**62, "y")]
    sql = "SELECT a, SUM(b) FROM t GROUP BY a"
    with pytest.raises(polars_engine.IntegerOverflow):
        engine_rows(sql, T, rows)
    con = connect()
    create_table(con, "t", T, rows)
    with pytest.raises(duckdb.Error, match="overflow in SUM"):
        run_plan(con, written_plan(substrait_json(con, sql)), "duckdb")


def close(x: object, y: object) -> bool:
    """Lean prints doubles with six decimals."""
    if isinstance(x, float) and isinstance(y, float):
        if math.isnan(x) or math.isnan(y):
            return math.isnan(x) and math.isnan(y)
        return x == y or math.isclose(x, y, rel_tol=1e-6, abs_tol=1e-6)
    return x == y


FLOATS = [
    "SELECT k, SUM(x), AVG(x), COUNT(x) FROM t GROUP BY k",
    "SELECT x, COUNT(*) FROM t GROUP BY x",
    "SELECT k, AVG(k) FROM t GROUP BY k",
    "SELECT AVG(x), SUM(x) FROM t",
]


@pytest.mark.parametrize("sql", FLOATS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=f_rows)
def test_double_aggregates_match_datafusion(sql, t):
    got, expected = run(sql, F, t)
    # Lean prints tiny doubles (±0.0) as their codes.
    floats = {i for row in expected for i, v in enumerate(row) if isinstance(v, float)}
    got = [
        tuple(
            decode_double(v) if i in floats and isinstance(v, int) else v for i, v in enumerate(row)
        )
        for row in got
    ]
    # Group keys are exact: sort both by them (rendered), then compare loosely.
    got, expected = sorted(got, key=repr), sorted(expected, key=repr)
    assert len(got) == len(expected)
    for g, e in zip(got, expected, strict=True):
        assert all(close(x, y) for x, y in zip(g, e, strict=True)), (g, e)


@pytest.mark.parametrize("sql", FLOATS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=f_rows)
def test_engines_add_doubles_in_lean_order(sql, t):
    """Both engines add in Lean's list order, so they agree bit for bit; with
    DataFusion, whose order is its own, only approximately."""
    out = engine_rows(sql, F, t)
    assert canonical(out["polars"]) == canonical(out["duckdb"])  # bit for bit
    expected = sorted(datafusion_rows(sql, F, t), key=repr)
    got = sorted(out["polars"], key=repr)
    assert len(got) == len(expected)
    for g, e in zip(got, expected, strict=True):
        assert all(close(x, y) for x, y in zip(g, e, strict=True)), (g, e)


def test_min_and_max_of_doubles_are_refused():
    # DataFusion's grouped MIN of a group of +∞ is the largest finite double.
    expected = datafusion_rows("SELECT k, MIN(x) FROM t GROUP BY k", F, [(1, math.inf)])
    assert expected == [(1, 1.7976931348623157e308)]
    readings = ibis.table({"k": "int64", "x": "float64"}, name="readings")
    with pytest.raises(ValueError, match="min of doubles is not supported"):
        sv.verify(readings.group_by("k").aggregate(m=readings.x.min()))


def test_integer_sum_wraps_around_in_datafusion():
    # 2⁶³ - 1 + 1 wraps to -2⁶³ in DataFusion; Lean's sum is exact, so the
    # checker warns.
    rows = [(2**63 - 1, None, None), (1, None, None)]
    assert datafusion_rows("SELECT SUM(a) FROM t", T, rows) == [(-(2**63),)]
    report = sv.verify(orders.aggregate(total=orders.amount.sum()))
    assert [str(i) for i in report.issues] == ["may wrap around: $2"]
    assert report.proved  # a warning, not an error


by_customer = orders.group_by("customer").aggregate(
    n=orders.count(), total=orders.amount.sum(), top=orders.amount.max()
)


def test_aggregate_postconditions_are_proved():
    report = sv.verify(
        by_customer,
        requires={"orders": [_.amount >= 0]},
        ensures=[
            _.n >= 0,
            _.n.notnull(),
            _.total.isnull() | (_.total >= 0),
            _.top.isnull() | (_.top >= 0),
            sv.unique("customer"),
        ],
    )
    assert report.proved, str(report)
    assert report.facts["n"] == "an integer ≥ 0"
    assert report.facts["top"] == "an integer ≥ 0 or NULL"


def test_sum_has_no_upper_bound():
    report = sv.verify(
        by_customer,
        requires={"orders": [_.amount <= 10]},
        ensures=[_.top.isnull() | (_.top <= 10), _.total.isnull() | (_.total <= 10)],
    )
    assert [c.proved for c in report.ensures] == [True, False]


def test_a_global_aggregate_has_one_row():
    report = sv.verify(orders.aggregate(n=orders.count()), ensures=[sv.unique()])
    assert report.proved, str(report)


def test_errors_in_measures_are_reported():
    expr = orders.group_by("customer").aggregate(q=(100 // orders.amount).sum())
    report = sv.verify(expr)
    assert any(i.kind == "division by zero" for i in report.errors)
    guarded = (
        orders.filter(orders.amount != 0)
        .group_by("customer")
        .aggregate(q=(100 // orders.amount).max())
    )
    assert not sv.verify(guarded).errors
