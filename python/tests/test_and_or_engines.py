"""D50 on the engines: the lifted plan runs where the guard is FALSE, on DuckDB and on
Polars (collected without common-subexpression elimination, which would hoist the
guarded operand's copies, `polars-exec-cse-hoist`)."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify.engine import connect, put_table
from sverify.errors import UnverifiedRunWarning

pytestmark = pytest.mark.backend("duckdb")

ENGINES = ["duckdb", "polars", "spark"]
FLT = ibis.table({"x": "float64"}, name="t")
INT = ibis.table({"x": "int64"}, name="t")
STR = ibis.table({"s": "string"}, name="t")


def _run(sql, table, data, engine="duckdb"):
    """The verified report, and the target to run it on: a DuckDB connection, which
    Polars reads too, or the Spark session with the table in it."""
    report = sv.verify(sql, tables={"t": table}, on_inferred="off")
    con = connect()
    put_table(con, "t", pa.table(data))
    if engine == "spark":
        import spark_session

        spark_session.put_tables({"t": pa.table(data)})
        return report, con, spark_session.session()
    return report, con, engine


@pytest.mark.parametrize("engine", ENGINES)
def test_a_cast_guarded_by_a_range_runs_where_the_guard_is_false(engine):
    """A float-to-integer cast raises outside the integer range; the range guard
    keeps it from running there. The analysis does not yet narrow a bound through
    the chain's `IS NOT FALSE` (it proves a zero guard, not an interval), so the
    plan runs unverified: the test is about the engine, which must take the guard."""
    sql = "SELECT x FROM t WHERE x BETWEEN -1000000.0 AND 1000000.0 AND CAST(x AS BIGINT) > 1"
    report, con, target = _run(sql, FLT, {"x": [1e30, 5.5, -3.0, 2.5]}, engine)
    with pytest.warns(UnverifiedRunWarning):
        got = report.run(con, target, unverified=True)
    assert got.column("x").to_pylist() == [5.5, 2.5]


def test_a_cast_guarded_by_a_pattern_runs_where_the_guard_is_false():
    """A string-to-integer cast raises on text that is not a number (DuckDB only:
    the other engines refuse it, D49). The analysis has no domain bound for it, so
    the plan runs unverified."""
    sql = "SELECT s FROM t WHERE s LIKE '1%' AND CAST(s AS BIGINT) > 1"
    report, con, target = _run(sql, STR, {"s": ["12", "ab", "5", "10"]})
    with pytest.warns(UnverifiedRunWarning):
        got = report.run(con, target, unverified=True)
    assert got.column("s").to_pylist() == ["12", "10"]


@pytest.mark.parametrize("engine", ENGINES)
def test_an_aggregate_filter_runs_where_the_guard_is_false(engine):
    """`polars-exec-when-eager` excludes a branch under `group_by().agg`; the
    guard of the filter still holds there."""
    sql = "SELECT COUNT(*) FILTER (WHERE x <> 0 AND 10 // x > 1) AS c FROM t"
    report, con, target = _run(sql, INT, {"x": [0, 2, 5]}, engine)
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert report.run(con, target).column("c").to_pylist() == [2]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_window_argument_runs_where_the_guard_is_false(engine):
    """The guard inside a window's argument (`over()`, which the masking fact
    excludes) still holds."""
    sql = (
        "SELECT x, MAX(CASE WHEN x <> 0 AND 10 // x > 1 THEN x END) "
        "OVER (ORDER BY x ROWS BETWEEN UNBOUNDED PRECEDING AND UNBOUNDED FOLLOWING) AS m FROM t"
    )
    report, con, target = _run(sql, INT, {"x": [0, 2, 5]}, engine)
    assert report.verdict == sv.Verdict.PROVED, str(report)
    got = report.run(con, target).to_pylist()
    assert sorted((r["x"], r["m"]) for r in got) == [(0, 5), (2, 5), (5, 5)]


@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(st.integers(-3, 3), st.integers(-9, 9)), max_size=8))
def test_the_lifted_plan_agrees_with_the_eager_one_where_that_returns(rows):
    """The lifted plan returns the rows an SQL reader expects on every input; the
    eager reading (`semantics="duckdb"`) returns the same where it returns."""
    t = ibis.table({"qty": "int64", "total": "int64"}, name="t")
    sql = "SELECT qty, total FROM t WHERE qty <> 0 AND total // qty > 1"
    want = [{"qty": q, "total": v} for q, v in rows if q != 0 and v // q > 1]
    con = connect()
    schema = pa.schema([("qty", pa.int64()), ("total", pa.int64())])
    cols = {"qty": [q for q, _ in rows], "total": [v for _, v in rows]}
    put_table(con, "t", pa.table(cols, schema=schema))
    lifted = sv.verify(sql, tables={"t": t}, on_inferred="off")
    assert [e.kind for e in lifted.errors] == ["overflow"]  # `MIN // -1`; the guard is not it
    assert lifted.run(con, "duckdb", unverified=True).to_pylist() == want
    if all(q != 0 for q, _ in rows):
        eager = sv.verify(sql, tables={"t": t}, on_inferred="off", semantics="duckdb")
        assert eager.run(con, "duckdb", unverified=True).to_pylist() == want


# A plain operand (`is_plain`, `plan_json.py`) raises on no row and needs no precondition.
PLAIN = ibis.table(
    {
        "i": "int64",
        "f": "float64",
        "s": "string",
        "d": "date",
        "n": "decimal(10, 2)",
    },
    name="t",
)


def _leaf():
    t = PLAIN
    return st.one_of(
        st.builds(lambda k: t.i < k, st.integers(-5, 5)),
        st.builds(lambda k: t.i == k, st.integers(-5, 5)),
        st.builds(lambda k: t.f < k, st.floats(-5, 5, allow_nan=False)),
        st.builds(lambda k: t.s == k, st.sampled_from(["a", "b", ""])),
        st.builds(lambda ks: t.s.isin(ks), st.lists(st.sampled_from(["a", "b", "c"]), min_size=1)),
        st.builds(lambda ks: t.i.isin(ks), st.lists(st.integers(-3, 3), min_size=1, max_size=3)),
        st.just(t.d.isnull()),
        st.builds(lambda k: t.n > k, st.decimals(-5, 5, places=2)),
        st.just(t.i < t.i),
    )


plain_exprs = st.recursive(
    _leaf(),
    lambda c: st.one_of(
        st.builds(lambda a, b: a & b, c, c),
        st.builds(lambda a, b: a | b, c, c),
        st.builds(lambda a: ~a, c),
    ),
    max_leaves=6,
)


@settings(max_examples=60, deadline=None)
@given(e=plain_exprs)
def test_a_plain_operand_has_no_error_and_no_inferred_precondition(e):
    report = sv.verify(PLAIN.select(x=e), on_inferred="off")
    assert report.errors == [], str(report)
    assert not report.needs
