"""Guard elimination (`analysis/Sverify/Analysis/Guards.lean`): when a contract report is
`guard_free`, the SQL and the Polars plan without run-time checks give the
same result as with them, on data that meets the preconditions."""

import json

import duckdb
import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, plan_json, written_plan
from sverify.sql import Unsupported, to_sql
from sverify.sql.snowflake import SNOWFLAKE
from sverify.testing import canonical
from sverify_duckdb import engine as duckdb_engine
from sverify_duckdb.dialect import DUCKDB
from sverify_polars import engine as polars_engine

pytestmark = pytest.mark.backend("duckdb")

T = ibis.table({"a": "int64", "b": "int64"}, name="t")
U = ibis.table({"a": "int64", "d": "int64"}, name="u")
BOUNDED = {"t": [_.a >= 0, _.a <= 1000, _.b >= 1, _.b <= 100]}

GUARD_FREE = [
    T.select(q=T.a // T.b, m=T.a % T.b, s=T.a * 3 + T.b),
    T.filter(T.a % T.b == 0).select(x=T.a - T.b),
    T.group_by("b").agg(n=T.a.count(), s=(T.a * 3).sum()),
    T.select(p=T.a * T.b, q=(T.a - 500) * (T.b - 50)),
]

SETTINGS = settings(
    max_examples=25,
    deadline=None,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)

bounded_rows = st.lists(st.tuples(st.integers(0, 1000), st.integers(1, 100)), max_size=20)


def plan(expr: ibis.Table) -> dict:
    return json.loads(plan_json(connect(), expr))


@pytest.mark.parametrize("expr", GUARD_FREE)
def test_preconditions_make_plans_guard_free(expr):
    assert sv.verify(expr, requires=BOUNDED)._guard_free


@pytest.mark.parametrize("expr", GUARD_FREE)
def test_without_preconditions_guards_stay(expr):
    assert not sv.verify(expr, on_inferred="off")._guard_free


def test_unguarded_sql_has_no_row_checks():
    p = plan(GUARD_FREE[0])
    assert "error(" in to_sql(p, DUCKDB)
    assert "error(" not in to_sql(p, DUCKDB, guards=False)
    assert "sverify: integer overflow" in to_sql(p, SNOWFLAKE)
    assert "sverify: integer overflow" not in to_sql(p, SNOWFLAKE, guards=False)


def test_product_of_unbounded_columns_keeps_its_guard():
    """`Bound.mul` multiplies the corners of two finite intervals only."""
    report = sv.verify(T.select(p=T.a * T.b), requires={"t": [_.a >= 0, _.b >= 1]})
    assert not report._guard_free


# `a // b` cannot divide by zero; `a * b` may overflow (`b` has no upper bound).
MIXED = T.select(q=T.a // T.b, p=T.a * T.b)
# The filter's remainder runs unchecked, the product above it keeps its check.
MIXED_FILTER = T.filter(T.a % T.b == 0).select(p=T.a * T.b)
MIXED_REQUIRES = {"t": [_.a >= 0, _.a <= 1000, _.b >= 1]}


def test_per_expression_guards():
    """`Rel.evalG_marks`: the division runs unchecked, the product keeps its check."""
    report = sv.verify(MIXED, requires=MIXED_REQUIRES, on_inferred="off")
    assert not report._guard_free and report._unchecked is not None
    p = plan(MIXED)
    checked = to_sql(p, SNOWFLAKE)
    sql = to_sql(p, SNOWFLAKE, unchecked=report._unchecked)
    assert "division by zero" in checked and "division by zero" not in sql
    assert "sverify: integer overflow" in sql


def test_per_expression_guards_below_a_projection():
    report = sv.verify(MIXED_FILTER, requires=MIXED_REQUIRES, on_inferred="off")
    sql = to_sql(plan(MIXED_FILTER), SNOWFLAKE, unchecked=report._unchecked)
    assert "division by zero" not in sql and "sverify: integer overflow" in sql


def test_unchecked_marks_are_checked_against_the_plan():
    report = sv.verify(MIXED, requires=MIXED_REQUIRES, on_inferred="off")
    with pytest.raises(Unsupported, match="another plan"):
        to_sql(plan(GUARD_FREE[1]), DUCKDB, unchecked=report._unchecked)


def test_unchecked_aggregate_keeps_its_sum_check():
    expr = T.group_by("b").agg(s=(T.a // T.b).sum())
    report = sv.verify(expr, requires=BOUNDED)
    sql = to_sql(plan(expr), DUCKDB, unchecked=report._unchecked)
    assert "division by zero" not in sql and "integer overflow in SUM" in sql


@pytest.mark.parametrize("expr", [*GUARD_FREE, MIXED, MIXED_FILTER])
@SETTINGS
@given(rows=bounded_rows)
def test_unchecked_runs_agree(expr, rows):
    tables = {"t": pa.table({"a": [r[0] for r in rows], "b": [r[1] for r in rows]})}
    p = plan(expr)
    requires = MIXED_REQUIRES if any(expr is x for x in (MIXED, MIXED_FILTER)) else BOUNDED
    report = sv.verify(expr, requires=requires, on_inferred="off")
    con = duckdb.connect()
    con.register("t", tables["t"])
    want = canonical(con.execute(to_sql(p, DUCKDB)).fetchall())
    got = con.execute(to_sql(p, DUCKDB, unchecked=report._unchecked)).fetchall()
    assert canonical(got) == want


def test_sum_keeps_its_check():
    """`SUM` may wrap whatever the rows are (`Issue.sumWraps`): it stays checked."""
    report = sv.verify(GUARD_FREE[2], requires=BOUNDED)
    # Assumed to fit, and checked on the data: the check stays.
    assert report._guard_free and [i.kind for i in report.assumed] == ["SUM overflow"]
    assert "integer overflow in SUM" in to_sql(plan(GUARD_FREE[2]), DUCKDB, guards=False)


def test_filtered_right_side_of_a_left_join_keeps_guards():
    """`Rel.HasIssue` sees the rows of `Rel.loose`, which under a left join
    whose right side has a filter are not all the rows (`Rel.looseSub`)."""
    expr = T.left_join(U.filter(U.d > 0), "a").select(x=T.b + 1)
    report = sv.verify(expr, requires=BOUNDED)
    assert not report.issues and not report._guard_free


@pytest.mark.parametrize("expr", GUARD_FREE)
@SETTINGS
@given(rows=bounded_rows)
def test_unguarded_runs_agree(expr, rows):
    tables = {"t": pa.table({"a": [r[0] for r in rows], "b": [r[1] for r in rows]})}
    p = plan_json(connect(), expr)
    want = canonical(tuple(r.values()) for r in duckdb_engine.run(p, tables).to_pylist())
    unguarded = duckdb_engine.run(p, tables, guards=False)
    assert canonical(tuple(r.values()) for r in unguarded.to_pylist()) == want
    w = written_plan(p)
    on_polars = polars_engine.run(w, tables, guards=False)
    assert canonical(tuple(r.values()) for r in on_polars.to_pylist()) == want


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_run_drops_the_discharged_checks(monkeypatch, engine):
    """`Report.run` runs a guard-free plan without its per-row checks on an
    engine whose writer a theorem covers without them, as the checker names it
    (`"guard_free_theorem"`, #1166), once the preconditions are checked on the
    data: Polars (`Rel.polars_sound`). DuckDB keeps every check until its
    writer's theorem lands (#1169); so does a run without the precondition
    check, and a plan that is not guard-free."""
    from sverify import report as report_module

    seen: list[str] = []
    for name in ("run_plan", "run_guard_free"):
        real = getattr(report_module, name)

        def spy(*args, _name=name, _real=real, **kwargs):
            seen.append(_name)
            return _real(*args, **kwargs)

        monkeypatch.setattr(report_module, name, spy)
    con = sv.connect()
    con.put("t", pa.table({"a": [6, 9, 1000], "b": [3, 1, 100]}))
    con.put("u", pa.table({"a": [6], "d": [1]}))
    free = sv.verify(GUARD_FREE[0], requires=BOUNDED)
    covered = (free._engines or {})[engine]["guard_free_theorem"] is not None
    assert covered is (engine == "polars")
    want = free.run(con, engine, check_requires=False).to_pylist()
    assert seen[-1] == "run_plan"
    assert free.run(con, engine).to_pylist() == want
    assert seen[-1] == ("run_guard_free" if covered else "run_plan")
    # Not guard-free (`Rel.looseSub`): every check stays.
    loose = sv.verify(T.left_join(U.filter(U.d > 0), "a").select(x=T.b + 1), requires=BOUNDED)
    assert loose.proved and not loose._guard_free
    loose.run(con, engine)
    assert seen[-1] == "run_plan"


def test_no_writer_runs_without_guards_unless_a_theorem_covers_it():
    from sverify.engine import run_guard_free

    con = sv.connect()
    con.put("t", pa.table({"a": [6], "b": [3]}))
    p = written_plan(plan_json(connect(), GUARD_FREE[0]))
    for engine, theorem in [("duckdb", "Rel.duckdb_guardFree_sound"), ("polars", "Rel.other")]:
        with pytest.raises(ValueError, match="no theorem covers"):
            run_guard_free(con, p, engine, theorem)
    assert run_guard_free(con, p, "polars", "Rel.polars_sound").num_rows == 1
