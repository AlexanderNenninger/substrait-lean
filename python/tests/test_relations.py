"""Sorts, semi/anti/outer joins, `IN` subqueries and `DISTINCT` set operations.

* Lean's semantics (`Rel.eval`) agrees with DataFusion on random tables,
  including NULLs: as bags, and for sorts also in the order of the sort keys
  (ties may come out either way).
* `FULL OUTER JOIN`, `IN (subquery)` and `IS NOT DISTINCT FROM` are parser
  rewrites (trusted code); these tests check them.
* Contracts and runtime errors carry through the new operators, and sorted
  views are maintained incrementally.
"""

import json

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import connect, create_table, run_sql, substrait_json
from sverify.testing import canonical, inline_tables, lean_values

T = ibis.schema({"a": "int64", "b": "int64"})
U = ibis.schema({"a": "int64", "s": "string"})

small = st.one_of(st.none(), st.integers(-2, 3))
t_rows = st.lists(st.tuples(small, small), max_size=7)
u_rows = st.lists(st.tuples(small, st.sampled_from(["x", "y", None])), max_size=5)

BAGS = [
    "SELECT * FROM t LEFT SEMI JOIN u ON t.a = u.a",
    "SELECT * FROM t LEFT ANTI JOIN u ON t.a = u.a",
    "SELECT * FROM t LEFT SEMI JOIN u ON t.b < u.a",
    "SELECT * FROM t RIGHT SEMI JOIN u ON t.a = u.a",
    "SELECT * FROM t FULL OUTER JOIN u ON t.a = u.a",
    "SELECT * FROM t FULL OUTER JOIN u ON t.a = u.a AND t.b > 0",
    "SELECT * FROM t WHERE a IN (SELECT a FROM u) AND b > 0",
    "SELECT * FROM t WHERE b IN (SELECT a FROM u WHERE s = 'x')",
    "SELECT DISTINCT a FROM t",
    "SELECT DISTINCT * FROM t",
    "SELECT a FROM t UNION SELECT a FROM u",
    "SELECT a FROM t INTERSECT SELECT a FROM u",
    "SELECT a FROM t EXCEPT SELECT a FROM u",
    "SELECT a, b FROM t ORDER BY a DESC NULLS FIRST, b",
]


def both(sql: str, t: list, u: list) -> tuple[list, list]:
    con = connect()
    create_table(con, "t", T, t)
    create_table(con, "u", U, u)
    # Column-wise: `SELECT *` over both tables has two columns named `a`.
    out = run_sql(con, sql)
    expected = list(zip(*(c.to_pylist() for c in out.columns), strict=True))
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"t": t, "u": u})
    return lean_values(json.dumps(plan)), expected


@pytest.mark.parametrize("sql", BAGS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows, u=u_rows)
def test_bags_match_datafusion(sql, t, u):
    got, expected = both(sql, t, u)
    assert canonical(got) == canonical(expected)


SORTS = [
    ("SELECT a, b FROM t ORDER BY a", 1),
    ("SELECT a, b FROM t ORDER BY a DESC, b NULLS FIRST", 2),
    ("SELECT b, a FROM t ORDER BY b DESC NULLS LAST LIMIT 3", 1),
    ("SELECT a, b FROM t ORDER BY a NULLS FIRST, b DESC LIMIT 4 OFFSET 1", 2),
]


@pytest.mark.parametrize(("sql", "keys"), SORTS)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(t=t_rows)
def test_sort_keys_come_out_in_order(sql, keys, t):
    got, expected = both(sql, t, [])
    # Ties may come out in either order, but the sort keys may not.
    assert [r[:keys] for r in got] == [r[:keys] for r in expected]
    if "LIMIT" not in sql:
        assert canonical(got) == canonical(expected)


t = ibis.table(T, name="t")
u = ibis.table(U, name="u")


def test_contracts_through_new_operators():
    expr = (
        t.filter(t.a > 0)
        .semi_join(u, t.a == u.a)
        .order_by(t.b.desc())
        .select("a")
        .distinct()
        .union(t.filter(t.a > 5).select("a"), distinct=True)
    )
    report = sv.verify(expr, ensures=[_.a > 0])
    assert report.proved, str(report)


def test_semi_join_condition_issues_are_reported():
    report = sv.verify(t.semi_join(u, (t.b // u.a) == 1))
    assert {i.kind for i in report.errors} == {"division by zero", "overflow"}


def test_distinct_rows_are_a_key():
    # After `DISTINCT`, `ROW_NUMBER` over all columns has no ties.
    report = sv.verify(t.distinct().mutate(n=ibis.row_number().over(order_by=["a", "b"])))
    assert report.proved, str(report)


@settings(max_examples=30, deadline=None)
@given(rows=t_rows, more=t_rows)
def test_sorted_views_are_maintained(rows, more):
    con = connect()
    create_table(con, "t", T, rows)
    view = sv.IncrementalView(con, t.filter(t.a > 0).order_by(t.b), "v")
    view.apply({"t": sv.Changes(inserts=more, deletes=[])})
    assert view.rows() == view.recompute()
