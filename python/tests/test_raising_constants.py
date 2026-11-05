"""#609, D21: a constant subexpression that raises raises for the whole plan.
DuckDB folds a `CASE`'s constant conditions when it plans the query, with the
evaluator that raises (DD-7), so the plan raises on any data, an empty table
included, whichever branch the rows take. The reference counts every such
constant as raising, and no precondition rules it out."""

from __future__ import annotations

import functools

import duckdb
import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.contracts import CONSTANT_HINT
from sverify.engine import connect, put_table, run_plan, substrait_json, written_plan

#: These tests are about inferred preconditions: assume them, as before
#: `on_inferred` (#655); `test_on_inferred.py` tests the default.
verify = functools.partial(sv.verify, on_inferred="ignore")
transform = functools.partial(sv.transform, on_inferred="ignore")


T = ibis.table({"x": "int64"}, name="t")
LATER_WHEN = "SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END AS v FROM t"


@pytest.mark.parametrize(
    "sql",
    [
        LATER_WHEN,
        # Stricter than DuckDB, which does not fold a constant ELSE or WHERE.
        "SELECT CASE WHEN x > 0 THEN 1 ELSE 1 // 0 END AS v FROM t",
        "SELECT x FROM t WHERE 1 // 0 = 1",
    ],
)
def test_a_constant_that_raises_is_reported_whatever_the_preconditions(sql):
    report = verify(sql, tables={"t": T}, requires={"t": ["x > 0"]})
    assert not report.proved
    [issue] = report.errors
    assert issue.kind == "division by zero" and issue.constant
    assert issue.hint == CONSTANT_HINT
    assert not report._guard_free


def test_a_constant_without_an_error_is_nothing():
    report = verify("SELECT x + 6 // 3 AS v FROM t", tables={"t": T})
    assert report.proved and report.errors == []


@pytest.mark.parametrize("rows", [[], [5, 7]])
def test_duckdb_raises_on_the_issues_query_on_any_data(rows):
    """The probe of #609: every row takes the first branch, or there are no
    rows, and DuckDB still raises."""
    t = pa.table({"x": pa.array(rows, pa.int64())})
    native = duckdb.connect()
    native.register("t", t)
    with pytest.raises(Exception, match="(?i)division by zero"):
        native.sql(LATER_WHEN).fetchall()
    con = connect()
    put_table(con, "t", t)
    plan = written_plan(substrait_json(con, LATER_WHEN, "reference"))
    with pytest.raises(Exception, match="(?i)division by zero"):
        run_plan(con, plan, "duckdb")


def test_an_integer_cast_of_a_constant_string_is_refused():
    """`CAST('a' AS INTEGER) = 1` in a later `WHEN` (DD-7): the checker refuses
    the plan outright."""
    sql = "SELECT CASE WHEN x > 0 THEN 1 WHEN CAST('a' AS INTEGER) = 1 THEN 2 END AS v FROM t"
    with pytest.raises(ValueError, match="cannot cast"):
        verify(sql, tables={"t": T})
