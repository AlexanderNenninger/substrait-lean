"""#604, D19: `AND` and `OR` evaluate both operands, in the reference as in
DuckDB and Polars, so a guard in one operand does not protect the other."""

from __future__ import annotations

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.engine import connect, put_table
from sverify.errors import PreconditionError

T = ibis.table({"x": "int64"}, name="t")
REQUIRES = {"t": [_.x.notnull(), _.x.between(-10, 10)]}
GUARDED_BY_AND = T.filter((_.x != 0) & ((10 // _.x) > 1)).select("x")
GUARDED_BY_CASE = T.filter(ibis.cases((_.x != 0, 10 // _.x)) > 1).select("x")  # pyrefly: ignore


def test_an_error_under_and_is_reported_with_the_case_rewrite():
    report = sv.verify(GUARDED_BY_AND, tables={"t": T}, requires=REQUIRES, infer=False)
    assert not report.proved
    [issue] = report.errors
    assert issue.kind == "division by zero" and issue.under_and_or
    assert any("inside an AND or OR" in h and "CASE" in h for h in report.hints)


def test_the_inferred_precondition_names_the_and():
    """With `infer`, the plan is proved under `x != 0`, which the report says
    comes from a guard under `AND`."""
    report = sv.verify(GUARDED_BY_AND, tables={"t": T}, requires=REQUIRES)
    assert report.proved
    assert report.inferred
    assert any("inside an AND or OR" in h for h in report.hints)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_issues_batch_is_refused_before_the_run(engine):
    """#604's plan, proved under the inferred `x != 0`: `Report.run` checks
    the preconditions on the data first, so the batch with `x = 0` is refused
    with the precondition named, and nothing runs on the engine."""
    report = sv.verify(GUARDED_BY_AND, tables={"t": T}, requires=REQUIRES)
    con = connect()
    put_table(con, "t", pa.table({"x": [0, 2, 5]}))
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of t violate .*x != 0.*refused"):
        report.run(con, engine)
    # Opting out gives up the guarantee: the engine raises.
    with pytest.raises(Exception, match="(?i)divi"):
        report.run(con, engine, check_inputs=False)
    put_table(con, "t", pa.table({"x": [2, 5]}))
    assert report.run(con, engine).column("x").to_pylist() == [2, 5]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_case_form_is_proved_and_runs(engine):
    report = sv.verify(GUARDED_BY_CASE, tables={"t": T}, requires=REQUIRES, infer=False)
    assert report.proved, str(report)
    con = connect()
    put_table(con, "t", pa.table({"x": [0, 2, 5]}))
    assert report.run(con, engine).column("x").to_pylist() == [2, 5]


def test_a_where_above_a_join_is_analysed_on_every_row_of_its_side():
    """DuckDB may push a raising `WHERE` into one side of a join
    (duckdb-exec-filter-pushdown): the analysis evaluates it on the cross
    product of the loose inputs, so a join condition does not guard it."""
    a = ibis.table({"k": "int64", "x": "int64"}, name="a")
    b = ibis.table({"k": "int64"}, name="b")
    for sql in [
        "SELECT a.k FROM a JOIN b ON a.k = b.k WHERE 10 // a.x > 1",
        "SELECT a.k FROM a JOIN b ON a.k = b.k AND b.k <> 0 WHERE 10 // b.k > 1",
    ]:
        report = sv.verify(sql, tables={"a": a, "b": b}, infer=False)
        assert [i.kind for i in report.errors] == ["division by zero"], sql
