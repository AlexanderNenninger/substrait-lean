"""#604, D19, D50: the core's `AND` and `OR` evaluate both operands; the SQL
and Ibis frontends lift them (D50) so a guard in one operand protects the
next."""

from __future__ import annotations

import functools

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.engine import connect, put_table

#: These tests are about inferred preconditions: assume them, as before
#: `on_inferred` (#655); `test_on_inferred.py` tests the default.
verify = functools.partial(sv.verify, on_inferred="ignore")
transform = functools.partial(sv.transform, on_inferred="ignore")


T = ibis.table({"x": "int64"}, name="t")
REQUIRES = {"t": [_.x.notnull(), _.x.between(-10, 10)]}
GUARDED_BY_AND = T.filter((_.x != 0) & ((10 // _.x) > 1)).select("x")
GUARDED_BY_CASE = T.filter(ibis.cases((_.x != 0, 10 // _.x)) > 1).select("x")  # pyrefly: ignore


def test_a_guard_under_and_protects_the_other_operand():
    """D50: `x != 0 AND 10 // x > 1` is lifted so the division runs only
    where the guard is not FALSE: proved with no inferred precondition."""
    report = verify(GUARDED_BY_AND, tables={"t": T}, requires=REQUIRES, on_inferred="off")
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert not report.errors and not report._inferred


def test_an_error_in_the_first_operand_is_still_reported():
    """Nothing guards the first operand, so its division is an error."""
    unguarded = T.filter(((10 // _.x) > 1) & (_.x != 0)).select("x")
    report = verify(unguarded, tables={"t": T}, requires=REQUIRES, on_inferred="off")
    assert report.verdict == sv.Verdict.UNPROVED
    assert [i.kind for i in report.errors] == ["division by zero"]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_guarded_plan_runs_where_the_guard_is_false(engine):
    """The batch with `x = 0` runs: the lifted plan never divides there."""
    report = verify(GUARDED_BY_AND, tables={"t": T}, requires=REQUIRES, on_inferred="off")
    con = connect()
    put_table(con, "t", pa.table({"x": [0, 2, 5]}))
    assert report.run(con, engine).column("x").to_pylist() == [2, 5]


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_the_case_form_is_proved_and_runs(engine):
    report = verify(GUARDED_BY_CASE, tables={"t": T}, requires=REQUIRES, on_inferred="off")
    assert report.verdict == sv.Verdict.PROVED, str(report)
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
        report = verify(sql, tables={"a": a, "b": b}, on_inferred="off")
        assert [i.kind for i in report.errors] == ["division by zero"], sql


def test_an_aggregate_filter_under_and_is_guarded():
    """`SUM(…) FILTER (WHERE a AND b)`: the filter's `AND` is lifted too (D50)."""
    sql = "SELECT COUNT(*) FILTER (WHERE x <> 0 AND 10 // x > 1) AS s FROM t"
    report = verify(sql, tables={"t": T}, requires=REQUIRES, on_inferred="off")
    assert report.verdict == sv.Verdict.PROVED, str(report)
    con = connect()
    put_table(con, "t", pa.table({"x": [0, 2, 5]}))
    assert report.run(con, "duckdb").column("s").to_pylist() == [2]
