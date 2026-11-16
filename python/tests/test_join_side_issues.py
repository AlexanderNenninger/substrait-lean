"""A condition that reads one side of a join, above a join whose other side is
empty or unmatched (R3, #1484 round 2).

DuckDB pushes the filter into the input it reads, so the condition runs on
every row of that side although the join keeps none (`duckdb-exec-filter-pushdown`):
`10 // a.x` raises on `x = 0` with an empty `b`. `Rel.HasIssue`'s join clause
quantifies over rows of both sides, which an empty side makes false; the report
must list the issue all the same (`Rel.mayIssues` does not know a side is empty).
"""

import duckdb
import ibis
import pytest

import sverify as sv

A = ibis.table({"id": "!int64", "x": "!int64"}, name="a")
B = ibis.table({"id": "!int64"}, name="b")
SQL = "SELECT a.id FROM a JOIN b ON a.id = b.id WHERE 10 // a.x > 1"
#: The rows of `b` under which DuckDB runs the plan: none, and none that matches.
OTHER_SIDE = {"empty": [], "unmatched": [(99,)]}


@pytest.mark.parametrize("other", OTHER_SIDE)
def test_duckdb_raises_on_the_rows_of_one_side_although_the_join_keeps_none(other):
    con = duckdb.connect()
    con.execute("CREATE TABLE a(id BIGINT, x BIGINT)")
    con.execute("INSERT INTO a VALUES (1, 0), (2, 5)")
    con.execute("CREATE TABLE b(id BIGINT)")
    for row in OTHER_SIDE[other]:
        con.execute("INSERT INTO b VALUES (?)", row)
    if other == "empty":
        with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
            con.execute(SQL).fetchall()
    else:
        # The pushdown does not reach the rows when `b` has a row: record it,
        # so a change of the engine shows.
        assert con.execute(SQL).fetchall() == []


def test_the_report_lists_the_issue_of_a_condition_above_a_join():
    report = sv.verify(SQL, tables={"a": A, "b": B}, counterexamples=0)
    assert not report.proved
    assert [n.label for n in report.needs] == ["(_.x != 0)"]
    assert report.needs[0].issue is not None
    assert report.needs[0].issue.kind == "division by zero"


def test_a_declared_precondition_proves_it_whatever_the_other_side_holds():
    report = sv.verify(
        SQL, tables={"a": A, "b": B}, requires={"a": [ibis._.x != 0]}, counterexamples=0
    )
    assert report.proved
