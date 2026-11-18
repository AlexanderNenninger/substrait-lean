"""A condition that reads one side of a join, above a join whose other side is
empty or unmatched (R3, #1484 round 2; Fable's ruling on `Rel.HasIssue`).

DuckDB pushes a filter into the input it reads, so the condition runs on every
row of that side although the join keeps none (`duckdb-exec-filter-pushdown`):
`10 // a.x` raises on `x = 0` with an empty `b`. `Rel.HasIssue`'s join clause
quantifies over rows of both sides, which an empty side makes false, so the
model does not state this; the report must list the issue all the same
(`Rel.mayIssues` does not know a side is empty). Each probe records what DuckDB
does (raise or not, so an engine change shows) and sverify's verdict without
the precondition and with it. A probe where sverify said "proved" and DuckDB
raised would be a soundness bug of the implementation: none is.
"""

import duckdb
import ibis
import pytest
from ibis import _

import sverify as sv
from sverify.plan_json import Unsupported

SCHEMAS = {
    "a": {"id": "!int64", "x": "!int64"},
    "b": {"id": "!int64", "x": "!int64"},
    "c": {"id": "!int64"},
}
TABLES = {name: ibis.table(cols, name=name) for name, cols in SCHEMAS.items()}
ROWS = {"a": [(1, 0), (2, 5)], "b": [(1, 0), (2, 5)], "c": [(1,), (2,)]}
BASE = "SELECT a.id FROM a JOIN b ON a.id = b.id WHERE 10 // a.x > 1"
X_NOT_ZERO = {"a": [_.x != 0]}
B_NOT_ZERO = {"b": [_.x != 0]}
#: `a.x + b.x` stays in range and its quotient by 0 is the only error.
BOTH_POSITIVE = {"a": [_.x.between(1, 100)], "b": [_.x.between(1, 100)]}

#: (id, SQL, the empty table, raises on DuckDB 2.0.0, precondition that proves it)
PROBES = [
    pytest.param(BASE, "b", True, X_NOT_ZERO, id="inner-join-b-empty"),
    pytest.param(
        "SELECT a.id FROM a LEFT JOIN b ON a.id = b.id WHERE 10 // a.x > 1",
        "b",
        True,
        X_NOT_ZERO,
        id="1-left-join-where-left-b-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a LEFT JOIN b ON a.id = b.id WHERE 10 // b.x > 1",
        "a",
        True,
        B_NOT_ZERO,
        id="2-left-join-where-right-null-rejecting-a-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a JOIN b ON a.id = b.id AND 10 // a.x > 1",
        "b",
        True,
        X_NOT_ZERO,
        id="3-condition-in-on-b-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a JOIN b ON 10 // a.x = b.id",
        "b",
        False,
        X_NOT_ZERO,
        id="4a-join-key-b-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a JOIN b ON a.id = 10 // b.x",
        "a",
        False,
        B_NOT_ZERO,
        id="4b-join-key-mirrored-a-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a JOIN b ON a.id = b.id JOIN c ON b.id = c.id"
        " WHERE 10 // (a.x + b.x) > 1",
        "c",
        False,
        BOTH_POSITIVE,
        id="5-three-inputs-c-empty",
    ),
    pytest.param(
        "SELECT * FROM (SELECT a.id, 10 // a.x AS q FROM a JOIN b ON a.id = b.id) WHERE q > 1",
        "b",
        True,
        X_NOT_ZERO,
        id="6-filter-above-projection-b-empty",
    ),
    pytest.param(
        "SELECT a.id FROM a WHERE a.id IN (SELECT id FROM b) AND 10 // a.x > 1",
        "b",
        True,
        X_NOT_ZERO,
        id="7b-semi-in-b-empty",
    ),
]


def _duckdb(empty: str):
    con = duckdb.connect()
    for name, cols in SCHEMAS.items():
        con.execute(f"CREATE TABLE {name}({', '.join(f'{c} BIGINT' for c in cols)})")
        for row in [] if name == empty else ROWS[name]:
            con.execute(f"INSERT INTO {name} VALUES ({', '.join(map(str, row))})")
    return con


@pytest.mark.parametrize(("sql", "empty", "raises", "requires"), PROBES)
def test_duckdb_and_the_report_on_a_condition_above_a_join_with_an_empty_side(
    sql, empty, raises, requires
):
    con = _duckdb(empty)
    if raises:
        with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
            con.execute(sql).fetchall()
    else:
        assert con.execute(sql).fetchall() == []
    # Whatever DuckDB does with the data, the report lists the issue without
    # the precondition, and proves the plan with it.
    without = sv.verify(sql, tables=TABLES, counterexamples=0)
    assert without.verdict == sv.Verdict.UNPROVED
    assert without.needs or without.errors
    with_it = sv.verify(sql, tables=TABLES, requires=requires, counterexamples=0)
    assert with_it.verdict == sv.Verdict.PROVED


def test_duckdb_raises_with_the_other_side_empty_but_not_when_it_is_unmatched():
    """The pushdown does not reach the rows when `b` has a row that matches
    nothing: recorded, so a change of the engine shows."""
    con = _duckdb("b")
    con.execute("INSERT INTO b VALUES (99, 1)")
    assert con.execute(BASE).fetchall() == []


def test_a_semi_join_written_with_exists_is_refused_for_now():
    """DuckDB raises on it with `b` empty; sverify refuses a correlated
    subquery (#813), so no report states anything."""
    sql = "SELECT a.id FROM a WHERE EXISTS (SELECT 1 FROM b WHERE b.id = a.id) AND 10 // a.x > 1"
    with pytest.raises(Unsupported, match="correlated subqueries"):
        sv.verify(sql, tables=TABLES, counterexamples=0)
    with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
        _duckdb("b").execute(sql).fetchall()


def test_a_constant_raising_condition_over_an_empty_table_is_reported():
    """DuckDB does not raise (nothing evaluates the constant); the model counts
    a constant subexpression that raises (D21, `Rel.constIssues`)."""
    sql = "SELECT a.id FROM a WHERE 10 // 0 > 1"
    assert _duckdb("a").execute(sql).fetchall() == []
    report = sv.verify(sql, tables=TABLES, counterexamples=0)
    assert report.verdict == sv.Verdict.UNPROVED
    assert [i.kind for i in report.errors] == ["division by zero"]


@pytest.mark.parametrize("empty", ["b", "a"])
def test_declaring_a_side_empty_does_not_change_the_report(empty):
    """`sv.max_rows(0)` on a side: the abstract evaluation never uses emptiness,
    so the issue is still reported (`Rel.mayIssues` over-approximates)."""
    report = sv.verify(BASE, tables=TABLES, requires={empty: [sv.max_rows(0)]}, counterexamples=0)
    assert report.verdict == sv.Verdict.UNPROVED
    assert [n.label for n in report.needs] == ["(_.x != 0)"]
