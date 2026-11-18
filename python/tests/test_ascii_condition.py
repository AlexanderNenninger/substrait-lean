"""The ASCII precondition of the text black boxes (#1506): one predicate for
the writers' guard (`ascii_text`, DuckDB's own dialect) and for the inferred
condition `Report.check_inputs` checks, in both of its forms (the SQL it is
counted with, and the Ibis expression shown to the user), on text with and
without the vertical tab. The reference's `Text.classesDiffer` joins them
with the Lean side of #1506."""

from __future__ import annotations

import duckdb
import ibis
import pytest

from sverify.contracts import _ascii_condition
from sverify.sql.core import ascii_text
from sverify_duckdb.dialect import DuckDBDialect

SAMPLE = ["ab", "", "héllo", "ÉCOLE", "a\x0bb", "\x0b", "ß", "tab\there", None]


@pytest.mark.parametrize("classes", [False, True])
def test_the_guard_and_the_precondition_are_one_predicate(classes):
    con = duckdb.connect()
    con.execute("CREATE TABLE t (s VARCHAR)")
    con.executemany("INSERT INTO t VALUES (?)", [(x,) for x in SAMPLE])

    def rows(where: str) -> set:
        return {r[0] for r in con.sql(f"SELECT s FROM t WHERE {where}").fetchall()}

    guard = ascii_text(DuckDBDialect("duckdb"), '"s"', classes)
    cond = _ascii_condition("s", classes)
    # The guard raises where the text is not plain (NULL passes its CASE); the
    # condition fails on the same rows.
    broken = rows(f"NOT ({cond})")
    assert rows(f"NOT {guard}") == broken
    assert broken == {"héllo", "ÉCOLE", "ß"} | ({"a\x0bb", "\x0b"} if classes else set())
    # The Ibis form the report shows is the same predicate (NULL is not a value).
    t = ibis.memtable({"s": SAMPLE}, schema={"s": "string"})
    shown = eval(cond.text, {"_": ibis._, "ibis": ibis})  # noqa: S307 - the label is Ibis code
    kept = set(t.filter(shown.resolve(t))["s"].to_pyarrow().to_pylist())
    assert kept == {x for x in SAMPLE if x is not None} - broken


@pytest.mark.parametrize(
    ("sql", "classes"),
    [
        ("SELECT regexp_matches(s, '\\d') AS u FROM r", True),
        ("SELECT upper(s) AS u FROM r", False),
    ],
)
def test_the_reference_raises_where_the_condition_fails(sql, classes):
    """The third side: `Text.classesDiffer` and `Text.isAscii` in the checker
    (`nonAscii`, D43) raise on the sample's rows the condition rules out."""
    import json

    from sverify._checker import run_checker
    from sverify.testing import inline_tables
    from test_text import R, connect, plan_of

    con = connect()
    con.create("r", R, [])
    cond = _ascii_condition("s", classes)
    db = duckdb.connect()
    db.execute("CREATE TABLE t (s VARCHAR)")
    db.executemany("INSERT INTO t VALUES (?)", [(x,) for x in SAMPLE if x is not None])
    broken = {r[0] for r in db.sql(f"SELECT s FROM t WHERE NOT ({cond})").fetchall()}
    for value in (x for x in SAMPLE if x is not None):
        plan = inline_tables(json.loads(plan_of(con, sql)), {"r": [(value, "x", 1)]})
        code, _, err = run_checker((), json.dumps(plan))
        assert (code == 1) == (value in broken), (value, err)


T = ibis.schema({"s": "string"})
PLANS = [
    "SELECT upper(s) AS u FROM t",
    "SELECT lower(s) AS u FROM t",
    "SELECT s ILIKE 'a%' AS u FROM t",
    "SELECT regexp_matches(s, '\\d') AS u FROM t",
    "SELECT regexp_replace(s, '\\d', 'x') AS u FROM t",
]


@pytest.mark.parametrize("sql", PLANS)
def test_a_plan_with_a_black_box_needs_the_ascii_condition_end_to_end(sql):
    """Without the condition the plan is not proved and the report names it;
    with it inferred, `Report.run` checks it on the data before anything runs
    (`check_inputs`): the batch with non-ASCII text is refused."""
    import pyarrow as pa

    import sverify as sv
    from sverify.engine import connect, put_table
    from sverify.errors import PreconditionError
    from sverify.report import InferredWarning

    off = sv.verify(sql, tables={"t": T})
    assert off.verdict == sv.Verdict.UNPROVED
    assert "non-ASCII text" in str(off)
    with pytest.warns(InferredWarning):
        report = sv.verify(sql, tables={"t": T}, on_inferred="warn")
    assert report.verdict == sv.Verdict.PROVED
    assert any(getattr(c, "ascii", None) for cs in report._inferred.values() for c in cs)
    con = connect()
    put_table(con, "t", pa.table({"s": ["ab", "é", None]}))
    with pytest.raises(PreconditionError, match="refused before the run"):
        report.run(con, "duckdb")
    put_table(con, "t", pa.table({"s": ["ab", "c1", None]}))
    report.run(con, "duckdb")
