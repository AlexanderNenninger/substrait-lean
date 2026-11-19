"""The text preconditions of the text black boxes (#1506, D51): one predicate for
the writers' guard (`ascii_text`, `case_differs`; DuckDB's own dialect) and for
the inferred condition `Report.check_inputs` checks, in both of its forms (the
SQL it is counted with, and the Ibis expression shown to the user): ASCII, with
and without the vertical tab, and free of the scalars `UPPER` or `LOWER` raise
on. The reference's `Text.classesDiffer`, `Text.upperRaises` and
`Text.lowerRaises` join them with the Lean side."""

from __future__ import annotations

import duckdb
import ibis
import pytest

from sverify.contracts import _text_condition
from sverify.sql.core import ascii_text
from sverify_duckdb.dialect import DuckDBDialect

SAMPLE = [
    "ab",
    "",
    "héllo",
    "ÉCOLE",
    "a\x0bb",
    "\x0b",
    "ß",
    "İ",
    "ΑΣ",
    "tab\there",
    "\U00010d50",
    "\U00010d70",
    None,
]
#: The rows each fact rules out. `é` is neither's: the engines agree on it.
BROKEN = {
    "ascii": {"héllo", "ÉCOLE", "ß", "İ", "ΑΣ", "\U00010d50", "\U00010d70"},
    "plain": {"héllo", "ÉCOLE", "ß", "İ", "ΑΣ", "\U00010d50", "\U00010d70", "a\x0bb", "\x0b"},
    "upper_agreed": {"ß", "\U00010d70"},
    "lower_agreed": {"İ", "ΑΣ", "\U00010d50"},
}


def _guard(fact: str) -> str:
    d = DuckDBDialect("duckdb")
    if fact in ("upper_agreed", "lower_agreed"):
        which = "upper" if fact == "upper_agreed" else "lower"
        return f"(NOT {d.case_differs('"s"', which)})"
    return ascii_text(d, '"s"', fact == "plain")


@pytest.mark.parametrize("fact", ["ascii", "plain", "upper_agreed", "lower_agreed"])
def test_the_guard_and_the_precondition_are_one_predicate(fact):
    con = duckdb.connect()
    con.execute("CREATE TABLE t (s VARCHAR)")
    con.executemany("INSERT INTO t VALUES (?)", [(x,) for x in SAMPLE])

    def rows(where: str) -> set:
        return {r[0] for r in con.sql(f"SELECT s FROM t WHERE {where}").fetchall()}

    cond = _text_condition("s", fact)
    # The guard raises where the text is outside the fact (NULL passes its CASE); the
    # condition fails on the same rows.
    broken = rows(f"NOT ({cond})")
    assert rows(f"NOT {_guard(fact)}") == broken
    assert broken == BROKEN[fact]
    # The Ibis form the report shows is the same predicate (NULL is not a value).
    t = ibis.memtable({"s": SAMPLE}, schema={"s": "string"})
    shown = eval(cond.text, {"_": ibis._, "ibis": ibis})  # noqa: S307 - the label is Ibis code
    kept = set(t.filter(shown.resolve(t))["s"].to_pyarrow().to_pylist())
    assert kept == {x for x in SAMPLE if x is not None} - broken


@pytest.mark.parametrize(
    ("sql", "fact"),
    [
        ("SELECT regexp_matches(s, '\\d') AS u FROM r", "plain"),
        ("SELECT s ILIKE 'a%' AS u FROM r", "ascii"),
        ("SELECT upper(s) AS u FROM r", "upper_agreed"),
        ("SELECT lower(s) AS u FROM r", "lower_agreed"),
    ],
)
def test_the_reference_raises_where_the_condition_fails(sql, fact):
    """The third side: `Text.classesDiffer`, `Text.isAscii`, `Text.upperRaises` and
    `Text.lowerRaises` in the checker raise on the sample's rows the condition
    rules out."""
    import json

    from sverify._checker import run_checker
    from sverify.testing import inline_tables
    from test_text import R, connect, plan_of

    con = connect()
    con.create("r", R, [])
    for value in (x for x in SAMPLE if x is not None):
        plan = inline_tables(json.loads(plan_of(con, sql)), {"r": [(value, "x", 1)]})
        code, out, err = run_checker(("--outcomes",), json.dumps(plan))
        # An issue is an error outcome; `ILIKE` and the regular expressions still stop on
        # a panic (D43).
        assert (code == 1 or '"error"' in out) == (value in BROKEN[fact]), (value, out, err)


T = ibis.schema({"s": "string"})
#: A plan, the fact it needs, a value that breaks it and one that does not.
PLANS = [
    ("SELECT upper(s) AS u FROM t", "upper_agreed", "ß", "é"),
    ("SELECT lower(s) AS u FROM t", "lower_agreed", "İ", "é"),
    ("SELECT s ILIKE 'a%' AS u FROM t", "ascii", "é", "c1"),
    ("SELECT regexp_matches(s, '\\d') AS u FROM t", "plain", "é", "c1"),
    ("SELECT regexp_replace(s, '\\d', 'x') AS u FROM t", "plain", "é", "c1"),
]


@pytest.mark.parametrize(("sql", "fact", "bad", "good"), PLANS)
def test_a_plan_with_a_black_box_needs_its_condition_end_to_end(sql, fact, bad, good):
    """Without the condition the plan is not proved and the report names it;
    with it inferred, `Report.run` checks it on the data before anything runs
    (`check_inputs`): the batch with a scalar outside it is refused."""
    import pyarrow as pa

    import sverify as sv
    from sverify.engine import connect, put_table
    from sverify.errors import PreconditionError
    from sverify.report import InferredWarning

    off = sv.verify(sql, tables={"t": T})
    assert off.verdict == sv.Verdict.UNPROVED
    assert ("non-ASCII text" if fact in ("ascii", "plain") else "case mapping") in str(off)
    with pytest.warns(InferredWarning):
        report = sv.verify(sql, tables={"t": T}, on_inferred="warn")
    assert report.verdict == sv.Verdict.PROVED
    assert {c.fact for cs in report._inferred.values() for c in cs if getattr(c, "fact", None)} == {
        fact
    }
    con = connect()
    put_table(con, "t", pa.table({"s": ["ab", bad, None]}))
    with pytest.raises(PreconditionError, match="refused before the run"):
        report.run(con, "duckdb")
    put_table(con, "t", pa.table({"s": ["ab", good, None]}))
    report.run(con, "duckdb")
