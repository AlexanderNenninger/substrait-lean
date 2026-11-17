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
