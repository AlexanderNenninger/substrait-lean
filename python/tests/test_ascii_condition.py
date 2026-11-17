"""The ASCII precondition of the text black boxes (#1506): one predicate for
the writers' guard (`ascii_text`) and for the inferred condition
`Report.check_inputs` checks, on text with and without the vertical tab."""

from __future__ import annotations

import duckdb
import pytest

from sverify.contracts import _ascii_condition
from sverify.sql.core._base import Dialect, ascii_text

SAMPLE = ["ab", "", "héllo", "ÉCOLE", "a\x0bb", "\x0b", "ß", "tab\there", None]


class Plain(Dialect):
    """The standard SQL spellings the base class has, for DuckDB to run."""

    name = "plain"

    def is_ascii(self, s: str) -> str:
        return f"(strlen({s}) = length({s}))"


def run(con: duckdb.DuckDBPyConnection, where: str) -> list:
    return [r[0] for r in con.sql(f"SELECT s FROM t WHERE {where}").fetchall()]


@pytest.mark.parametrize("classes", [False, True])
def test_the_guard_and_the_precondition_are_one_predicate(classes):
    con = duckdb.connect()
    con.execute("CREATE TABLE t (s VARCHAR)")
    con.executemany("INSERT INTO t VALUES (?)", [(x,) for x in SAMPLE])
    guard = ascii_text(Plain("plain"), '"s"', classes)
    inferred = _ascii_condition("s", classes)
    # The guard raises where the text is not plain; the condition fails there
    # (and passes NULL, which the guard's CASE also lets through).
    raises = {r for r in run(con, f"NOT {guard}")}
    broken = {r for r in run(con, f"NOT ({inferred})")}
    assert raises == broken
    expected = {"héllo", "ÉCOLE", "ß"} | ({"a\x0bb", "\x0b"} if classes else set())
    assert broken == expected
