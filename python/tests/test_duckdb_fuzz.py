"""DuckDB's own SQL against `Rel.eval` (`sverify.duckdb_fuzz`), on fixed
cases: the fuzzer's search is `sverify.fuzz`'s, tested in `test_fuzz.py`."""

import json

import pytest
from hypothesis import given, settings

from sverify import duckdb_fuzz, fuzz
from sverify.fuzz import INT

pytestmark = pytest.mark.backend("duckdb")

T_ROW = (None, None, None, None, None, None)


def _check(sql: str, t: list[tuple], ordered: bool = False) -> duckdb_fuzz.Outcome:
    return duckdb_fuzz.check(fuzz.Query(sql, {"c0": INT}, ordered=ordered), {"t": t, "u": []})


def test_agree():
    out = _check("SELECT (i / j) AS c0 FROM t AS q", [(-7, 2, *T_ROW[2:])])
    # DuckDB's `/` truncates under `integer_division`, as DataFusion's does.
    assert out.agree and out.duckdb == '[["-3"]]'


def test_overflow():
    big = 2**63 - 1
    out = _check("SELECT (i + i) AS c0 FROM t AS q", [(big, None, *T_ROW[2:])])
    assert not out.agree
    assert out.lean == f'[["{2 * big}"]]'  # unbounded
    assert out.duckdb.startswith("error: Out of Range Error: Overflow in addition")
    assert duckdb_fuzz.kind(out) == "error: Out of Range Error: Overflow in addition of INT"
    assert any("may wrap around" in i for i in out.issues)


def test_division_by_zero():
    out = _check("SELECT (i % j) AS c0 FROM t AS q", [(7, 0, *T_ROW[2:])])
    assert (out.agree, out.lean) == (False, '[["NULL"]]')
    assert out.duckdb.startswith("error: Invalid Input Error: Division by zero")


def test_aimed_restores():
    before = fuzz.VALUES[INT], fuzz.LITERALS[INT], dict(fuzz._KINDS)
    target = duckdb_fuzz.TARGETS["int_overflow"]
    with duckdb_fuzz.aimed(target) as cases:

        @settings(max_examples=5, database=None, deadline=None)
        @given(cases)
        def drawn(case):
            _, tables = case
            assert all(r[0] in target.ints for r in tables["t"])

        drawn()
    assert (fuzz.VALUES[INT], fuzz.LITERALS[INT], dict(fuzz._KINDS)) == before


def test_write(tmp_path):
    out = _check("SELECT (i % j) AS c0 FROM t AS q", [(7, 0, *T_ROW[2:])])
    path = duckdb_fuzz.write("int_division", "2.0.0", [out], 10, tmp_path)
    led = json.loads(path.read_text())
    assert (led["area"], led["checked"]) == ("fuzz/int_division", 10)
    assert led["summary"] == {"agree": 9, "disagree": 1, "refused": 0, "skipped": 0}
    (r,) = led["results"]
    assert r["file"] == "fuzz:int_division" and r["tables"] == {"t": [["7", "0"] + ["NULL"] * 4]}
