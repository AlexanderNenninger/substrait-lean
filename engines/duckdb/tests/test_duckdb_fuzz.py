"""DuckDB's own SQL against `Rel.eval` (`sverify_dev.duckdb_fuzz`), on fixed
cases: the fuzzer's search is `sverify_dev.fuzz`'s, tested in `test_fuzz.py`."""

import json

import pytest
from hypothesis import given, settings

from sverify_dev import duckdb_fuzz, fuzz
from sverify_dev.fuzz import INT

pytestmark = pytest.mark.backend("duckdb")

T_ROW = (None, None, None, None, None, None)


def _check(sql: str, t: list[tuple], ordered: bool = False) -> duckdb_fuzz.Outcome:
    return duckdb_fuzz.check(fuzz.Query(sql, {"c0": INT}, ordered=ordered), {"t": t, "u": []})


def test_agree():
    out = _check("SELECT (i // j) AS c0 FROM t AS q", [(-7, 2, *T_ROW[2:])])
    # DuckDB's `//` on integers truncates, as Substrait's `divide` does.
    assert out.agree and out.duckdb == '[["-3"]]'


def test_overflow():
    big = 2**63 - 1
    out = _check("SELECT (i + i) AS c0 FROM t AS q", [(big, None, *T_ROW[2:])])
    # `verify` reports the overflow, so a verified plan excludes the input:
    # an expected refusal, not a finding (#638).
    assert out.agree
    assert out.lean == f'[["{2 * big}"]]'  # unbounded
    assert out.duckdb.startswith("error: Out of Range Error: Overflow in addition")
    assert duckdb_fuzz.kind(out) == "error: Out of Range Error: Overflow in addition of INT"
    assert any("overflow" in i for i in out.issues)


def test_division_by_zero():
    out = _check("SELECT (i % j) AS c0 FROM t AS q", [(7, 0, *T_ROW[2:])])
    assert (out.agree, out.lean) == (True, '[["NULL"]]')
    assert out.duckdb.startswith("error: Invalid Input Error: Division by zero")
    assert any("division by zero" in i for i in out.issues)


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
    # The settings DuckDB ran with (#619): its defaults, `/` of doubles a `/`.
    assert led["settings"]["integer_division"] is False
    assert led["settings"]["ieee_floating_point_ops"] is True
    assert led["summary"] == {"agree": 9, "disagree": 1, "refused": 0, "skipped": 0}
    (r,) = led["results"]
    assert r["file"] == "fuzz:int_division" and r["tables"] == {"t": [["7", "0"] + ["NULL"] * 4]}


def test_doubles_divide_as_doubles():
    """`d / d` of `0.0` is NaN on DuckDB's defaults; a ledger of 2026-11-01
    recorded DuckDB's `//`, from a connection with `integer_division` on
    (#619)."""
    out = _check("SELECT (d / d) AS c0 FROM t AS q", [(None, None, 0.0, *T_ROW[3:])])
    assert out.duckdb == '[["nan"]]'


def test_aimed_swaps_the_double_values_and_restores_them():
    before = (fuzz.VALUES[fuzz.DOUBLE], fuzz.LITERALS[fuzz.DOUBLE], dict(fuzz._KINDS))
    with duckdb_fuzz.aimed(duckdb_fuzz.TARGETS["float_special"]):
        assert fuzz.VALUES[fuzz.DOUBLE] is not before[0]
        assert "neg" in fuzz._KINDS[fuzz.DOUBLE] and "cast_int" not in fuzz._KINDS[fuzz.DOUBLE]
    assert (fuzz.VALUES[fuzz.DOUBLE], fuzz.LITERALS[fuzz.DOUBLE], dict(fuzz._KINDS)) == before
    with duckdb_fuzz.aimed(duckdb_fuzz.TARGETS["eval_order"]):
        assert fuzz.VALUES[fuzz.DOUBLE] is before[0]


def test_an_error_verify_reports_is_an_expected_refusal():
    # DuckDB raises; `Rel.eval` gives rows; `verify` reports the overflow, so
    # a verified plan's precondition excludes the input (#638).
    out = _check("SELECT (i - 1) AS c0 FROM t AS q", [(-(2**63), *T_ROW[1:])])
    assert out.duckdb.startswith("error: ") and not out.lean.startswith("error: ")
    assert out.agree and any("overflow" in i for i in out.issues)


I64_MIN, I64_MAX = -(2**63), 2**63 - 1


def _check_u(sql: str, k: int) -> duckdb_fuzz.Outcome:
    query = fuzz.Query(sql, {"c0": INT}, ordered=" ORDER BY " in sql)
    return duckdb_fuzz.check(query, {"t": [], "u": [(k, None)]})


@pytest.mark.parametrize(
    ("sql", "k", "error"),
    [
        ("SELECT DISTINCT (k * k) AS c0 FROM u AS q", 9007199254740993, "multiplication"),
        ("SELECT DISTINCT (- (k * 9223372036854775807)) AS c0 FROM u AS q", 2, "multiplication"),
        ("SELECT DISTINCT (abs(k) IS NULL) AS c0 FROM u AS q ORDER BY c0", I64_MIN, "abs"),
        ("SELECT DISTINCT (k + (- k)) AS c0 FROM u AS q ORDER BY c0", I64_MIN, "negation"),
    ],
)
def test_ledger_overflows_are_expected_refusals(sql, k, error):
    """The fuzz ledgers' (`engines/duckdb/replay/fuzz__*.json`) overflows
    of 2026-11: DuckDB raises, `Rel.eval` gives rows, `verify` reports the
    overflow (#638)."""
    out = _check_u(sql, k)
    assert out.duckdb.startswith("error: Out of Range Error: Overflow") and error in out.duckdb
    assert out.agree and any("overflow" in i for i in out.issues)


def test_ledger_overflow_under_a_filter_and_a_nested_one():
    out = _check("SELECT COUNT(b) AS c0 FROM t AS q WHERE (i = (i * i))", [(I64_MAX, *T_ROW[1:])])
    assert out.duckdb.startswith("error: Out of Range Error: Overflow in multiplication")
    assert out.agree and out.lean == '[["0"]]'
    sql = "SELECT DISTINCT b AS c0, b AS c1, (i + (i - j)) AS c2 FROM t AS q ORDER BY c0, c1, c2"
    out = _check(sql, [T_ROW, (0, I64_MIN, *T_ROW[2:])], ordered=True)
    assert out.duckdb.startswith("error: Out of Range Error: Overflow in subtraction")
    assert out.agree and any("overflow" in i for i in out.issues)


@pytest.mark.parametrize(
    ("sql", "row", "rows"),
    [
        # `%` of doubles by zero is NaN on DuckDB and under `semantics="duckdb"`.
        ("SELECT DISTINCT (- (d % d)) AS c0 FROM t AS q", (None, None, 0.0), '[["nan"]]'),
        ("SELECT DISTINCT (d + (d % d)) AS c0 FROM t AS q", (None, None, 0.0), '[["nan"]]'),
        # `/` of integers is a double division on DuckDB's defaults (#619):
        # `0 / 0` is NaN, and `i64 min / -1` does not overflow.
        ("SELECT DISTINCT (i / i) AS c0 FROM t AS q", (0, None, None), '[["nan"]]'),
        (
            "SELECT COUNT(b) AS c0 FROM t AS q WHERE (i = (j / -1))",
            (None, I64_MIN, None),
            '[["0"]]',
        ),
    ],
)
def test_ledger_rows_that_now_agree(sql, row, rows):
    """The ledgers' other disagreements, from a connection with
    `integer_division` on or before the NaN modelling: both sides now give
    the same rows."""
    out = _check(sql, [(*row, *T_ROW[3:])])
    assert out.agree and out.lean == out.duckdb == rows
