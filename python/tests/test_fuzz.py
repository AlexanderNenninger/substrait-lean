"""Random queries with Lean as the oracle (`sverify.fuzz`), on a small budget.

Every random query and input either falls outside the model or gives no
finding that an open issue (`sverify.fuzz.KNOWN`) does not explain. The
findings the generator turned up are pinned below as strict `xfail`s, so a
fix shows up as an XPASS. The examples are fixed (`derandomize`); `poe fuzz`
runs a long, random budget and prints the shrunk findings.
"""

import math

import pytest
from hypothesis import HealthCheck, given, settings

from sverify import fuzz
from sverify.fuzz import Finding, Query, Refused, check, check_contract, known, same_rows

# The same examples on every run, so that CI is not flaky; `poe fuzz` explores.
CHEAP = settings(
    max_examples=60,
    derandomize=True,
    deadline=None,
    suppress_health_check=[HealthCheck.too_slow, HealthCheck.filter_too_much],
)


def unexplained(findings: list[Finding]) -> list[str]:
    return [str(f) for f in findings if known(f) is None]


@CHEAP
@given(case=fuzz.cases)
def test_random_queries_agree_with_lean(case):
    query, tables = case
    try:
        findings = check(query, tables)
    except Refused:
        return
    assert not unexplained(findings)


@CHEAP
@given(case=fuzz.contract_cases())
def test_proved_postconditions_hold(case):
    try:
        findings = check_contract(*case)
    except Refused:
        return
    assert not unexplained(findings)


def test_same_rows_is_a_bag_comparison_with_approximate_doubles():
    assert same_rows([(1, 0.5), (None, math.nan)], [(None, math.nan), (1, 0.5000001)])
    assert not same_rows([(1,)], [(1,), (1,)])
    assert not same_rows([(True,)], [(1,)])
    assert not same_rows([(1,), (2,)], [(2,), (1,)], ordered=True)


def test_proved_postconditions_are_checked_on_the_output():
    q = Query("SELECT i AS c0 FROM t AS q WHERE i > 0", {"c0": fuzz.INT})
    rows = {"t": [(1, None, None, None, None, None), (-1, None, None, None, None, None)]}
    assert check_contract(q, rows, None, "c0 > 0") == []


T_ROW = (1, 2, 0.5, "a", True, None)


def finding(sql: str, oracle: str, tables: dict) -> list[Finding]:
    return check(Query(sql, {}), tables, oracles=(oracle,))


@pytest.mark.parametrize("value", ["1.5", "-2.0", "0.25"])
def test_written_bare_double_literal(value):
    """#96: a bare double is written as an `fp64` literal, not its code."""
    assert not finding(f"SELECT {value} AS c0 FROM t AS q", "engines", {"t": [T_ROW]})


@pytest.mark.xfail(strict=True, reason="#96: 0.0 and a double NULL are an integer and NULL")
@pytest.mark.parametrize("value", ["0.0", "CAST(NULL AS DOUBLE)"])
def test_written_bare_double_zero_or_null(value):
    """The model has `0.0` as code 0 and a double NULL as NULL, so the writer
    cannot tell them from an integer: the engines give the right value with
    an integer type. Needs the parser to keep a literal's kind."""
    assert not finding(f"SELECT {value} AS c0 FROM t AS q", "engines", {"t": [T_ROW]})


def test_written_typed_null():
    """#96: a NULL under NOT is written as a boolean NULL."""
    assert not finding(
        "SELECT NOT CAST(NULL AS BOOLEAN) AS c0 FROM t AS q", "engines", {"t": [T_ROW]}
    )


@pytest.mark.parametrize("fn", ["upper", "lower"])
def test_written_string_null(fn):
    """#96: a NULL under a string function is written as a string NULL."""
    sql = f"SELECT {fn}(CAST(NULL AS VARCHAR)) AS c0 FROM t AS q"
    assert not finding(sql, "engines", {"t": [T_ROW]})


def test_written_timestamp_literal_in_case():
    sql = (
        "SELECT CASE WHEN b THEN CASE WHEN b THEN TIMESTAMP '2024-01-01 00:00:00' "
        "ELSE TIMESTAMP '2024-01-01 00:00:00' END ELSE ts END AS c0 FROM t AS q"
    )
    assert not finding(sql, "engines", {"t": [T_ROW]})


def test_smallest_bigint_is_printed_as_an_integer():
    row = (None, -(2**63), None, None, None, None)
    assert not finding("SELECT MIN(j) AS c0 FROM t AS q", "rows", {"t": [row]})


def test_double_literal_arithmetic():
    assert not finding("SELECT 3.0 / 2.0 AS c0 FROM t AS q", "rows", {"t": [T_ROW]})


def test_double_literal_arithmetic_proofs():
    q = Query("SELECT 1.5 * 2.0 AS c0 FROM t AS q", {"c0": fuzz.DOUBLE})
    assert not check_contract(q, {"t": [T_ROW]}, None, "c0 <> 3.0")


def test_join_condition_over_one_side():
    """#98: the DataFusion plan moves `t.i = t.j` out of the join's keys."""
    sql = "SELECT COUNT(*) AS c0 FROM t JOIN u ON t.i = u.k AND t.i = t.j"
    assert not finding(sql, "engines", {"t": [T_ROW], "u": [(1, "x")]})


def test_limit_on_datafusion():
    """#109: Lean writes `FetchRel.countExpr`, which DataFusion reads."""
    assert not finding("SELECT i AS c0 FROM t AS q ORDER BY c0 LIMIT 1", "engines", {"t": [T_ROW]})


def test_full_join_on_datafusion():
    """#96: a FULL JOIN's NULL padding takes the other branch's types."""
    sql = "SELECT COUNT(i) AS c0 FROM (SELECT t.i, u.k FROM t FULL JOIN u ON t.i = u.k) AS q"
    assert not finding(sql, "engines", {"t": [T_ROW], "u": [(2, "x")]})


def test_null_divided_by_zero_on_duckdb():
    """#111: `NULL / 0` is NULL; the DuckDB guard raises only on a number."""
    row = (0, None, None, None, None, None)
    assert not finding("SELECT j / i AS c0 FROM t AS q", "engines", {"t": [row]})


def test_boolean_ordering():
    row = (1, 2, 0.5, "a", False, None)
    assert not finding("SELECT (b <= b) AS c0 FROM t AS q", "rows", {"t": [row]})


@pytest.mark.parametrize(
    "f",
    [
        Finding("rows:polars", "q", {}, "Unsupported('integer 607 does not fit in 64 bits')"),
        Finding("rows:duckdb", "q", {}, "Cannot mix values of type TIMESTAMP and BIGINT"),
        Finding("types:polars", "q", {}, "DataFusion's SQL: ['double']\npolars: ['int64']"),
    ],
)
def test_known_findings_name_their_issue(f):
    assert known(f) == 96


def test_known_findings_need_the_symptom():
    assert known(Finding("rows", "q", {}, "Lean: [] DataFusion: [(1,)]")) is None


def test_findings_print_a_reproduction():
    f = Finding("rows", "SELECT 1", {"t": [(1,)], "u": []}, "Lean: [] DataFusion: [(1,)]")
    assert str(f) == "[rows] SELECT 1\n  t: [(1,)]\nLean: [] DataFusion: [(1,)]"
