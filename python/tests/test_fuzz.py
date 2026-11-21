"""Random queries with Lean as the oracle (`sverify_dev.fuzz`), on a small budget.

Every random query and input either falls outside the model or gives no
finding that an open issue (`sverify_dev.fuzz.KNOWN`) does not explain. The
examples are fixed (`derandomize`); `poe fuzz`
runs a long, random budget and prints the shrunk findings.
"""

import datetime as dt
import json
import math

import pytest
from hypothesis import HealthCheck, given, settings

from sverify_dev import fuzz
from sverify_dev.fuzz import Finding, Query, Refused, check, check_contract, known, same_rows

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


@pytest.mark.slow
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


def test_a_recorded_case_round_trips_and_replays():
    ts = dt.datetime(2026, 11, 19, 1, 2, 3)
    row = (1, None, math.inf, "a", True, ts)
    q = Query("SELECT i AS c0 FROM t AS q", {"c0": fuzz.INT})
    f = Finding("rows", q.sql, {"t": [row]}, "detail", case=(q, {"t": [row], "u": []}))
    record = json.loads(json.dumps(fuzz.to_json(f, seed=5)))
    assert record["seed"] == 5 and record["tables"]["t"][0][2] == {"float": "inf"}
    assert [fuzz._decode(v) for v in record["tables"]["t"][0]] == list(row)
    assert fuzz.replay(record) == []


def test_a_checker_over_its_cap_is_a_finding_not_an_exception(monkeypatch, tmp_path):
    from sverify._checker import CheckerMemoryError

    def runaway(*case):
        raise CheckerMemoryError("substrait-check used 5000 MB on one request, over its cap")

    monkeypatch.setattr(fuzz, "check", runaway)
    monkeypatch.setenv("SVERIFY_FUZZ_PROGRESS", str(tmp_path / "progress.json"))
    q = Query("SELECT i AS c0 FROM t AS q", {"c0": fuzz.INT})
    (f,) = fuzz._findings((q, {"t": [], "u": []}))
    assert f.oracle == "checker" and f.detail.startswith("memory cap:")
    assert "plan" in f.extra and f.case is not None
    # The case was written before the check, for a batch the watchdog stops.
    assert json.loads((tmp_path / "progress.json").read_text())["sql"] == q.sql


def test_a_reference_raise_that_verify_flags_is_not_a_finding():
    # Lean raises divByZero; verify reports the possible runtime error, so
    # this is the reference's designed raise, not a disagreement (the nightly
    # run's first batch crashed on this case before).
    q = Query("SELECT (k // 0) AS c0 FROM u AS q", {"c0": fuzz.INT})
    assert fuzz._findings((q, {"t": [], "u": [(1, "a")]})) == []


def test_a_raise_on_data_that_breaks_an_inferred_precondition_is_not_a_finding():
    # `k // k` at k = 0: verify infers `k IS NULL OR k <> 0` and does not prove
    # the plan without it, so the raise is covered (#638, #2101); where the
    # data meets the precondition, nothing raises.
    q = Query("SELECT COUNT(k) AS c0 FROM u AS q WHERE (k = (k // k))", {"c0": fuzz.INT})
    assert fuzz._findings((q, {"t": [], "u": [(0, "a")]})) == []


def test_an_assumed_issue_does_not_cover_an_unrelated_raise():
    # The report assumes the `SUM` fits 64 bits: an assumption is no cover for
    # a raise, which `checked` ties to its own issue (#2162).
    s = fuzz.Session({"t": [(2**62, None, None, None, None, None)] * 3, "u": []})
    assert not fuzz.reports_runtime_error(s, "SELECT SUM(i) AS c0 FROM t")


def test_a_tagged_raise_of_a_reported_assumption_is_not_a_finding():
    # A sum past 64 bits: the written plan's guard raises "integer overflow in
    # SUM", the report lists "SUM overflow" and Lean finds it on this data
    # (ruling 230, #2162). With a small sum nothing raises.
    q = Query("SELECT SUM(i) AS c0 FROM t AS q", {"c0": fuzz.INT})
    big = 2**62
    row = (big, None, None, None, None, None)
    engines = ("rows", "engines")
    assert check(q, {"t": [row, row, row], "u": []}, engines) == []
    assert check(q, {"t": [(1, None, None, None, None, None)], "u": []}, engines) == []


def test_a_tlp_predicate_that_raises_is_not_a_finding():
    # The partition `WHERE (k // k) = 1` raises on k = 0 where the whole query
    # doesn't: no partition to compare, and no harness error (the first
    # nightly run's four `core:harness` signatures).
    base = "SELECT * FROM u AS q"
    q = Query(
        "SELECT TRUE AS c0 FROM u AS q", {"c0": fuzz.BOOL}, base=base, tlp_pred="(k // k) = 1"
    )
    assert fuzz._findings((q, {"t": [], "u": [(0, "a")]})) == []


T_ROW = (1, 2, 0.5, "a", True, None)


def finding(sql: str, oracle: str, tables: dict) -> list[Finding]:
    return check(Query(sql, {}), tables, oracles=(oracle,))


@pytest.mark.parametrize("value", ["1.5::DOUBLE", "-2.0::DOUBLE", "0.25::DOUBLE"])
def test_written_bare_double_literal(value):
    """#96: a bare double is written as an `fp64` literal, not its code. (In
    DuckDB's SQL, `1.5` alone is a DECIMAL.)"""
    assert not finding(f"SELECT {value} AS c0 FROM t AS q", "engines", {"t": [T_ROW]})


@pytest.mark.parametrize(
    "value",
    [
        "0.0::DOUBLE",
        "CAST(NULL AS DOUBLE)",
        "- CAST(NULL AS DOUBLE)",
        "TIMESTAMP '2024-01-01 00:00:00'",
        "CAST(NULL AS TIMESTAMP)",
        "DATE '2024-01-01'",
        "CAST(NULL AS BOOLEAN)",
        "CAST(NULL AS VARCHAR)",
        "CASE WHEN b THEN 0.0::DOUBLE ELSE 1.5::DOUBLE END",
        "CASE WHEN b THEN TIMESTAMP '2024-01-01 00:00:00' ELSE TIMESTAMP '2024-01-02 00:00:00' END",
    ],
)
def test_written_projected_literal(value):
    """#96: a projected literal has the type its source plan declares. The
    model has `0.0` as code 0, a timestamp as microseconds and a typed NULL
    as NULL; the engines check the values and the column types."""
    assert not finding(f"SELECT {value} AS c0 FROM t AS q", "engines", {"t": [T_ROW]})


def test_written_projected_literal_read_by_a_filter():
    """#96: the declared kind carries through to the relation reading it."""
    sql = "SELECT c0 FROM (SELECT 0.0::DOUBLE AS c0 FROM t) AS q WHERE c0 = 0.0::DOUBLE"
    assert not finding(sql, "engines", {"t": [T_ROW]})


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


def test_written_string_null_under_length():
    """#96: `length`'s NULL argument is a string NULL, so every engine runs
    the plan. (DataFusion's SQL gives an `int32` result, the plan `int64`.)"""
    sql = "SELECT length(CAST(NULL AS VARCHAR)) AS c0 FROM t AS q"
    found = finding(sql, "engines", {"t": [T_ROW]})
    assert not [f for f in found if f.oracle.startswith("rows:")]


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
    """#98: the written plan moves `t.i = t.j` out of the join's keys."""
    sql = "SELECT COUNT(*) AS c0 FROM t JOIN u ON t.i = u.k AND t.i = t.j"
    assert not finding(sql, "engines", {"t": [T_ROW], "u": [(1, "x")]})


def test_limit_on_the_engines():
    """#109: Lean writes `FetchRel.countExpr`, which the engines read."""
    assert not finding("SELECT i AS c0 FROM t AS q ORDER BY c0 LIMIT 1", "engines", {"t": [T_ROW]})


def test_full_join_on_the_engines():
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


def test_known_findings_name_their_issue():
    f = Finding("types:polars", "q", {}, "DataFusion's SQL: ['int64']\npolars: ['int32']")
    assert known(f) == 18


def test_known_findings_need_the_symptom():
    assert known(Finding("rows", "q", {}, "Lean: [] DataFusion: [(1,)]")) is None


def test_findings_print_a_reproduction():
    f = Finding("rows", "SELECT 1", {"t": [(1,)], "u": []}, "Lean: [] DataFusion: [(1,)]")
    assert str(f) == "[rows] SELECT 1\n  t: [(1,)]\nLean: [] DataFusion: [(1,)]"
