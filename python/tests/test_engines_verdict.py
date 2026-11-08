"""The checker's verdict per engine (`"engines"`, `SubstraitLean/Realize.lean`,
#1166), which `sverify.routes` reads: the class over the options the proof
depends on, its evidence and what it rests on, the transfer check, and
whether the result comes out of a sort.
"""

from __future__ import annotations

import ibis
import pytest
from ibis import _

import sverify as sv

T = ibis.table({"k": "int64", "a": "int64", "b": "int64", "x": "float64", "s": "string"}, name="t")
BOUNDED = {"t": [_.a.between(0, 1000), _.b.between(1, 100), _.x.between(0, 1)]}
CAPPED = {"t": [*BOUNDED["t"], sv.max_rows(1000)]}

CASES = {
    "projection": (T.select("k", "a"), BOUNDED),
    "int division": (T.select(q=T.a // T.b, m=T.a % T.b), BOUNDED),
    "int sum": (T.group_by("k").aggregate(s=T.a.sum()), CAPPED),
    "double sum": (T.group_by("k").aggregate(s=T.x.sum()), CAPPED),
    "double mean": (T.group_by("k").aggregate(m=T.x.mean()), CAPPED),
    "filter on a double sum": (
        T.group_by("k").aggregate(s=T.x.sum()).filter(_.s > 500),
        CAPPED,
    ),
    "sort, nulls stated": (T.order_by([ibis.asc("a", nulls_first=True), "k"]), BOUNDED),
    "sort, nulls unstated": (T.order_by(["a", "k"]), BOUNDED),
    "string length": (T.select(n=T.s.length()), BOUNDED),
    "double division": (T.select(r=T.x / (T.b + 0.5)), BOUNDED),
}

#: Each case's class per engine: exact, observed, after a shim, or refused.
#: A threshold filter on a double sum runs with its margin check (#929), a
#: precondition on the data, in place of #568's refusal.
EXPECTED = {
    "projection": {"duckdb": "exact", "polars": "exact", "spark": "exact"},
    "int division": {"duckdb": "exact", "polars": "shim", "spark": "exact"},
    "int sum": {"duckdb": "exact", "polars": "exact", "spark": "shim"},
    "double sum": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
    "double mean": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
    "filter on a double sum": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
    "sort, nulls stated": {"duckdb": "exact", "polars": "exact", "spark": "exact"},
    "sort, nulls unstated": {"duckdb": "exact", "polars": "exact", "spark": "exact"},
    "string length": {"duckdb": "exact", "polars": "exact", "spark": "exact"},
    "double division": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
}


@pytest.mark.parametrize("case", sorted(CASES))
def test_the_checker_s_verdict(case: str) -> None:
    """Each case's verdict, as the routes read it: the class per engine."""
    expr, requires = CASES[case]
    report = sv.verify(expr, requires=requires)
    got = {e: v["class"] for e, v in (report._engines or {}).items() if v["profile"]}
    assert got == EXPECTED[case], case


def test_the_checker_says_whether_the_result_is_sorted() -> None:
    sorted_ = sv.verify(T.order_by("k").select("k", "a"), requires=BOUNDED)
    unsorted = sv.verify(T.select("k", "a"), requires=BOUNDED)
    assert (sorted_._sorted, unsorted._sorted) == (True, False)


def test_the_checker_s_transfer_is_its_own_check() -> None:
    """`"transfer"` per source profile matches `substrait-check --transfer`
    on the plan's reads (`transferB`)."""
    report = sv.verify(CASES["int division"][0], requires=BOUNDED)
    engines = report._engines or {}
    assert engines["polars"]["transfer"]["duckdb"]["ok"] is False
    failed = {f["option"] for f in engines["polars"]["transfer"]["duckdb"]["failures"]}
    assert "division_type" in failed


def test_the_verdict_says_what_it_rests_on() -> None:
    """The class and the sort are computed, not proved (#900); the guard-free
    theorem is named per engine; an option without a row makes the evidence
    tested, and the block names it."""
    report = sv.verify(CASES["int division"][0], requires=BOUNDED)
    engines = report._engines or {}
    assert report._sorted is False
    for e, v in engines.items():
        assert v["class_basis"] == "computed", e
        assert isinstance(v["issues"], list) and isinstance(v["without_row"], list), e
        if v["without_row"]:
            assert v["evidence"] == "tested", e
    assert engines["polars"]["guard_free_theorem"] == "Rel.polars_sound"
    assert engines["duckdb"]["guard_free_theorem"] is None


def _checker_out(monkeypatch: pytest.MonkeyPatch, expr, **kw) -> dict:
    """The checker's answer to the first `--contract` request `verify`
    sends, before it adds any inferred precondition."""
    import json

    from sverify import contracts

    seen: list[dict] = []
    real = contracts.run_checker

    def spy(args, text):
        code, out, err = real(args, text)
        if args == ("--contract",):
            seen.append(json.loads(out))
        return code, out, err

    monkeypatch.setattr(contracts, "run_checker", spy)
    sv.verify(expr, **kw)
    return seen[0]


def test_the_checker_says_which_issues_are_assumed(monkeypatch: pytest.MonkeyPatch) -> None:
    """A SUM that may leave its type and a double that may overflow to ±∞ are
    assumed and checked on the data (`Issue.assumed`, #575); the checker says
    so per issue, and its `proved` does not count them (#1088)."""
    expr = T.group_by("k").aggregate(s=T.a.sum(), p=(T.x * T.x).sum())
    out = _checker_out(monkeypatch, expr, on_inferred="ignore")
    kinds = {i["kind"]: i["assumed"] for i in out["issues"]}
    assert kinds["SUM overflow"] is True
    assert kinds["overflow to infinity"] is True


def test_an_overflow_to_infinity_is_the_reference_s_error(monkeypatch: pytest.MonkeyPatch) -> None:
    """Under DuckDB's semantics a double that overflows gives ±∞, as DuckDB
    does: the checker reports no issue for it (#575)."""
    expr = T.select(y=T.x * T.x)
    ref = _checker_out(monkeypatch, expr, on_inferred="ignore")
    duck = _checker_out(monkeypatch, expr, semantics="duckdb", on_inferred="ignore")
    assert "overflow to infinity" in {i["kind"] for i in ref["issues"]}
    assert "overflow to infinity" not in {i["kind"] for i in duck["issues"]}


def test_an_engine_without_a_profile_gets_a_verdict() -> None:
    """DataFusion has no profile in the checker: the translation's tests
    stand for the plan, and the checker says so (#1166)."""
    report = sv.verify(CASES["projection"][0], requires=BOUNDED)
    v = (report._engines or {})["datafusion"]
    assert (v["class"], v["evidence"], v["profile"]) == ("exact", "tested", False)
    assert v["tested_because"] == ["no_profile"]


def test_the_translated_evidence_says_why_it_is_tested() -> None:
    report = sv.verify(CASES["projection"][0], requires=BOUNDED)
    for e, v in (report._engines or {}).items():
        assert isinstance(v["tested_because"], list), e
        proved = v["evidence"] == "proved" and not v["tested_because"]
        assert v["translated_evidence"] == ("proved" if proved else "tested"), e
