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

#: Each case's class per engine: exact, observed, after a shim, or refused
#: by #568's threshold rule.
EXPECTED = {
    "projection": {"duckdb": "exact", "polars": "exact", "spark": "exact"},
    "int division": {"duckdb": "exact", "polars": "shim", "spark": "exact"},
    "int sum": {"duckdb": "exact", "polars": "exact", "spark": "shim"},
    "double sum": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
    "double mean": {"duckdb": "observed", "polars": "observed", "spark": "observed"},
    "filter on a double sum": {"duckdb": "refused", "polars": "refused", "spark": "refused"},
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
    got = {e: v["class"] for e, v in (report._engines or {}).items()}
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
