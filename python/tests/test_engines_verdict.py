"""The checker's verdict per engine (`"engines"`, `SubstraitLean/Realize.lean`,
#1166) agrees with what `sverify.routes.realization` computes from the tables.

The checker's block covers what the tables decide: the class over the options
the proof depends on, its evidence, the theorems, facts and shims, refused
options and #568's threshold rule. What the postcondition observes still
applies in Python, so the comparison is under the coarsest observation, where
it refuses nothing. Once `routes.py` reads the block (#1166 C2), this test
goes with the Python side.
"""

from __future__ import annotations

import json

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.observation import Observation

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

#: Every component at its coarsest: no row's observation is coarser.
COARSEST = Observation(
    rows="multiset",
    elements="multiset",
    floats="plan",
    zeros="canon",
    timestamps="s",
    strings="nfc",
    decimals="value",
    errors="kind",
)


@pytest.mark.parametrize("case", sorted(CASES))
def test_the_checker_s_verdict_is_the_tables(case: str) -> None:
    expr, requires = CASES[case]
    report = sv.verify(expr, requires=requires)
    assert report._engines is not None, "the checker reports no engines"
    for engine, lean in report._engines.items():
        if not (routes._options_json().get("choices") or {}).get(engine):
            continue
        py = routes.realization(
            engine,
            report._depends or [],
            COARSEST,
            report._epsilon,
            None,
            (report._rows_exact or {}).get(engine),
        )
        where = f"{case} on {engine}"
        assert lean["class"] == ("refused" if py.problems else py.cls), where
        if not lean["observed"]:
            # Python marks an observed row's evidence tested where its bound
            # is unproved; the checker leaves that to the observation step.
            assert lean["evidence"] == py.evidence, where
        assert tuple(lean["theorems"]) == py.theorems, where
        assert set(lean["facts"]) == set(py.facts), where
        shims = tuple(
            f"{routes._where(s['group'], s['option'])}: {s['shim']}" for s in lean["shims"]
        )
        assert shims == py.shims, where
        codes = [p["code"] for p in lean["problems"]]
        assert ("threshold" in codes) == any("threshold" in p for p in py.problems), where
        assert codes.count("option_refused") == sum(" is refused on " in p for p in py.problems)


def test_the_checker_says_whether_the_result_is_sorted() -> None:
    sorted_ = sv.verify(T.order_by("k").select("k", "a"), requires=BOUNDED)
    unsorted = sv.verify(T.select("k", "a"), requires=BOUNDED)
    assert (sorted_._sorted, unsorted._sorted) == (True, False)
    assert sorted_.internal_plan is not None and unsorted.internal_plan is not None
    assert routes._sorted_root(json.loads(sorted_.internal_plan))
    assert not routes._sorted_root(json.loads(unsorted.internal_plan))


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
