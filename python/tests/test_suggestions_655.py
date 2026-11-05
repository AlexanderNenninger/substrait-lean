"""Structured "declare this to make the plan verify" suggestions (#655):
`IS NOT NULL` where a postcondition fails only on NULL, `sv.unique(...)`
for a result with ties, `sv.max_rows(N)` for a tolerance."""

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes


def _needed(report):
    """The labels of `report.needs` per input table."""
    out: dict[str, list[str]] = {}
    for n in report.needs:
        out.setdefault(n.table, []).append(n.label)
    return out


T = ibis.table({"k": "string", "s": "string", "x": "float64"}, name="t")


def test_a_postcondition_failing_only_on_null_needs_not_null() -> None:
    report = sv.verify(T.select("k", n=T.s.length()), ensures=[_.n >= 0])
    assert not report.proved
    assert _needed(report) == {"t": ["_.s.notnull()"]}
    assert "needs: _.s.notnull() on t, inferred from `(_.n >= 0)` (a NULL result otherwise)" in str(
        report
    )
    assumed = sv.verify(T.select("k", n=T.s.length()), ensures=[_.n >= 0], on_inferred="silent")
    assert assumed.proved and "_.s.notnull()" in assumed.requires["t"]


def test_a_postcondition_that_may_be_false_gets_no_null_advice() -> None:
    report = sv.verify(T.select("k", n=T.s.length()), ensures=[_.n >= 1])
    assert _needed(report) == {}
    line = next(x for x in str(report).splitlines() if x.startswith("ensures"))
    assert line == "ensures (_.n >= 1): NOT proved: it may be FALSE or NULL on some rows"


def test_ties_suggest_the_unique_that_determines_the_result() -> None:
    report = sv.verify(T.group_by("k").aggregate(f=T.x.first(order_by=T.x)))
    assert not report.deterministic
    assert report.ties == {"t": ["unique(k, x)"]}
    r = routes.choose(report, "duckdb", deterministic=True)
    assert r.refused and r.suggested == {"t": ["unique(k, x)"]}
    assert "declare sv.unique('k', 'x') on t in requires" in r.reason


def _mean(ensures):
    con = sv.connect()
    con.put("t", pa.table({"k": ["a", "a"], "s": ["", ""], "x": [1.0, 2.0]}))
    t = con.table("t")
    return sv.verify(
        t.group_by("k").aggregate(m=t.x.mean()),
        requires={"t": [_.x.between(0, 1000), sv.max_rows(1000)]},
        ensures=ensures,
    )


@pytest.fixture
def mean_report():
    """A tolerance below the plan's bound: not proved at verify (#689)."""
    return _mean([sv.equivalent(floats=sv.within(rel=1e-14))])


@pytest.fixture
def plan_report():
    """The plan's own bound, which every engine meets."""
    return _mean([])


def test_a_tolerance_suggests_the_row_cap_that_meets_it(mean_report, plan_report) -> None:
    rel = routes._bounds(mean_report.epsilon["m"])["rel"][0]
    want = int(1000 * 1e-14 / rel)
    assert not mean_report.proved
    assert f"or declare sv.max_rows({want:_}) on t, under which the bound meets it" in str(
        mean_report
    )
    r = routes.choose(mean_report, "polars")
    assert r.refused and r.suggested == {"t": [f"max_rows({want})"]}
    assert f"or declare sv.max_rows({want:_}) on t, under which the bound meets it" in r.reason
    rerun = routes.choose(
        plan_report, "polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-15))
    )
    assert rerun.refused and rerun.suggested == {"t": [f"max_rows({int(1000 * 1e-15 / rel)})"]}


def test_no_row_cap_meets_a_tolerance_below_one_row(plan_report) -> None:
    r = routes.choose(
        plan_report, "polars", reproducible=sv.equivalent(floats=sv.within(rel=1e-20))
    )
    assert r.suggested == {"t": ["max_rows(0)"]}
    assert "no row cap on t makes the plan's bound meet the tolerance" in r.reason
