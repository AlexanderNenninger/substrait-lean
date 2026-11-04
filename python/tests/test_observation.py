"""Postconditions that name the observation (`sv.equivalent`, #444 D11, D12, D18)."""

from __future__ import annotations

import math
import sys
from datetime import datetime

import ibis
import pyarrow as pa
import pytest
from hypothesis import given
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.observation import EXACT, Observation, Within

T = ibis.table({"k": "int64", "x": "float64", "s": "string", "ts": "timestamp"}, name="t")


def test_default_is_multiset_exact() -> None:
    q = sv.equivalent()
    assert q == Observation()
    assert q.ignored() == ["rows"]
    assert EXACT.refines(q) and not q.refines(EXACT)


def test_refinement_is_componentwise() -> None:
    fine = sv.equivalent(floats=sv.within(rel=1e-12))
    coarse = sv.equivalent(floats=sv.within(rel=1e-6), timestamps="ms")
    assert fine.refines(coarse)
    assert not coarse.refines(fine)
    assert coarse.coarser_than(fine) == ["floats", "timestamps"]
    # Rows as a sequence and strings up to NFC are incomparable with their swap.
    a = sv.equivalent(rows="sequence", strings="nfc")
    b = sv.equivalent(rows="multiset", strings="exact")
    assert not a.refines(b) and not b.refines(a)


def test_tolerances_on_different_bounds_are_incomparable() -> None:
    assert sv.within(abs=1e-9).refines(sv.within(abs=1e-6, rel=1e-6))
    assert not sv.within(abs=1e-9).refines(sv.within(rel=1e-6))
    assert not sv.within(ulps=4).refines(sv.within(ulps=2))


def test_unknown_level_raises() -> None:
    with pytest.raises(ValueError, match="rows"):
        sv.equivalent(rows="bag")  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="at least one"):
        sv.within()


@given(
    st.floats(allow_nan=False, allow_infinity=False, width=64).filter(
        lambda x: x < sys.float_info.max
    )
)
def test_one_ulp_apart(x: float) -> None:
    y = math.nextafter(x, math.inf)
    assert sv.within(ulps=1).close(x, y)
    assert not sv.within(ulps=0).close(x, y) or x == y


@pytest.mark.parametrize("big", [sys.float_info.max, -sys.float_info.max])
def test_a_finite_value_is_never_close_to_an_infinity(big: float) -> None:
    """One ulp past the largest double is an infinity, and no tolerance
    makes a finite value close to it: a run that turns a finite value into
    ±inf creates a non-finite value (D-goal 2)."""
    inf = math.copysign(math.inf, big)
    assert math.nextafter(big, inf) == inf
    for w in (sv.within(ulps=1), sv.within(rel=1.0), sv.within(abs=sys.float_info.max)):
        assert not w.close(big, inf)
        assert not w.close(inf, big)


def test_equal_up_to_the_observation() -> None:
    a = pa.table({"k": [2, 1], "x": [0.1 + 0.2, -0.0]})
    b = pa.table({"k": [1, 2], "x": [0.0, 0.3]})
    assert not sv.equivalent().equal(a, b)
    assert not sv.equivalent(zeros="canon").equal(a, b)
    q = sv.equivalent(floats=sv.within(rel=1e-12), zeros="canon")
    assert q.equal(a, b)
    assert "row" in (
        sv.equivalent(rows="sequence", floats=sv.within(rel=1e-12)).difference(a, b) or ""
    )


def test_canonical_truncates_and_normalises() -> None:
    a = pa.table(
        {
            "s": ["é"],
            "ts": pa.array([datetime(2026, 1, 1, 0, 0, 0, 123456)], pa.timestamp("us")),
        }
    )
    b = pa.table(
        {"s": ["é"], "ts": pa.array([datetime(2026, 1, 1, 0, 0, 0, 123000)], pa.timestamp("us"))}
    )
    assert not sv.equivalent().equal(a, b)
    assert sv.equivalent(strings="nfc", timestamps="ms").equal(a, b)


def test_decimals_up_to_their_scale() -> None:
    from decimal import Decimal

    a = pa.table({"d": pa.array([Decimal("1.50")], pa.decimal128(5, 2))})
    b = pa.table({"d": pa.array([Decimal("1.5")], pa.decimal128(5, 1))})
    assert "scales" in (sv.equivalent().difference(a, b) or "")
    assert sv.equivalent(decimals="value").equal(a, b)


def test_report_names_what_a_condition_depends_on() -> None:
    expr = T.group_by("k").aggregate(avg=T.x.mean(), n=T.k.count(), last=T.ts.max())
    report = sv.verify(
        expr,
        requires={"t": [_.x.between(0, 100), _.x.notnull(), sv.max_rows(1000)]},
        ensures=[
            sv.equivalent(floats=sv.within(rel=1e-9), timestamps="s"),
            _.avg <= 100,
            sv.approx(_.avg <= 100),
            sv.unique("k"),
            sv.unique("last"),
            "n >= 0",
        ],
        counterexamples=0,
    )
    ignores = {c.label: c.ignores for c in report.ensures}
    assert ignores == {
        "(_.avg <= 100)": ("floats",),
        "approx((_.avg <= 100), rel=1e-06)": (),
        "unique(k)": (),
        "unique(last)": ("timestamps",),
        "n >= 0": (),
    }
    assert report.observation == sv.equivalent(floats=sv.within(rel=1e-9), timestamps="s")
    assert not report.proved
    assert "depends on floats, which the observation ignores" in str(report)
    assert "observes: equivalent(" in str(report)


def test_without_an_observation_nothing_changes() -> None:
    expr = T.select("k", y=T.k + 1)
    req = {"t": [_.k.between(0, 100)]}
    plain = sv.verify(expr, requires=req, ensures=[_.y >= 1], counterexamples=0)
    observed = sv.verify(expr, requires=req, ensures=[sv.equivalent(), _.y >= 1], counterexamples=0)
    assert plain.proved and observed.proved
    assert plain.observation == observed.observation == Observation()
    assert "observes" not in str(plain)


def test_transform_takes_an_observation() -> None:
    @sv.transform(ensures=[sv.equivalent(floats=sv.within(abs=1e-9)), sv.unique("k")])
    def per_key(t):
        return t.group_by("k").aggregate(m=t.x.max())

    con = sv.connect()
    con.put("t", pa.table({"k": [1, 1, 2], "x": [1.0, 2.0, 3.0]}))
    out = per_key(con.table("t")).to_pyarrow()
    assert sorted(out.column("k").to_pylist()) == [1, 2]
    assert per_key.last_report is not None
    assert isinstance(per_key.last_report.observation.floats, Within)


def test_two_observations_are_refused() -> None:
    with pytest.raises(ValueError, match="observations"):
        sv.verify(T, ensures=[sv.equivalent(), sv.equivalent(rows="sequence")])
