"""Postconditions that name the observation (`sv.equivalent`, #444 D11, D12, D18)."""

from __future__ import annotations

import json
import math
import subprocess
import sys
import unicodedata
from datetime import datetime
from typing import Any

import ibis
import pyarrow as pa
import pytest
from hypothesis import given
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _repo import ROOT, needs_repo
from sverify.engine import checker_path
from sverify.observation import (
    _COMPONENTS,
    _STRINGS,
    EXACT,
    PLAN_BOUND,
    Observation,
    Within,
    string_key,
)

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


def test_the_order_agrees_with_lean() -> None:
    """`Observation.refines` orders each component's levels as `Obs.le`
    does (`--options`' `levels`), on every pair of levels both sides name."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    levels = json.loads(out.stdout)["levels"]
    assert set(levels) == {name for name, _ in _COMPONENTS}
    for component, table in levels.items():
        le = {tuple(p) for p in table["le"]}
        names = [n for n in table["levels"] if n in _python_levels(component)]
        assert len(names) >= 2, component
        for a in names:
            for b in names:
                fine: dict[str, Any] = {component: a}
                coarse: dict[str, Any] = {component: b}
                mine = Observation(**fine).refines(Observation(**coarse))
                assert mine == ((a, b) in le), (component, a, b)


def test_the_string_levels_are_leans() -> None:
    """Lean's `StringObs` constructors, in Lean's order, are `_STRINGS`."""
    out = subprocess.run(
        [str(checker_path()), "--options"], capture_output=True, text=True, check=True
    )
    assert tuple(json.loads(out.stdout)["levels"]["strings"]["levels"]) == _STRINGS


@given(st.text())
def test_each_string_level_is_a_function_of_the_one_before(s: str) -> None:
    """Equal at `nfc` is equal at `casefold` is equal at `ascii`: a key is a
    function of the previous level's key (`str_mono`), so the levels are
    equivalences that refine one another."""
    t = unicodedata.normalize("NFD", s)
    assert string_key("casefold", s) == string_key("casefold", string_key("nfc", s))
    assert string_key("ascii", s) == string_key("ascii", string_key("casefold", s))
    assert string_key("ascii", s) == string_key("ascii", t)
    assert all(ord(c) < 0x80 for c in string_key("ascii", s))


def test_the_ascii_level_hides_what_it_says() -> None:
    """`docs/core-semantics.md`'s examples: a case or width variant is one string,
    a code point without an ASCII decomposition disappears."""
    a = pa.table({"s": ["Straße", "Søren", "日本", "ﬃ"]})
    b = pa.table({"s": ["STRASSE", "sren", "", "FFI"]})
    assert not sv.equivalent(strings="casefold").equal(a, b)
    assert sv.equivalent(strings="ascii").equal(a, b)
    assert not sv.equivalent(strings="nfc").equal(a, b)
    assert sv.equivalent(strings="ascii").refines(sv.equivalent(strings="ascii"))
    assert sv.equivalent(strings="casefold").refines(sv.equivalent(strings="ascii"))
    assert not sv.equivalent(strings="ascii").refines(sv.equivalent(strings="casefold"))


def _python_levels(component: str) -> tuple[str, ...]:
    if component == "floats":
        return ("exact", "plan")
    return dict(_COMPONENTS)[component]


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
    assert report.lenses == sv.equivalent(floats=sv.within(rel=1e-9), timestamps="s")
    assert report.verdict == sv.Verdict.UNPROVED
    assert "depends on floats, which the observation ignores" in report.details()
    assert "lenses: equivalent(" in report.details()
    # `str(report)` lists a postcondition that is proved but depends on what the
    # observation ignores under "Not proved", with the same reason.
    lines = str(report).splitlines()
    start = lines.index("Not proved:")
    shown = [line for line in lines[start + 1 :] if line.startswith("  ")]
    assert any("avg ≤ 100" in line and "depends on floats" in line for line in shown), lines
    assert "  avg ≤ 100" not in lines[:start]


def test_the_checker_names_what_a_condition_depends_on() -> None:
    """The checker reports the components each condition's value depends on
    (`Expr.depends`), and `ignores` reads them (#898): a mean of doubles under
    a tolerance depends on the floats, and `sv.approx` allows for them."""
    expr = T.group_by("k").aggregate(mean_x=T.x.mean(), n=T.k.count())
    report = sv.verify(
        expr,
        requires={"t": [_.x.between(0, 100), _.x.notnull(), sv.max_rows(1000)]},
        ensures=[
            sv.equivalent(floats=sv.within(abs=1e-3)),
            _.mean_x <= 100,
            sv.approx(_.mean_x <= 100),
            _.n >= 0,
        ],
        counterexamples=0,
    )
    plain, approx, count = report.ensures
    assert plain.depends is not None and "floats" in plain.depends
    assert plain.ignores == ("floats",)
    assert approx.ignores == ()
    assert approx.portable
    assert count.depends is not None and "floats" not in count.depends
    assert count.portable


def test_without_an_observation_nothing_changes() -> None:
    """Without doubles, the default (`floats="plan"`) and `sv.equivalent()`
    prove the same, and the report prints no `lenses:` line."""
    expr = T.select("k", y=T.k + 1)
    req = {"t": [_.k.between(0, 100)]}
    plain = sv.verify(expr, requires=req, ensures=[_.y >= 1], counterexamples=0)
    observed = sv.verify(expr, requires=req, ensures=[sv.equivalent(), _.y >= 1], counterexamples=0)
    assert plain.verdict == sv.Verdict.PROVED and observed.verdict == sv.Verdict.PROVED
    assert plain.lenses == PLAN_BOUND
    assert observed.lenses == Observation()
    assert "observes" not in str(plain)


def test_transform_takes_an_observation() -> None:
    @sv.transform(ensures=[sv.equivalent(floats=sv.within(abs=1e-9)), sv.unique("k")])
    def per_key(t):
        return t.group_by("k").aggregate(m=t.x.max())

    con = sv.connect()
    con.put("t", pa.table({"k": [1, 1, 2], "x": [1.0, 2.0, 3.0]}))
    out = per_key(con.table("t")).to_pyarrow()
    assert sorted(out.column("k").to_pylist()) == [1, 2]
    assert per_key.report is not None
    assert isinstance(per_key.report.lenses.floats, Within)


def test_two_observations_are_refused() -> None:
    with pytest.raises(ValueError, match="observations"):
        sv.verify(T, ensures=[sv.equivalent(), sv.equivalent(rows="sequence")])


def test_proved_on_every_allowed_result() -> None:
    """A postcondition is proved on every result the reference allows
    (`contract_sound_allowed`, #899). Since D25 a double sum is the exact sum
    rounded once, one value whatever the order, so a postcondition that reads
    it is too."""
    expr = T.group_by("k").aggregate(total=T.x.sum(), n=T.k.count())
    report = sv.verify(
        expr,
        requires={"t": [_.x.between(0, 100), _.x.notnull(), sv.max_rows(1000)]},
        ensures=[_.n >= 0, sv.approx(_.total <= 1e6)],
        counterexamples=0,
    )
    count, total = report.ensures
    assert count.proved and count.allowed
    assert total.proved and total.allowed
    plain = sv.verify(
        T.select("k", y=T.k + 1),
        requires={"t": [_.k.between(0, 9)]},
        ensures=[_.y >= 1],
        counterexamples=0,
    )
    assert plain.ensures[0].proved and plain.ensures[0].allowed


@pytest.mark.parametrize(
    ("zero", "negative_zero"),
    [([0.0, 1.0], [-0.0, 1.0]), ([[0.0]], [[-0.0]]), ([{"a": 0.0}], [{"a": -0.0}])],
    ids=["double", "list", "struct"],
)
def test_one_zero_unless_the_observation_reads_the_members(zero, negative_zero):
    """D48: `floats="plan"` reads one zero, bound or not; exact doubles and
    zeros read the members, also where Arrow's equality takes `-0.0` for
    `0.0` and nested in a list or a struct."""
    a, b = pa.table({"c": zero}), pa.table({"c": negative_zero})
    assert sv.equivalent(floats="plan").equal(a, b)
    assert sv.equivalent(zeros="canon").equal(a, b)
    assert sv.equivalent().reads_members and not sv.equivalent().equal(a, b)
    assert not sv.equivalent(floats="plan").reads_members


@needs_repo
def test_the_docs_state_the_default_observation() -> None:
    """`docs/core-semantics.md` has one row per component with `PLAN_BOUND`'s level."""
    text = (ROOT / "docs" / "core-semantics.md").read_text()
    section = text.split("### The default observation", 1)[1].split("\n### ", 1)[0]
    rows = {
        cells[0].strip("` "): cells[1].strip("` ")
        for line in section.splitlines()
        if line.startswith("| `")
        and len(cells := [c.strip() for c in line.strip("|").split("|")]) > 2
    }
    assert rows == {name: str(getattr(PLAN_BOUND, name)) for name, _ in _COMPONENTS}


def test_a_lens_on_element_order_keeps_a_condition_on_a_list_column_dependent():
    """`ensures list_position(pair, a) = 1` changes between results equal up
    to `elements="multiset"`, so a condition reading a list column depends on
    the order of its elements; one reading a scalar does not (#2005)."""
    from sverify.observation import PLAN_BOUND, dependencies

    cols = {"pair": ibis.dtype("array<int64>"), "a": ibis.dtype("int64")}
    assert dependencies(PLAN_BOUND, object(), cols, ["pair", "a"]) == ["elements"]
    assert dependencies(PLAN_BOUND, object(), cols, ["a"]) == []
    assert dependencies(Observation(), object(), cols, ["pair"]) == []


#: Scalars whose engines' `UPPER` or `LOWER` values differ in `strings="ascii"`'s key
#: (a raise in 3b, #1285). None today: the level hides every difference D51 records.
_ASCII_KEY_EXCEPTIONS: dict[str, set[str]] = {"upper": set(), "lower": set()}


@needs_repo
def test_the_ascii_level_hides_every_case_mapping_difference() -> None:
    """D51's probed tables: for each scalar the engines map differently, and for
    `UPPER` and `LOWER`, every engine's value has the same `ascii` key, but for
    the committed exceptions (`_ASCII_KEY_EXCEPTIONS`)."""
    import sys

    sys.path.insert(0, str(ROOT / "python" / "tools"))
    from sverify_dev.case_mapping import SIGMA, tables

    recorded = json.loads((ROOT / "characterization" / "case-differences.json").read_text())
    probed = tables(recorded["engines"])
    for d in ("upper", "lower"):
        scalars = {int(h, 16) for h in recorded[d]["differ"]} | ({SIGMA} if d == "lower" else set())
        odd = set()
        for c in scalars:
            values = {t[d].get(f"{c:04X}", chr(c)) for t in probed.values()}
            if len({string_key("ascii", v) for v in values}) > 1:
                odd.add(f"{c:04X}")
        assert odd == _ASCII_KEY_EXCEPTIONS[d], (d, sorted(odd))
