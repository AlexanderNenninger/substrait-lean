"""What makes checks faster (#825): the search skipped for conditions only
ties leave open, the checker's `--rows` mode, and the benchmark's report."""

from __future__ import annotations

import ibis
from ibis import _

import sverify as sv
from sverify import _stages
from sverify.ibis_substrait import to_substrait_json
from sverify.testing import _checked, parse_rows
from sverify_dev import bench

T = ibis.table({"g": "int64", "x": "int64"}, name="t")
LAGGED = T.mutate(prev=_.x.lag().over(ibis.window(group_by="g", order_by="x")))
STRICT = _.prev.isnull() | (_.x > _.prev)
NOT_NULL = [_.g.notnull(), _.x.notnull()]


def test_a_condition_only_ties_leave_open_skips_the_search() -> None:
    with _stages.timing() as t:
        report = sv.verify(
            LAGGED, requires={"t": NOT_NULL}, ensures=[STRICT, _.prev.isnull() | (_.x >= _.prev)]
        )
    strict, weak = report.ensures
    assert not strict.proved and strict.ties
    assert strict.reason == "ties"
    assert "tie" in strict.why
    assert strict.counterexample is None
    assert t.calls["counterexamples"] == 0
    assert weak.proved and not weak.ties


def test_a_key_that_breaks_the_ties_proves_it() -> None:
    report = sv.verify(LAGGED, requires={"t": [*NOT_NULL, sv.unique("g", "x")]}, ensures=[STRICT])
    assert report.proved


def test_other_unproved_conditions_are_searched() -> None:
    with _stages.timing() as t:
        report = sv.verify(T, ensures=[_.x > 0])
    (c,) = report.ensures
    assert not c.ties and c.reason == "may_be_false"
    assert c.counterexample is not None
    assert t.calls["counterexamples"] == 1


def test_rows_mode_gives_the_rows_of_the_full_check() -> None:
    values = ibis.memtable({"g": [1, 1, 2], "x": [3, 3, 5]})
    q = values.mutate(prev=_.x.lag().over(ibis.window(group_by="g", order_by="x")))
    plan = to_substrait_json(q)
    full = _checked(plan)
    rows = _checked(plan, ("--rows",))
    assert "roundtrip" in full and "roundtrip" not in rows
    assert parse_rows(rows, doubles=True) == parse_rows(full, doubles=True)


def _results(cold: float, warm: float) -> dict:
    run = lambda s: bench.Run(s, {"lift": 0.0, "checker": s, "other": 0.0})  # noqa: E731
    return {
        "catalogue": {"a": {"cold": run(cold), "warm": run(warm)}},
        "cli": {"cold": run(1.0), "warm": run(0.5)},
    }


def test_the_report_names_the_slowest_stage() -> None:
    text = bench.report(_results(1.5, 0.1))
    assert "| a | 1.50 | 0.10 |" in text and text.rstrip().endswith("|")
    assert "checker |" in text


def test_budgets() -> None:
    assert bench.over_budget(_results(1.5, 0.1)) == []
    over = bench.over_budget(_results(40.0, 2.0))
    assert any(o.startswith("slowest cold") for o in over)
    assert any(o.startswith("slowest warm") for o in over)
    assert any(o.startswith("typical cold") for o in over)
