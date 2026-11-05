"""Suggested preconditions for unproved postconditions: the weakest
per-column bound under which Lean proves one (`Infer.suggest`), confirmed by
a proof and never assumed."""

import ibis
from ibis import _

import sverify as sv
from sverify.contracts import label

T = ibis.table({"id": "int64", "x": "!int64", "y": "!int64"}, name="t")


def test_a_bound_on_the_input_is_suggested():
    report = sv.verify(T.select(T.id, d=T.x * 2), requires={"t": [_.x >= 0]}, ensures=[_.d <= 100])
    [c] = report.unproved
    assert [label(s) for s in c.suggested["t"]] == ["(_.x < 51)"]
    [(post, [n])] = report.suggestions.items()
    assert (post, n.table, n.label, n.op, n.value) == ("(_.d <= 100)", "t", "(_.x < 51)", "<", "51")
    assert repr(n.condition) == repr(_["x"] < 51)
    assert "  would hold with `(_.x < 51)` in the requires of 't'" in str(report)
    # Suggested, not assumed (`x * 2` adds the inferred `x < 2**62`).
    assert report.requires == {"t": ["(_.x >= 0)", "(_.x < 2**62)"]}
    assert not report.proved


def test_a_suggestion_is_a_working_precondition():
    expr = T.select(T.id, d=T.x - T.y)
    report = sv.verify(expr, requires={"t": [_.y >= 0, _.y <= 10]}, ensures=[_.d >= 0])
    [c] = report.unproved
    proved = sv.verify(
        expr, requires={"t": [_.y >= 0, _.y <= 10, *c.suggested["t"]]}, ensures=[_.d >= 0]
    )
    assert proved.proved


def test_no_suggestion_without_a_comparison():
    report = sv.verify(T.select(T.id, d=T.x * 2), ensures=[_.d.isnull()])
    [c] = report.unproved
    assert c.suggested == {} and report.suggestions == {}


def test_proved_conditions_have_no_suggestion():
    report = sv.verify(
        T.select(T.id, d=T.x * 2), requires={"t": [_.x >= 0, _.x <= 10]}, ensures=[_.d <= 100]
    )
    assert report.proved and report.suggestions == {}
