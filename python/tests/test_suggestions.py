"""Suggested preconditions for unproved postconditions: the weakest
per-column bound under which Lean proves one (`Infer.suggest`), confirmed by
a proof and never assumed."""

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify.errors import InferredWarning

T = ibis.table({"id": "int64", "x": "!int64", "y": "!int64"}, name="t")


def test_a_bound_on_the_input_is_suggested():
    report = sv.verify(T.select(T.id, d=T.x * 2), requires={"t": [_.x >= 0]}, ensures=[_.d <= 100])
    [c] = report.unproved
    [n] = c.needs
    assert (n.table, n.label, n.op, n.value) == ("t", "(_.x < 51)", "<", "51")
    assert n.text == "(_.x < 51) on t would prove (_.d <= 100)"
    assert repr(n.condition) == repr(_["x"] < 51)
    assert "  would hold with `(_.x < 51)` in the requires of 't'" in str(report)
    # Suggested, not assumed (`x * 2` adds the inferred `x < 2**62`).
    assert report.requires == {"t": ["(_.x >= 0)", "(_.x < 2**62)"]}
    assert report.verdict == sv.Verdict.UNPROVED


def test_a_suggestion_is_a_working_precondition():
    expr = T.select(T.id, d=T.x - T.y)
    report = sv.verify(expr, requires={"t": [_.y >= 0, _.y <= 10]}, ensures=[_.d >= 0])
    [c] = report.unproved
    proved = sv.verify(
        expr,
        requires={
            "t": [_.y >= 0, _.y <= 10, *(n.condition for n in c.needs if n.condition is not None)]
        },
        ensures=[_.d >= 0],
    )
    assert proved.verdict == sv.Verdict.PROVED


def test_no_suggestion_without_a_comparison():
    report = sv.verify(T.select(T.id, d=T.x * 2), ensures=[_.d.isnull()])
    [c] = report.unproved
    assert c.needs == ()


def test_proved_conditions_have_no_suggestion():
    report = sv.verify(
        T.select(T.id, d=T.x * 2), requires={"t": [_.x >= 0, _.x <= 10]}, ensures=[_.d <= 100]
    )
    assert report.verdict == sv.Verdict.PROVED
    assert all(c.needs == () for c in report.ensures)


# -- a postcondition proved only with an inferred bound (#701) ------------------


S = {"s": {"mrr": "BIGINT", "n": "BIGINT"}}


def test_a_postcondition_needing_an_inferred_bound_is_not_proved():
    r = sv.verify(
        "select mrr * 12 as arr, n from s",
        tables=S,
        requires={"s": ["mrr >= 0"]},
        ensures=["arr >= 0", "arr < 10"],
    )
    [n] = r.needs
    assert n.code == "_.mrr < 7 * 10**17"
    holds, small = r.ensures
    # `arr >= 0` holds on every run that does not raise, with or without the bound.
    assert holds.proved and holds.needs == () and holds.reason is None
    assert not small.proved and small.reason != "needs"


def test_the_bound_a_proof_used_is_its_needs():
    r = sv.verify(
        "select mrr * 12 as arr from s",
        tables=S,
        requires={"s": ["mrr >= 0"]},
        ensures=["arr < 9000000000000000000"],
    )
    [c] = r.ensures
    assert not c.proved and c.reason == "needs"
    assert [n.code for n in c.needs] == [n.code for n in r.needs]
    assert "is proved only with `_.mrr < 7 * 10**17`" in c.why
    again = sv.Report.from_json(r.to_json())
    assert again.ensures[0].reason == "needs" and not again.ensures[0].proved


def test_a_bound_assumed_by_on_inferred_proves_it():
    with pytest.warns(InferredWarning):
        r = sv.verify(
            "select mrr * 12 as arr from s",
            tables=S,
            requires={"s": ["mrr >= 0"]},
            ensures=["arr < 9000000000000000000"],
            on_inferred="warn",
        )
    [c] = r.ensures
    assert c.proved and c.needs == ()


def test_postconditions_sharing_a_suggestion_share_its_proof(monkeypatch):
    from sverify import contracts

    calls = []
    once = contracts._verify_once
    monkeypatch.setattr(contracts, "_verify_once", lambda *a, **k: calls.append(1) or once(*a, **k))
    report = sv.verify(
        T.select(T.id, d=T.x * 2),
        requires={"t": [_.x >= 0, _.x < 1000]},
        ensures=[_.d <= 100, _.d < 101],
    )
    assert [[n.label for n in c.needs] for c in report.ensures] == [["(_.x < 51)"]] * 2
    # The proof, its counterexamples, and one confirmation for both suggestions.
    assert len(calls) == 3


@pytest.mark.parametrize(
    ("sql", "ensures"),
    [
        ("select mrr * 12 as arr, n from s", ["arr >= 0", "arr < 9000000000000000000", "n >= 0"]),
        ("select n / mrr as r, mrr + n as t from s", ["r is not null", "t >= 0", "t < 10"]),
        ("select sum(mrr) as m, count(*) as c from s", ["m >= 0", "c >= 1"]),
    ],
)
def test_proved_means_proved_from_the_stated_preconditions(sql, ensures):
    """Ruling 184 N2, #701's law: under `on_inferred="error"` a condition is
    proved exactly when the stated `requires` alone prove it."""
    requires = {"s": ["mrr >= 0", "n >= 0"]}
    r = sv.verify(sql, tables=S, requires=requires, ensures=ensures)
    alone = sv.verify(sql, tables=S, requires=requires, ensures=ensures, on_inferred="off")
    assert [c.proved for c in r.ensures] == [c.proved for c in alone.ensures]


def test_a_postcondition_proved_through_a_siblings_inferred_not_null_is_not_proved():
    """Reviewer 2 on #701: the second postcondition holds only through the
    `IS NOT NULL` inferred for the first; it reads unproved too."""
    t = ibis.table({"id": "int64", "x": "int64"}, name="t")
    expr = t.select(t.id, d=t.x)
    r = sv.verify(expr, ensures=[_.d.notnull() | (_.d < 0), _.d.notnull()])
    alone = sv.verify(expr, ensures=[_.d.notnull() | (_.d < 0), _.d.notnull()], on_inferred="off")
    assert [c.proved for c in r.ensures] == [c.proved for c in alone.ensures]
    first, second = r.ensures
    assert (first.reason, second.reason) == ("needs", "needs")
    assert [n.code for n in second.needs] == ["_.x.notnull()"]
