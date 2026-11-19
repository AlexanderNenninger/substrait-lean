"""One place decides what is proved: `Report.verdict`. The run gate
(`routes.verified`), its refusal text (`routes.not_verified`) and the CLI's
findings (`cli._findings.of`) read the report's own predicates and agree with
the verdict on each of its values (#1088)."""

from __future__ import annotations

from dataclasses import replace
from types import SimpleNamespace

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.cli import _findings

T = ibis.table({"k": "int64", "amount": "int64"}, name="t")
SUM = T.group_by("k").aggregate(total=T.amount.sum())
SQUARE = T.select("k", x=T.amount * T.amount)


def _reports() -> dict[str, sv.Report]:
    return {
        "proved": sv.verify(T.select("k")),
        "proved_with_checks": sv.verify(SUM),
        "unproved": sv.verify(SQUARE, on_inferred="off"),
    }


@pytest.mark.parametrize("name", ["proved", "proved_with_checks", "unproved"])
def test_the_three_sites_agree_with_the_verdict(name: str) -> None:
    report = _reports()[name]
    assert report.verdict == sv.Verdict(name)
    proved = report.verdict != sv.Verdict.UNPROVED
    assert routes.verified(report) is proved
    stub = SimpleNamespace(name="t", nodes=[], report=report, transform=None, links=[])
    found = _findings.of(stub)  # type: ignore[arg-type]
    assert (not found) is proved
    assert ("may fail" in routes.not_verified(report)) is (not proved)


def test_a_postcondition_checked_on_the_data_is_verified_not_proved() -> None:
    report = sv.verify(T.select("k", big=T.amount.clip(0, 10)), ensures=[_.big > 100])
    assert report.verdict == sv.Verdict.UNPROVED and not routes.verified(report)
    checked = replace(report, ensures=[replace(c, checked=True) for c in report.ensures])
    assert checked.verdict == sv.Verdict.UNPROVED
    assert routes.verified(checked)
    assert not checked._unmet_ensures()
