"""The 1.0 coverage targets (#743): each target's probes give what
`sverify_dev.coverage_targets` records, and the list is well formed and in
`docs/coverage-targets.md`."""

from pathlib import Path

import pytest

from sverify_dev.coverage import CASES
from sverify_dev.coverage_targets import AREAS, TARGETS, Target, probe, report

DOC = Path(__file__).resolve().parents[2] / "docs" / "coverage-targets.md"


@pytest.mark.parametrize("t", TARGETS, ids=lambda t: f"{t.area}: {t.name}")
def test_target_is_as_recorded(t: Target):
    refusals = probe(t)
    if t.covered:
        assert not refusals, refusals
    else:
        assert refusals, "covered now: set covered=True in its area's file"


def test_targets_are_well_formed():
    names = [t.name for t in TARGETS]
    assert len(names) == len(set(names))
    labels = {c.label for c in CASES}
    for t in TARGETS:
        assert t.area == next(m.AREA for m in AREAS if t in m.TARGETS)
        assert t.sql or t.ibis, t.name
        assert t.ibis is None or t.ibis in labels, t.ibis
        if not t.covered:
            # What is left says where it is tracked, or why it is left.
            assert t.issue or t.why, t.name
        if t.decision == "skipped":
            assert t.why, t.name


def test_doc_lists_every_target():
    doc = DOC.read_text()
    missing = [t.name for t in TARGETS if t.name not in doc]
    assert not missing, missing


def test_report_counts_in_targets():
    probed = {t.name: [] if t.covered else ["refused"] for t in TARGETS}
    ins = [t for t in TARGETS if t.decision == "in"]
    done = sum(t.covered for t in ins)
    assert report(probed).startswith(f"{done} of {len(ins)} constructs in for 1.0 are covered")
