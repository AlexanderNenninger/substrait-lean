"""Every probed Ibis operation reaches the checker, and every verified one
each engine, exactly as `sverify.coverage` records it, so coverage only
changes by a deliberate edit there."""

import re

import pytest

from sverify.coverage import (
    CASES,
    OUT_OF_SCOPE,
    REFUSED,
    TIE_FREE,
    Case,
    check,
    ibis_operations,
    probed_operations,
    refusal,
)


@pytest.mark.parametrize("c", CASES, ids=lambda c: f"{c.area}: {c.label}")
def test_coverage_is_as_recorded(c: Case):
    r = check(c)
    assert r.status == c.expected, r.detail
    expected = REFUSED.get(c.label, {})
    assert set(r.refused) == set(expected), r.refused
    for engine, why in r.refused.items():
        assert re.search(expected[engine], why), why
    if c.label in TIE_FREE:
        for engine in ("snowflake", "spark"):
            assert refusal(c, engine, tie_free=True) is None


def test_every_ibis_operation_is_probed():
    """Each concrete operation of `ibis.expr.operations` (geospatial aside)
    occurs in some case, or `OUT_OF_SCOPE` says why not."""
    probed = set().union(*(probed_operations(c) for c in CASES))
    assert ibis_operations() - probed - set(OUT_OF_SCOPE) == set()
    assert set(OUT_OF_SCOPE) <= ibis_operations()
    assert not set(OUT_OF_SCOPE) & probed


def test_labels_are_unique():
    labels = [c.label for c in CASES]
    assert len(labels) == len(set(labels))
