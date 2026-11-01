"""Every probed Ibis operation reaches the checker, and every verified one
each engine, exactly as `sverify_dev.coverage` records it, so coverage only
changes by a deliberate edit there."""

import re

import pytest

from sverify_dev.coverage import CASES, REFUSED, TIE_FREE, Case, check, refusal


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
