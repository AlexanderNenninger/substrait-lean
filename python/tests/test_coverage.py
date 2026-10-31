"""Every probed Ibis operation reaches the checker, and every verified one
each engine, exactly as `sverify.coverage` records it, so coverage only
changes by a deliberate edit there."""

import re

import pytest

from sverify.coverage import CASES, REFUSED, TIE_FREE, Case, check, refusal, setup


@pytest.fixture(scope="module")
def con():
    return setup()


@pytest.mark.parametrize("c", CASES, ids=lambda c: f"{c.area}: {c.label}")
def test_coverage_is_as_recorded(con, c: Case):
    r = check(con, c)
    assert r.status == c.expected, r.detail
    expected = REFUSED.get(c.label, {})
    assert set(r.refused) == set(expected), r.refused
    for engine, why in r.refused.items():
        assert re.search(expected[engine], why), why
    if c.label in TIE_FREE:
        assert refusal(con, c, "snowflake", tie_free=True) is None
