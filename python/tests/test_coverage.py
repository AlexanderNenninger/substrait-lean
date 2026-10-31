"""Every probed Ibis operation reaches the checker exactly as `sverify.coverage`
records it, so coverage only changes by a deliberate edit there."""

import pytest

from sverify.coverage import CASES, Case, check


@pytest.mark.parametrize("c", CASES, ids=lambda c: f"{c.area}: {c.label}")
def test_coverage_is_as_recorded(c: Case):
    r = check(c)
    assert r.status == c.expected, r.detail
