"""A double divided by a decimal converted to a double does not overflow to
`±inf` where the bounds rule it out (#1787). A zero divisor raises division by
zero first. A nonzero decimal at scale `s` converts to at least
`CAST(10⁻ˢ AS DOUBLE)` in size, and every decimal's double is finite. So the
quotient stays within the dividend's bound over those two parts of the
divisor's bound (`decQuotFinite_sound`), even where the divisor's own bound
holds zero."""

import ibis
from ibis import _

import sverify as sv

T = ibis.table({"a": "decimal(22,6)", "d": "decimal(10,2)", "f": "float64"}, name="t")
INF = "overflow to infinity"


def _issues(expr, requires=None):
    report = sv.verify(T.select(r=expr), requires=requires)
    return {i.kind for i in [*report.assumed, *report.errors]}


def test_a_decimal_over_a_decimal_does_not_overflow():
    # The types bound both, and the divisor's bound holds zero.
    issues = _issues(T.a.cast("float64") / T.d.cast("float64"))
    assert INF not in issues
    assert "division by zero" in issues


def test_a_bounded_double_over_a_decimal_does_not_overflow():
    q = T.f / T.d.cast("float64")
    assert INF not in _issues(q, {"t": [_.f.between(-1e6, 1e6)]})


def test_an_unbounded_double_over_a_decimal_may_overflow():
    assert INF in _issues(T.f / T.d.cast("float64"))
