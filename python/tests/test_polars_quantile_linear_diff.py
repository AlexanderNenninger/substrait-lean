"""#900 follow-up: Polars's own `quantile(q, "linear")` against `LINEAR_DIFF`.

`QuantInterp "LINEAR_DIFF"` (`core/Sverify/Core/AllowedP.lean`) is a double
between the neighbours of the engine's double position `(n - 1)·q`
(`contNeighboursD`), NaN where the lower neighbour is `-inf` and the upper one
greater, or `+inf` where `hi - lo` overflows (`contDiffExtra`). Polars adds
the null count inside the position (`float_idx = (n - 1)·q + nulls`); the set
over the values without nulls is claimed to cover it. Each case here is a
membership test of the engine's value against that set.
"""

import math
from decimal import Decimal

import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

pl = pytest.importorskip("polars")

FLOATS = st.one_of(
    st.floats(min_value=-1e308, max_value=1e308, allow_nan=False),
    st.sampled_from([math.inf, -math.inf, 1e308, -1e308, 0.0, 1.0, 1e-300]),
)


def neighbours(values: list[float], q: str) -> tuple[float, float]:
    """`contNeighboursD`: the values at the floor and the ceiling of `(n - 1)·q` in doubles."""
    s = sorted(values)
    pos = (len(s) - 1) * float(Decimal(q))
    return s[math.floor(pos)], s[math.ceil(pos)]


def allowed(values: list[float], q: str, got: float) -> bool:
    lo, hi = neighbours(values, q)
    if lo <= got <= hi:
        return True
    if math.isnan(got):
        return lo == -math.inf and hi > lo
    return got == math.inf and hi - lo == math.inf


def polars_quantile(values: list[float | None], q: str) -> float:
    df = pl.DataFrame({"x": values}, schema={"x": pl.Float64})
    return df.select(pl.col("x").quantile(float(Decimal(q)), "linear")).item()


@settings(max_examples=300, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    st.lists(FLOATS, min_size=2, max_size=60),
    st.integers(min_value=0, max_value=6),
    st.integers(min_value=1, max_value=99),
)
def test_polars_linear_stays_in_the_widened_set(values, nulls, num):
    q = f"0.{num:02d}"
    got = polars_quantile([*values, *([None] * nulls)], q)
    assert allowed(values, q, got), (values, nulls, q, got)


def test_the_double_position_cases():
    # n = 26, q = 0.28: position 7.000000000000001, neighbours 7 and 8.
    ramp = [float(i) for i in range(26)]
    assert polars_quantile(ramp, "0.28") == 7.000000000000001
    assert allowed(ramp, "0.28", 7.000000000000001)
    step = [1.0] * 8 + [1e300] * 18
    assert allowed(step, "0.28", polars_quantile(step, "0.28"))
    # n = 51, q = 0.58: position 28.999999999999996.
    ramp = [float(i) for i in range(51)]
    assert polars_quantile(ramp, "0.58") == 28.999999999999996
    assert allowed(ramp, "0.58", 28.999999999999996)
    # With nulls the engine's position shifts by a whole number: still inside.
    assert allowed(
        [float(i) for i in range(26)], "0.28", polars_quantile([*ramp[:26], None], "0.28")
    )
    assert allowed(ramp, "0.58", polars_quantile([*ramp, None, None, None, None], "0.58"))


def test_an_overflowing_difference_is_in_the_set():
    values = [-1e308, 1e308]
    assert polars_quantile(values, "0.25") == math.inf
    assert allowed(values, "0.25", math.inf)
    assert allowed([-math.inf, 1.0], "0.5", math.nan)
