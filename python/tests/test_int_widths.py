"""Integer widths: a widening cast keeps its target's width (#1541), and a computed
integer is 64-bit in the model and the written plan (ruling 114)."""

import ibis
import pytest
from ibis import _

import sverify as sv

T = ibis.table({"a": "int32"}, name="t")
MAX_I32 = 2**31 - 1


@pytest.mark.parametrize(
    "expr",
    [T.a.cast("int64") + T.a.cast("int64"), T.a + T.a],
    ids=["widening cast", "int32 sum"],
)
def test_a_sum_of_the_largest_int32_does_not_wrap_at_32_bits(expr):
    """#1541: `CAST(i AS BIGINT)` of an INTEGER is 64-bit (`argBits` reads the cast's
    target, not the inner width), so `2**31 - 1` doubled is `2**32 - 2`. The sum
    without a cast is no wrap either: a computed integer is 64-bit in the model and
    the written plan (ruling 114), so neither path leaves the proof unchecked."""
    report = sv.verify(
        T.filter(T.a == MAX_I32).select(x=expr), ensures=[_.x > 2**31], on_inferred="ignore"
    )
    assert report.verdict == sv.Verdict.PROVED and not report.errors
