"""A typed decimal NULL literal reads with its declared decimal kind (#2026): a call whose only
arguments are such NULLs is a decimal call, not refused as "a DECIMAL result of non-decimal
arguments"."""

import ibis
import ibis.expr.datatypes as dt
import pytest

import sverify as sv

T = ibis.table({"k": "int64"}, name="t")


def _null(p: int, s: int):
    return ibis.literal(None, type=dt.Decimal(p, s))


CALLS = {
    "negate": lambda n: -n,
    "abs": lambda n: n.abs(),
    "add": lambda n: n + n,
    "coalesce": lambda n: ibis.coalesce(n, n),
    "nullif": lambda n: n.nullif(n),
}


@pytest.mark.parametrize("precision", [9, 18, 38])
@pytest.mark.parametrize("name", CALLS)
def test_a_call_of_typed_decimal_nulls_is_read(name, precision):
    expr = T.select(T.k, x=CALLS[name](_null(precision, 0)))
    report = sv.verify(expr, counterexamples=0)
    assert report.output["x"].is_decimal(), name
