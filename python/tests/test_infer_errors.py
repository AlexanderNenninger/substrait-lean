"""Inferred preconditions for runtime errors besides overflow: division by
zero, domain errors, casts out of range, string arguments, decimal
precision and date arithmetic. Like #244's bounds, Lean proposes them
(`SubstraitLean/Infer.lean`), the unchanged proof checks them, and they are
checked on the data."""

import functools

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import discharged
from sverify.contracts import ON_DATA, label
from sverify.errors import PreconditionError
from sverify.io import StaticSource

#: These tests are about inferred preconditions: assume them, as before
#: `on_inferred` (#655); `test_on_inferred.py` tests the default.
verify = functools.partial(sv.verify, on_inferred="silent")
transform = functools.partial(sv.transform, on_inferred="silent")


T = ibis.table(
    {
        "a": "int64",
        "b": "int64",
        "x": "float64",
        "y": "float64",
        "s": "string",
        "d": "date",
        "big": "decimal(38, 2)",
    },
    name="t",
)


def inferred(report: sv.Report) -> list[str]:
    return [label(c) for cs in report.inferred.values() for c in cs]


@pytest.mark.parametrize(
    ("expr", "conds"),
    [
        (T.select(r=T.a % T.b), ["(_.b != 0)"]),
        # `MIN / -1` is an overflow too: a bound symmetric about 0 rules it out.
        (T.select(r=T.a // T.b), ["(_.a >= -9 * 10**18)", "(_.b != 0)"]),
        # `b - 1` may overflow too.
        (T.select(r=T.a % (T.b - 1)), ["(_.b >= -9 * 10**18)", "(_.b != 1)"]),
        (T.select(r=T.x.sqrt()), ["(_.x >= 0.0)"]),
        (T.select(r=T.x.ln()), ["(_.x > 0)"]),
        (T.select(r=T.x.asin()), ["(_.x >= -1.0)", "(_.x <= 1.0)"]),
        (T.select(r=T.x**0.5), ["(_.x >= 0.0)"]),
        (T.select(r=T.x.cast("int64")), ["(_.x >= -2**63)", "(_.x < 2**63)"]),
        (T.select(r=T.a.cast("int32")), ["(_.a >= -2**31)", "(_.a < 2**31)"]),
        (T.select(r=ibis.literal("ab").repeat(T.a)), ["(_.a < 2**30)"]),  # pyrefly: ignore
        (T.select(r=T.big * 2), ["(_.big >= -4 * 10**35)", "(_.big < 5 * 10**35)"]),
        (
            T.select(r=T.d + ibis.interval(days=10)),
            ["(_.d >= date(1, 1, 1))", "(_.d < date(9999, 1, 1))"],
        ),
    ],
    ids=lambda v: v if isinstance(v, str) else None,
)
def test_inferred_preconditions_prove_the_plan(expr, conds):
    report = verify(expr, counterexamples=0)
    assert report.proved, str(report)
    assert inferred(report) == conds
    off = verify(expr, counterexamples=0, on_inferred="off")
    assert not off.proved
    assert all(i.hint for i in off.errors)


@pytest.mark.parametrize(
    ("expr", "hint"),
    [
        # Either side finite rules out `∞ / ∞`: no single weakest choice.
        (T.select(r=T.x / T.y), "no single bound rules it out"),
        # An offset from the start or from the end: two incomparable ranges.
        (T.select(r=T.s.substr(T.a)), "no single bound rules it out"),
        (T.select(r=T.big + T.big), "no single bound rules it out"),
    ],
)
def test_choices_are_suggested_not_assumed(expr, hint):
    report = verify(expr, counterexamples=0)
    assert not report.proved
    assert any(i.hint and i.hint.startswith(hint) for i in report.errors), report.errors


G = T.group_by("s")


@pytest.mark.parametrize(
    ("expr", "conds"),
    [
        # A SUM of integers that are each at least 1 is not 0.
        (G.aggregate(r=T.x.sum() / T.a.sum()), ["(_.a >= 1)"]),
        # A grouped COUNT of a column that is never NULL is at least 1.
        (G.aggregate(r=T.x.sum() / T.b.count()), ["_.b.notnull()"]),
        (G.aggregate(r=T.x.sum() / T.b.nunique()), ["_.b.notnull()"]),
        # A decimal SUM, converted to a double: each value at least 0.01.
        (
            G.aggregate(r=T.x.sum() / T.big.sum().cast("float64")),
            ["(_.big >= 0.01)", "(_.big < 9 * 10**16)"],
        ),
    ],
    ids=["sum", "count", "count distinct", "decimal sum"],
)
def test_a_divisor_that_is_an_aggregate(expr, conds):
    """The inference looks through a divisor's `SUM` or `COUNT`
    (`Infer.pullNe`), and the proof holds with what it proposes."""
    report = verify(expr, counterexamples=0)
    assert inferred(report) == conds
    assert "division by zero" not in [i.kind for i in report.errors]


def test_a_global_count_divisor_gets_no_bound():
    """Without groups an empty input has a COUNT of 0, which no column rules out."""
    report = verify(T.aggregate(r=T.x.sum() / T.b.count()), counterexamples=0)
    [issue] = [i for i in report.errors if i.kind == "division by zero"]
    assert issue.hint is not None and issue.hint.startswith("no bound on an input column")


def test_a_computed_divisor_gets_no_bound():
    report = verify(T.select(r=T.a % (T.b * T.b)), counterexamples=0, on_inferred="off")
    [issue] = [i for i in report.errors if i.kind == "division by zero"]
    assert issue.hint is not None and issue.hint.startswith("no bound on an input column")


@transform(requires={"orders": [_.qty >= 0]}, ensures=[])
def unit_price(orders):
    return orders.select(orders.id, price=orders.total // orders.qty)


def test_a_divisor_is_checked_on_the_data():
    rows = {"id": [1, 2], "total": [30, 10], "qty": [3, 2]}
    src = StaticSource(pa.table(rows), name="orders")
    node = src.pipe(unit_price)
    first = node.refresh()[node.name]
    assert discharged(first.preconditions)[("orders", "(_.qty != 0)")] == ON_DATA
    assert "requires orders: (_.qty != 0) (inferred, checked on data)" in str(first)
    zero = StaticSource(pa.table({"id": [1], "total": [5], "qty": [0]}), name="zeros")
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of zeros violate \(_.qty != 0\)"):
        zero.pipe(unit_price).refresh()
