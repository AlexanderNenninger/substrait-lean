"""The checker bounds a double `+`, `-`, `*` and `/` by one divisor at the
exact result's ends rounded as the operation rounds them, so true range
statements about doubles are proved (#1485, items 7 and 26, #441)."""

import ibis
import pytest

import sverify as sv


def facts(expr, **kw) -> str:
    return str(sv.verify(expr, counterexamples=0, **kw).facts["v"])


def bounded():
    t = ibis.table({"a": "!int64", "x": "!float64", "y": "!float64"}, name="t")
    return t.filter(t.a.between(0, 8) & t.x.between(0, 1) & t.y.between(0, 1))


@pytest.mark.parametrize(
    ("name", "build", "want"),
    [
        ("a / 8", lambda t: t.a / 8, "a double ≥ 0.0 and ≤ 1.0"),
        ("a * 0.125", lambda t: t.a * 0.125, "a double ≥ 0.0 and ≤ 1.0"),
        ("x + y", lambda t: t.x + t.y, "a double ≥ 0.0 and ≤ 2.0"),
        ("(x + y) / 2", lambda t: (t.x + t.y) / 2, "a double ≥ 0.0 and ≤ 1.0"),
        ("x - y", lambda t: t.x - t.y, "a double ≥ -1.0 and ≤ 1.0"),
        ("a / -8", lambda t: t.a / -8, "a double ≥ -1.0 and ≤ 0.0"),
        ("x.clip(0, 1)", lambda t: t.x.clip(0, 1), "a double ≥ 0.0 and ≤ 1.0"),
    ],
)
def test_the_range_of_a_double_operation_is_the_exact_results(name, build, want):
    t = bounded()
    assert facts(t.select(v=build(t))) == want, name


def test_a_sum_keeps_its_lower_end_and_a_product_by_a_constant_proves_positive():
    """`amount >= 0` and `amount < 1e300` prove `amount * 3 + 1 > 0` (#1485, item 7): the
    result is at least `1`, where the error term of the sum used to pull it to `0`."""
    t = ibis.table({"amount": "!float64"}, name="t")
    t = t.filter(t.amount.between(0, 1e300))
    report = sv.verify(t.select(v=t.amount * 3 + 1), ensures=[ibis._.v > 0], counterexamples=0)
    assert report.verdict == sv.Verdict.PROVED
    assert str(report.facts["v"]) == "a double ≥ 1.0 and ≤ 3e+300"
    # `amount * 3` alone can be `0`, so the same statement is not proved of it.
    report = sv.verify(t.select(v=t.amount * 3), ensures=[ibis._.v > 0], counterexamples=0)
    assert report.verdict == sv.Verdict.UNPROVED


def test_the_bound_holds_at_its_ends_on_data():
    """The ends are values the operation takes: `8 / 8` and `1 + 1` meet them."""
    import pyarrow as pa

    t = bounded()
    report = sv.verify(t.select(q=t.a / 8, s=t.x + t.y), counterexamples=0)
    con = sv.connect()
    con.put(
        "t",
        pa.table({"a": pa.array([0, 8], pa.int64()), "x": [0.0, 1.0], "y": [0.0, 1.0]}),
    )
    out = report.run(con, "duckdb")
    assert out.column("q").to_pylist() == [0.0, 1.0]
    assert out.column("s").to_pylist() == [0.0, 2.0]


def test_a_bound_with_one_end_proves_the_headline_case():
    """`amount >= 0` alone proves `amount * 3 + 1 > 0` (#1485, item 7): the sum and the
    product keep their lower end whatever the column is above it, `+∞` and NaN included."""
    t = ibis.table({"amount": "!float64"}, name="t")
    t = t.filter(t.amount >= 0)
    report = sv.verify(t.select(v=t.amount * 3 + 1), ensures=[ibis._.v > 0], counterexamples=0)
    assert report.verdict != sv.Verdict.UNPROVED
    assert str(report.facts["v"]) == "a double ≥ 1.0"
    assert (
        str(sv.verify(t.select(v=t.amount + 1), counterexamples=0).facts["v"]) == "a double ≥ 1.0"
    )
    # `amount * 3` can be `0`, and the ends below `0` are not kept.
    assert sv.verify(
        t.select(v=t.amount * 3), ensures=[ibis._.v > 0], counterexamples=0
    ).verdict == (sv.Verdict.UNPROVED)
    # A difference keeps the lower end too, where the subtrahend is a finite range
    # (`FloatCode.fsub_lower`); a subtrahend with no upper end keeps nothing.
    assert (
        str(sv.verify(t.select(v=t.amount - 1), counterexamples=0).facts["v"]) == "a double ≥ -1.0"
    )
    assert (
        str(sv.verify(t.select(v=t.amount - t.amount), counterexamples=0).facts["v"])
        == "any double"
    )


def test_a_quotient_of_a_non_negative_dividend_by_a_positive_divisor_is_at_least_zero():
    """`x / y` with `x >= 0` and `y >= 1`, each with one end only (`FloatCode.fdiv_nonneg_open`).
    The upper end is not kept: `y` may be NaN, which is above every bound."""
    t = ibis.table({"x": "!float64", "y": "!float64"}, name="t")
    t = t.filter((t.x >= 0) & (t.y >= 1))
    assert str(sv.verify(t.select(v=t.x / t.y), counterexamples=0).facts["v"]) == "a double ≥ 0.0"
    assert str(sv.verify(t.select(v=10 / t.y), counterexamples=0).facts["v"]) == "a double ≥ 0.0"


def test_a_one_ended_bound_is_sound_at_infinity_and_nan_on_data():
    """The values the lower end does not bound: `+∞` and NaN stay at least `1` as codes."""
    import pyarrow as pa

    t = ibis.table({"amount": "!float64"}, name="t")
    t = t.filter(t.amount >= 0)
    report = sv.verify(t.select(v=t.amount * 3 + 1), counterexamples=0)
    con = sv.connect()
    con.put("t", pa.table({"amount": [0.0, 1.5, float("inf"), float("nan")]}))
    got = report.run(con, "duckdb", unverified=True).column("v").to_pylist()
    assert got[:3] == [1.0, 5.5, float("inf")]
    assert got[3] != got[3]  # NaN
