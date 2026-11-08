"""The margin check of a threshold on a double `SUM` (#929, `Rel.marginCheck`).

A filter `SUM(x) > t` over an aggregate keeps a group on an engine as on the
reference when the engine's sum is farther from `t` than twice its bound, a
bound per group from its count and `Σ|x|` (`StdModel.margin_check` in
`float-bounds/FloatBounds/Margin.lean`). The checker writes the check as a
plan of its own; `Report.run` runs it on the engine first and raises if it
flags a group, or, with `on_inferred="warn"`, warns and counts them.
"""

import warnings

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.errors import InferredWarning, PreconditionError

ORDERS = ibis.table({"customer_id": "int64", "amount": "float64"}, name="orders")
HAVING = ORDERS.group_by("customer_id").aggregate(total=_.amount.sum()).filter(_.total > 1000)
REQUIRES = {"orders": [_.amount >= 0]}


@pytest.fixture(scope="module")
def having() -> sv.Report:
    return sv.verify(HAVING, requires=REQUIRES)


@pytest.fixture(scope="module")
def having_warn() -> sv.Report:
    """Any finite amounts, the flagged groups kept."""
    return sv.verify(
        HAVING, requires={"orders": [_.amount.between(-1e300, 1e300)]}, on_inferred="warn"
    )


def _con(ids: list[int], amounts: list[float]) -> sv.engine.Connection:
    c = sv.connect()
    c.put("orders", pa.table({"customer_id": ids, "amount": amounts}))
    return c


def _flagged(groups: list[list[float]], t: float) -> int:
    """The check in Python's doubles, on sums every order agrees on."""
    tiny = 2.0**-1022
    out = 0
    for xs in groups:
        n = len(xs)
        v, a = sum(xs), sum(abs(x) for x in xs)
        c = (8.0 * n + 16.0) * 2.0**-53
        if not abs(v - t) > c * (a + n * tiny) or n > 2**32:
            out += 1
    return out


def test_the_checker_writes_the_check_and_the_rows_are_exact_given_it(having):
    r = having
    assert r.proved
    assert len(r._margin_checks) == 1
    assert r._margin_checks[0]["column"] == "total"
    assert r._rows_exact is not None and all(r._rows_exact.values())
    # No row cap: the SUM's bound is per group, from its own values.
    assert r.epsilon["total"]["theorem"] == "FloatBounds.StdModel.epsilon_group"
    # Without the check the threshold rule refuses the plan, as before (#568).
    off = sv.verify(HAVING, requires=REQUIRES, on_inferred="off")
    assert off._margin_checks == []
    assert off._rows_exact is not None and not any(off._rows_exact.values())


def test_a_filter_no_static_bound_needs_has_no_check():
    """A threshold outside the sums' range, widened by their bound, is
    decided statically (`rule_threshold`)."""
    capped = {"orders": [_.amount.between(0, 1), sv.max_rows(10)]}
    r = sv.verify(HAVING, requires=capped)
    assert r._margin_checks == []


@pytest.mark.parametrize("engine", ["duckdb", pytest.param("polars", marks=pytest.mark.slow)])
def test_far_groups_pass_and_a_near_one_is_refused(having, engine):
    r = having
    far = _con([1, 1, 2, 3], [600.0, 500.0, 5000.0, 10.0])
    got = sorted(r.run(far, engine).to_pylist(), key=lambda row: row["customer_id"])
    assert got == [{"customer_id": 1, "total": 1100.0}, {"customer_id": 2, "total": 5000.0}]
    # 500 + 500 is the threshold itself: the engine's sum may fall either side.
    near = _con([1, 1, 2], [500.0, 500.0, 5000.0])
    with pytest.raises(PreconditionError, match=r"1 group\(s\) have total within its bound"):
        r.run(near, engine)


def test_warn_keeps_the_flagged_groups_and_counts_them(having_warn):
    r = having_warn
    near = _con([1, 1, 2], [500.0, 500.0, 5000.0])
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        got = r.run(near, "duckdb").to_pylist()
    assert got == [{"customer_id": 2, "total": 5000.0}]
    assert r.margin_flags == {"duckdb": 1}
    assert any(isinstance(x.message, InferredWarning) and "group(s)" in str(x.message) for x in w)


@pytest.mark.parametrize(
    "groups",
    [
        [[500.0, 500.0]],
        [[500.0, 500.0000001]],
        [[1000.0], [999.9999999999999], [1000.0000000000002]],
        [[2.0**40, -(2.0**40), 1000.0], [1e-300, 1000.0]],
        [[0.5] * 2000, [1001.0]],
    ],
)
def test_the_check_counts_what_its_formula_says(having_warn, groups):
    ids = [g for g, xs in enumerate(groups) for _x in xs]
    amounts = [x for xs in groups for x in xs]
    r = having_warn
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        r.run(_con(ids, amounts), "duckdb")
    assert r.margin_flags["duckdb"] == _flagged(groups, 1000.0)


def test_a_group_with_no_values_is_not_flagged():
    """Its sum is NULL, which the filter drops on every engine; the check
    decides only groups with a value (`n ≥ 1`, which `check_sound` needs)."""
    c = sv.connect()
    c.put(
        "orders",
        pa.table({"customer_id": [1, 2], "amount": pa.array([None, 5000.0], pa.float64())}),
    )
    r = sv.verify(HAVING, requires={"orders": [_.amount.isnull() | (_.amount >= 0)]})
    assert r.run(c, "duckdb").to_pylist() == [{"customer_id": 2, "total": 5000.0}]
    assert "n ≥ 1" in " ".join(r._margin_checks[0]["conditions"])


AVG_HAVING = ORDERS.group_by("customer_id").aggregate(m=_.amount.mean()).filter(_.m >= 50)


def _flagged_avg(groups: list[list[float]], t: float) -> int:
    """The `AVG` check in Python's doubles (`check_sound_avg`)."""
    tiny = 2.0**-1022
    out = 0
    for xs in groups:
        n = len(xs)
        v, a = sum(xs) / n, sum(abs(x) for x in xs)
        c = (8.0 * n + 32.0) * 2.0**-53
        if not abs(v - t) > c * ((a + n * tiny) / n) or n > 2**32:
            out += 1
    return out


def test_an_avg_threshold_has_a_check():
    r = sv.verify(AVG_HAVING, requires={"orders": [_.amount.between(0, 100)]}, on_inferred="warn")
    assert len(r._margin_checks) == 1
    assert r._rows_exact is not None and all(r._rows_exact.values())
    assert r.epsilon["m"]["theorem"] == "FloatBounds.StdModel.epsilon_group_avg"
    groups = [[40.0, 60.0], [50.0, 50.0, 50.0], [10.0, 99.0], [49.0]]
    ids = [g for g, xs in enumerate(groups) for _x in xs]
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        got = r.run(_con(ids, [x for xs in groups for x in xs]), "duckdb").to_pylist()
    assert r.margin_flags["duckdb"] == _flagged_avg(groups, 50.0) == 2
    assert sorted(row["customer_id"] for row in got) == [0, 1, 2]
