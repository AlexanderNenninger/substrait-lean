"""Preconditions that relate columns, in proofs (#597, steps 1 and 2).

A precondition is kept whole as a fact about each row. An `ensures` that
restates it is proved where the plan carries it through unchanged, and a
filter or a `CASE` branch that rules out some of its disjuncts narrows the
columns of the rest.
"""

import ibis
import pytest
from ibis import _

import sverify as sv

t = ibis.table({"a": "int64", "b": "int64"}, name="t")
u = ibis.table({"a": "int64", "b": "int64"}, name="u")
s = ibis.table({"a": "int64", "c": "int64"}, name="s")

IMPLIES = (_.a <= 0) | (_.b < 0)  # a > 0 implies b < 0
NOT_NULL = [_.a.notnull(), _.b.notnull()]


def verify(q, requires, ensures, tables=None):
    return sv.verify(q, tables=tables or {"t": t}, requires=requires, ensures=ensures)


# The table of #597: what steps 1 and 2 prove.
@pytest.mark.parametrize(
    ("requires", "ensures"),
    [
        pytest.param([_.b < 0], [_.b < 0], id="per-column"),
        pytest.param([IMPLIES, *NOT_NULL], [_.b < 0], id="implication-under-filter"),
        pytest.param([IMPLIES], [_.b < 0], id="implication-nullable-under-filter"),
        pytest.param([ibis.ifelse(_.a > 0, _.b < 0, True)], [_.b < 0], id="ifelse-under-filter"),
    ],
)
def test_a_filter_selects_the_disjunct(requires, ensures):
    q = t.filter(_.a > 0).select("a", "b")
    report = verify(q, {"t": requires}, ensures)
    assert report.proved
    assert report.facts["b"] == "an integer ≤ -1"


@pytest.mark.parametrize("not_null", [True, False])
def test_an_ensures_that_restates_a_requires_is_proved(not_null):
    requires = [IMPLIES, *NOT_NULL] if not_null else [IMPLIES]
    report = verify(t.select("a", "b"), {"t": requires}, [IMPLIES])
    assert report.proved


def test_a_case_branch_selects_the_disjunct():
    report = verify(t.select("a", "b"), {"t": [IMPLIES]}, [ibis.ifelse(_.a > 0, _.b < 0, True)])
    assert report.proved


def test_a_case_branch_narrows_a_computed_column():
    # In the branch where `a > 0`, `b < 0`, so `-b` is positive.
    q = t.select(d=ibis.ifelse(_.a > 0, -_.b, 1))
    report = verify(q, {"t": [IMPLIES, *NOT_NULL, _.b > -1000]}, [_.d >= 1])
    assert report.proved
    assert report.facts["d"] == "an integer in [1, 999]"


def test_a_projection_renames_the_columns_of_a_fact():
    q = t.select(x=_.a, y=_.b)
    report = verify(q, {"t": [IMPLIES]}, [(_.x <= 0) | (_.y < 0)])
    assert report.proved


def test_a_projection_that_drops_a_column_drops_its_facts():
    q = t.select(y=_.b)
    report = verify(q, {"t": [IMPLIES, *NOT_NULL]}, [_.y < 0])
    assert not report.proved


def test_a_union_keeps_the_facts_of_both_inputs():
    q = t.union(u)
    tables = {"t": t, "u": u}
    both = verify(q, {"t": [IMPLIES], "u": [IMPLIES]}, [IMPLIES], tables)
    assert both.proved
    one = verify(q, {"t": [IMPLIES]}, [IMPLIES], tables)
    assert not one.proved


def test_the_right_side_of_a_left_join_loses_its_facts():
    # A row of `t` without a match has NULLs for `s`'s columns, where
    # `c > 0` is not TRUE.
    q = t.left_join(s, t.a == s.a).select(t.a, t.b, s.c)
    tables = {"t": t, "s": s}
    report = verify(q, {"s": [(_.a <= 0) | (_.c > 0)]}, [(_.a <= 0) | (_.c > 0)], tables)
    assert not report.proved


def test_a_filter_keeps_its_own_condition_whole():
    q = t.filter((_.a <= 0) | (_.b < 0)).select("a", "b")
    report = verify(q, {}, [IMPLIES])
    assert report.proved


def test_without_the_filter_the_disjunct_stays_open():
    report = verify(t.select("a", "b"), {"t": [IMPLIES, *NOT_NULL]}, [_.b < 0])
    assert not report.proved
    assert report.unproved[0].counterexample is not None


def test_a_product_needs_more_than_the_implication():
    # `a = -1, b = -1` satisfies the implication, and `a * b = 1`. The fourth
    # row of #597's table does not hold.
    requires = [IMPLIES, *NOT_NULL, _.a.between(-100, 100), _.b.between(-100, 100)]
    report = verify(t.select("a", "b"), {"t": requires}, [_.a * _.b <= 0])
    assert not report.proved
    assert report.unproved[0].counterexample is not None
