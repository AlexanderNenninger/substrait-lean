"""Composing contracted transformations: a downstream precondition on an
upstream result is proved from the upstream contract, never checked on data."""

import pytest
from ibis import _

import sverify as sv
from _pipelines import bound_orders, spy_on
from sverify.contracts import label, provenance
from sverify.errors import CompositionError, PreconditionError
from sverify_dev.examples import orders


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount >= 0, _.amount.notnull()])
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull()],
)
def doubled(t):
    return t.select(t.id, doubled=t.amount * 2)


@sv.transform(requires={"t": ["doubled > 0"]}, ensures=["doubled > 0"])
def positive(t):
    return t


def test_composed_contracts_connect():
    result = doubled(paid(orders))
    report = doubled.last_report
    assert report is not None and report.proved
    # `doubled` was proved against `paid`'s guarantees, not against `orders`.
    assert report.requires == {"paid": ["(_.amount >= 0)", "_.amount.notnull()"]}
    prov = provenance(result)
    assert prov is not None and prov.transform is doubled
    assert {t: [label(c) for c in cs] for t, cs in prov.external.items()} == {
        "orders": ["(_.amount >= 0)"]
    }
    assert not prov.unproved_links


def test_broken_link_names_both_sides():
    @sv.transform(ensures=[_.amount.notnull()])
    def not_null(orders):
        return orders.filter(orders.amount.notnull())

    with pytest.raises(CompositionError) as e:
        doubled(not_null(orders))
    msg = str(e.value)
    assert msg.startswith("doubled needs (_.amount >= 0) (it is TRUE or FALSE) on 't'")
    assert msg.endswith("not_null only guarantees _.amount.notnull()")


def test_obligation_may_follow_from_more_than_the_ensures():
    # `positive` needs `doubled > 0`, which `doubled` does not promise but
    # establishes from what `strictly_paid` guarantees.
    @sv.transform(requires={"orders": [_.amount > 0]}, ensures=[_.amount > 0])
    def strictly_paid(orders):
        return orders.filter(orders.amount.notnull())

    positive(doubled(strictly_paid(orders)))
    with pytest.raises(CompositionError, match="positive needs doubled > 0"):
        positive(doubled(paid(orders)))


def test_links_are_not_checked_on_data(monkeypatch):
    checked = spy_on(monkeypatch, "sverify.contracts.violations", lambda t, cond, *a: label(cond))
    data = bound_orders([(1, "ada", 5), (2, "bob", 7)])
    result = doubled(paid(data))
    # Only the base table's precondition is checked on the data.
    assert checked == ["(_.amount >= 0)"]
    assert sorted(result.execute()["doubled"]) == [10, 14]


def test_plain_ibis_in_the_chain():
    # A plain expression carries no guarantees, but obligations that follow
    # from its own operations are still proved...
    doubled(paid(orders).filter(_.id > 3))
    doubled(orders.filter(orders.amount > 0))
    # ...and the rest are checked on the data like a base table's.
    with pytest.raises(PreconditionError, match="violate"):
        doubled(bound_orders([(1, "ada", -5)]).filter(_.id > 0))
    prov = provenance(doubled(bound_orders([(1, "ada", 5)]).filter(_.id > 0)))
    assert prov is not None and prov.unproved_links


def test_keys_propagate_through_links():
    @sv.transform(requires={"orders": [sv.unique("id")]}, ensures=[sv.unique("id")])
    def big(orders):
        return orders.filter(orders.amount > 10)

    @sv.transform(requires={"t": [sv.unique("id")]}, ensures=[sv.unique("id")])
    def tagged(t):
        return t.mutate(tag=t.amount + 1)

    tagged(big(orders))
    assert tagged.last_report is not None
    assert tagged.last_report.requires == {"big": ["unique(id)"]}
    with pytest.raises(CompositionError, match=r"tagged needs unique\(id\)"):
        tagged(paid(orders))


def test_two_contracted_inputs():
    @sv.transform(
        requires={"a": [_.doubled.notnull()], "b": [_.amount.notnull()]},
        ensures=[_.total.notnull()],
    )
    def combine(a, b):
        j = a.join(b, a.id == b.id)
        return j.select(total=j.doubled + j.amount)

    combine(doubled(paid(orders)), paid(orders))
    assert combine.last_report is not None
    assert set(combine.last_report.requires) == {"doubled", "paid"}


def test_runtime_mode_checks_a_broken_link_on_data():
    @sv.transform(ensures=[_.amount.notnull()])
    def not_null(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(requires={"t": [_.amount >= 0]}, ensures=[_.amount >= 0], on_unproved="runtime")
    def lenient(t):
        return t

    lenient(not_null(bound_orders([(1, "ada", 5)])))
    with pytest.raises(PreconditionError, match="violate"):
        lenient(not_null(bound_orders([(1, "ada", -5)])))
    prov = provenance(lenient(not_null(bound_orders([(1, "ada", 5)]))))
    assert prov is not None and prov.unproved_links == ["lenient: (_.amount >= 0) on t"]
