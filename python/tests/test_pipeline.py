"""Contracted incremental views and pipelines of views over views.

Contracted views check preconditions per batch and keep their guarantees in
every state; pipelines pass each view's change on to the views reading it.
Both are tested differentially against recomputation from scratch."""

import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.contracts import label, violations
from sverify.examples import create_tables, orders

SETTINGS = settings(max_examples=20, deadline=None, suppress_health_check=[HealthCheck.too_slow])


@sv.transform(
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount.notnull(), sv.unique("id")]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)


def setup(orders=(), customers=()):
    con = sv.connect()
    create_tables(con, orders, customers)
    return con


def ensures_hold(view):
    for c in view.guarantees:
        assert violations(view.table, c) == 0, label(c)


# -- Step 2: contracted views ------------------------------------------------


def test_contracted_view_knows_its_contract():
    con = setup([(1, "ada", 5), (2, "bob", 0)])
    view = sv.IncrementalView(con, doubled(paid(con.table("orders"))), "v")
    assert [label(c) for c in view.guarantees] == [
        "(_.doubled >= 0)",
        "_.doubled.notnull()",
        "unique(id)",
    ]
    assert [label(c) for c in view.requires["orders"]] == ["(_.amount >= 0)", "unique(id)"]
    assert view.rows() == [(1, "ada", 10), (2, "bob", 0)]


def test_preconditions_are_checked_at_creation():
    # Built on the unbound `orders`, so the call itself checks nothing.
    con = setup([(1, "ada", 5), (1, "bob", 7)])
    with pytest.raises(sv.PreconditionError, match=r"unique\(id\)"):
        sv.IncrementalView(con, paid(orders), "v")


def test_batches_violating_preconditions_change_nothing():
    con = setup([(1, "ada", 5), (2, "bob", 7)])
    view = sv.IncrementalView(con, doubled(paid(con.table("orders"))), "v")
    before = view.rows()
    with pytest.raises(sv.PreconditionError, match=r"inserted row\(s\) of orders violate"):
        view.apply({"orders": sv.Changes(inserts=[(3, "cy", -1)])})
    with pytest.raises(sv.PreconditionError, match=r"inserted key\(s\) of orders violate unique"):
        view.apply({"orders": sv.Changes(inserts=[(2, "cy", 1)])})
    with pytest.raises(sv.PreconditionError, match="unique"):
        view.apply({"orders": sv.Changes(inserts=[(3, "cy", 1), (3, "dan", 2)])})
    assert view.rows() == before
    assert sv.table_rows(con, "orders") == [(1, "ada", 5), (2, "bob", 7)]
    # Deleting a key frees it for the same batch.
    view.apply({"orders": sv.Changes(inserts=[(2, "cy", 1)], deletes=[(2, "bob", 7)])})
    assert view.rows() == view.recompute() == [(1, "ada", 10), (2, "cy", 2)]


def test_batches_are_checked_without_reading_the_tables(monkeypatch):
    con = setup([(1, "ada", 5), (2, "bob", 7)])
    view = sv.IncrementalView(con, doubled(paid(con.table("orders"))), "v")
    checked = []
    real = violations

    def spy(table, cond):
        checked.append(table.get_name())
        return real(table, cond)

    monkeypatch.setattr(sv.incremental, "violations", spy)
    view.apply({"orders": sv.Changes(inserts=[(3, "cy", 1)])})
    assert checked == ["orders$inserts"]


def test_unproved_links_cannot_be_maintained():
    con = setup([(1, "ada", 5)])
    derived = con.table("orders").filter(_.id > 0)
    with pytest.raises(ValueError, match="not proved"):
        sv.IncrementalView(con, doubled(derived), "v")


names = st.sampled_from(["ada", "bob", None])


@st.composite
def keyed_batch(draw, con):
    """Inserts and deletes that keep `id` a key and `amount` non-negative."""
    current = sv.table_rows(con, "orders")
    deletes = draw(st.lists(st.sampled_from(current), unique=True, max_size=2)) if current else []
    kept = {r[0] for r in current} - {r[0] for r in deletes}
    fresh = st.integers(0, 8).filter(lambda i: i not in kept)
    ids = draw(st.lists(fresh, unique=True, max_size=3))
    amounts = st.integers(0, 30)
    return sv.Changes(inserts=[(i, draw(names), draw(amounts)) for i in ids], deletes=deletes)


@pytest.mark.parametrize("engine", sv.ENGINES)
@SETTINGS
@given(data=st.data())
def test_guarantees_hold_in_every_state(engine, data):
    con = setup()
    view = sv.IncrementalView(con, doubled(paid(con.table("orders"))), "v", engine)
    for _step in range(data.draw(st.integers(1, 4))):
        view.apply({"orders": data.draw(keyed_batch(con))})
        assert view.rows() == view.recompute()
        ensures_hold(view)
