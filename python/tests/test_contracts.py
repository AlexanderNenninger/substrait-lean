"""Contracts: postconditions are proved from preconditions, or refused."""

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.contracts import violations
from sverify.examples import customers, orders


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL", _.doubled > 20],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


def test_postconditions_are_proved():
    doubled(orders)
    report = doubled.last_report
    assert report is not None
    assert report.proved
    assert report.facts["doubled"] == "an integer ≥ 22"
    assert report.facts["id"] == "any integer"  # never NULL, by the precondition


def test_unprovable_postcondition_is_refused():
    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    with pytest.raises(sv.VerificationError) as e:
        plus_one(orders)
    assert e.value.report.unproved[0].value == "TRUE or FALSE"
    assert e.value.report.facts["total"] == "an integer ≥ 1"


def test_null_propagates_unless_ruled_out():
    # Without a precondition, `amount + 1` can be NULL...
    report = sv.verify(orders.select(t=orders.amount + 1), ensures=[_.t.notnull()])
    assert not report.proved
    # ...and a filter on `amount` rules that out (NULL > 0 is not TRUE).
    report = sv.verify(
        orders.filter(orders.amount > 0).select(t=orders.amount + 1), ensures=[_.t.notnull()]
    )
    assert report.proved


def test_inner_join_keeps_facts_left_join_does_not():
    inner = orders.join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    )
    left = orders.left_join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    )
    pre = {"customers": [_.city.notnull()]}
    assert sv.verify(inner, requires=pre, ensures=[_.city.notnull()]).proved
    report = sv.verify(left, requires=pre, ensures=[_.city.notnull()])
    assert not report.proved
    assert "NULL" in report.facts["city"]


def test_sql_transform_and_conditions():
    report = sv.verify(
        "select id, amount - 5 as rest from orders where amount >= 5",
        tables={"orders": orders},
        ensures=["rest >= 0", "rest IS NOT NULL"],
    )
    assert report.proved


def test_non_nullable_schema_is_used():
    strict = ibis.table({"id": "!int64", "amount": "int64"}, name="strict")
    assert sv.verify(strict.select("id"), ensures=[_.id.notnull()]).proved
    assert not sv.verify(strict.select("amount"), ensures=[_.amount.notnull()]).proved


def bound_orders(rows):
    con = sv.connect()
    con.sql("create table orders(id bigint, customer varchar, amount bigint)")
    if rows:
        con.executemany("insert into orders values (?, ?, ?)", rows)
    return ibis.duckdb.from_connection(con).table("orders")


def test_preconditions_are_checked_on_data():
    with pytest.raises(sv.PreconditionError, match="amount >= 0"):
        doubled(bound_orders([(1, "ada", -3)]))
    doubled(bound_orders([(1, "ada", 30)]))


def test_runtime_fallback_checks_unproved_postconditions():
    @sv.transform(ensures=[_.amount < 100], on_unproved="runtime")
    def passthrough(orders):
        return orders.select(orders.amount)

    passthrough(bound_orders([(1, "ada", 30)]))
    with pytest.raises(sv.PostconditionError):
        passthrough(bound_orders([(1, "ada", 300)]))


# Soundness on data: whatever Lean proves must hold on any input that satisfies
# the preconditions.
CONTRACTS = [
    (
        {"orders": [_.amount >= 0, _.id.notnull()]},
        lambda o: o.filter(o.amount > 10).select(o.id, d=o.amount * 2 - 3),
        [_.d > 15, _.d.notnull(), _.id.notnull(), _.d >= 19, _.d > 19],
    ),
    (
        {"orders": [_.amount <= 50]},
        lambda o: o.filter(o.amount >= -5).select(n=-o.amount, s=o.amount - 7),
        [_.n >= -50, _.n <= 5, _.s <= 43, _.s >= -12, _.n.notnull(), _.n > -50],
    ),
]
amounts = st.one_of(st.none(), st.integers(-100, 100))


@pytest.mark.parametrize("index", range(len(CONTRACTS)))
@settings(max_examples=25, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(data=st.data())
def test_proved_postconditions_hold_on_data(index, data):
    requires, make, ensures = CONTRACTS[index]
    report = sv.verify(make(orders), requires=requires, ensures=ensures)
    assert any(c.proved for c in report.ensures)
    rows = data.draw(st.lists(st.tuples(st.integers(0, 5) | st.none(), st.just("ada"), amounts)))
    table = bound_orders(rows)
    rows_ok = all(violations(table, c) == 0 for c in requires["orders"])
    if not rows_ok:
        return
    result = make(table)
    for cond, checked in zip(ensures, report.ensures, strict=True):
        if checked.proved:
            assert violations(result, cond) == 0, checked.label
