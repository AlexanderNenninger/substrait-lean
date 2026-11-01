"""An example test file for a contracted transform, with sverify's pytest
plugin (`sverify.pytest_plugin`) and `sverify.testing`.

The plugin is registered when sverify is installed, so these tests need no
conftest: `sv_source` makes in-memory sources, and a test that takes
`sv_engine` runs once per installed engine. `tests/test_testing.py` also
runs this file on its own with pytester.
"""

import datetime as dt

from hypothesis import given, settings
from ibis import _

import sverify as sv
from sverify.testing import assert_contract, assert_engines_agree, cases

ORDERS = {"id": "!int64", "customer": "string", "amount": "!int64", "ts": "!timestamp"}
CUSTOMERS = {"name": "!string", "city": "string"}


@sv.transform(
    requires={"orders": [sv.unique("id"), _.amount >= 0, _.ts < dt.datetime(2100, 1, 1)]},
    ensures=[sv.unique("id"), _.amount > 10, _.doubled > 20],
)
def big_orders(orders):
    big = orders.filter(orders.amount > 10)
    return big.select(big.id, big.customer, big.amount, doubled=big.amount * 2)


@sv.transform(
    requires={"orders": [_.amount > 10], "customers": [sv.unique("name")]},
    ensures=[_.city.notnull(), sv.unique("city"), _.n_orders >= 0],
)
def city_revenue(orders, customers):
    joined = orders.join(customers, orders.customer == customers.name)
    known = joined.filter(joined.city.notnull())
    return known.group_by("city").aggregate(n_orders=_.count(), revenue=_.amount.sum())


def day(d: int) -> dt.datetime:
    return dt.datetime(2026, 5, d)


def test_the_contracts_are_proved(sv_source):
    orders = sv_source([], ORDERS, name="orders")
    customers = sv_source([], CUSTOMERS, name="customers")
    # Building the nodes proves each contract, and that `city_revenue`'s
    # precondition follows from what `big_orders` guarantees.
    assert_contract(orders.pipe(big_orders).pipe(city_revenue, customers=customers))


def test_big_orders_on_rows(sv_source, sv_engine):
    orders = sv_source([], ORDERS, name="orders")
    data = {"orders": [(1, "ada", 30, day(1)), (2, "bob", 5, day(2)), (3, None, 11, day(3))]}
    assert_contract(
        orders.pipe(big_orders),
        data=data,
        expected=[(1, "ada", 30, 60), (3, None, 11, 22)],
        engine=sv_engine,
    )


def test_city_revenue_on_rows(sv_source):
    orders = sv_source([], ORDERS, name="orders")
    customers = sv_source([], CUSTOMERS, name="customers")
    node = orders.pipe(big_orders).pipe(city_revenue, customers=customers)
    data = {
        "orders": [(1, "ada", 30, day(1)), (2, "bob", 50, day(2)), (3, "cy", 12, day(3))],
        "customers": [("ada", "Paris"), ("bob", "Paris"), ("cy", None)],
    }
    assert_contract(node, data=data, expected=[{"city": "Paris", "n_orders": 2, "revenue": 80}])
    assert_engines_agree(node, data)


def test_every_city_has_a_big_order(sv_source):
    orders = sv_source([], ORDERS, name="orders")
    customers = sv_source([], CUSTOMERS, name="customers")
    node = orders.pipe(big_orders).pipe(city_revenue, customers=customers)

    # `cases` draws inputs that meet the preconditions; the property is about
    # the code around the node: each city in the output has a big order.
    @settings(max_examples=25, deadline=None)
    @given(cases(node, max_rows=4))
    def check(data):
        out = assert_contract(node, data=data)
        cities = {c["name"]: c["city"] for c in data["customers"].to_pylist()}
        big = {cities.get(o["customer"]) for o in data["orders"].to_pylist() if o["amount"] > 10}
        assert set(out["city"].to_pylist()) <= big

    check()
