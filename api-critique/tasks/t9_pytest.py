"""Task 9: test a transform with pytest, as the README's "Testing with pytest" shows.

Run with: pytest api-critique/tasks/t9_pytest.py -q
"""

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify.testing import assert_contract, assert_engines_agree, cases, source


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000, _.id.notnull(), sv.unique("id")]},
    ensures=[_.doubled >= 22, sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


SCHEMA = {"id": "int64", "customer": "string", "amount": "int64"}


def test_contract_proved():
    orders = source([], SCHEMA, name="orders")
    assert_contract(orders.pipe(big_orders))


def test_expected_rows():
    orders = source([], SCHEMA, name="orders")
    node = orders.pipe(big_orders)
    data = {"orders": [(1, "ada", 30), (2, "bob", 5)]}
    assert_contract(node, data=data, expected=[(1, 60)])


def test_wrong_expected_rows():
    """What does a failure look like? (Expected to fail; the message is the point.)"""
    orders = source([], SCHEMA, name="orders")
    node = orders.pipe(big_orders)
    with pytest.raises(AssertionError) as info:
        assert_contract(node, data={"orders": [(1, "ada", 30)]}, expected=[(1, 61)])
    print("\nmismatch message:\n", info.value)


def test_bad_input_rows():
    orders = source([], SCHEMA, name="orders")
    node = orders.pipe(big_orders)
    with pytest.raises(Exception) as info:
        assert_contract(node, data={"orders": [(1, "ada", -5), (1, "bob", 30)]}, expected=[])
    print("\nbad input:", type(info.value).__name__, info.value)


def test_engines_agree():
    orders = source([], SCHEMA, name="orders")
    assert_engines_agree(orders.pipe(big_orders), {"orders": [(1, "ada", 30), (2, "bob", 50)]})


def test_engine_fixture(sv_engine, sv_source):
    orders = sv_source([(1, "ada", 30)], SCHEMA, name="orders")
    node = orders.pipe(big_orders)
    node.refresh(engine=sv_engine)
    assert node.to_arrow().to_pylist() == [{"id": 1, "doubled": 60}]


def test_property():
    hypothesis = pytest.importorskip("hypothesis")
    orders = source([], SCHEMA, name="orders")
    node = orders.pipe(big_orders)

    @hypothesis.settings(max_examples=20, deadline=None)
    @hypothesis.given(cases(node))
    def check(data):
        # First try was `all(r[2] >= 0 for r in data["orders"])`, as for `data=`
        # in assert_contract (lists of tuples); cases() yields pyarrow Tables.
        assert all(v >= 0 for v in data["orders"].column("amount").to_pylist())

    check()


def test_contract_of_plain_ibis():
    """Can I assert a contract on an Ibis expression, without a source?"""
    t = ibis.table(SCHEMA, name="orders")
    try:
        assert_contract(big_orders(t))
        print("\nassert_contract on an Ibis expression: works")
    except Exception as e:
        print(f"\nassert_contract on an Ibis expression: {type(e).__name__}: {e}")
