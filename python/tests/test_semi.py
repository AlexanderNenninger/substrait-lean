"""Delta rules for semi and anti joins (`sverify._semi`,
`SubstraitLean/IncrementalSemi.lean`, #248): the view keeps a count of
matches per key and changes with each batch of either side, and its rows
equal a full recompute over random change streams."""

import random

import pyarrow as pa
import pytest

from _pipelines import recomputed, rows
from sverify.io import Changes, StaticSource

ORDERS = pa.schema([("id", pa.int64()), ("cust", pa.string()), ("amount", pa.int64())])
CUSTOMERS = pa.schema([("cust", pa.string()), ("tier", pa.int64())])
ENGINES = ["duckdb", "polars", "datafusion"]


def table(schema: pa.Schema, rows) -> pa.Table:
    return pa.table({n: [r[i] for r in rows] for i, n in enumerate(schema.names)}, schema=schema)


def gold_orders(orders, customers, *, anti=False):
    gold = customers.filter(customers.tier > 0)
    on = orders.cust == gold.cust
    j = orders.anti_join(gold, on) if anti else orders.semi_join(gold, on)
    return j.filter(j.amount > -40).select(j.id, j.cust, doubled=j.amount * 2)


def view(node):
    assert node._stage is not None
    return node._stage.view


def run_stream(seed: int, engine: str, anti: bool, steps: int = 40) -> None:
    """Inserts and deletes on both sides over few keys, NULLs among them, so
    that keys gain and lose their matches."""
    rng = random.Random(seed)
    custs = ["a", "b", "c", None]

    def order():
        return (rng.randrange(5), rng.choice(custs), rng.randrange(-50, 50))

    def customer():
        return (rng.choice(custs), rng.randrange(-1, 3))

    live: dict[str, list[tuple]] = {
        "orders": [order() for _ in range(10)],
        "customers": [customer() for _ in range(4)],
    }
    orders = StaticSource(table(ORDERS, live["orders"]), name="orders")
    customers = StaticSource(table(CUSTOMERS, live["customers"]), name="customers")
    node = orders.pipe(
        lambda o, customers: gold_orders(o, customers, anti=anti), customers=customers
    )
    node.refresh(engine=engine)
    assert view(node).strategy == "delta rules" and view(node).semi is not None
    sides = [(orders, "orders", order, ORDERS), (customers, "customers", customer, CUSTOMERS)]
    for _ in range(steps):
        for src, name, make, schema in sides:
            if rng.random() < 0.4:
                continue
            ins = [make() for _ in range(rng.randrange(3))]
            dels = rng.sample(live[name], min(len(live[name]), rng.randrange(3)))
            for d in dels:
                live[name].remove(d)
            live[name] += ins
            src.apply(Changes(inserts=table(schema, ins), deletes=table(schema, dels)))
        out = node.refresh(engine=engine)
        report = out[node.name].report
        assert report is not None and not report.touched and not report.diffed
        assert rows(node) == recomputed(node, orders, customers)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("seed", range(3))
def test_semi_join_matches_a_full_recompute(seed, engine):
    run_stream(seed, engine, anti=False)


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("seed", range(3))
def test_anti_join_matches_a_full_recompute(seed, engine):
    run_stream(seed, engine, anti=True)


@pytest.mark.parametrize("anti", [False, True], ids=["semi", "anti"])
def test_a_key_gains_and_loses_its_matches(anti):
    orders = StaticSource(table(ORDERS, [(1, "a", 5), (2, "a", 7), (3, None, 1)]), name="orders")
    customers = StaticSource(table(CUSTOMERS, [("b", 1)]), name="customers")
    node = orders.pipe(
        lambda o, customers: gold_orders(o, customers, anti=anti), customers=customers
    )
    node.refresh()
    with_a = [(1, "a", 10), (2, "a", 14)]
    without_a = [(3, None, 2)]
    for batch, matched in [
        # a's first match emits a's old orders (an anti join retracts them).
        (Changes(inserts=table(CUSTOMERS, [("a", 2)])), True),
        # A second match changes nothing.
        (Changes(inserts=table(CUSTOMERS, [("a", 1)])), True),
        (Changes(deletes=table(CUSTOMERS, [("a", 2)])), True),
        # The last one goes: the orders go back.
        (Changes(deletes=table(CUSTOMERS, [("a", 1)])), False),
        # A customer that is not gold does not count.
        (Changes(inserts=table(CUSTOMERS, [("a", 0), (None, 1)])), False),
    ]:
        customers.apply(batch)
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, orders, customers)
        semi = with_a if matched else []
        anti_rows = without_a + ([] if matched else with_a)
        assert sorted(rows(node), key=str) == sorted(anti_rows if anti else semi, key=str)


def test_both_sides_change_in_one_batch():
    orders = StaticSource(table(ORDERS, [(1, "a", 5)]), name="orders")
    customers = StaticSource(table(CUSTOMERS, [("a", 1)]), name="customers")
    node = orders.pipe(gold_orders, customers=customers)
    node.refresh()
    # a loses its match while a new order of a arrives; b gains one with its order.
    orders.apply(Changes(inserts=table(ORDERS, [(2, "a", 3), (3, "b", 4)])))
    customers.apply(
        Changes(deletes=table(CUSTOMERS, [("a", 1)]), inserts=table(CUSTOMERS, [("b", 2)]))
    )
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, orders, customers) == [(3, "b", 8)]


def test_a_composite_key():
    schema = pa.schema([("x", pa.int64()), ("y", pa.string()), ("v", pa.int64())])
    left = StaticSource(table(schema, [(1, "p", 1), (1, "q", 2), (2, "p", 3)]), name="left")
    right = StaticSource(table(schema, [(1, "p", 0)]), name="right")

    def step(left, right):
        return left.semi_join(right, [left.x == right.x, left.y == right.y])

    node = left.pipe(step, right=right)
    node.refresh()
    assert view(node).strategy == "delta rules"
    for batch in [
        Changes(inserts=table(schema, [(2, "p", 9), (1, None, 1)])),
        Changes(deletes=table(schema, [(1, "p", 0)])),
    ]:
        right.apply(batch)
        left.apply(Changes(inserts=table(schema, [(1, None, 5)])))
        node.refresh(audit=True)
        assert rows(node) == recomputed(node, left, right)


def test_a_condition_other_than_equal_keys_is_recomputed():
    orders = StaticSource(table(ORDERS, [(1, "a", 5)]), name="orders")
    customers = StaticSource(table(CUSTOMERS, [("a", 1)]), name="customers")

    def step(orders, customers):
        return orders.semi_join(customers, orders.amount > customers.tier)

    node = orders.pipe(step, customers=customers)
    node.refresh()
    assert view(node).semi is None
    assert view(node).strategy == "recompute and diff"


def test_status_says_the_view_is_maintained():
    orders = StaticSource(table(ORDERS, [(1, "a", 5)]), name="orders")
    customers = StaticSource(table(CUSTOMERS, [("a", 1)]), name="customers")
    node = orders.pipe(gold_orders, customers=customers)
    node.refresh()
    status = node.status().nodes[0]
    assert status.recomputed is None and status.touched is None
    customers.apply(Changes(inserts=table(CUSTOMERS, [("b", 1)])))
    out = node.refresh()
    assert "recomputed" not in out[node.name].summary()
