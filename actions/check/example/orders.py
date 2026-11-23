"""A pipeline the action's own test checks: one node, proved."""

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.io import StaticSource

orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders")


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000]},
    ensures=[_.doubled >= 0],
)
def doubled(orders):
    return orders.select(orders.id, doubled=orders.amount * 2)


doubled_orders = orders.pipe(doubled)
