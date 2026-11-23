"""A pipeline the action's own test checks: a postcondition it cannot prove (exit 1)."""

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.io import StaticSource

orders = StaticSource(pa.table({"id": [1, 2], "amount": [30, 5], "qty": [1, 2]}), name="orders")


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.unit >= 0])
def unit_price(orders):
    return orders.select(orders.id, unit=orders.amount // orders.qty)


unit_prices = orders.pipe(unit_price)
