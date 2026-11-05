"""Task 6b: on_unproved="warn" builds the node; does refresh then run it?"""

import warnings

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.io import StaticSource

orders = StaticSource(pa.table({"id": [1, 2], "amount": [5, 50]}), name="orders")


@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.amount > 10], on_unproved="warn")
def big(orders):
    return orders.select("id", "amount")


with warnings.catch_warnings(record=True) as w:
    warnings.simplefilter("always")
    node = orders.pipe(big)
    print("warnings:", [f"{x.category.__name__}: {str(x.message)[:200]}" for x in w])
try:
    print(node.refresh())
except Exception as e:
    print(f"refresh: {type(e).__name__}: {e}")
print(node.refresh(unverified=True).summary())
