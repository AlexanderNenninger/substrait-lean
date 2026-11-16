"""The transform the orchestrator examples verify.

`big_orders` keeps the orders above 10. Its contract says what it needs of
`orders` and what it promises about the result. `schemas` lets
`sverify check templates/orchestrators/orders.py` prove it in CI without a
driver script; the orchestrator examples (`dagster_asset.py`, `airflow_dag.py`)
prove it again before each run and apply it to the data.
"""

from __future__ import annotations

import ibis
import pyarrow as pa
import sverify as sv
from ibis import _

SCHEMA = {"id": "int64", "amount": "int64"}


@sv.transform(
    requires=[_.amount >= 0, _.amount < 2**62, sv.unique("id")],
    ensures=[_.amount > 10, sv.unique("id")],
    schemas={"orders": SCHEMA},
)
def big_orders(orders):
    return orders.filter(orders.amount > 10)


def prove() -> sv.Report:
    """The contract's proof for the declared schema: no data is read."""
    return big_orders.check(orders=SCHEMA)


def run(orders: pa.Table) -> pa.Table:
    """Apply the transform to `orders`: the preconditions are checked on the
    data, the postconditions are proved, and the result is computed."""
    con = ibis.duckdb.connect()
    return big_orders(con.create_table("orders", orders)).to_pyarrow()
