"""Task 3: daily revenue per region from a Delta table, into a Delta sink, refreshed.

The data engineer's job: a Delta source with Change Data Feed, a rollup with
a contract, a sink that carries it, and an incremental refresh.
"""

import datetime as dt
import shutil
import tempfile
from pathlib import Path

import pyarrow as pa
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify.errors import PreconditionError, VerificationError
from sverify.io import DeltaSink, DeltaSource

lake = Path(tempfile.mkdtemp())
orders_uri = str(lake / "orders")
d = dt.date(2026, 11, 1)
write_deltalake(
    orders_uri,
    pa.table(
        {
            "order_id": pa.array([1, 2, 3, 4], pa.int64()),
            "region": ["eu", "eu", "us", "us"],
            "day": [d, d, d, d + dt.timedelta(days=1)],
            "amount_cents": pa.array([1000, 2500, 400, 900], pa.int64()),
        }
    ),
    configuration={"delta.enableChangeDataFeed": "true"},
)


@sv.transform(
    requires={
        "orders": [
            sv.unique("order_id"),
            _.amount_cents >= 0,
            _.amount_cents <= 10_000_000,
            _.region.notnull(),
            _.day.notnull(),
        ]
    },
    ensures=[sv.unique("region", "day"), _.revenue_cents >= 0, _.n_orders >= 1],
)
def daily_revenue(orders):
    return orders.group_by(["region", "day"]).aggregate(
        revenue_cents=orders.amount_cents.sum(), n_orders=orders.count()
    )


try:
    rollup = DeltaSource(orders_uri).pipe(daily_revenue).write(DeltaSink(str(lake / "daily")))
except VerificationError as e:
    print("refused:\n", e)
    raise SystemExit

print(daily_revenue.last_report)
print(rollup.refresh())

# New orders arrive, one is deleted.
write_deltalake(
    orders_uri,
    pa.table(
        {
            "order_id": pa.array([5], pa.int64()),
            "region": ["eu"],
            "day": [d],
            "amount_cents": pa.array([100], pa.int64()),
        }
    ),
    mode="append",
)
DeltaTable(orders_uri).delete("order_id = 3")
print(rollup.refresh())
print(sorted(rollup.to_arrow().to_pylist(), key=str))

# What did the sink record? Read the Delta table as a consumer would.
dt_out = DeltaTable(str(lake / "daily"))
print("schema:", dt_out.schema())
print("constraints/config:", dt_out.metadata().configuration)
print("history:", [h.get("operation") for h in dt_out.history()])

# A bad row: a negative amount.
write_deltalake(
    orders_uri,
    pa.table(
        {
            "order_id": pa.array([6], pa.int64()),
            "region": ["us"],
            "day": [d],
            "amount_cents": pa.array([-5], pa.int64()),
        }
    ),
    mode="append",
)
try:
    rollup.refresh()
except PreconditionError as e:
    print("refused batch:", e)

print("contract:", DeltaSource(str(lake / "daily")).contract())
shutil.rmtree(lake)
