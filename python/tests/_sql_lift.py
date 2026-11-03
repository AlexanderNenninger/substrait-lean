"""What the tests of sverify's own lift (`sverify.sql_lift`, #239) share:
the orders and customers tables, their rows, and their schemas. The tests
are split by area, in `test_sql_lift_<area>.py`."""

import datetime as dt
from decimal import Decimal

import ibis
import pyarrow as pa

from _pipelines import arrow_table as table

ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64(), nullable=False),
        pa.field("qty", pa.int32()),
        pa.field("price", pa.float64()),
        pa.field("cost", pa.decimal128(15, 2)),
        pa.field("day", pa.date32()),
        pa.field("placed", pa.timestamp("us")),
    ]
)
CUSTOMERS = pa.schema([pa.field("name", pa.string()), pa.field("region", pa.string())])

ORDER_ROWS = [
    (1, "ada", 5, 3, 2.5, Decimal("10.50"), dt.date(2024, 1, 1), dt.datetime(2024, 1, 1, 9, 30)),
    (2, "bob", 7, None, 0.0, Decimal("3.25"), dt.date(2024, 1, 2), dt.datetime(2024, 1, 7, 23, 59)),
    (3, "ada", 0, 4, -1.5, None, dt.date(2024, 2, 1), None),
    (4, "cy", 9, 2, None, Decimal("0.01"), None, dt.datetime(2023, 12, 31, 0, 0, 1)),
    (5, None, 2, 7, 10.0, Decimal("99.99"), dt.date(2023, 12, 31), dt.datetime(2024, 3, 31, 12)),
]
CUSTOMER_ROWS = [("ada", "eu"), ("bob", "us"), ("dan", "eu")]
TABLES = {"orders": table(ORDERS, ORDER_ROWS), "customers": table(CUSTOMERS, CUSTOMER_ROWS)}
SCHEMAS = {n: ibis.Schema.from_pyarrow(t.schema) for n, t in TABLES.items()}
