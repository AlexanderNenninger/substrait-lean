"""A correlated `[NOT] EXISTS` runs on every engine (#345, #1608 item 11).

The lift writes it as a semi or anti join (`sql_lift`, oracles A and C in
`test_sql_lift_relations.py`); here the verified query runs on each engine
and gives the rows SQL gives: a NULL key matches nothing, so `EXISTS` is false
and `NOT EXISTS` true for it."""

import pyarrow as pa
import pytest

import sverify as sv
from _engines import PROFILED

SCHEMAS = {
    "orders": pa.schema([("id", pa.int64()), ("customer", pa.string())]),
    "customers": pa.schema([("name", pa.string()), ("region", pa.string())]),
}
ORDERS = pa.table(
    {"id": [1, 2, 3, 4], "customer": ["ada", "bob", None, "zed"]}, schema=SCHEMAS["orders"]
)
CUSTOMERS = pa.table({"name": ["ada", "bob"], "region": ["eu", "us"]}, schema=SCHEMAS["customers"])


@pytest.mark.parametrize("engine", PROFILED)
@pytest.mark.parametrize(
    ("query", "ids"),
    [
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c"
            " WHERE c.name = o.customer)",
            [1, 2],
        ),
        (
            "SELECT id FROM orders o WHERE NOT EXISTS (SELECT 1 FROM customers c"
            " WHERE c.name = o.customer)",
            [3, 4],
        ),
        (
            "SELECT id FROM orders o WHERE EXISTS (SELECT 1 FROM customers c"
            " WHERE c.name = o.customer AND c.region = 'eu') AND o.id > 0",
            [1],
        ),
    ],
)
def test_the_semi_and_anti_joins_agree_on_every_engine(engine, query, ids):
    report = sv.verify(query, tables=SCHEMAS, on_inferred="warn")
    con = sv.connect()
    con.put("orders", ORDERS)
    con.put("customers", CUSTOMERS)
    got = report.run(con, engine)
    assert sorted(r["id"] for r in got.to_pylist()) == ids
