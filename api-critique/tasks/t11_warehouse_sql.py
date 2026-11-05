"""Task 11: hand the checked plan to a warehouse as SQL (Snowflake, Spark, DuckDB).

The data engineer whose production runs in Snowflake wants the SQL that
sverify checked, to paste into a dbt model or a scheduled query.
"""

import json

import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.engines import DUCKDB, SNOWFLAKE, SPARK, Unsupported, to_sql
from sverify.io import StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id"), _.id.notnull()]},
    ensures=[_.total >= 0, sv.unique("customer")],
)
def per_customer(orders):
    return orders.group_by("customer").aggregate(total=orders.amount.sum(), n=orders.count())


node = orders.pipe(per_customer)

# 1. The README's way.
for name, dialect in [("duckdb", DUCKDB), ("snowflake", SNOWFLAKE), ("spark", SPARK)]:
    try:
        sql = to_sql(json.loads(node.plan), dialect)
        print(f"--- {name} ({len(sql)} chars)\n{sql[:600]}\n")
    except Unsupported as e:
        print(f"--- {name}: Unsupported: {e}")

# 2. From a report, and with a sort + limit (needs tie_free?).
# `node.table` raised "per_customer has no state yet: call refresh() first",
# so refresh first to get an Ibis table to build on.
node.refresh()
top = sv.verify(
    node.table.order_by(_.total.desc()).limit(1),
    # requires on "orders" raised: unknown table 'orders'; the inputs are: per_customer.
    # node.table is the stored state, so the upstream contract does not come along.
    requires={"per_customer": [_.total >= 0]},
)
print("report.to_sql:", hasattr(top, "to_sql"))
try:
    print(to_sql(json.loads(top.plan) if isinstance(top.plan, str) else top.plan, SNOWFLAKE)[:300])
except Unsupported as e:
    print("top-1 on snowflake:", e)
print("deterministic:", top.deterministic)
