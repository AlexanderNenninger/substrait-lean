"""Task 4: a dbt-style SQL model, checked with sv.sql and sv.verify.

A customer mart: orders joined to customers, a CTE, a window rank, the dbt
tests (unique, not_null, accepted range) as the contract.
"""

import pyarrow as pa

import sverify as sv
from sverify.errors import VerificationError
from sverify.io import StaticSource

orders_t = pa.table(
    {
        "order_id": pa.array([1, 2, 3, 4], pa.int64()),
        "customer_id": pa.array([10, 10, 20, 30], pa.int64()),
        "amount": pa.array([12.5, 7.5, 100.0, 3.0]),
        "status": ["paid", "paid", "refunded", "paid"],
    }
)
customers_t = pa.table({"customer_id": pa.array([10, 20, 30], pa.int64()), "name": ["ada", "bob", "cy"]})

MODEL = """
WITH paid AS (
    SELECT * FROM orders WHERE status = 'paid'
),
per_customer AS (
    SELECT customer_id, count(*) AS n_orders, sum(amount) AS revenue
    FROM paid
    GROUP BY customer_id
)
SELECT c.customer_id, c.name, p.n_orders, p.revenue,
       rank() OVER (ORDER BY p.revenue DESC) AS revenue_rank
FROM per_customer p
JOIN customers c ON c.customer_id = p.customer_id
"""

# 1. sv.verify on the SQL, with the dbt tests as SQL conditions.
con = sv.connect()
con.put("orders", orders_t)
con.put("customers", customers_t)
report = sv.verify(
    MODEL,
    tables={"orders": con.table("orders"), "customers": con.table("customers")},
    requires={
        "orders": ["order_id IS NOT NULL", "amount >= 0", "customer_id IS NOT NULL"],
        "customers": ["customer_id IS NOT NULL"],
    },
    ensures=[
        sv.unique("customer_id"),
        "customer_id IS NOT NULL",
        "n_orders >= 1",
        "revenue >= 0",
        "revenue_rank >= 1",
    ],
)
print("proved:", report.proved)
print(report)

# 2. Same model as a transform over sources, as the README's SQL section shows.
orders = StaticSource(orders_t, name="orders")
customers = StaticSource(customers_t, name="customers")


@sv.transform(
    requires={
        "orders": ["order_id IS NOT NULL", "amount >= 0", "customer_id IS NOT NULL", sv.unique("order_id")],
        "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")],
    },
    ensures=[sv.unique("customer_id"), "n_orders >= 1", "revenue >= 0"],
)
def customer_mart(orders, customers):
    return sv.sql(MODEL, orders=orders, customers=customers)


try:
    mart = orders.pipe(customer_mart, customers=customers)
    print(customer_mart.last_report)
    print(mart.refresh())
    print(mart.to_arrow().to_pylist())
except VerificationError as e:
    print("transform refused:\n", e)

# 3. SQL that the lift doesn't read: QUALIFY and a DuckDB-only function.
for q in [
    "SELECT * FROM orders QUALIFY row_number() OVER (PARTITION BY customer_id ORDER BY order_id) = 1",
    "SELECT order_id, list_value(amount, amount) AS xs FROM orders",
    "SELECT order_id, amount::DECIMAL(10,2) AS amt FROM orders",
    "SELECT customer_id, any_value(status) FROM orders GROUP BY ALL",
    "SELECT order_id, amount / 0 AS boom FROM orders",
]:
    try:
        r = sv.verify(q, tables={"orders": con.table("orders")})
        print(f"\n{q[:60]!r}: proved={r.proved}")
        print(str(r).splitlines()[:4])
    except Exception as e:
        print(f"\n{q[:60]!r}: {type(e).__name__}: {str(e)[:400]}")

# 4. Is it the RANK? Break the tie with the key, then drop the rank.
for label, model in [
    ("tie broken by key", MODEL.replace("ORDER BY p.revenue DESC", "ORDER BY p.revenue DESC, c.customer_id")),
    ("no rank", MODEL.replace(",\n       rank() OVER (ORDER BY p.revenue DESC) AS revenue_rank", "")),
]:
    r = sv.verify(
        model,
        tables={"orders": con.table("orders"), "customers": con.table("customers")},
        requires={
            "orders": ["order_id IS NOT NULL", "amount >= 0", "customer_id IS NOT NULL", sv.unique("order_id")],
            "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")],
        },
        ensures=[sv.unique("customer_id"), "n_orders >= 1", "revenue >= 0"],
    )
    print(f"\n{label}: proved={r.proved}")
    print("\n".join(str(r).splitlines()[:12]))

# Where does Unsupported live?
try:
    sv.verify("SELECT * FROM orders QUALIFY row_number() OVER (ORDER BY order_id) = 1", tables={"orders": con.table("orders")})
except Exception as e:
    print(type(e).__module__, type(e).__mro__)
