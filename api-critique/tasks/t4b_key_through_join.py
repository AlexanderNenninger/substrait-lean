"""Task 4b: a key survives a join on its own column only from the side it is read from."""
import pyarrow as pa, sverify as sv
con = sv.connect()
con.put("orders", pa.table({"order_id": pa.array([1], pa.int64()), "customer_id": pa.array([10], pa.int64()), "amount": [1.0]}))
con.put("customers", pa.table({"customer_id": pa.array([10], pa.int64()), "name": ["a"]}))
T = {"orders": con.table("orders"), "customers": con.table("customers")}
R = {"orders": ["customer_id IS NOT NULL"], "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")]}
for q in [
 "SELECT customer_id, count(*) AS n FROM orders GROUP BY customer_id",
 "SELECT p.customer_id, c.name FROM (SELECT customer_id, count(*) n FROM orders GROUP BY customer_id) p JOIN customers c ON c.customer_id = p.customer_id",
 "SELECT c.customer_id, c.name FROM (SELECT customer_id, count(*) n FROM orders GROUP BY customer_id) p JOIN customers c ON c.customer_id = p.customer_id",
]:
    r = sv.verify(q, tables=T, requires=R, ensures=[sv.unique("customer_id")])
    print(r.proved, [l for l in str(r).splitlines() if l.startswith("ensures")])
