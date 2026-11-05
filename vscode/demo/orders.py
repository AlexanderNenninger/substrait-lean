"""Contracts on an orders table (tour notebook 4, "Contracts").

Save the file to check it. Each transform below shows one kind of finding.
"""

import ibis
import sverify as sv
from ibis import _

# An unbound table has a name and a schema and no data. The extension calls
# each transform on the unbound tables named like its parameters.
orders = ibis.table(
    {"id": "int64", "customer": "string", "amount": "int64", "qty": "int64"}, name="orders"
)


# Proved: hover `doubled` for the report, `doubled=` for what Lean knows.
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, _.id.notnull()]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
)
def doubled(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


# Not proved: amount = 0 gives total = 1. The counterexample says so.
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)


# Needs a precondition: `amount // qty` divides by zero where qty is 0.
# The quick fixes state it, filter first, or guard the division with a CASE.
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.unit >= 0])
def unit_price(orders):
    return orders.select(orders.id, unit=orders.amount // orders.qty)


# A key: `id` is unique in the output only if it is in the input.
@sv.transform(ensures=[sv.unique("id")])
def by_id(orders):
    return orders.select("id", "customer")


# A typo in a contract: `amout` is no column of orders.
@sv.transform(requires={"orders": [_.amout >= 0]}, ensures=[_.amount >= 0])
def typo(orders):
    return orders.select("id", "amount")


# A SUM sverify assumes fits 64 bits; the hint's bounds and row cap prove it.
@sv.transform(requires={"orders": [sv.unique("id")]}, ensures=[sv.unique("customer")])
def per_customer(orders):
    return orders.group_by("customer").aggregate(total=_.amount.sum())


# The same division in SQL, as the body of a transform. The fixes state the
# precondition as a SQL snippet's Ibis twin, or guard it with a CASE.
@sv.transform(requires={"orders": ["amount >= 0"]}, ensures=["unit >= 0"])
def unit_price_sql(orders):
    return sv.sql("select id, amount // qty as unit from orders", orders=orders)


# Misplaced and misspelled contract parts: the editor flags them as you type.
@sv.transform(requires={"order": [sv.unique("id")]}, ensures=[sv.unique("id")])
def wrong_table(orders):
    return orders.select("id")


if __name__ == "__main__":
    # Runs on data stay out of the editor's check (it runs the file as a
    # module named __sverify_check__).
    con = sv.connect()
