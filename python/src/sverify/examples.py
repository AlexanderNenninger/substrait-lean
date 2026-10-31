"""Example pipelines over a small orders/customers schema, as Ibis expressions.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Used by the tests, by `scripts/capture_fixtures.py` and in the docs. The
tables are unbound: `ibis.to_sql` (and so `IncrementalView.from_ibis`)
compiles them without a backend, and any connection with tables of the same
names and columns can run them.
"""

import ibis

ORDERS_SCHEMA = {"id": "int64", "customer": "string", "amount": "int64"}
CUSTOMERS_SCHEMA = {"name": "string", "city": "string"}

orders = ibis.table(ORDERS_SCHEMA, name="orders")
customers = ibis.table(CUSTOMERS_SCHEMA, name="customers")
_other = orders.view()

#: Pipelines in the incremental fragment.
PIPELINES: dict[str, ibis.Table] = {
    "filter_project": orders.filter(orders.amount > 10).select(
        orders.id, doubled=orders.amount * 2
    ),
    "inner_join": orders.join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    ),
    "union_all": ibis.union(
        orders.select("id"), orders.filter(orders.amount < 3).select("id"), distinct=False
    ),
    "cross_filter": orders.filter(orders.amount > 20)
    .cross_join(customers)
    .select(orders.id, customers.city),
    "self_join": orders.join(_other, orders.customer == _other.customer).select(
        id=orders.id, other=_other.id
    ),
    "filter_join_compute": orders.filter(orders.amount > 5)
    .join(customers, orders.customer == customers.name)
    .select(orders.id, customers.city, total=orders.amount + 1),
}

#: Pipelines outside the fragment, which `IncrementalView` must refuse.
UNSUPPORTED: dict[str, ibis.Table] = {
    "left_join": orders.left_join(customers, orders.customer == customers.name).select(
        orders.id, customers.city
    ),
    "aggregate": orders.group_by("customer").aggregate(total=orders.amount.sum()),
}


def create_tables(con, orders_rows=(), customers_rows=()) -> None:
    """Create `orders` and `customers` on a connection (`sverify.connect()`)."""
    from sverify.engine import create_table

    create_table(con, "orders", ibis.schema(ORDERS_SCHEMA), orders_rows)
    create_table(con, "customers", ibis.schema(CUSTOMERS_SCHEMA), customers_rows)
