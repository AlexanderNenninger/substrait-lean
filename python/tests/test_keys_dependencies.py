"""A key that a GROUP BY or a join loses survives as a functional dependency (#1993).

`GROUP BY customer_id, name` has the key `(customer_id, name)`. With
`customer_id` a key of the input, `customer_id` gives `name` on every row, so
`customer_id` alone is a key of the output (`KeyOn.of_fd`). After
`customers LEFT JOIN orders`, `customer_id` is no key (a customer has many
orders), yet it still gives `name`, since the left part of every row is a
`customers` row: grouping that join by `customer_id, name` keeps the key too.
"""

import ibis

import sverify as sv

TABLES = {
    "orders": ibis.schema({"order_id": "int64", "customer_id": "int64", "amount": "int64"}),
    "customers": ibis.schema({"customer_id": "int64", "name": "string"}),
}
REQUIRES = {
    "orders": ["customer_id IS NOT NULL", sv.unique("order_id")],
    "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")],
}
PROVED = (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS)


def _verify(sql, ensures):
    return sv.verify(sql, tables=TABLES, requires=REQUIRES, ensures=ensures)


def test_grouping_by_a_key_and_its_attributes_keeps_the_key():
    sql = "SELECT customer_id, name, count(*) AS n FROM customers GROUP BY customer_id, name"
    report = _verify(sql, [sv.unique("customer_id")])
    assert report.verdict in PROVED, str(report)


def test_a_left_join_mart_keeps_the_left_key():
    sql = (
        "SELECT c.customer_id, c.name, count(o.order_id) AS orders, sum(o.amount) AS revenue "
        "FROM customers c LEFT JOIN orders o ON o.customer_id = c.customer_id "
        "GROUP BY c.customer_id, c.name"
    )
    report = _verify(sql, [sv.unique("customer_id")])
    assert report.verdict in PROVED, str(report)


def test_an_attribute_alone_is_no_key():
    sql = "SELECT customer_id, name, count(*) AS n FROM customers GROUP BY customer_id, name"
    assert _verify(sql, [sv.unique("name")]).verdict == sv.Verdict.UNPROVED
