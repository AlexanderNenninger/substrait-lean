"""Columns an equality ties together are one column for keys (#694).

An inner join's output rows satisfy its condition, so after
`JOIN customers c ON c.customer_id = p.customer_id` the two copies of
`customer_id` are equal on every row: a key on one is a key on the other, and
a window ordered by either one is ordered by the key (`KeyOn.eqVariants`). A
filter's equality does the same. A left join's unmatched rows have NULL in the
right side's copy, so there the copies differ.
"""

import ibis
import pytest

import sverify as sv

TABLES = {
    "orders": ibis.schema({"order_id": "int64", "customer_id": "int64", "amount": "int64"}),
    "customers": ibis.schema({"customer_id": "int64", "name": "string"}),
}
REQUIRES = {
    "orders": ["customer_id IS NOT NULL", sv.unique("order_id")],
    "customers": ["customer_id IS NOT NULL", sv.unique("customer_id")],
}
PER_CUSTOMER = "(SELECT customer_id, count(*) AS n, sum(amount) AS revenue FROM orders GROUP BY customer_id)"


def _verify(sql, ensures):
    return sv.verify(sql, tables=TABLES, requires=REQUIRES, ensures=ensures)


@pytest.mark.parametrize("side", ["p", "c"])
def test_a_key_survives_from_either_copy_of_the_join_column(side):
    sql = (
        f"SELECT {side}.customer_id, c.name FROM {PER_CUSTOMER} p "
        "JOIN customers c ON c.customer_id = p.customer_id"
    )
    report = _verify(sql, [sv.unique("customer_id")])
    assert report.proved, str(report)


def test_a_rank_broken_by_the_other_copy_is_determined():
    sql = (
        "SELECT c.customer_id, c.name, p.revenue, "
        "rank() OVER (ORDER BY p.revenue DESC, c.customer_id) AS revenue_rank "
        f"FROM {PER_CUSTOMER} p JOIN customers c ON c.customer_id = p.customer_id"
    )
    report = _verify(sql, [sv.unique("customer_id"), "revenue_rank >= 1"])
    assert report.deterministic, str(report)
    assert report.proved, str(report)


def test_a_filters_equality_ties_the_columns():
    sql = "SELECT o2.order_id AS id FROM orders o, orders o2 WHERE o.order_id = o2.order_id"
    report = _verify(sql, [sv.unique("id")])
    assert report.proved, str(report)


def test_a_left_joins_right_copy_is_no_key():
    sql = (
        f"SELECT c.customer_id FROM {PER_CUSTOMER} p "
        "LEFT JOIN customers c ON c.customer_id = p.customer_id"
    )
    assert not _verify(sql, [sv.unique("customer_id")]).proved
