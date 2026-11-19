"""`substrait-check --delta` names the operators that block a delta plan
(#1484): each with the tables under it, where the plan has several."""

import ibis
import pytest

from sverify.engine import NotIncrementalError, connect, delta_plans, plan_json

ORDERS = ibis.table({"id": "int64", "cust": "int64", "amount": "int64"}, name="o")
CUSTOMERS = ibis.table({"cid": "int64", "name": "string"}, name="c")
PREFIX = "not incrementally maintainable: no delta rule for "


def refusal(expr) -> str:
    with pytest.raises(NotIncrementalError) as e:
        delta_plans(plan_json(connect(), expr))
    return str(e.value)


def test_a_global_aggregate_is_named():
    assert refusal(ORDERS.aggregate(total=ORDERS.amount.sum())) == PREFIX + "aggregate over o"


def test_a_distinct_count_is_named():
    got = refusal(ORDERS.aggregate(n=ORDERS.cust.nunique()))
    assert got.startswith(PREFIX + "aggregate over o")
    assert "left join" not in got and "window" not in got


def test_a_left_join_names_its_tables():
    left = ORDERS.left_join(CUSTOMERS, ORDERS.cust == CUSTOMERS.cid).select(ORDERS.id)
    assert refusal(left) == PREFIX + "left join over o, c"


def test_a_window_is_named():
    running = ORDERS.select(total=ORDERS.amount.sum().over(group_by="cust", order_by="id"))
    assert refusal(running) == PREFIX + "window over o"


def test_each_blocking_operator_is_listed_with_where():
    """A limit over an aggregate over one table, joined to another."""
    top = ORDERS.group_by("cust").aggregate(total=ORDERS.amount.sum()).limit(3)
    both = top.left_join(CUSTOMERS, top.cust == CUSTOMERS.cid).select(top.cust)
    assert refusal(both) == PREFIX + "left join over o, c; fetch over o; aggregate over o"
