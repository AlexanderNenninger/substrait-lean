"""Messages a user reads (#1485 item 21): column names where Lean numbers
columns, contradictory `requires`, a suggestion for a misspelt column."""

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify._vacuity import contradictions

pytestmark = pytest.mark.backend("duckdb")

ORDERS = ibis.table({"order_id": "!int64", "amount": "!int64", "p": "!float64"}, name="orders")
SCHEMA = {"orders": ibis.schema({"order_id": "!int64", "amount": "!int64"})}


def test_an_overflow_after_an_aggregate_names_the_measure():
    t = ORDERS.group_by("order_id").agg(t=ORDERS.amount.sum() * 2 + 1)
    report = sv.verify(t, ensures=[])
    assert "$" not in str(report)
    assert "overflow: sum(amount) * 2 + 1" in str(report)


@pytest.mark.parametrize(
    ("requires", "vacuous"),
    [
        ([_.amount > 5, _.amount < 3], True),
        ([_.amount > 5, _.amount < 6], True),  # no integer between
        ([_.amount >= 5, _.amount <= 5], False),
        ([_.p > 1.0, _.p < 1.0], True),
        ([_.p > 1.0, _.p < 1.5], False),
        ([_.amount > 5], False),
        ([_.amount == 3, _.amount > 3], True),
    ],
)
def test_requires_that_no_row_meets_are_flagged(requires, vacuous):
    t = ORDERS.select(ORDERS.order_id, y=ORDERS.amount)
    report = sv.verify(t, requires={"orders": requires}, ensures=[_.y > 0])
    flagged = [n for n in report._all_hints() if "contradict" in n]
    assert bool(flagged) is vacuous, report
    if vacuous:
        assert "no row meets them" in flagged[0]


def test_contradictory_sql_requires_are_flagged():
    report = sv.verify(
        "SELECT order_id, amount AS y FROM orders",
        tables=SCHEMA,
        requires={"orders": ["amount > 5", "amount < 3"]},
        ensures=["y > 0"],
    )
    assert any("`amount`" in n and "contradict" in n for n in report._all_hints())


def test_a_condition_the_check_cannot_read_is_not_flagged():
    assert contradictions({"orders": [_.amount + 1 > 5, "amount % 2 = 0"]}, SCHEMA) == []


def test_a_misspelt_column_in_requires_gets_a_suggestion():
    with pytest.raises(AttributeError, match=r"no column 'amout'; did you mean 'amount'\?"):
        sv.verify(ORDERS, requires={"orders": [_.amout > 5]}, ensures=[])


def test_a_misspelt_column_in_sql_gets_a_suggestion():
    with pytest.raises(sv.errors.UnsupportedError, match=r"did you mean 'amount'\?"):
        sv.verify("SELECT amout FROM orders", tables=SCHEMA, ensures=[])
