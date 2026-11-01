"""Counterexamples for unproved postconditions (`sverify.counterexample`).

Each counterexample is checked independently of Lean: its tables meet the
preconditions and the transformation breaks the postcondition on DuckDB.
"""

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify.contracts import violations
from sverify.counterexample import Counterexample
from sverify.engines import create_table
from sverify.errors import VerificationError
from sverify_dev.examples import customers, orders


def left(o, c):
    return o.left_join(c, o.customer == c.name).select(o.id, c.city)


UNPROVABLE = [
    (lambda o, c: o.select(o.id, total=o.amount + 1), {"orders": [_.amount >= 0]}, _.total > 5),
    (lambda o, c: o.select(t=o.amount + 1), {}, _.t.notnull()),
    (lambda o, c: o.filter(o.amount > 10).select("amount"), {}, _.amount == 11),
    (lambda o, c: o.filter(o.amount > 10).select("amount"), {}, _.amount == 5),
    (left, {"customers": [_.city.notnull()]}, _.city.notnull()),
    (lambda o, c: o.filter(o.amount > 10), {}, sv.unique("id")),
    (left, {"orders": [sv.unique("id")]}, sv.unique("id")),
    (lambda o, c: o.filter(o.customer == "ada").select("id", "customer"), {}, _.customer != "ada"),
    # The foreign key holds in the counterexample: a matching customer with no city, or no customer.
    (left, {"orders": [sv.references("customer", "customers", "name")]}, _.city.notnull()),
]


def bound(cex: Counterexample) -> dict:
    con = sv.connect()
    schemas = {"orders": orders.schema(), "customers": customers.schema()}
    for name, schema in schemas.items():
        create_table(con, name, schema, cex.tables.get(name, []))
    return {name: con.table(name) for name in schemas}


@pytest.mark.parametrize(("transform", "requires", "ensures"), UNPROVABLE)
def test_unprovable_postconditions_have_a_counterexample(transform, requires, ensures):
    report = sv.verify(transform(orders, customers), requires=requires, ensures=[ensures])
    [cond] = report.ensures
    assert not cond.proved
    cex = cond.counterexample
    assert cex is not None, str(report)
    # Independently of Lean: the inputs meet the preconditions...
    tables = bound(cex)
    for name, conds in requires.items():
        for c in conds:
            assert violations(tables[name], c) == 0, (name, c)
    # ...and the output breaks the postcondition.
    assert violations(transform(tables["orders"], tables["customers"]), ensures) > 0
    assert str(cex) in str(report)


def test_counterexamples_are_shrunk():
    report = sv.verify(orders.select(t=orders.amount + 1), ensures=[_.t.notnull()])
    cex = report.ensures[0].counterexample
    assert cex is not None
    assert cex.tables["orders"] == [(0, "", None)]
    assert str(cex) == "orders(id, customer, amount) = [(0, '', None)] gives (t) = [(None,)]"


def test_constants_guide_the_search():
    # Only 41 breaks the condition: the search tries the plan's constants and
    # their neighbours.
    expr = orders.filter(orders.amount > 40).select("amount")
    cex = sv.verify(expr, ensures=[_.amount != 41]).ensures[0].counterexample
    assert cex is not None and cex.output == [(41,)]


def test_doubles_strings_and_timestamps():
    t = ibis.table({"x": "float64", "s": "string", "ts": "timestamp"}, name="t")
    report = sv.verify(
        t.filter(t.x > 2.5).select("x", "s", "ts"),
        ensures=[_.x > 3.0, _.s != "b", _.ts.notnull()],
    )
    assert all(c.counterexample is not None for c in report.ensures), str(report)


def test_none_when_proved_or_not_searched():
    report = sv.verify(orders.filter(orders.amount > 10), ensures=[_.amount > 10])
    assert report.ensures[0].proved and report.ensures[0].counterexample is None
    report = sv.verify(orders.select(t=orders.amount + 1), ensures=[_.t > 5], counterexamples=0)
    assert report.ensures[0].counterexample is None


def test_no_counterexample_for_a_true_but_unproved_postcondition():
    # True on every input, but the intervals can't show it: the search finds
    # nothing, which says nothing.
    report = sv.verify(
        orders.select(t=orders.amount * orders.amount),
        requires={"orders": [_.amount.notnull()]},
        ensures=[_.t >= 0],
    )
    assert not report.ensures[0].proved
    assert report.ensures[0].counterexample is None


def test_verification_errors_show_the_counterexample():
    @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
    def plus_one(orders):
        return orders.select(orders.id, total=orders.amount + 1)

    with pytest.raises(VerificationError, match="counterexample: orders"):
        plus_one(orders)
    report = plus_one.last_report
    assert report is not None
    assert "fails on `orders(id, customer, amount)" in report._repr_markdown_()
