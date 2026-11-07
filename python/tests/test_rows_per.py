"""Rows per key (#219): `sv.rows_per(cols, at_most=n)` in `requires` bounds
the rows of a table that agree on `cols`. Lean carries the bound through the
plan (`Rel.perKey_sound`), so an aggregate grouping by `cols` has groups of
at most `n` rows (`Rel.groupRows_sound`), and an integer or decimal SUM over
such a group is proved to fit (`Rel.sumsPer_sound`, `Rel.issuesCapped_sound`)."""

import gc

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _pipelines import orders_table
from sverify.contracts import RelationRows, label, violations
from sverify.errors import PreconditionError
from sverify.io import StaticSource

ORDERS = ibis.table(
    {"id": "int64", "customer": "string", "region": "string", "amount": "int64"}, name="orders"
)
CUSTOMERS = ibis.table({"id": "string", "country": "string"}, name="customers")

SUM_OVERFLOW = "SUM overflow"
BOUNDED = [_.amount >= 0, _.amount <= 1_000_000]


def sum_risks(report: sv.Report) -> list[str]:
    """The SUMs that may overflow: assumed to fit (`Report.assumed`), or errors."""
    return [i.expr for i in [*report.issues, *report.assumed] if i.kind == SUM_OVERFLOW]


def per_customer(orders):
    return orders.group_by("customer").aggregate(total=orders.amount.sum())


def test_rows_per_group_prove_a_sum_fits():
    report = sv.verify(per_customer(ORDERS), requires={"orders": BOUNDED})
    assert sum_risks(report)
    per_key = sv.rows_per("customer", at_most=10**12)
    report = sv.verify(per_customer(ORDERS), requires={"orders": [*BOUNDED, per_key]})
    # 10¹² rows per customer of at most 10⁶ each: below 2⁶³. The table itself
    # has no bound.
    assert not sum_risks(report), str(report)
    assert report.proved
    assert report.rows is None
    assert "requires orders: rows_per(customer, at_most=1000000000000)" in str(report)


def test_too_many_rows_per_group_leave_the_sum_checked():
    per_key = sv.rows_per("customer", at_most=10**13)
    report = sv.verify(per_customer(ORDERS), requires={"orders": [*BOUNDED, per_key]})
    assert sum_risks(report)


def test_a_bound_on_other_columns_bounds_no_group():
    per_key = sv.rows_per("region", at_most=10)
    report = sv.verify(per_customer(ORDERS), requires={"orders": [*BOUNDED, per_key]})
    assert sum_risks(report)


def test_grouping_by_more_columns_keeps_the_bound():
    q = ORDERS.group_by(["region", "customer"]).aggregate(total=_.amount.sum())
    per_key = sv.rows_per("customer", at_most=1000)
    report = sv.verify(q, requires={"orders": [*BOUNDED, per_key]})
    assert not sum_risks(report)


def test_a_bound_on_several_columns_needs_all_of_them():
    per_key = sv.rows_per("customer", "region", at_most=1000)
    report = sv.verify(per_customer(ORDERS), requires={"orders": [*BOUNDED, per_key]})
    assert sum_risks(report)
    q = ORDERS.group_by(["customer", "region"]).aggregate(total=_.amount.sum())
    report = sv.verify(q, requires={"orders": [*BOUNDED, per_key]})
    assert not sum_risks(report)


def test_a_filter_keeps_the_bound():
    q = per_customer(ORDERS.filter(_.amount > 10))
    per_key = sv.rows_per("customer", at_most=1000)
    report = sv.verify(q, requires={"orders": [*BOUNDED, per_key]})
    assert not sum_risks(report)


def test_a_join_on_a_key_of_its_right_side_keeps_the_bound():
    """Each order has at most one customer, so the orders per customer stay
    at most 1000 after the join."""
    joined = ORDERS.join(CUSTOMERS, ORDERS.customer == CUSTOMERS.id)
    q = joined.group_by(["customer", "country"]).aggregate(total=_.amount.sum())
    per_key = sv.rows_per("customer", at_most=1000)
    requires = {"orders": [*BOUNDED, per_key], "customers": [sv.unique("id")]}
    report = sv.verify(q, requires=requires)
    assert not sum_risks(report), str(report)
    # Without the key, a customer may match many rows.
    report = sv.verify(q, requires={"orders": [*BOUNDED, per_key]})
    assert sum_risks(report)


def test_grouping_by_a_key_bounds_a_group_by_one_row():
    q = ORDERS.group_by("id").aggregate(total=_.amount.sum())
    report = sv.verify(q, requires={"orders": [*BOUNDED, sv.unique("id")]})
    assert not sum_risks(report)
    assert report._relations[0] == RelationRows("aggregate", 0, None, 1)


def test_relations_list_the_bounds():
    q = per_customer(ORDERS.filter(_.amount > 10))
    per_key = sv.rows_per("customer", at_most=1000)
    report = sv.verify(q, requires={"orders": [*BOUNDED, per_key, sv.max_rows(10**6)]})
    ops = [(r.op, r.depth, r.rows, r.group_rows) for r in report._relations]
    assert ops[0] == ("aggregate", 0, 10**6, 1000)
    assert ("read orders", ops[-1][1], 10**6, None) == ops[-1]
    assert any(op == "filter" and rows == 10**6 for op, _, rows, _ in ops)


def test_a_decimal_sum_scaled_after_a_capped_aggregate_fits():
    """#470: a row cap bounds an exact SUM's magnitude, so arithmetic on it
    fits its precision."""
    t = ibis.table({"c": "decimal(15,2)", "g": "int64"}, name="t")
    q = t.group_by("g").aggregate(s=_.c.sum() * 0.0001)
    report = sv.verify(
        q, requires={"t": [_.c.between(1, 1000), sv.max_rows(1000)]}, ensures=[], on_inferred="off"
    )
    assert report.errors == [], str(report)
    lo, hi = report._bounds.get("s", (None, None)) if report._bounds else (None, None)
    assert lo is None or lo >= 0


def test_rows_per_bounds_a_decimal_sum():
    t = ibis.table({"d": "decimal(20,0)", "g": "int64"}, name="t")
    q = t.group_by("g").aggregate(s=t.d.sum())
    bounded = [_.d.between(-(10**18), 10**18)]
    report = sv.verify(
        q, requires={"t": [*bounded, sv.rows_per("g", at_most=1000)]}, on_inferred="off"
    )
    assert report.errors == [] and report.assumed == [], str(report)
    report = sv.verify(q, requires={"t": bounded}, on_inferred="off")
    assert [i.kind for i in report.errors] == [SUM_OVERFLOW]


def test_rows_per_is_not_proved_in_ensures():
    report = sv.verify(
        per_customer(ORDERS),
        requires={"orders": BOUNDED},
        ensures=[sv.rows_per("customer", at_most=1)],
    )
    [c] = report.ensures
    assert not c.proved and c.value == "rows per key are checked on inputs only"


def test_rows_per_checks_its_arguments():
    with pytest.raises(ValueError, match="needs at_most="):
        sv.rows_per("customer")
    with pytest.warns(DeprecationWarning, match=r"rows_per\(\*cols, at_most=\.\.\.\)"):
        assert sv.rows_per(["a", "b"], 3) == sv.rows_per("a", "b", at_most=3)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="0 or more"):
        sv.rows_per("customer", at_most=-1)
    assert label(sv.rows_per("a", "b", at_most=3)) == "rows_per(a, b, at_most=3)"


def test_violations_count_the_rows_beyond_the_bound():
    con = sv.connect()
    con.put("t", pa.table({"k": ["a", "a", "a", "b", None, None], "v": [1, 2, 3, 4, 5, 6]}))
    t = con.table("t")
    assert violations(t, sv.rows_per("k", at_most=3)) == 0
    # Three a's (one too many) and two NULLs, which are one key.
    assert violations(t, sv.rows_per("k", at_most=2)) == 1
    assert violations(t, sv.rows_per("k", at_most=1)) == 3
    assert violations(t, sv.rows_per(at_most=4)) == 2


def test_a_transform_checks_rows_per_on_data():
    con = sv.connect()
    con.put("orders", orders_table([(1, "ada", 5), (2, "ada", 7), (3, "bob", 1)]))
    orders = con.table("orders")
    contracted = sv.transform(
        requires={"orders": [_.amount >= 0, sv.rows_per("customer", at_most=1)]}, ensures=[]
    )(lambda orders: orders.group_by("customer").aggregate(total=orders.amount.sum()))
    with pytest.raises(PreconditionError, match=r"1 row\(s\) of orders violate rows_per"):
        contracted(orders)


def test_incremental_views_refuse_rows_per():
    src = StaticSource(pa.table({"id": [1], "customer": ["ada"], "amount": [5]}), name="orders")
    contracted = sv.transform(
        requires={"orders": [_.amount >= 0, sv.rows_per("customer", at_most=10)]}, ensures=[]
    )(lambda orders: orders.group_by("customer").aggregate(total=orders.amount.sum()))
    with pytest.raises(ValueError, match="rows_per"):
        src.pipe(contracted).refresh()


def test_a_new_connection_does_not_inherit_a_dead_ones_facts():
    # A backend that is gone may leave its `id` to a new one; the facts
    # registered for the old one stay with it (the data check still runs).
    from sverify import contracts

    old = sv.connect()
    contracts.register_facts(old, "orders", [contracts.Fact("TRUE", "rows @v1", rows=1)])
    con = sv.connect()
    con.put("orders", orders_table([(1, "ada", 5), (2, "ada", 7)]))
    entry = contracts._facts.pop((id(old._ibis), "orders"))
    contracts._facts[(id(con._ibis), "orders")] = entry
    del old, entry
    gc.collect()
    try:
        assert contracts.table_facts(con.table("orders")) is None
        contracted = sv.transform(
            requires={"orders": [sv.rows_per("customer", at_most=1)]}, ensures=[]
        )(lambda orders: orders.group_by("customer").aggregate(total=orders.amount.sum()))
        with pytest.raises(PreconditionError, match=r"1 row\(s\) of orders violate rows_per"):
            contracted(con.table("orders"))
    finally:
        contracts._facts.pop((id(con._ibis), "orders"), None)
