"""A LEFT JOIN on a declared foreign key keeps the right side's non-NULLs (#2512).

A fact table left-joined to a per-key sum over a detail table is the common dbt
shape (jaffle_shop's `orders`). Where the detail table has a row for every key
of the fact table, which `sv.references` states, the sum's column is as
non-NULL as the right side's own. Without the declaration, the left join
pads with NULLs and the column stays unproved, and the report proposes the
reference.
"""

import ibis
import pytest
from ibis import _

import sverify as sv

orders = ibis.table({"id": "int64", "status": "string"}, name="orders")
payments = ibis.table({"order_id": "int64", "amount": "int64"}, name="payments")


def per_order():
    return payments.group_by("order_id").aggregate(total=payments.amount.sum())


def joined():
    per = per_order()
    return orders.left_join(per, orders.id == per.order_id).select("id", "total")


NOT_NULL = {"orders": [_.id.notnull()], "payments": [_.amount.notnull(), _.amount < 1000]}
REFERENCES = {
    **NOT_NULL,
    "orders": [*NOT_NULL["orders"], sv.references("id", to=("payments", "order_id"))],
}


def test_the_sum_is_not_null_where_every_order_has_a_payment():
    report = sv.verify(joined(), requires=REFERENCES, ensures=[_.total.notnull()])
    assert report.verdict != sv.Verdict.UNPROVED, str(report)
    assert "left join on a foreign key" in str(report)
    assert "orders.id -> payments.order_id" in str(report)


def test_without_the_relationship_the_column_is_unproved_and_the_report_says_what_to_declare():
    report = sv.verify(joined(), requires=NOT_NULL, ensures=[_.total.notnull()])
    assert report.verdict == sv.Verdict.UNPROVED
    assert "sv.references('id', to=('payments', 'order_id'))" in str(report)
    suggested = report.suggested_requires
    assert any(isinstance(c, sv.conditions.References) for c in suggested.get("orders", [])), (
        suggested
    )
    # What it proposes proves it.
    again = sv.verify(joined(), requires=suggested, ensures=[_.total.notnull()])
    assert again.verdict != sv.Verdict.UNPROVED, str(again)


def test_the_plan_that_runs_is_still_a_left_join():
    report = sv.verify(joined(), requires=REFERENCES, ensures=[_.total.notnull()])
    sql = report.to_sql("duckdb")
    assert "LEFT JOIN" in sql.upper()


def test_data_that_breaks_the_relationship_is_refused():
    """The proof is conditional on `references`: a run checks it on the data."""
    import pyarrow as pa

    from sverify.engine import connect, put_table

    con = connect()
    put_table(con, "orders", pa.table({"id": [1, 2], "status": ["a", "b"]}))
    put_table(con, "payments", pa.table({"order_id": [1], "amount": [5]}))
    report = sv.verify(joined(), requires=REFERENCES, ensures=[_.total.notnull()])
    with pytest.raises(sv.errors.PreconditionError, match="references"):
        report.run(con, "duckdb")
