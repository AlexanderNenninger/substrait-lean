"""SQL models: a transform's body in SQL (`sv.sql`), as a node like any other."""

import pyarrow as pa
import pytest
from deltalake import DeltaTable
from ibis import _

import sverify as sv
from _pipelines import arrow_table as table
from _pipelines import paid_nonzero as paid
from _pipelines import rows
from sverify.engines import ENGINES, Unsupported, run
from sverify.errors import PreconditionError, VerificationError
from sverify.io import DeltaSink, StaticSource

ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64(), nullable=False),
    ]
)
CUSTOMERS = pa.schema([pa.field("name", pa.string()), pa.field("region", pa.string())])


def sources():
    orders = StaticSource(
        table(ORDERS, [(1, "ada", 5), (2, "bob", 7), (3, "ada", 0)]), version=1, name="orders"
    )
    customers = StaticSource(
        table(CUSTOMERS, [("ada", "eu"), ("bob", "us")]), version=1, name="customers"
    )
    return orders, customers


@sv.transform(
    requires={"orders": ["amount > 0"]},
    ensures=["total >= 0", "total IS NOT NULL", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, coalesce(sum(amount), 1) AS total FROM orders GROUP BY customer",
        orders=orders,
    )


@sv.transform(requires={"t": [_.total >= 0, _.total.notnull()]}, ensures=[_.total > 6])
def large(t):
    return t.filter(t.total > 6)


def test_a_sql_node_between_ibis_nodes_fuses():
    orders, _customers = sources()
    node = large(per_customer(paid(orders)))
    report = node.refresh()
    assert [s.node for s in report.nodes] == ["large"]
    assert node.versions == {"orders": 1}
    assert rows(node) == [("bob", 7)]
    # Composed: `large` builds on what the SQL model proved.
    assert large.last_report is not None and large.last_report.proved
    orders.apply(sv.Changes(inserts=[(4, "ada", 3)]))
    node.refresh()
    assert rows(node) == [("ada", 8), ("bob", 7)]


def test_a_stored_sql_node_is_read_downstream(tmp_path):
    orders, _customers = sources()
    stored = per_customer(paid(orders)).write(DeltaSink(str(tmp_path / "per_customer")))
    node = large(stored)
    report = node.refresh()
    assert [s.node for s in report.nodes] == ["per_customer", "large"]
    assert node.versions == {"per_customer": DeltaTable(tmp_path / "per_customer").version()}
    assert rows(node) == [("bob", 7)]


def test_a_sql_node_reads_several_inputs():
    orders, customers = sources()

    @sv.transform(
        requires={"orders": [sv.unique("id")], "customers": [sv.unique("name")]},
        ensures=[sv.unique("id")],
    )
    def regions(orders, customers):
        return sv.sql(
            "SELECT o.id, c.region FROM orders o JOIN customers c ON o.customer = c.name",
            orders=orders,
            customers=customers,
        )

    node = regions(orders, customers)
    node.refresh()
    assert rows(node) == [(1, "eu"), (2, "us"), (3, "eu")]
    customers.apply(sv.Changes(deletes=[("bob", "us")], inserts=[("bob", "eu")]))
    node.refresh()
    assert rows(node) == [(1, "eu"), (2, "eu"), (3, "eu")]


def test_an_unproved_ensures_raises_when_the_node_is_built():
    orders, _customers = sources()

    @sv.transform(ensures=["total > 0"])
    def totals(orders):
        return sv.sql("SELECT sum(amount) AS total FROM orders", orders=orders)

    with pytest.raises(VerificationError, match="total > 0"):
        totals(orders)


@pytest.mark.parametrize("engine", ENGINES)
def test_engines_give_the_rows_of_run(engine):
    orders, _customers = sources()
    node = per_customer(paid(orders))
    node.refresh(engine=engine)
    con = sv.connect()
    con.put("orders", orders.table)
    want = sorted(tuple(r.values()) for r in run(con, node.plan, engine).to_pylist())
    assert rows(node) == want == [("ada", 5), ("bob", 7)]


def test_without_a_sql_producer_the_error_names_the_extra(monkeypatch):
    def none():
        raise ImportError("no producer")

    monkeypatch.setattr("sverify.engine.default_sql_producer", none)
    orders, _customers = sources()
    with pytest.raises(ImportError, match=r"sverify\[datafusion\]"):
        per_customer(orders)


def test_refused_sql_says_what_is_refused():
    orders, _customers = sources()

    @sv.transform()
    def money(orders):
        return sv.sql("SELECT CAST(amount AS DECIMAL(10, 2)) / 3 AS d FROM orders", orders=orders)

    with pytest.raises(Unsupported, match="Lean refuses the SQL: divide of DECIMAL"):
        money(orders)

    @sv.transform()
    def missing(orders):
        return sv.sql("SELECT * FROM nope", orders=orders)

    with pytest.raises(Unsupported, match="nope"):
        missing(orders)


def test_sql_takes_tables_not_nodes():
    orders, _customers = sources()
    with pytest.raises(TypeError, match="inside a transform"):
        sv.sql("SELECT * FROM orders", orders=orders)


def test_sv_sql_stays_the_function():
    import sverify.sql.snowflake  # noqa: F401

    assert callable(sv.sql)


def test_sql_preconditions_are_checked_on_the_data():
    orders, _customers = sources()
    node = per_customer(orders)  # "amount > 0" on the source itself
    with pytest.raises(PreconditionError, match="amount > 0"):
        node.refresh()
