"""Differential tests: an incrementally maintained view must always equal the
view recomputed from scratch, across random batches of inserts and deletes."""

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv

QUERIES = {
    "filter_project": "select id, amount * 2 as doubled from orders where amount > 10",
    "inner_join": "select o.id, c.city from orders o join customers c on o.customer = c.name",
    "union_all": "select id from orders union all select id from orders where amount < 3",
    "cross_filter": "select o.id, c.city from orders o, customers c where o.amount > 20",
    "self_join": (
        "select a.id, b.id as other from orders a join orders b on a.customer = b.customer"
    ),
}

names = st.sampled_from(["ada", "bob", "cy", None])
orders_row = st.tuples(st.integers(0, 5), names, st.one_of(st.none(), st.integers(0, 40)))
customers_row = st.tuples(names, st.sampled_from(["Paris", "Rome", None]))


def setup(orders, customers):
    con = sv.connect()
    con.sql("create table orders(id bigint, customer varchar, amount bigint)")
    con.sql("create table customers(name varchar, city varchar)")
    if orders:
        con.executemany("insert into orders values (?, ?, ?)", orders)
    if customers:
        con.executemany("insert into customers values (?, ?)", customers)
    return con


def table_rows(con, t):
    return con.sql(f"select * from {t}").fetchall()


@st.composite
def batch(draw, con, t, row):
    """Random inserts plus deletes of rows that currently exist."""
    current = table_rows(con, t)
    deletes = draw(st.lists(st.sampled_from(current), unique_by=id, max_size=3)) if current else []
    # Deleting a row twice needs two copies of it.
    deletes = [r for i, r in enumerate(deletes) if deletes[: i + 1].count(r) <= current.count(r)]
    return sv.Changes(inserts=draw(st.lists(row, max_size=3)), deletes=deletes)


def run_differential(data, make_view):
    con = setup(
        data.draw(st.lists(orders_row, max_size=6)), data.draw(st.lists(customers_row, max_size=4))
    )
    view = make_view(con)
    assert view.rows() == view.recompute()
    for _ in range(data.draw(st.integers(1, 4))):
        changes = {
            t: data.draw(batch(con, t, orders_row if t == "orders" else customers_row))
            for t in view.tables
        }
        view.apply(changes)
        assert view.rows() == view.recompute()


SETTINGS = settings(max_examples=30, deadline=None, suppress_health_check=[HealthCheck.too_slow])


@pytest.mark.parametrize("name", QUERIES)
@SETTINGS
@given(data=st.data())
def test_sql_view_matches_recompute(name, data):
    run_differential(data, lambda con: sv.IncrementalView(con, QUERIES[name], "v"))


@SETTINGS
@given(data=st.data())
def test_ibis_view_matches_recompute(data):
    def make(con):
        db = ibis.duckdb.from_connection(con)
        orders, customers = db.table("orders"), db.table("customers")
        expr = (
            orders.filter(orders.amount > 5)
            .join(customers, orders.customer == customers.name)
            .select(orders.id, customers.city, total=orders.amount + 1)
        )
        return sv.IncrementalView.from_ibis(con, expr, "v")

    run_differential(data, make)


def test_left_join_is_rejected():
    con = setup([], [])
    with pytest.raises(sv.NotIncremental):
        sv.IncrementalView(
            con,
            "select o.id, c.city from orders o left join customers c on o.customer = c.name",
            "v",
        )


def test_deleting_a_missing_row_fails_and_rolls_back():
    con = setup([(1, "ada", 30)], [])
    view = sv.IncrementalView(con, QUERIES["filter_project"], "v")
    with pytest.raises(ValueError):
        view.apply({"orders": sv.Changes(deletes=[(9, "zed", 1)])})
    assert view.rows() == view.recompute() == [(1, 60)]
    assert table_rows(con, "orders") == [(1, "ada", 30)]
