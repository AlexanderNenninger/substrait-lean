"""Differential tests: an incrementally maintained view must always equal the
view recomputed from scratch, across random batches of inserts and deletes, on
every engine."""

import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from sverify.examples import PIPELINES, UNSUPPORTED, create_tables

# Plain SQL goes through the same route as Ibis (both reach DataFusion as SQL);
# one query keeps that entry point covered.
SQL_QUERY = "select o.id, c.city from orders o, customers c where o.amount > 20"

names = st.sampled_from(["ada", "bob", "cy", None])
orders_row = st.tuples(st.integers(0, 5), names, st.one_of(st.none(), st.integers(0, 40)))
customers_row = st.tuples(names, st.sampled_from(["Paris", "Rome", None]))


def setup(orders, customers):
    con = sv.connect()
    create_tables(con, orders, customers)
    return con


table_rows = sv.table_rows


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
ENGINES = ["datafusion", "duckdb"]


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", PIPELINES)
@SETTINGS
@given(data=st.data())
def test_ibis_view_matches_recompute(name, engine, data):
    run_differential(data, lambda con: sv.IncrementalView(con, PIPELINES[name], "v", engine))


@pytest.mark.parametrize("engine", ENGINES)
@SETTINGS
@given(data=st.data())
def test_sql_view_matches_recompute(engine, data):
    run_differential(data, lambda con: sv.IncrementalView(con, SQL_QUERY, "v", engine))


def test_left_join_is_rejected():
    con = setup([], [])
    with pytest.raises(sv.NotIncremental):
        sv.IncrementalView(con, UNSUPPORTED["left_join"], "v")


def test_aggregate_is_rejected():
    con = setup([], [])
    with pytest.raises(ValueError, match="unsupported relation"):
        sv.IncrementalView(con, UNSUPPORTED["aggregate"], "v")


@pytest.mark.parametrize("engine", ENGINES)
def test_deleting_a_missing_row_fails_and_rolls_back(engine):
    con = setup([(1, "ada", 30)], [])
    view = sv.IncrementalView(con, PIPELINES["filter_project"], "v", engine)
    with pytest.raises(ValueError):
        view.apply({"orders": sv.Changes(deletes=[(9, "zed", 1)])})
    assert view.rows() == view.recompute() == [(1, 60)]
    assert table_rows(con, "orders") == [(1, "ada", 30)]
