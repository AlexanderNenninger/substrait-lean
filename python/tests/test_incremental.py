"""Differential tests: an incrementally maintained view must always equal the
view recomputed from scratch, across random batches of inserts and deletes, on
every engine.

These drive `IncrementalView` and `Pipeline` directly: they test the delta
rules on any batch, and the guards of a pipeline of several views, which a
node (one view per stage, fed by its sources) does not reach. What users see
of both is tested through nodes in `test_nodes.py`."""

from datetime import datetime

import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import sverify as sv
from _pipelines import connect_with, doubled, paid
from sverify.engines import ENGINES, create_table, table_rows
from sverify.errors import NotIncremental
from sverify.incremental import IncrementalView, Pipeline
from sverify_dev.examples import PIPELINES, UNSUPPORTED

# Plain SQL goes through the same route as Ibis (both reach DataFusion as SQL);
# one query keeps that entry point covered.
SQL_QUERY = "select o.id, c.city from orders o, customers c where o.amount > 20"

names = st.sampled_from(["ada", "bob", "cy", None])
orders_row = st.tuples(st.integers(0, 5), names, st.one_of(st.none(), st.integers(0, 40)))
customers_row = st.tuples(names, st.sampled_from(["Paris", "Rome", None]))


@st.composite
def batch(draw, con, t, row):
    """Random inserts plus deletes of rows that currently exist."""
    current = table_rows(con, t)
    deletes = draw(st.lists(st.sampled_from(current), unique_by=id, max_size=3)) if current else []
    # Deleting a row twice needs two copies of it.
    deletes = [r for i, r in enumerate(deletes) if deletes[: i + 1].count(r) <= current.count(r)]
    return sv.Changes(inserts=draw(st.lists(row, max_size=3)), deletes=deletes)


def run_differential(data, make_view):
    con = connect_with(
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


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", PIPELINES)
@SETTINGS
@given(data=st.data())
def test_ibis_view_matches_recompute(name, engine, data):
    run_differential(data, lambda con: IncrementalView(con, PIPELINES[name], "v", engine))


@pytest.mark.parametrize("engine", ENGINES)
@SETTINGS
@given(data=st.data())
def test_sql_view_matches_recompute(engine, data):
    run_differential(data, lambda con: IncrementalView(con, SQL_QUERY, "v", engine))


def test_left_join_is_rejected():
    con = connect_with([], [])
    with pytest.raises(NotIncremental):
        IncrementalView(con, UNSUPPORTED["left_join"], "v")


def test_aggregate_is_rejected():
    con = connect_with([], [])
    with pytest.raises(NotIncremental):
        IncrementalView(con, UNSUPPORTED["aggregate"], "v")


def test_view_named_after_an_input_is_rejected():
    con = connect_with([(1, "ada", 30), (2, "bob", 5)], [])
    with pytest.raises(ValueError, match="is a table the view reads"):
        IncrementalView(con, PIPELINES["filter_project"], "orders")
    assert table_rows(con, "orders") == [(1, "ada", 30), (2, "bob", 5)]


@pytest.mark.parametrize("engine", ENGINES)
def test_deleting_a_missing_row_fails_and_rolls_back(engine):
    con = connect_with([(1, "ada", 30)], [])
    view = IncrementalView(con, PIPELINES["filter_project"], "v", engine)
    with pytest.raises(ValueError):
        view.apply({"orders": sv.Changes(deletes=[(9, "zed", 1)])})
    assert view.rows() == view.recompute() == [(1, 60)]
    assert table_rows(con, "orders") == [(1, "ada", 30)]


EVENTS = ibis.table({"name": "string", "ts": "timestamp"}, name="events")
#: Views with the string and time functions, whose delta plans Lean writes.
EVENT_VIEWS = {
    "strings": EVENTS.filter(EVENTS.name.like("a%") | EVENTS.name.re_search("^b")).select(
        u=EVENTS.name.upper(),
        n=EVENTS.name.length(),
        s=EVENTS.name.substr(1, 2),
        t=EVENTS.name.strip(),
        c=EVENTS.name + "!",
        e=EVENTS.name.endswith("y"),
    ),
    "time": EVENTS.filter(EVENTS.ts.year() >= 2000).select(
        "name",
        d=EVENTS.ts.date(),
        h=EVENTS.ts.truncate("h"),
        m=EVENTS.ts.month(),
        w=EVENTS.ts.week_of_year(),
    ),
}
events_row = st.tuples(
    st.sampled_from(["ada", "bob", " amy ", "by", None]),
    st.one_of(st.none(), st.datetimes(datetime(1990, 1, 1), datetime(2030, 1, 1))),
)


@pytest.mark.parametrize("name", EVENT_VIEWS)
@SETTINGS
@given(data=st.data())
def test_string_and_time_views_match_recompute(name, data):
    con = sv.connect()
    create_table(con, "events", EVENTS.schema(), data.draw(st.lists(events_row, max_size=6)))
    view = IncrementalView(con, EVENT_VIEWS[name], "v")
    assert view.rows() == view.recompute()
    for _ in range(data.draw(st.integers(1, 3))):
        view.apply({"events": data.draw(batch(con, "events", events_row))})
        assert view.rows() == view.recompute()


# -- Pipeline guards ----------------------------------------------------------


def test_unproved_links_cannot_be_maintained():
    con = connect_with([(1, "ada", 5)])
    derived = con.table("orders").filter(ibis._.id > 0)
    with pytest.raises(ValueError, match="not proved"):
        IncrementalView(con, doubled(derived), "v")


def test_preconditions_on_unproved_views_are_refused():
    con = connect_with([(1, "ada", 15)])
    pipe = Pipeline(con)
    plain = pipe.view("plain", con.table("orders").filter(ibis._.amount > 0))
    with pytest.raises(ValueError, match="must be proved"):
        pipe.view("p", paid(plain.table))


def test_views_change_only_through_their_inputs():
    con = connect_with([(1, "ada", 15)])
    pipe = Pipeline(con)
    pipe.view("base", doubled(paid(con.table("orders"))))
    with pytest.raises(ValueError, match="views change only through their inputs"):
        pipe.apply({"base": sv.Changes(inserts=[(9, "x", 1)])})
