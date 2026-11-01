"""Nodes: transforms composed over sources, fused unless `.write` stores a
result, refreshed upstream first with each stored node written once."""

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _pipelines import (
    ORDERS,
    arrow_table,
    doubled,
    make_orders,
    orders_table,
    paid,
    recomputed,
    rows,
    spy_on,
)
from sverify import nodes
from sverify.contracts import label, violations
from sverify.engines import ENGINES, create_table, delta_plans
from sverify.errors import CompositionError, PreconditionError, VerificationError
from sverify.io import DeltaSink, DeltaSource, StaticSource, sink_from

SETTINGS = settings(max_examples=20, deadline=None, suppress_health_check=[HealthCheck.too_slow])


@sv.transform(requires={"t": [_.amount.notnull()]}, ensures=[_.amount.notnull()])
def big(t):
    return t.filter(t.amount > 5)


def versions(uri):
    return DeltaTable(uri).version()


# -- building nodes -----------------------------------------------------------


def test_a_transform_on_a_source_builds_a_node(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = doubled(paid(orders))
    assert isinstance(node, sv.Node)
    assert node.name == "doubled"
    assert list(node.schema) == ["id", "customer", "doubled"]
    # Plain Ibis tables still give Ibis expressions.
    con = sv.connect()
    create_table(con, "orders", ORDERS, [(1, "ada", 5)])
    assert not isinstance(doubled(paid(con.table("orders"))), sv.Node)


def test_a_broken_link_raises_when_the_node_is_built(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])

    @sv.transform(requires={"t": [_.amount > 100]})
    def huge(t):
        return t

    with pytest.raises(CompositionError, match="huge needs"):
        huge(paid(orders))
    # Through a stored node too: what it guarantees is what its stage proved.
    with pytest.raises(CompositionError, match="huge needs"):
        huge(paid(orders).write(DeltaSink(str(tmp_path / "paid"))))


def test_an_unproved_postcondition_raises_when_the_node_is_built(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])

    @sv.transform(ensures=[_.amount > 0])
    def positive(t):
        return t

    with pytest.raises(VerificationError):
        positive(orders)


def test_a_node_and_an_ibis_table_do_not_mix(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])

    @sv.transform()
    def both(a, b):
        return a.union(b)

    con = sv.connect()
    create_table(con, "orders", ORDERS, [])
    with pytest.raises(TypeError, match="StaticSource"):
        both(orders, con.table("orders"))


def test_two_tables_of_one_name_are_refused(tmp_path):
    a = make_orders(tmp_path / "a" / "orders", [(1, "ada", 5)])
    b = make_orders(tmp_path / "b" / "orders", [(2, "bob", 7)])

    @sv.transform()
    def both(x, y):
        return x.union(y)

    with pytest.raises(ValueError, match="two tables named 'orders'"):
        both(a, b)
    renamed = DeltaSource(b.uri, name="orders_b")
    assert both(a, renamed).refresh() is not None


def test_the_plan_is_the_one_the_stage_runs(tmp_path):
    node = doubled(paid(make_orders(tmp_path / "orders", [(1, "ada", 5)])))
    plan = node.plan
    node.refresh()
    assert node._stage is not None and node._stage.view.plan == plan
    assert delta_plans(plan) == node._stage.view.deltas


def test_results_need_a_refresh(tmp_path):
    node = paid(make_orders(tmp_path / "orders", [(1, "ada", 5)]))
    with pytest.raises(RuntimeError, match="call refresh"):
        node.to_arrow()
    assert "not refreshed yet" in str(node.status())


# -- fusing and storing -------------------------------------------------------


def test_transforms_without_a_write_fuse_into_one_plan(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(orders))
    report = node.refresh()
    # One stage: one view over the source, nothing stored in between.
    assert [s.node for s in report.nodes] == ["doubled"]
    assert node._stage is not None
    assert list(node._stage.pipe.views) == ["doubled"]
    assert list(node._stage.pipe.sources) == ["orders"]
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14)]
    assert node.versions == {"orders": 1}


def test_write_ends_a_stage_and_the_next_reads_it_as_a_source(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    p = paid(orders).write(DeltaSink(str(tmp_path / "paid")))
    d = doubled(p).write(DeltaSink(str(tmp_path / "doubled")))
    report = d.refresh()
    assert [s.node for s in report.nodes] == ["paid", "doubled"]
    assert [w.mode for w in report.writes] == ["created", "created"]
    # The second stage reads the stored table, not the orders.
    assert d._stage is not None
    assert list(d._stage.pipe.sources) == ["paid"]
    assert d.versions == {"paid": versions(tmp_path / "paid")}
    assert rows(d) == [(1, "ada", 10), (2, "bob", 14)]
    stored = sorted(
        tuple(r.values()) for r in DeltaTable(tmp_path / "doubled").to_pyarrow_table().to_pylist()
    )
    assert stored == rows(d)
    # A change flows through both stages, each through its change feed.
    write_deltalake(orders.uri, orders_table([(3, "cy", 1)]), mode="append")
    report = d.refresh()
    assert [w.mode for w in report.writes] == ["merge", "merge"]
    assert "Delta CDF" in str(report["doubled"])
    assert rows(d) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]


def test_each_stored_node_is_written_exactly_once(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    p = paid(orders).write(DeltaSink(str(tmp_path / "paid")))
    d = doubled(p).write(DeltaSink(str(tmp_path / "doubled")))
    d.refresh()
    before = versions(tmp_path / "paid"), versions(tmp_path / "doubled")
    # Nothing new: both writes are skipped and no commit is made.
    report = d.refresh()
    assert [w.mode for w in report.writes] == ["skipped", "skipped"]
    assert (versions(tmp_path / "paid"), versions(tmp_path / "doubled")) == before


def test_a_shared_stored_node_is_refreshed_once(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    p = paid(orders).write(DeltaSink(str(tmp_path / "paid")))
    a = doubled(p)
    b = big(p).write(DeltaSink(str(tmp_path / "big")))
    report = sv.group(a, b).refresh()
    assert [s.node for s in report.nodes] == ["paid", "doubled", "big"]
    assert [w.contract.view for w in report.writes] == ["paid", "big"]
    write_deltalake(orders.uri, orders_table([(3, "cy", 9)]), mode="append")
    report = sv.group(a, b).refresh()
    assert [s.node for s in report.nodes] == ["paid", "doubled", "big"]
    assert report["paid"].write is not None and report["paid"].write.mode == "merge"
    assert rows(a) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 18)]
    assert rows(b) == [(2, "bob", 7), (3, "cy", 9)]
    assert a.versions == b.versions
    status = str(sv.group(a, b).status())
    assert "doubled: paid@v" in status and "stored in" in status


def test_a_group_reads_every_source_at_one_version(tmp_path, monkeypatch):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    a, b = paid(orders), big(orders)
    real = nodes._Stage.build

    def build_then_change(*args, **kwargs):
        stage = real(*args, **kwargs)
        if versions(orders.uri) == 1:  # another writer, between the two nodes
            write_deltalake(orders.uri, orders_table([(2, "bob", 7)]), mode="append")
        return stage

    monkeypatch.setattr(nodes._Stage, "build", build_then_change)
    sv.group(a, b).refresh()
    assert a.versions == b.versions == {"orders": 1}
    assert rows(b) == []
    monkeypatch.undo()
    sv.group(a, b).refresh()
    assert a.versions == b.versions == {"orders": 2}
    assert rows(b) == [(2, "bob", 7)]


def test_a_restarted_job_resumes_from_its_stored_nodes(tmp_path):
    def job():
        orders = DeltaSource(str(tmp_path / "orders"))
        p = paid(orders).write(DeltaSink(str(tmp_path / "paid")))
        return doubled(p).write(DeltaSink(str(tmp_path / "doubled")))

    make_orders(tmp_path / "orders", [(1, "ada", 5)])
    job().refresh()
    write_deltalake(tmp_path / "orders", orders_table([(2, "bob", 7)]), mode="append")
    # A new process: both stages start from what their sinks stored, and
    # bring it up to date with one MERGE each.
    d = job()
    report = d.refresh()
    assert report["paid"].started is not None
    assert report["paid"].started.startswith("resumed from")
    assert report["paid"].report is not None
    assert report["paid"].report.sources[0].mode == "change feed"
    assert [w.mode for w in report.writes] == ["merge", "merge"]
    assert rows(d) == [(1, "ada", 10), (2, "bob", 14)]


def test_preconditions_on_sources_are_checked_at_refresh(tmp_path):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = paid(orders)
    node.refresh()
    write_deltalake(orders.uri, orders_table([(1, "eve", 3)]), mode="append")
    with pytest.raises(PreconditionError, match="unique"):
        node.refresh()
    assert rows(node) == [(1, "ada", 5)]


def test_a_static_source_feeds_its_changes(tmp_path):
    src = StaticSource(orders_table([(1, "ada", 5)]), version=1, name="orders")
    node = doubled(paid(src))
    node.refresh()
    src.apply(sv.Changes(inserts=[(2, "bob", 7)], deletes=[(1, "ada", 5)]))
    report = node.refresh()
    [s] = report["doubled"].report.sources  # type: ignore[union-attr]
    assert (s.start, s.end, s.mode, s.inserts, s.deletes) == (1, 2, "change feed", 1, 1)
    assert "Δ as applied to orders v1→v2" in s.detail
    assert rows(node) == [(2, "bob", 14)]


# -- engines and results ------------------------------------------------------


@pytest.mark.parametrize("engine", ["duckdb", "polars", "datafusion"])
def test_the_engine_is_chosen_at_refresh(tmp_path, engine, monkeypatch):
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(orders))
    used = spy_on(
        monkeypatch, "sverify.incremental.run_plan", lambda con, plan, eng=None: eng or con.engine
    )
    node.refresh(engine=engine)
    write_deltalake(orders.uri, orders_table([(3, "cy", 1)]), mode="append")
    node.refresh(engine=engine)
    assert used and set(used) == {engine}
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]
    # The same node, another engine.
    used.clear()
    write_deltalake(orders.uri, orders_table([(4, "dan", 2)]), mode="append")
    other = "polars" if engine != "polars" else "duckdb"
    node.refresh(engine=other)
    assert set(used) == {other}
    assert rows(node)[-1] == (4, "dan", 4)


def test_a_spark_session_as_the_engine(tmp_path):
    from spark_session import session

    orders = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(orders))
    node.refresh(engine=session())
    write_deltalake(orders.uri, orders_table([(3, "cy", 1)]), mode="append")
    node.refresh(engine=session())
    assert node._stage is not None and node._stage.view.engine is session()
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]


def test_results_come_out_as_arrow_polars_pandas_and_ibis(tmp_path):
    node = doubled(paid(make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])))
    node.refresh()
    assert node.to_arrow().num_rows == 2
    assert sorted(node.to_polars()["doubled"].to_list()) == [10, 14]
    assert sorted(node.to_pandas()["doubled"]) == [10, 14]
    assert node.table.filter(_.doubled > 12).to_pandas()["customer"].tolist() == ["bob"]


# -- contracts across refreshes -------------------------------------------------


def static_orders(rows):
    return StaticSource(orders_table(rows), version=1, name="orders")


def ensures_hold(node, transform):
    for c in transform.ensures:
        assert violations(node.table, c) == 0, label(c)


def test_the_first_refresh_checks_the_preconditions_on_the_sources():
    node = doubled(paid(static_orders([(1, "ada", 5), (2, "bob", 0)])))
    report = node.refresh()
    assert {p.condition for p in report["doubled"].preconditions} == {
        "(_.amount >= 0)",
        "_.id.notnull()",
        "unique(id)",
    }
    assert rows(node) == [(1, "ada", 10), (2, "bob", 0)]
    node = doubled(paid(static_orders([(1, "ada", 5), (1, "bob", 7)])))
    with pytest.raises(PreconditionError, match=r"unique\(id\)"):
        node.refresh()


@pytest.mark.parametrize(
    ("batch", "error"),
    [
        (sv.Changes(inserts=[(3, "cy", -1)]), r"inserted row\(s\) of orders violate"),
        (sv.Changes(inserts=[(2, "cy", 1)]), r"inserted key\(s\) of orders violate unique"),
        (sv.Changes(inserts=[(3, "cy", 1), (3, "dan", 2)]), "unique"),
    ],
)
def test_a_batch_violating_a_precondition_changes_nothing(batch, error):
    src = static_orders([(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    src.apply(batch)
    with pytest.raises(PreconditionError, match=error):
        node.refresh()
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14)]
    assert node.versions == {"orders": 1}


def test_deleting_a_key_frees_it_for_the_same_batch():
    src = static_orders([(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    src.apply(sv.Changes(inserts=[(2, "cy", 1)], deletes=[(2, "bob", 7)]))
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src) == [(1, "ada", 10), (2, "cy", 2)]


def test_batches_are_checked_without_reading_the_tables(monkeypatch):
    src = static_orders([(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    checked = spy_on(monkeypatch, "sverify.contracts.violations", lambda t, *a: t.get_name())
    src.apply(sv.Changes(inserts=[(3, "cy", 1)]))
    node.refresh()
    assert checked == ["orders$inserts"]


names = st.sampled_from(["ada", "bob", None])


@st.composite
def keyed_batch(draw, src):
    """Inserts and deletes that keep `id` a key and `amount` non-negative."""
    current = [tuple(r.values()) for r in src.table.to_pylist()]
    deletes = draw(st.lists(st.sampled_from(current), unique=True, max_size=2)) if current else []
    kept = {r[0] for r in current} - {r[0] for r in deletes}
    fresh = st.integers(0, 8).filter(lambda i: i not in kept)
    ids = draw(st.lists(fresh, unique=True, max_size=3))
    amounts = st.integers(0, 30)
    return sv.Changes(inserts=[(i, draw(names), draw(amounts)) for i in ids], deletes=deletes)


@pytest.mark.parametrize("engine", ENGINES)
@SETTINGS
@given(data=st.data())
def test_guarantees_hold_in_every_state(engine, data):
    src = static_orders([])
    node = doubled(paid(src))
    node.refresh(engine=engine)
    for _step in range(data.draw(st.integers(1, 4))):
        src.apply(data.draw(keyed_batch(src)))
        node.refresh(engine=engine)
        assert rows(node) == recomputed(node, src)
        ensures_hold(node, doubled)


# -- jobs of stored nodes over stored nodes ---------------------------------------

CUSTOMERS = pa.schema([pa.field("name", pa.string()), pa.field("city", pa.string())])


@sv.transform(requires={"t": [_.doubled >= 0, sv.unique("id")]}, ensures=[_.big.notnull()])
def flagged(t):
    return t.select(t.id, t.customer, big=t.doubled > 20)


def cities(flags, customers):
    return flags.join(customers, flags.customer == customers.name).select("id", "big", "city")


def located(base, customers):
    # A left join has no delta rule: recomputed and diffed, and its change
    # still flows on.
    return base.left_join(customers, base.customer == customers.name).select(
        "id", "doubled", "city"
    )


def job(orders, customers):
    """base, by_city, located and rich: nodes over stored nodes in memory."""
    base = doubled(paid(orders)).write(sink_from(lambda t: None, name="base"))
    by_city = flagged(base).pipe(cities, customers=customers)
    loc = base.pipe(located, customers=customers).write(sink_from(lambda t: None, name="located"))
    rich = loc.pipe(lambda t: t.filter(t.doubled > 10))
    return base, by_city, loc, rich


def test_nodes_read_stored_nodes_and_contracts_connect():
    customers = StaticSource(arrow_table(CUSTOMERS, [("ada", "Rome")]), name="customers")
    base, by_city, loc, rich = job(static_orders([(1, "ada", 15), (2, "bob", 3)]), customers)
    # `flagged`'s precondition on `base` was proved from `doubled`'s contract.
    assert flagged.last_report is not None
    assert flagged.last_report.requires == {
        "doubled": ["(_.doubled >= 0)", "_.doubled.notnull()", "unique(id)"]
    }
    jobs = sv.group(base, by_city, loc, rich)
    jobs.refresh()
    assert [s.node for s in jobs.status().nodes if s.recomputed] == ["located"]
    assert rows(by_city) == [(1, True, "Rome")]
    assert rows(rich) == [(1, 30, "Rome")]


customers_row = st.tuples(names, st.sampled_from(["Paris", "Rome", None]))


@pytest.mark.parametrize("engine", ENGINES)
@SETTINGS
@given(data=st.data())
def test_a_job_of_stored_nodes_matches_recompute(engine, data):
    orders = static_orders([])
    customers = StaticSource(
        arrow_table(CUSTOMERS, data.draw(st.lists(customers_row, max_size=3))), name="customers"
    )
    nodes_ = job(orders, customers)
    sv.group(*nodes_).refresh(engine=engine)
    for _step in range(data.draw(st.integers(1, 4))):
        current = [tuple(r.values()) for r in customers.table.to_pylist()]
        deletes = data.draw(st.lists(st.sampled_from(current), max_size=1)) if current else []
        orders.apply(data.draw(keyed_batch(orders)))
        customers.apply(
            sv.Changes(inserts=data.draw(st.lists(customers_row, max_size=2)), deletes=deletes)
        )
        sv.group(*nodes_).refresh(engine=engine)
        fresh = job(
            StaticSource(orders.table, name="orders"),
            StaticSource(customers.table, name="customers"),
        )
        sv.group(*fresh).refresh(engine=engine)
        for node, want in zip(nodes_, fresh, strict=True):
            assert rows(node) == rows(want), node.name
        ensures_hold(nodes_[0], doubled)
        ensures_hold(nodes_[1], flagged)
