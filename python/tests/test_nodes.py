"""Nodes: transforms composed over sources, fused unless `.write` stores a
result, refreshed upstream first with each stored node written once."""

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from sverify import nodes
from sverify.errors import CompositionError, PreconditionError, VerificationError
from sverify.io import DeltaSink, DeltaSource, StaticSource

ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64()),
    ]
)


def orders_table(rows):
    return pa.Table.from_pylist(
        [dict(zip(ORDERS.names, r, strict=True)) for r in rows], schema=ORDERS
    )


def make_orders(path, rows):
    DeltaTable.create(path, ORDERS, configuration={"delta.enableChangeDataFeed": "true"})
    write_deltalake(path, orders_table(rows), mode="append")
    return DeltaSource(str(path))


@sv.transform(
    requires={"orders": [_.amount >= 0, _.id.notnull(), sv.unique("id")]},
    ensures=[_.amount >= 0, _.amount.notnull(), sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount.notnull())


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount.notnull(), sv.unique("id")]},
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(t):
    return t.select(t.id, t.customer, doubled=t.amount * 2)


@sv.transform(requires={"t": [_.amount.notnull()]}, ensures=[_.amount.notnull()])
def big(t):
    return t.filter(t.amount > 5)


def rows(node):
    return sorted(tuple(r.values()) for r in node.to_arrow().to_pylist())


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
    sv.create_table(con, "orders", ORDERS, [(1, "ada", 5)])
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
    sv.create_table(con, "orders", ORDERS, [])
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
    used = []
    real = sv.engine.run_plan

    def spy(con, plan, eng=None):
        used.append(eng or con.engine)
        return real(con, plan, eng)

    monkeypatch.setattr("sverify.incremental.run_plan", spy)
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
