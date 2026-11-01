"""Delta Lake tables as change sources (CDF), sources of preconditions and
sinks, on local tables in temporary directories."""

import shutil
from collections import Counter
from datetime import datetime
from pathlib import Path

import ibis
import pyarrow as pa
import pyarrow.compute as pc
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _

import sverify as sv
from _pipelines import (
    ORDERS,
    batch,
    discharged,
    doubled,
    make_orders,
    orders_table,
    paid,
    recomputed,
    rows,
    spy_on,
)
from sverify.contracts import ON_DATA, SCHEMA, label
from sverify.engine import Engine
from sverify.engines import create_table
from sverify.errors import AuditError, PreconditionError, SchemaError
from sverify.incremental import IncrementalView, Pipeline, arrow_rows
from sverify.io import DeltaSink, DeltaSource, StaticSource
from sverify.io._common import ColumnStats
from sverify.io.delta import file_stats


def source_schema(node, name):
    """The schema `node`'s stage holds source `name` in (internal: what the
    stage reads, not what the node gives)."""
    assert node._stage is not None
    return node._stage.pipe.con.arrow[name].schema


# -- Step 1: the Change Data Feed as a change source --------------------------


@pytest.mark.parametrize("engine", ["datafusion", "polars", "duckdb"])
def test_refresh_applies_cdf(tmp_path, engine: Engine):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh(engine=engine)
    assert node.versions == {"orders": 1}
    dt = DeltaTable(src.uri)
    write_deltalake(dt, orders_table([(3, "cy", 1)]), mode="append")
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    dt.delete("id = 2")
    report = batch(node, engine=engine)
    assert rows(node) == recomputed(node, src) == [(1, "ada", 12), (3, "cy", 2)]
    assert node.versions == {"orders": 4}
    [s] = report.sources
    assert (s.start, s.end, s.mode) == (1, 4, "change feed")
    assert (s.inserts, s.deletes) == (2, 2)
    assert "Δ trusted as coming from Delta CDF v1→v4" in str(report)
    assert "view doubled: orders@v4" in str(report)


def test_refresh_without_new_version_is_a_no_op(tmp_path):
    node = doubled(paid(make_orders(tmp_path / "orders", [(1, "ada", 5)])))
    node.refresh()
    assert str(batch(node).sources[0]) == "orders@v1: no new version"


def test_a_failed_refresh_changes_nothing_and_a_retry_applies_once(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = doubled(paid(src))
    node.refresh()
    # A duplicate key: Delta does not enforce keys, the node does.
    write_deltalake(src.uri, orders_table([(1, "eve", 3)]), mode="append")
    with pytest.raises(PreconditionError, match="unique"):
        node.refresh()
    assert node.versions == {"orders": 1}
    assert rows(node) == [(1, "ada", 10)]
    DeltaTable(src.uri).delete("customer = 'eve'")
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = batch(node)
    # The CDF from v1 holds eve's insert and delete; they cancel out.
    assert (report.sources[0].inserts, report.sources[0].deletes) == (1, 0)
    assert rows(node) == [(1, "ada", 10), (2, "bob", 2)]
    assert batch(node).sources[0].mode == "unchanged"
    assert rows(node) == [(1, "ada", 10), (2, "bob", 2)]


def test_no_cdf_recomputes_and_says_so(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)], cdf=False)
    node = doubled(paid(src))
    node.refresh()
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = batch(node)
    [s] = report.sources
    assert s.mode == "recomputed"
    assert report.recomputed == ["orders"]
    assert "Delta CDF v1→v2 unavailable" in s.detail
    assert "recomputed from scratch" in str(report)
    assert rows(node) == [(1, "ada", 10), (2, "bob", 2)]


def test_vacuumed_history_recomputes(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="overwrite")
    DeltaTable(src.uri).vacuum(retention_hours=0, enforce_retention_duration=False, dry_run=False)
    assert batch(node).sources[0].mode == "recomputed"
    assert rows(node) == [(3, "cy", 2)]


def test_audit_compares_with_the_snapshot(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = doubled(paid(src))
    node.refresh()
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = batch(node, audit=True)
    assert report.audited and "audit:" in str(report)
    assert rows(node) == recomputed(node, src)


def test_audit_catches_a_wrong_feed(tmp_path, monkeypatch):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    node = doubled(paid(src))
    node.refresh()
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    real = DeltaSource.changes

    def lossy(self, since, *args):
        out = real(self, since, *args)
        out.changes = sv.Changes()
        return out

    monkeypatch.setattr(DeltaSource, "changes", lossy)
    with pytest.raises(AuditError, match="nothing was applied"):
        node.refresh(audit=True)
    assert node.versions == {"orders": 1} and rows(node) == [(1, "ada", 10)]


def test_audit_catches_a_wrong_view_before_the_commit(tmp_path, monkeypatch):
    src, stored = job1(tmp_path)
    stored.refresh()
    sink_version = DeltaTable(str(tmp_path / "big")).version()
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    real = IncrementalView._delta

    def wrong(self, deltas):
        delta, examples = real(self, deltas)
        delta = Counter({k: 2 * n for k, n in delta.items()})
        return delta, examples

    monkeypatch.setattr(IncrementalView, "_delta", wrong)
    with pytest.raises(AuditError, match="big differs from its recomputation; nothing was applied"):
        stored.refresh(audit=True)
    # State, versions and sink are as before the refresh.
    assert stored.versions == {"orders": 1}
    assert rows(stored) == [(1, "ada", 10), (2, "bob", 14)]
    assert DeltaTable(str(tmp_path / "big")).version() == sink_version
    monkeypatch.undo()
    # Audited again: had the failed refresh applied the batch to the stage's
    # copy of orders, this one would not match the snapshot.
    report = stored.refresh(audit=True)
    assert [w.mode for w in report.writes] == ["merge"]
    assert rows(stored) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]


def test_views_over_views_record_source_versions(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    top = doubled(paid(src)).pipe(lambda t: t.filter(t.doubled > 4))
    top.refresh()
    write_deltalake(src.uri, orders_table([(2, "bob", 9)]), mode="append")
    report = batch(top)
    assert top.versions == {"orders": 2}
    assert report.versions == {"step": {"orders": 2}}
    assert rows(top) == [(1, "ada", 10), (2, "bob", 18)]


def test_timestamps_and_nulls_round_trip(tmp_path):
    schema = pa.schema(
        [pa.field("k", pa.int64(), nullable=False), pa.field("ts", pa.timestamp("us"))]
    )
    t1 = datetime(2024, 1, 1, 0, 0, 0, 123456)
    write_deltalake(
        tmp_path / "ev",
        pa.Table.from_pylist([{"k": 1, "ts": t1}], schema=schema),
        configuration={"delta.enableChangeDataFeed": "true"},
    )
    ev = DeltaSource(str(tmp_path / "ev"))
    node = ev.pipe(lambda t: t.filter(t.k > 0))
    node.refresh()
    write_deltalake(
        tmp_path / "ev", pa.Table.from_pylist([{"k": 2, "ts": None}], schema=schema), mode="append"
    )
    node.refresh()
    assert rows(node) == recomputed(node, ev) == [(1, t1), (2, None)]


# -- Step 2: preconditions from table metadata --------------------------------


@sv.transform(
    requires={
        "orders": [
            _.id.notnull(),
            _.amount >= 0,
            _.amount <= 100,
            _.customer.notnull(),
            _.customer != "eve",
            sv.unique("id"),
        ]
    },
    ensures=[_.amount >= 0],
)
def checked(orders):
    return orders.select(orders.id, orders.amount)


def first_preconditions(node):
    """How the first refresh of `node` established each precondition."""
    return discharged(node.refresh()[node.name].preconditions)


def test_preconditions_come_from_metadata(tmp_path):
    src = make_orders(
        tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)], constraints={"pos": "amount >= 0"}
    )
    node = checked(src)
    first = node.refresh()["checked"]
    assert discharged(first.preconditions) == {
        ("orders", "_.id.notnull()"): SCHEMA,
        ("orders", "(_.amount >= 0)"): "Delta constraint",
        ("orders", "(_.amount <= 100)"): "file stats @v2",
        # NULL counts are exact, even for strings ...
        ("orders", "_.customer.notnull()"): "file stats @v2",
        # ... but string bounds are not used.
        ("orders", "(_.customer != 'eve')"): ON_DATA,
        # Neither format enforces keys.
        ("orders", "unique(id)"): ON_DATA,
    }
    assert "requires orders: (_.amount <= 100) (file stats @v2)" in str(first)
    # A batch is discharged from the statistics of the files it added.
    write_deltalake(src.uri, orders_table([(3, "cy", 50)]), mode="append")
    report = batch(node)
    found = discharged(report.preconditions)
    assert found[("orders", "(_.amount <= 100)")] == "file stats @v3 (new files)"
    assert found[("orders", "(_.amount >= 0)")] == "Delta constraint"
    assert found[("orders", "unique(id)")] == ON_DATA
    assert "requires orders: (_.amount <= 100) (file stats @v3 (new files))" in str(report)
    # Statistics that do not bound the batch leave it to the data.
    write_deltalake(src.uri, orders_table([(4, "dan", 500)]), mode="append")
    with pytest.raises(PreconditionError, match=r"inserted row\(s\) of orders violate"):
        node.refresh()
    assert node.versions == {"orders": 3}


def test_missing_statistics_are_unknown(tmp_path):
    path = tmp_path / "orders"
    write_deltalake(
        path,
        orders_table([(1, "ada", 5)]),
        configuration={"delta.dataSkippingNumIndexedCols": "0"},
    )
    found = first_preconditions(checked(DeltaSource(str(path))))
    assert found[("orders", "(_.amount <= 100)")] == ON_DATA
    assert found[("orders", "_.id.notnull()")] == SCHEMA


def test_one_file_without_statistics_makes_a_column_unknown(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    DeltaTable(src.uri).alter.set_table_properties({"delta.dataSkippingNumIndexedCols": "0"})
    write_deltalake(src.uri, orders_table([(2, "bob", 6)]), mode="append")
    assert first_preconditions(checked(src))[("orders", "(_.amount <= 100)")] == ON_DATA


def test_truncated_timestamp_statistics_are_widened(tmp_path):
    schema = pa.schema([pa.field("ts", pa.timestamp("us"), nullable=False)])
    t1 = datetime(2024, 1, 1, 0, 0, 0, 123456)
    write_deltalake(tmp_path / "ev", pa.Table.from_pylist([{"ts": t1}], schema=schema))
    bounds = [
        _.ts >= datetime(2024, 1, 1),
        _.ts <= datetime(2024, 1, 1, 0, 0, 0, 124000),
        _.ts <= t1,
    ]

    @sv.transform(requires={"t": bounds})
    def f(t):
        return t

    found = first_preconditions(f(DeltaSource(str(tmp_path / "ev"))))
    # Delta keeps the maximum as ...00.123000; the true maximum is up to
    # 999 µs later, so only the weaker bound follows from the statistics.
    assert [found[("ev", label(c))] for c in bounds] == [
        "file stats @v0",
        "file stats @v0",
        ON_DATA,
    ]


def test_tables_without_metadata_are_checked_on_data():
    con = sv.connect()
    create_table(
        con,
        "orders",
        ibis.schema({"id": "!int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 5)],
    )
    checked(con.table("orders"))
    assert set(discharged(checked.last_preconditions).values()) == {ON_DATA}


# -- Step 3: a Delta sink that carries the contract ---------------------------


def delta_rows(uri):
    t = pa.table(DeltaTable(uri).to_pyarrow_table())
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def job1(tmp_path, src=None):
    """`doubled(paid(orders))` stored in `big`; a new job each call."""
    if src is None:
        src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    return src, doubled(paid(src)).write(DeltaSink(str(tmp_path / "big")))


def test_sink_writes_contract_and_changes(tmp_path):
    src, stored = job1(tmp_path)
    uri = str(tmp_path / "big")
    first = stored.refresh().writes[0]
    assert first.mode == "created"
    assert delta_rows(uri) == sorted(rows(stored), key=repr)
    out = DeltaTable(uri)
    fields = {f.name: f.nullable for f in pa.schema(out.schema().to_arrow())}
    assert fields == {"id": True, "customer": True, "doubled": False}
    assert out.metadata().configuration["delta.constraints.sverify_1"] == "doubled >= 0"
    assert out.transaction_version("sverify:big") == 1
    contract = DeltaSource(uri).contract()
    assert contract is not None
    assert contract.sources == {"orders": 1} and contract.unique == [["id"]]
    assert contract.plan == first.contract.plan and len(contract.plan) == 64
    # A change to the source becomes one MERGE commit on the sink.
    dt = DeltaTable(src.uri)
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    write_deltalake(dt, orders_table([(3, "cy", 0)]), mode="append")
    before = DeltaTable(uri).version()
    second = stored.refresh().writes[0]
    assert second.mode == "merge" and second.version == before + 1
    assert (second.inserted, second.deleted) == (2, 1)
    assert delta_rows(uri) == rows(stored) == [(1, "ada", 12), (2, "bob", 14), (3, "cy", 0)]
    later = DeltaSource(uri).contract()
    assert later is not None and later.sources == {"orders": 3}
    assert DeltaTable(uri).transaction_version("sverify:big") == 3


def test_sink_writes_exactly_once(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()
    version = DeltaTable(str(tmp_path / "big")).version()
    assert stored.refresh().writes[0].mode == "skipped"
    # A restarted job at the same source versions finds its commit.
    _, again = job1(tmp_path, src)
    assert again.refresh().writes[0].mode == "skipped"
    assert DeltaTable(str(tmp_path / "big")).version() == version
    # At a later version, a restarted job resumes and merges the change.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    _, later = job1(tmp_path, src)
    assert later.refresh().writes[0].mode == "merge"
    assert delta_rows(str(tmp_path / "big")) == sorted(rows(later), key=repr)


def test_sink_keeps_multiplicities_and_nulls(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 5), (3, None, 1)])
    names = src.pipe(lambda o: o.select(o.customer, o.amount)).write(
        DeltaSink(str(tmp_path / "names"))
    )
    names.refresh()
    DeltaTable(src.uri).delete("id = 1")
    write_deltalake(src.uri, orders_table([(4, None, 1), (5, "ada", 5)]), mode="append")
    names.refresh()
    assert delta_rows(str(tmp_path / "names")) == sorted(rows(names), key=repr)
    assert len(rows(names)) == 4


def test_contracts_travel_between_jobs(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()

    @sv.transform(
        requires={"t": [_.doubled >= 0, _.doubled.notnull(), sv.unique("id")]},
        ensures=[_.half >= 0],
    )
    def halved(t):
        return t.select(t.id, half=t.doubled // 2)

    # Job 2 reads job 1's output; its preconditions come from job 1's contract.
    big = DeltaSource(str(tmp_path / "big"))
    halves = halved(big)
    assert first_preconditions(halves) == {
        ("big", "(_.doubled >= 0)"): "Delta constraint",
        ("big", "_.doubled.notnull()"): SCHEMA,
        ("big", "unique(id)"): ON_DATA,
    }
    # Job 1 moves on; job 2 follows the sink's own change feed.
    write_deltalake(src.uri, orders_table([(3, "cy", 4)]), mode="append")
    stored.refresh()
    report = batch(halves)
    assert report.sources[0].mode == "change feed"
    assert rows(halves) == recomputed(halves, big) == [(1, 5), (2, 7), (3, 4)]
    assert discharged(report.preconditions)[("big", "(_.doubled >= 0)")] == "Delta constraint"


# -- Schema evolution ---------------------------------------------------------


def test_added_column_is_left_out(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    wide = orders_table([(3, "cy", 1)]).append_column("note", pa.array(["new"]))
    write_deltalake(src.uri, wide, mode="append", schema_mode="merge")
    [s] = batch(node).sources
    assert "schema: added note, read in the old schema" in s.detail
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]
    assert source_schema(node, "orders") == ORDERS
    # The next batch is read the same way.
    write_deltalake(src.uri, wide.set_column(0, "id", pa.array([4])), mode="append")
    assert batch(node).sources[0].mode == "change feed"
    assert rows(node) == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2), (4, "cy", 2)]


NARROW = pa.schema([pa.field("id", pa.int64(), nullable=False), pa.field("amount", pa.int32())])


def narrow_orders(path, rows):
    cdf = {"delta.enableChangeDataFeed": "true"}
    write_deltalake(path, pa.Table.from_pylist(rows, schema=NARROW), configuration=cdf)
    return DeltaSource(str(path), name="orders")


def widen(path, rows):
    schema = pa.schema([NARROW.field("id"), pa.field("amount", pa.int64())])
    table = pa.Table.from_pylist(rows, schema=schema)
    write_deltalake(path, table, mode="overwrite", schema_mode="overwrite")


def pos(orders):
    return orders.filter(orders.amount > 0)


def ids(orders):
    return orders.select(orders.id)


def test_widened_column_whose_values_fit_is_read_as_before(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    node = src.pipe(pos)
    node.refresh()
    widen(src.uri, [{"id": 1, "amount": 5}, {"id": 2, "amount": 7}])
    [s] = batch(node).sources
    assert "widened amount int32→int64" in s.detail and s.mode != "recomputed"
    assert rows(node) == [(1, 5), (2, 7)]
    assert source_schema(node, "orders") == NARROW


def test_a_node_without_a_contract_is_planned_again_for_a_dropped_column(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    node = src.pipe(ids)
    node.refresh()
    only_id = pa.table({"id": pa.array([1, 2], pa.int64())})
    write_deltalake(src.uri, only_id, mode="overwrite", schema_mode="overwrite")
    [s] = batch(node).sources
    assert s.mode == "recomputed" and "dropped amount" in s.detail
    assert rows(node) == [(1,), (2,)]


def test_a_node_planned_again_overwrites_its_sink(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    node = src.pipe(ids).write(DeltaSink(str(tmp_path / "ids")))
    assert node.refresh().writes[0].mode == "created"
    only_id = pa.table({"id": pa.array([1, 2], pa.int64())})
    write_deltalake(src.uri, only_id, mode="overwrite", schema_mode="overwrite")
    # The plan reads another schema: its state replaces the old plan's.
    [w] = node.refresh().writes
    assert (w.mode, w.inserted) == ("overwrite", 2)
    assert delta_rows(str(tmp_path / "ids")) == [(1,), (2,)]


def test_incompatible_schema_change_under_a_contract_is_refused(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(paid(src))
    node.refresh()
    renamed = orders_table([(1, "ada", 5)]).rename_columns(["id", "who", "amount"])
    write_deltalake(src.uri, renamed, mode="overwrite", schema_mode="overwrite")
    with pytest.raises(SchemaError, match="contracts proved against the old schema"):
        node.refresh()
    assert node.versions == {"orders": 1} and rows(node) == [(1, "ada", 10), (2, "bob", 14)]


# -- Static inputs and resuming from a sink -----------------------------------

REGIONS = pa.table({"customer": ["ada", "bob", "cy"], "region": ["eu", "us", "eu"]})


def by_region(orders, regions):
    joined = orders.join(regions, orders.customer == regions.customer)
    return joined.select(orders.id, regions.region, orders.amount)


def job_with_lookup(tmp_path, src, regions):
    return src.pipe(by_region, regions=regions).write(DeltaSink(str(tmp_path / "by_region")))


def test_static_lookup_table_writes_exactly_once(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    regions = StaticSource(REGIONS, version=1, name="regions")
    node = job_with_lookup(tmp_path, src, regions)
    first = node.refresh().writes[0]
    assert first.mode == "created"
    assert first.contract.sources == {"orders": 1, "regions": 1}
    assert first.contract.digests == {"regions": regions.digest}
    assert node.refresh().writes[0].mode == "skipped"
    # A restarted job with the same inputs finds its commit.
    again = job_with_lookup(tmp_path, src, StaticSource(REGIONS, version=1, name="regions"))
    assert again.refresh().writes[0].mode == "skipped"
    # The source moves on: one MERGE.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    assert node.refresh().writes[0].mode == "merge"
    # A new release of the lookup table: the views reading it are recomputed.
    regions.replace(REGIONS.set_column(1, "region", pa.array(["us", "us", "us"])), version=2)
    report = node.refresh()
    [_, lookup] = report["by_region"].report.sources  # type: ignore[union-attr]
    assert (lookup.start, lookup.end, lookup.mode) == (1, 2, "recomputed")
    [written] = report.writes
    assert written.mode == "merge" and written.contract.epoch == 4
    assert (
        delta_rows(str(tmp_path / "by_region"))
        == rows(node)
        == [(1, "us", 5), (2, "us", 7), (3, "us", 1)]
    )


def test_static_table_changed_without_a_version_is_refused(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    job_with_lookup(tmp_path, src, StaticSource(REGIONS, version=1, name="regions")).refresh()
    other = REGIONS.set_column(1, "region", pa.array(["us", "us", "us"]))
    again = job_with_lookup(tmp_path, src, StaticSource(other, version=1, name="regions"))
    with pytest.raises(ValueError, match="give the changed static table a new version"):
        again.refresh()
    with pytest.raises(ValueError, match="version above 1"):
        StaticSource(REGIONS, version=1).replace(other, version=1)


def test_restarted_job_resumes_from_its_sink(tmp_path, monkeypatch):
    src, stored = job1(tmp_path)
    stored.refresh()
    uri = str(tmp_path / "big")
    # While the job is down, the source moves on.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    state = DeltaSource(uri).stored()
    assert state is not None and state.sources == {"orders": 1}
    seen = spy_on(
        monkeypatch,
        "sverify.incremental.run_plan",
        lambda con, plan, engine=None: con.arrow["orders"].num_rows,
    )
    _, again = job1(tmp_path, src)
    report = again.refresh()
    # The view is not computed: its first run is on empty inputs, for its schema.
    assert seen[0] == 0
    entry = report["big"]
    assert entry.started == f"resumed from {state.where}"
    assert entry.report is not None and entry.report.sources[0].mode == "change feed"
    assert entry.write is not None
    assert (entry.write.mode, entry.write.inserted, entry.write.deleted) == ("merge", 1, 0)
    assert delta_rows(uri) == sorted(rows(again), key=repr)
    assert rows(again) == recomputed(doubled(paid(src)), src)


def test_resume_recomputes_another_plan(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()
    other = doubled(src).write(DeltaSink(str(tmp_path / "big")))
    started = other.refresh()["big"].started
    assert started is not None and started.startswith("computed: the plan changed")
    # A sink commit that is not the last one is not resumed from.
    assert DeltaSource(src.uri).stored() is None


def test_another_plan_overwrites_the_sink(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()
    other = doubled(src).write(DeltaSink(str(tmp_path / "big")))
    assert other.refresh().writes[0].mode == "overwrite"
    assert delta_rows(str(tmp_path / "big")) == sorted(rows(other), key=repr)


def as_text(orders):
    return orders.select(orders.customer, doubled=orders.amount.cast("string"))


def constraints(uri):
    config = DeltaTable(uri).metadata().configuration
    return {k: v for k, v in config.items() if k.startswith("delta.constraints.")}


def test_another_plan_with_other_columns_replaces_the_table(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()
    uri = str(tmp_path / "big")
    assert constraints(uri) == {"delta.constraints.sverify_1": "doubled >= 0"}
    # Another plan at the same source versions: other columns, no constraint.
    other = src.pipe(as_text).write(DeltaSink(uri))
    w = other.refresh().writes[0]
    assert (w.mode, w.inserted, w.constraints) == ("overwrite", 2, {})
    assert DeltaTable(uri).schema().to_arrow().names == ["customer", "doubled"]
    assert constraints(uri) == {}
    assert delta_rows(uri) == sorted(rows(other), key=repr) == [("ada", "5"), ("bob", "7")]
    # The new plan's next state is a MERGE on its own rows.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    assert other.refresh().writes[0].mode == "merge"
    assert delta_rows(uri) == sorted(rows(other), key=repr)
    # Back to the first plan. Its constraint holds once its rows are in, so
    # the commit that adds it records the epoch, and a restarted job resumes.
    _, back = job1(tmp_path, src)
    w = back.refresh().writes[0]
    assert (w.mode, w.constraints) == ("overwrite", {"sverify_1": "doubled >= 0"})
    assert constraints(uri) == {"delta.constraints.sverify_1": "doubled >= 0"}
    _, again = job1(tmp_path, src)
    entry = again.refresh()["big"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    assert entry.write is not None and entry.write.mode == "skipped"
    assert delta_rows(uri) == sorted(rows(again), key=repr)


def test_a_constraint_of_another_writer_is_kept(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    uri = str(tmp_path / "big")
    src.pipe(as_text).write(DeltaSink(uri)).refresh()
    DeltaTable(uri).alter.add_constraint({"named": "customer IS NOT NULL"})
    _, other = job1(tmp_path, src)
    with pytest.raises(ValueError, match="constraints the view does not guarantee"):
        other.refresh()
    assert delta_rows(uri) == [("ada", "5")]


# -- Statistics: nullable columns, doubles, deletion vectors -------------------


@sv.transform(
    requires={"orders": [(_.amount >= 0) | _.amount.isnull()]},
    ensures=[(_.amount >= 0) | _.amount.isnull()],
)
def kept(orders):
    return orders.select(orders.id, orders.amount)


def test_nullable_columns_get_bounds_from_statistics(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", None), (3, "cy", 7)])
    facts = [f.condition for f in src.snapshot().facts]
    assert '"amount" IS NULL OR ("amount" >= 5 AND "amount" <= 7)' in facts
    node = kept(src)
    assert first_preconditions(node) == {
        ("orders", "((_.amount >= 0) | _.amount.isnull())"): "file stats @v1"
    }
    # A file whose amounts are all NULL adds NULL and no bound.
    write_deltalake(src.uri, orders_table([(4, "dan", None), (5, "eve", None)]), mode="append")
    report = batch(node)
    assert discharged(report.preconditions) == {
        ("orders", "((_.amount >= 0) | _.amount.isnull())"): "file stats @v2 (new files)"
    }
    assert [f.condition for f in src.changes(1).facts if "amount" in f.condition] == [
        '"amount" IS NULL'
    ]
    assert rows(node) == recomputed(node, src)


def test_double_statistics_give_a_minimum_only(tmp_path):
    schema = pa.schema(
        [pa.field("id", pa.int64(), nullable=False), pa.field("price", pa.float64())]
    )
    rows = [{"id": 1, "price": 0.5}, {"id": 2, "price": float("nan")}, {"id": 3, "price": 2.5}]
    write_deltalake(tmp_path / "t", pa.Table.from_pylist(rows, schema=schema))
    facts = [f.condition for f in DeltaSource(str(tmp_path / "t")).snapshot().facts]
    # NaN is above every double and Delta does not count NaNs: no maximum.
    assert '"price" IS NOT NULL AND "price" >= 0.5' in facts

    @sv.transform(requires={"t": [_.price >= 0.0]}, ensures=[])
    def priced(t):
        return t.select(t.id)

    found = first_preconditions(priced(DeltaSource(str(tmp_path / "t"))))
    assert found == {("t", "(_.price >= 0.0)"): "file stats @v0"}

    # A maximum of 2.5 would have "proved" this, but the NaN row violates it.
    @sv.transform(requires={"t": [_.price <= 100.0]}, ensures=[])
    def capped(t):
        return t.select(t.id)

    with pytest.raises(PreconditionError, match="1 row"):
        capped(DeltaSource(str(tmp_path / "t"))).refresh()


FIXTURE_DV = Path(__file__).parent / "data" / "delta_deletion_vectors"
"""Written by Spark 4.0.1 with Delta 4.0.0 (delta-rs cannot write deletion
vectors): a table with CDF and deletion vectors, `(1, ada, 5), (2, bob, NULL),
(3, cy, 1), (4, dan, 100)` inserted at v1 and ids 2 and 4 deleted at v2, which
adds a deletion vector to the one data file."""


def test_deletion_vectors(tmp_path, monkeypatch):
    shutil.copytree(FIXTURE_DV, tmp_path / "dv")
    src = DeltaSource(str(tmp_path / "dv"), name="orders")
    dt = src.table()
    [dv] = pa.table(dt.deletion_vectors()).to_pylist()
    assert dv["selection_vector"] == [True, False, True, False]
    # The statistics are those of all four physical rows (Delta writes
    # tightBounds: false): a NULL and 100 that are deleted. They still bound
    # the two live rows; the row count is left out.
    [stats] = file_stats(dt).values()
    assert stats["amount"] == ColumnStats(1, 100, 1, None)
    snap = src.snapshot()
    assert sorted(arrow_rows(snap.table)) == [(1, "ada", 5), (3, "cy", 1)]
    assert '"amount" IS NULL OR ("amount" >= 1 AND "amount" <= 100)' in [
        f.condition for f in snap.facts
    ]
    # Following the feed across the deletion-vector commit, from a job that
    # last ran at v1.
    node = kept(src)
    monkeypatch.setattr(src, "latest", lambda: 1)
    node.refresh()
    assert rows(node) == [(1, 5), (2, None), (3, 1), (4, 100)]
    monkeypatch.undo()
    [s] = batch(node, audit=True).sources
    assert (s.mode, s.inserts, s.deletes) == ("change feed", 0, 2)
    assert rows(node) == [(1, 5), (3, 1)]


# -- Pruning files with a proved criterion -------------------------------------


def test_where_skips_files_the_reader_would_scan(tmp_path):
    path = tmp_path / "orders"
    make_orders(path, [(1, "ada", 5), (2, "bob", 50)])
    write_deltalake(path, orders_table([(3, "cy", 60), (4, "dan", 80)]), mode="append")
    src = DeltaSource(str(path), where="amount * 2 > 100")
    snap = src.snapshot()
    # Lean proves amount * 2 > 100 is not TRUE in the file with amounts in [5, 50].
    assert len(src.skipped) == 1
    assert sorted(arrow_rows(snap.table)) == [(3, "cy", 60), (4, "dan", 80)]
    assert ("amount * 2 > 100", "source filter") in [(f.condition, f.source) for f in snap.facts]
    # pyarrow's statistics pushdown keeps both files for this filter.
    dataset = DeltaTable(str(path)).to_pyarrow_dataset()
    expr = pc.field("amount") * 2 > 100
    assert len([f for f in dataset.get_fragments() if f.subset(filter=expr).row_groups]) == 2
    # As a node's source, changes are filtered the same way.
    node = src.pipe(lambda o: o.select(o.id, o.amount))
    node.refresh()
    write_deltalake(path, orders_table([(5, "eve", 10), (6, "fay", 70)]), mode="append")
    DeltaTable(str(path)).delete("id = 3")
    node.refresh(audit=True)
    assert rows(node) == [(4, 80), (6, 70)]


# -- Pipeline internals that nodes cannot reach --------------------------------
# A node's stage is a `Pipeline` of one view whose sources it pins itself, so
# these drive `Pipeline` directly: its guard against applying changes to a
# source, a sink attached to a view without sources, resuming at another
# version than the sink stored, and replanning several views at once.


def attached(sink, view):
    """A sink writing `view` (what `node.write(sink)` sets up)."""
    sink._attach(view)
    return sink


def test_source_tables_change_only_through_refresh(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = Pipeline(sv.connect())
    pipe.view("big", doubled(paid(pipe.source("orders", src))))
    with pytest.raises(ValueError, match="refresh"):
        pipe.apply({"orders": sv.Changes(inserts=[(2, "bob", 1)])})


def test_sink_needs_source_versions(tmp_path):
    con = sv.connect()
    create_table(con, "orders", ibis.schema({"id": "int64"}), [(1,)])
    view = IncrementalView(con, con.table("orders"), "v")
    with pytest.raises(ValueError, match="without a source"):
        attached(DeltaSink(str(tmp_path / "v")), view)._commit()


def test_widened_column_that_does_not_fit_replans_the_views(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    pipe = Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    pos = pipe.view("pos", orders.filter(orders.amount > 0))
    top = pipe.view("top", pos.table.select(pos.table.amount))
    widen(src.uri, [{"id": 1, "amount": 5}, {"id": 2, "amount": 2**40}])
    [s] = pipe.refresh().sources
    assert s.mode == "recomputed"
    assert "widened amount int32→int64" in s.detail
    assert "views planned again and recomputed: pos, top" in s.detail
    assert pos.rows() == pos.recompute() == [(1, 5), (2, 2**40)]
    assert sorted(top.rows()) == [(5,), (2**40,)]
    assert pos.schema.field("amount").type == pa.int64()
    assert pipe.versions == {"orders": 1}
    # Incremental again from the new schema.
    write_deltalake(src.uri, pa.table({"id": [3], "amount": [-1]}).cast(pos.schema), mode="append")
    assert pipe.refresh().sources[0].mode == "change feed"
    assert top.rows() == top.recompute()


def test_dropped_column_read_by_a_view_changes_nothing(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    pipe = Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    ids = pipe.view("ids", orders.select(orders.id))
    pos = pipe.view("pos", orders.filter(orders.amount > 0))
    only_id = pa.table({"id": pa.array([1, 2], pa.int64())})
    write_deltalake(src.uri, only_id, mode="overwrite", schema_mode="overwrite")
    with pytest.raises(Exception, match="amount"):
        pipe.refresh()
    assert pipe.versions == {"orders": 0}
    assert ids.rows() == [(1,)] and pos.rows() == [(1, 5)]
    assert pipe.con.arrow["orders"].schema == NARROW


def test_dropped_column_no_view_reads_replans(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    pipe = Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    ids = pipe.view("ids", orders.select(orders.id))
    only_id = pa.table({"id": pa.array([1, 2], pa.int64())})
    write_deltalake(src.uri, only_id, mode="overwrite", schema_mode="overwrite")
    [s] = pipe.refresh().sources
    assert s.mode == "recomputed" and "dropped amount" in s.detail
    assert ids.rows() == [(1,), (2,)]


def test_resume_at_another_version_recomputes(tmp_path):
    src, stored = job1(tmp_path)
    stored.refresh()
    state = DeltaSource(str(tmp_path / "big")).stored()
    assert state is not None
    # The source at another version than the stored state.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    pipe = Pipeline(sv.connect())
    late = pipe.view("big", doubled(paid(pipe.source("orders", src))), resume=state)
    assert late.resumed is not None
    assert "stored from orders@v1, the pipeline holds orders@v2" in late.resumed
    assert late.rows() == late.recompute() and len(late.rows()) == 3
