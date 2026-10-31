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
from sverify.contracts import ON_DATA, SCHEMA
from sverify.engine import Engine
from sverify.incremental import AuditError, SchemaError, arrow_rows
from sverify.io import ColumnStats, DeltaSink, DeltaSource
from sverify.io.delta import file_stats

SCHEMA_ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64()),
    ]
)


def orders_table(rows):
    return pa.Table.from_pylist(
        [dict(zip(SCHEMA_ORDERS.names, r, strict=True)) for r in rows], schema=SCHEMA_ORDERS
    )


def make_orders(path, rows, *, cdf=True, constraints=None):
    DeltaTable.create(
        path,
        SCHEMA_ORDERS,
        configuration={"delta.enableChangeDataFeed": "true"} if cdf else None,
    )
    dt = DeltaTable(path)
    if constraints:
        dt.alter.add_constraint(constraints)
    write_deltalake(path, orders_table(rows), mode="append")
    return DeltaSource(path)


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


def sources(report):
    return {(p.table, p.condition): p.source for p in report}


# -- Step 1: the Change Data Feed as a change source --------------------------


@pytest.mark.parametrize("engine", ["datafusion", "polars", "duckdb"])
def test_refresh_applies_cdf(tmp_path, engine: Engine):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect(), engine)
    orders = pipe.source("orders", src)
    big = pipe.view("big", doubled(paid(orders)))
    assert big.versions == {"orders": 1}
    dt = DeltaTable(src.uri)
    write_deltalake(dt, orders_table([(3, "cy", 1)]), mode="append")
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    dt.delete("id = 2")
    report = pipe.refresh()
    assert big.rows() == [(1, "ada", 12), (3, "cy", 2)]
    assert big.rows() == big.recompute()
    assert big.versions == {"orders": 4}
    [s] = report.sources
    assert (s.start, s.end, s.mode) == (1, 4, "change feed")
    assert (s.inserts, s.deletes) == (2, 2)
    assert "Δ trusted as coming from Delta CDF v1→v4" in str(report)
    assert "view big: orders@v4" in str(report)


def test_refresh_without_new_version_is_a_no_op(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    pipe.view("big", doubled(paid(pipe.source("orders", src))))
    report = pipe.refresh()
    assert str(report.sources[0]) == "orders@v1: no new version"


def test_a_failed_refresh_changes_nothing_and_a_retry_applies_once(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    # A duplicate key: Delta does not enforce keys, the pipeline does.
    write_deltalake(src.uri, orders_table([(1, "eve", 3)]), mode="append")
    with pytest.raises(sv.PreconditionError, match="unique"):
        pipe.refresh()
    assert pipe.versions == {"orders": 1}
    assert big.rows() == [(1, "ada", 10)]
    DeltaTable(src.uri).delete("customer = 'eve'")
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh()
    # The CDF from v1 holds eve's insert and delete; they cancel out.
    assert (report.sources[0].inserts, report.sources[0].deletes) == (1, 0)
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]
    assert pipe.refresh().sources[0].mode == "unchanged"
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]


def test_no_cdf_recomputes_and_says_so(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)], cdf=False)
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh()
    [s] = report.sources
    assert s.mode == "recomputed"
    assert report.recomputed == ["orders"]
    assert "Delta CDF v1→v2 unavailable" in s.detail
    assert "recomputed from scratch" in str(report)
    assert big.rows() == [(1, "ada", 10), (2, "bob", 2)]


def test_vacuumed_history_recomputes(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="overwrite")
    DeltaTable(src.uri).vacuum(retention_hours=0, enforce_retention_duration=False, dry_run=False)
    report = pipe.refresh()
    assert report.sources[0].mode == "recomputed"
    assert big.rows() == [(3, "cy", 2)]


def test_audit_compares_with_the_snapshot(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    report = pipe.refresh(audit=True)
    assert report.audited and "audit:" in str(report)
    assert big.rows() == big.recompute()


def test_audit_catches_a_wrong_feed(tmp_path, monkeypatch):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    write_deltalake(src.uri, orders_table([(2, "bob", 1)]), mode="append")
    real = DeltaSource.changes

    def lossy(self, since):
        batch = real(self, since)
        batch.changes = sv.Changes()
        return batch

    monkeypatch.setattr(DeltaSource, "changes", lossy)
    with pytest.raises(AuditError, match="nothing was applied"):
        pipe.refresh(audit=True)
    assert pipe.versions == {"orders": 1} and big.rows() == [(1, "ada", 10)]


def test_audit_catches_a_wrong_view_before_the_commit(tmp_path, monkeypatch):
    src, pipe, big, sink = job1(tmp_path)
    sink.write()
    sink_version = DeltaTable(sink.uri).version()
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    real = sv.IncrementalView._delta

    def wrong(self, deltas):
        delta, examples = real(self, deltas)
        delta = Counter({k: 2 * n for k, n in delta.items()})
        return delta, examples

    monkeypatch.setattr(sv.IncrementalView, "_delta", wrong)
    with pytest.raises(AuditError, match="big differs from its recomputation; nothing was applied"):
        pipe.refresh(audit=True)
    # State, versions and sink are as before the refresh.
    assert pipe.versions == {"orders": 1}
    assert big.rows() == [(1, "ada", 10), (2, "bob", 14)]
    assert pipe.con.arrow["orders"].num_rows == 2
    assert sink.write().mode == "skipped"
    assert DeltaTable(sink.uri).version() == sink_version
    monkeypatch.undo()
    pipe.refresh(audit=True)
    assert big.rows() == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]


def test_source_tables_change_only_through_refresh(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    pipe.view("big", doubled(paid(pipe.source("orders", src))))
    with pytest.raises(ValueError, match="refresh"):
        pipe.apply({"orders": sv.Changes(inserts=[(2, "bob", 1)])})


def test_views_over_views_record_source_versions(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    top = pipe.view("top", big.table.filter(big.table.doubled > 4))
    write_deltalake(src.uri, orders_table([(2, "bob", 9)]), mode="append")
    report = pipe.refresh()
    assert top.versions == {"orders": 2}
    assert report.versions == {"big": {"orders": 2}, "top": {"orders": 2}}
    assert top.rows() == [(1, "ada", 10), (2, "bob", 18)]


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
    pipe = sv.Pipeline(sv.connect())
    ev = pipe.source("ev", DeltaSource(str(tmp_path / "ev")))
    view = pipe.view("v", ev.filter(ev.k > 0))
    write_deltalake(
        tmp_path / "ev", pa.Table.from_pylist([{"k": 2, "ts": None}], schema=schema), mode="append"
    )
    pipe.refresh()
    assert view.rows() == view.recompute() == [(1, t1), (2, None)]


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


def test_preconditions_come_from_metadata(tmp_path):
    src = make_orders(
        tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)], constraints={"pos": "amount >= 0"}
    )
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    checked(orders)
    assert sources(checked.last_preconditions) == {
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
    view = pipe.view("v", checked(orders))
    assert sources(pipe.preconditions)[("orders", "(_.amount <= 100)")] == "file stats @v2"
    assert "orders: (_.amount <= 100) (file stats @v2)" in [str(p) for p in pipe.preconditions]
    # A batch is discharged from the statistics of the files it added.
    write_deltalake(src.uri, orders_table([(3, "cy", 50)]), mode="append")
    report = pipe.refresh()
    found = sources(report.preconditions)
    assert found[("orders", "(_.amount <= 100)")] == "file stats @v3 (new files)"
    assert found[("orders", "(_.amount >= 0)")] == "Delta constraint"
    assert found[("orders", "unique(id)")] == ON_DATA
    assert "requires orders: (_.amount <= 100) (file stats @v3 (new files))" in str(report)
    # Statistics that do not bound the batch leave it to the data.
    write_deltalake(src.uri, orders_table([(4, "dan", 500)]), mode="append")
    with pytest.raises(sv.PreconditionError, match=r"inserted row\(s\) of orders violate"):
        pipe.refresh()
    assert view.versions == {"orders": 3}


def test_missing_statistics_are_unknown(tmp_path):
    path = tmp_path / "orders"
    write_deltalake(
        path,
        orders_table([(1, "ada", 5)]),
        configuration={"delta.dataSkippingNumIndexedCols": "0"},
    )
    checked(sv.Pipeline(sv.connect()).source("orders", DeltaSource(str(path))))
    found = sources(checked.last_preconditions)
    assert found[("orders", "(_.amount <= 100)")] == ON_DATA
    assert found[("orders", "_.id.notnull()")] == SCHEMA


def test_one_file_without_statistics_makes_a_column_unknown(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    DeltaTable(src.uri).alter.set_table_properties({"delta.dataSkippingNumIndexedCols": "0"})
    write_deltalake(src.uri, orders_table([(2, "bob", 6)]), mode="append")
    checked(sv.Pipeline(sv.connect()).source("orders", src))
    assert sources(checked.last_preconditions)[("orders", "(_.amount <= 100)")] == ON_DATA


def test_truncated_timestamp_statistics_are_widened(tmp_path):
    schema = pa.schema([pa.field("ts", pa.timestamp("us"), nullable=False)])
    t1 = datetime(2024, 1, 1, 0, 0, 0, 123456)
    write_deltalake(tmp_path / "ev", pa.Table.from_pylist([{"ts": t1}], schema=schema))
    ev = sv.Pipeline(sv.connect()).source("ev", DeltaSource(str(tmp_path / "ev")))

    @sv.transform(
        requires={
            "t": [
                _.ts >= datetime(2024, 1, 1),
                _.ts <= datetime(2024, 1, 1, 0, 0, 0, 124000),
                _.ts <= t1,
            ]
        }
    )
    def f(t):
        return t

    f(ev)
    # Delta keeps the maximum as ...00.123000; the true maximum is up to
    # 999 µs later, so only the weaker bound follows from the statistics.
    assert [p.source for p in f.last_preconditions] == ["file stats @v0", "file stats @v0", ON_DATA]


def test_tables_without_metadata_are_checked_on_data():
    con = sv.connect()
    sv.create_table(
        con,
        "orders",
        ibis.schema({"id": "!int64", "customer": "string", "amount": "int64"}),
        [(1, "ada", 5)],
    )
    checked(con.table("orders"))
    assert set(sources(checked.last_preconditions).values()) == {ON_DATA}


# -- Step 3: a Delta sink that carries the contract ---------------------------


def delta_rows(uri):
    t = pa.table(DeltaTable(uri).to_pyarrow_table())
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def job1(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    return src, pipe, big, DeltaSink(str(tmp_path / "big"), big)


def test_sink_writes_contract_and_changes(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    first = sink.write()
    assert first.mode == "created"
    assert delta_rows(sink.uri) == big.rows()
    out = DeltaTable(sink.uri)
    fields = {f.name: f.nullable for f in pa.schema(out.schema().to_arrow())}
    assert fields == {"id": True, "customer": True, "doubled": False}
    assert out.metadata().configuration["delta.constraints.sverify_1"] == "doubled >= 0"
    assert out.transaction_version("sverify:big") == 1
    contract = DeltaSource(sink.uri).contract()
    assert contract is not None
    assert contract.sources == {"orders": 1} and contract.unique == [["id"]]
    assert contract.plan == first.contract.plan and len(contract.plan) == 64
    # A change to the source becomes one MERGE commit on the sink.
    dt = DeltaTable(src.uri)
    dt.update(updates={"amount": "amount + 1"}, predicate="id = 1")
    write_deltalake(dt, orders_table([(3, "cy", 0)]), mode="append")
    pipe.refresh()
    before = DeltaTable(sink.uri).version()
    second = sink.write()
    assert second.mode == "merge" and second.version == before + 1
    assert (second.inserted, second.deleted) == (2, 1)
    assert delta_rows(sink.uri) == big.rows() == [(1, "ada", 12), (2, "bob", 14), (3, "cy", 0)]
    later = DeltaSource(sink.uri).contract()
    assert later is not None and later.sources == {"orders": 3}
    assert DeltaTable(sink.uri).transaction_version("sverify:big") == 3


def test_sink_writes_exactly_once(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    sink.write()
    version = DeltaTable(sink.uri).version()
    assert sink.write().mode == "skipped"
    # A restarted job at the same source versions finds its commit.
    _, _, _, again = job1_restart(src, tmp_path)
    assert again.write().mode == "skipped"
    assert DeltaTable(sink.uri).version() == version
    # At a later version, a new sink replaces the table's contents.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    _, _, big2, later = job1_restart(src, tmp_path)
    assert later.write().mode == "overwrite"
    assert delta_rows(sink.uri) == big2.rows()


def job1_restart(src, tmp_path):
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(paid(pipe.source("orders", src))))
    return src, pipe, big, DeltaSink(str(tmp_path / "big"), big)


def test_sink_keeps_multiplicities_and_nulls(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "ada", 5), (3, None, 1)])
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    names = pipe.view("names", orders.select(orders.customer, orders.amount))
    sink = DeltaSink(str(tmp_path / "names"), names)
    sink.write()
    DeltaTable(src.uri).delete("id = 1")
    write_deltalake(src.uri, orders_table([(4, None, 1), (5, "ada", 5)]), mode="append")
    pipe.refresh()
    sink.write()
    assert delta_rows(sink.uri) == sorted(names.rows(), key=repr)
    assert len(names.rows()) == 4


def test_contracts_travel_between_jobs(tmp_path):
    src, pipe, big, sink = job1(tmp_path)
    sink.write()

    @sv.transform(
        requires={"t": [_.doubled >= 0, _.doubled.notnull(), sv.unique("id")]},
        ensures=[_.half >= 0],
    )
    def halved(t):
        return t.select(t.id, half=t.doubled // 2)

    # Job 2 reads job 1's output; its preconditions come from job 1's contract.
    pipe2 = sv.Pipeline(sv.connect())
    big_in = pipe2.source("big", DeltaSource(sink.uri))
    halves = pipe2.view("halves", halved(big_in))
    assert sources(pipe2.preconditions) == {
        ("big", "(_.doubled >= 0)"): "Delta constraint",
        ("big", "_.doubled.notnull()"): SCHEMA,
        ("big", "unique(id)"): ON_DATA,
    }
    # Job 1 moves on; job 2 follows the sink's own change feed.
    write_deltalake(src.uri, orders_table([(3, "cy", 4)]), mode="append")
    pipe.refresh()
    sink.write()
    report = pipe2.refresh()
    assert report.sources[0].mode == "change feed"
    assert halves.rows() == halves.recompute() == [(1, 5), (2, 7), (3, 4)]
    assert sources(report.preconditions)[("big", "(_.doubled >= 0)")] == "Delta constraint"


def test_sink_needs_source_versions(tmp_path):
    con = sv.connect()
    sv.create_table(con, "orders", ibis.schema({"id": "int64"}), [(1,)])
    view = sv.IncrementalView(con, con.table("orders"), "v")
    with pytest.raises(ValueError, match="without a source"):
        DeltaSink(str(tmp_path / "v"), view).write()


# -- Schema evolution ---------------------------------------------------------


def test_added_column_is_left_out(tmp_path):
    src, pipe, big, _ = job1(tmp_path)
    wide = orders_table([(3, "cy", 1)]).append_column("note", pa.array(["new"]))
    write_deltalake(src.uri, wide, mode="append", schema_mode="merge")
    report = pipe.refresh()
    [s] = report.sources
    assert "schema: added note, read in the old schema" in s.detail
    assert big.rows() == big.recompute() == [(1, "ada", 10), (2, "bob", 14), (3, "cy", 2)]
    assert pipe.con.arrow["orders"].schema == SCHEMA_ORDERS
    # The next batch is read the same way.
    write_deltalake(src.uri, wide.set_column(0, "id", pa.array([4])), mode="append")
    assert pipe.refresh().sources[0].mode == "change feed"
    assert big.rows() == big.recompute()


NARROW = pa.schema([pa.field("id", pa.int64(), nullable=False), pa.field("amount", pa.int32())])


def narrow_orders(path, rows):
    cdf = {"delta.enableChangeDataFeed": "true"}
    write_deltalake(path, pa.Table.from_pylist(rows, schema=NARROW), configuration=cdf)
    return DeltaSource(str(path))


def widen(path, rows):
    schema = pa.schema([NARROW.field("id"), pa.field("amount", pa.int64())])
    table = pa.Table.from_pylist(rows, schema=schema)
    write_deltalake(path, table, mode="overwrite", schema_mode="overwrite")


def test_widened_column_whose_values_fit_is_read_as_before(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    pos = pipe.view("pos", orders.filter(orders.amount > 0))
    widen(src.uri, [{"id": 1, "amount": 5}, {"id": 2, "amount": 7}])
    [s] = pipe.refresh().sources
    assert "widened amount int32→int64" in s.detail and s.mode != "recomputed"
    assert pos.rows() == [(1, 5), (2, 7)]
    assert pipe.con.arrow["orders"].schema == NARROW


def test_widened_column_that_does_not_fit_replans_the_views(tmp_path):
    src = narrow_orders(tmp_path / "o", [{"id": 1, "amount": 5}])
    pipe = sv.Pipeline(sv.connect())
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
    pipe = sv.Pipeline(sv.connect())
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
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    ids = pipe.view("ids", orders.select(orders.id))
    only_id = pa.table({"id": pa.array([1, 2], pa.int64())})
    write_deltalake(src.uri, only_id, mode="overwrite", schema_mode="overwrite")
    [s] = pipe.refresh().sources
    assert s.mode == "recomputed" and "dropped amount" in s.detail
    assert ids.rows() == [(1,), (2,)]


def test_incompatible_schema_change_under_a_contract_is_refused(tmp_path):
    src, pipe, big, _ = job1(tmp_path)
    renamed = orders_table([(1, "ada", 5)]).rename_columns(["id", "who", "amount"])
    write_deltalake(src.uri, renamed, mode="overwrite", schema_mode="overwrite")
    with pytest.raises(SchemaError, match="contracts proved against the old schema"):
        pipe.refresh()
    assert pipe.versions == {"orders": 1} and big.rows() == [(1, "ada", 10), (2, "bob", 14)]


# -- Static inputs and resuming from a sink -----------------------------------

REGIONS = pa.table({"customer": ["ada", "bob", "cy"], "region": ["eu", "us", "eu"]})


def job_with_lookup(tmp_path, src, regions):
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    lookup = pipe.source("regions", regions)
    joined = orders.join(lookup, orders.customer == lookup.customer)
    view = pipe.view("by_region", joined.select(orders.id, lookup.region, orders.amount))
    return pipe, view, DeltaSink(str(tmp_path / "by_region"), view)


def test_static_lookup_table_writes_exactly_once(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    regions = sv.StaticSource(REGIONS, version=1)
    pipe, view, sink = job_with_lookup(tmp_path, src, regions)
    first = sink.write()
    assert first.mode == "created"
    assert first.contract.sources == {"orders": 1, "regions": 1}
    assert first.contract.digests == {"regions": regions.digest}
    assert sink.write().mode == "skipped"
    # A restarted job with the same inputs finds its commit.
    _, _, again = job_with_lookup(tmp_path, src, sv.StaticSource(REGIONS, version=1))
    assert again.write().mode == "skipped"
    # The source moves on: one MERGE.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    pipe.refresh()
    assert sink.write().mode == "merge"
    # A new release of the lookup table: the views reading it are recomputed.
    regions.replace(REGIONS.set_column(1, "region", pa.array(["us", "us", "us"])), version=2)
    [_, lookup] = pipe.refresh().sources
    assert (lookup.start, lookup.end, lookup.mode) == (1, 2, "recomputed")
    written = sink.write()
    assert written.mode == "merge" and written.contract.epoch == 4
    assert delta_rows(sink.uri) == view.rows() == [(1, "us", 5), (2, "us", 7), (3, "us", 1)]


def test_static_table_changed_without_a_version_is_refused(tmp_path):
    src = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    _, _, sink = job_with_lookup(tmp_path, src, sv.StaticSource(REGIONS, version=1))
    sink.write()
    other = REGIONS.set_column(1, "region", pa.array(["us", "us", "us"]))
    _, _, again = job_with_lookup(tmp_path, src, sv.StaticSource(other, version=1))
    with pytest.raises(ValueError, match="give the changed static table a new version"):
        again.write()
    with pytest.raises(ValueError, match="version above 1"):
        sv.StaticSource(REGIONS, version=1).replace(other, version=1)


def test_restarted_pipeline_resumes_from_its_sink(tmp_path, monkeypatch):
    src, _, big, sink = job1(tmp_path)
    sink.write()
    # While the job is down, the source moves on.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    stored = DeltaSource(sink.uri).stored()
    assert stored is not None and stored.sources == {"orders": 1}
    import sverify.incremental as inc

    real = inc.run_plan
    rows_seen = []

    def spy(con, plan, engine=None):
        rows_seen.append(con.arrow["orders"].num_rows)
        return real(con, plan, engine)

    monkeypatch.setattr(inc, "run_plan", spy)
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src, version=stored.sources["orders"])
    big2 = pipe.view("big", doubled(paid(orders)), resume=stored)
    # The view is not computed: the only run is on empty inputs, for its schema.
    assert rows_seen == [0]
    assert big2.resumed == f"resumed from {sink.uri}@v{DeltaTable(sink.uri).version()}"
    assert big2.rows() == big.rows() and big2.schema == big.schema
    sink2 = DeltaSink(sink.uri, big2)
    assert pipe.refresh().sources[0].mode == "change feed"
    written = sink2.write()
    assert (written.mode, written.inserted, written.deleted) == ("merge", 1, 0)
    assert delta_rows(sink.uri) == big2.rows() == big2.recompute()


def test_resume_recomputes_on_a_mismatch(tmp_path):
    src, _, _, sink = job1(tmp_path)
    sink.write()
    stored = DeltaSource(sink.uri).stored()
    assert stored is not None
    # Another plan.
    pipe = sv.Pipeline(sv.connect())
    other = pipe.view("big", doubled(pipe.source("orders", src)), resume=stored)
    assert other.resumed is not None and other.resumed.startswith("computed: the plan changed")
    # The source at another version than the stored state.
    write_deltalake(src.uri, orders_table([(3, "cy", 1)]), mode="append")
    pipe = sv.Pipeline(sv.connect())
    late = pipe.view("big", doubled(paid(pipe.source("orders", src))), resume=stored)
    assert late.resumed is not None
    assert "stored from orders@v1, the pipeline holds orders@v2" in late.resumed
    assert late.rows() == late.recompute() and len(late.rows()) == 3
    # A sink commit that is not the last one is not resumed from.
    assert DeltaSource(src.uri).stored() is None


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
    pipe = sv.Pipeline(sv.connect())
    view = pipe.view("kept", kept(pipe.source("orders", src)))
    assert sources(pipe.preconditions) == {
        ("orders", "((_.amount >= 0) | _.amount.isnull())"): "file stats @v1"
    }
    # A file whose amounts are all NULL adds NULL and no bound.
    write_deltalake(src.uri, orders_table([(4, "dan", None), (5, "eve", None)]), mode="append")
    report = pipe.refresh()
    assert sources(report.preconditions) == {
        ("orders", "((_.amount >= 0) | _.amount.isnull())"): "file stats @v2 (new files)"
    }
    assert [f.condition for f in src.changes(1).facts if "amount" in f.condition] == [
        '"amount" IS NULL'
    ]
    assert view.rows() == view.recompute()


def test_double_statistics_give_a_minimum_only(tmp_path):
    schema = pa.schema(
        [pa.field("id", pa.int64(), nullable=False), pa.field("price", pa.float64())]
    )
    rows = [{"id": 1, "price": 0.5}, {"id": 2, "price": float("nan")}, {"id": 3, "price": 2.5}]
    write_deltalake(tmp_path / "p", pa.Table.from_pylist(rows, schema=schema))
    facts = [f.condition for f in DeltaSource(str(tmp_path / "p")).snapshot().facts]
    # NaN is above every double and Delta does not count NaNs: no maximum.
    assert '"price" IS NOT NULL AND "price" >= 0.5' in facts

    @sv.transform(requires={"t": [_.price >= 0.0]}, ensures=[])
    def priced(t):
        return t.select(t.id)

    pipe = sv.Pipeline(sv.connect())
    pipe.view("ids", priced(pipe.source("t", DeltaSource(str(tmp_path / "p")))))
    assert sources(pipe.preconditions) == {("t", "(_.price >= 0.0)"): "file stats @v0"}

    # A maximum of 2.5 would have "proved" this, but the NaN row violates it.
    @sv.transform(requires={"t": [_.price <= 100.0]}, ensures=[])
    def capped(t):
        return t.select(t.id)

    pipe = sv.Pipeline(sv.connect())
    with pytest.raises(sv.PreconditionError, match="1 row"):
        pipe.view("ids", capped(pipe.source("t", DeltaSource(str(tmp_path / "p")))))


FIXTURE_DV = Path(__file__).parent / "data" / "delta_deletion_vectors"
"""Written by Spark 4.0.1 with Delta 4.0.0 (delta-rs cannot write deletion
vectors): a table with CDF and deletion vectors, `(1, ada, 5), (2, bob, NULL),
(3, cy, 1), (4, dan, 100)` inserted at v1 and ids 2 and 4 deleted at v2, which
adds a deletion vector to the one data file."""


def test_deletion_vectors(tmp_path):
    shutil.copytree(FIXTURE_DV, tmp_path / "dv")
    src = DeltaSource(str(tmp_path / "dv"))
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
    # Following the feed across the deletion-vector commit.
    pipe = sv.Pipeline(sv.connect())
    view = pipe.view("kept", kept(pipe.source("orders", src, version=1)))
    assert sorted(view.rows()) == [(1, 5), (2, None), (3, 1), (4, 100)]
    [s] = pipe.refresh(audit=True).sources
    assert (s.mode, s.inserts, s.deletes) == ("change feed", 0, 2)
    assert sorted(view.rows()) == [(1, 5), (3, 1)]


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
    # As a pipeline source, changes are filtered the same way.
    pipe = sv.Pipeline(sv.connect())
    orders = pipe.source("orders", src)
    view = pipe.view("ids", orders.select(orders.id, orders.amount))
    write_deltalake(path, orders_table([(5, "eve", 10), (6, "fay", 70)]), mode="append")
    DeltaTable(str(path)).delete("id = 3")
    pipe.refresh(audit=True)
    assert sorted(view.rows()) == [(4, 80), (6, 70)]
