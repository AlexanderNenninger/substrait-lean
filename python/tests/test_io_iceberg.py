"""Iceberg tables (pyiceberg, SQLite catalog in a temporary directory) as
change sources, sources of preconditions and sinks."""

import warnings
from datetime import datetime

import pyarrow as pa
import pytest
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog
from pyiceberg.table.snapshots import Operation

import sverify as sv
from _pipelines import batch, discharged, recomputed, rows
from sverify.contracts import ON_DATA, SCHEMA
from sverify.errors import PreconditionError
from sverify.incremental import snapshot_diff
from sverify.io import IcebergSink, IcebergSource
from sverify.io._common import ColumnStats, stats_facts
from sverify.io.iceberg import CONTRACT

SCHEMA_ORDERS = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("customer", pa.string()),
        pa.field("amount", pa.int64()),
        pa.field("ts", pa.timestamp("us")),
    ]
)
T0 = datetime(2024, 1, 1, 0, 0, 0, 123456)


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    return cat


def rows_table(rows):
    return pa.Table.from_pylist(
        [dict(zip(SCHEMA_ORDERS.names, (*r, T0), strict=True)) for r in rows], schema=SCHEMA_ORDERS
    )


def make_orders(catalog, rows):
    t = catalog.create_table("db.orders", schema=SCHEMA_ORDERS)
    t.append(rows_table(rows))
    return IcebergSource(catalog, "db.orders")


@sv.transform(
    requires={
        "orders": [
            _.id.notnull(),
            _.amount >= 0,
            _.ts >= datetime(2024, 1, 1),
            _.customer != "eve",
            sv.unique("id"),
        ]
    },
    ensures=[_.doubled >= 0, _.doubled.notnull(), sv.unique("id")],
)
def doubled(orders):
    return orders.select(orders.id, orders.customer, doubled=orders.amount * 2)


def test_appends_are_a_change_feed(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(src)
    first = node.refresh()["doubled"]
    assert node.versions == {"orders": 1}
    assert discharged(first.preconditions) == {
        ("orders", "_.id.notnull()"): SCHEMA,
        ("orders", "(_.amount >= 0)"): "file stats @v1",
        ("orders", f"(_.ts >= {datetime(2024, 1, 1)!r})"): "file stats @v1",
        ("orders", "(_.customer != 'eve')"): ON_DATA,
        ("orders", "unique(id)"): ON_DATA,
    }
    src.table().append(rows_table([(3, "cy", 1)]))
    src.table().append(rows_table([(4, "dan", 2)]))
    report = batch(node)
    [s] = report.sources
    assert (s.start, s.end, s.mode, s.inserts) == (1, 3, "change feed", 2)
    assert "Δ trusted as the files Iceberg appends v1→v3 added" in str(report)
    assert discharged(report.preconditions)[("orders", "(_.amount >= 0)")] == (
        "file stats @v3 (new files)"
    )
    assert rows(node) == recomputed(node, src)
    assert node.versions == {"orders": 3}


def test_row_level_deletes_fall_back_to_a_snapshot_diff(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    node = doubled(src)
    node.refresh()
    src.table().delete("id = 1")
    src.table().append(rows_table([(3, "cy", 1)]))
    [s] = batch(node).sources
    assert s.mode == "snapshot diff"
    assert "not append-only" in s.detail and "only the snapshots are trusted" in s.detail
    # The delete rewrote the first file: it and the appended file are read.
    assert "on the 1 + 2 data file(s) that changed" in s.detail
    assert rows(node) == recomputed(node, src) == [(2, "bob", 14), (3, "cy", 2)]


def test_iceberg_batch_violations_are_caught(catalog):
    src = make_orders(catalog, [(1, "ada", 5)])
    node = doubled(src)
    node.refresh()
    src.table().append(rows_table([(2, "eve", 1)]))
    with pytest.raises(PreconditionError, match="customer"):
        node.refresh()
    assert node.versions == {"orders": 1} and rows(node) == [(1, "ada", 10)]


def test_iceberg_sink_carries_the_contract(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    big = doubled(src).write(IcebergSink(catalog, "db.big"))
    assert big.refresh().writes[0].mode == "created"
    out = catalog.load_table("db.big")
    assert {f.name: f.required for f in out.schema().fields} == {
        "id": False,
        "customer": False,
        "doubled": True,
    }
    contract = IcebergSource(catalog, "db.big").contract()
    assert contract is not None and contract.checks == {"sverify_1": "doubled >= 0"}
    assert out.current_snapshot().summary.get("sverify.epoch") == "1"
    assert big.refresh().writes[0].mode == "skipped"
    # Inserts only: an append. Then a deletion: position deletes.
    src.table().append(rows_table([(3, "cy", 1)]))
    assert big.refresh().writes[0].mode == "append"
    src.table().delete("id = 2")
    assert big.refresh().writes[0].mode == "row-level"
    got = catalog.load_table("db.big").scan().to_arrow().to_pylist()
    assert sorted(tuple(r.values()) for r in got) == rows(big)

    # A downstream job builds on the contract.
    @sv.transform(requires={"t": [_.doubled >= 0, _.doubled.notnull()]}, ensures=[_.half >= 0])
    def halved(t):
        return t.select(t.id, half=t.doubled // 2)

    halves = halved(IcebergSource(catalog, "db.big"))
    assert discharged(halves.refresh()["halved"].preconditions) == {
        ("big", "(_.doubled >= 0)"): CONTRACT,
        ("big", "_.doubled.notnull()"): SCHEMA,
    }
    assert rows(halves) == [(1, 5), (3, 1)]
    # Another writer voids the contract.
    catalog.load_table("db.big").append(
        pa.Table.from_pylist(
            [{"id": 9, "customer": "x", "doubled": -2}], schema=sink_schema_of(catalog)
        )
    )
    with pytest.raises(PreconditionError, match="doubled >= 0"):
        halved(IcebergSource(catalog, "db.big")).refresh()


def sink_schema_of(catalog):
    from sverify.io.iceberg import _arrow_schema

    return _arrow_schema(catalog.load_table("db.big"))


def test_added_column_is_left_out(catalog):
    from pyiceberg.types import StringType

    src = make_orders(catalog, [(1, "ada", 5)])
    node = doubled(src)
    node.refresh()
    with src.table().update_schema() as update:
        update.add_column("note", StringType())
    wide = rows_table([(2, "bob", 1)]).append_column("note", pa.array(["new"]))
    src.table().append(wide)
    [s] = batch(node).sources
    assert s.mode == "change feed" and "schema: added note, read in the old schema" in s.detail
    assert rows(node) == [(1, "ada", 10), (2, "bob", 2)]


def test_restarted_job_resumes_from_its_iceberg_sink(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    doubled(src).write(IcebergSink(catalog, "db.big")).refresh()
    src.table().append(rows_table([(3, "cy", 1)]))
    stored = IcebergSource(catalog, "db.big").stored()
    assert stored is not None and stored.sources == {"orders": 1}
    again = doubled(src).write(IcebergSink(catalog, "db.big"))
    entry = again.refresh()["big"]
    assert entry.started is not None and entry.started.startswith("resumed from db.big@v")
    assert entry.write is not None and entry.write.mode == "append"
    got = catalog.load_table("db.big").scan().to_arrow().to_pylist()
    assert sorted(tuple(r.values()) for r in got) == rows(again)
    assert rows(again) == recomputed(doubled(src), src)


def test_double_statistics_use_the_nan_count(catalog):
    schema = pa.schema(
        [pa.field("id", pa.int64(), nullable=False), pa.field("price", pa.float64())]
    )
    t = catalog.create_table("db.prices", schema=schema)
    t.append(
        pa.Table.from_pylist([{"id": 1, "price": 0.5}, {"id": 2, "price": None}], schema=schema)
    )
    # pyiceberg records no NaN counts, so the maximum is unknown.
    facts = [f.condition for f in IcebergSource(catalog, "db.prices").snapshot().facts]
    assert '"price" IS NULL OR ("price" >= 0.5)' in facts
    # Writers that count NaNs (Spark, Java) give the maximum where there are none.
    price = pa.schema([schema.field("price")])
    no_nan = {"price": ColumnStats(0.5, 2.5, 1, 4, nans=0)}
    some_nan = {"price": ColumnStats(-1.0, 3.0, 0, 2, nans=1)}
    assert [f.condition for f in stats_facts([no_nan], price, "s")] == [
        '"price" IS NULL OR ("price" >= 0.5 AND "price" <= 2.5)'
    ]
    assert [f.condition for f in stats_facts([no_nan, some_nan], price, "s")] == [
        '"price" IS NULL OR ("price" >= -1.0)'
    ]


# -- Row-level changes: reading only changed files, writing position deletes --


def written_entries(t):
    """The manifest entries the current snapshot added, by content (0 data,
    1 position deletes) -> record counts."""
    snap = t.current_snapshot().snapshot_id
    out: dict[int, list[int]] = {}
    for e in t.inspect.entries().to_pylist():
        if e["snapshot_id"] == snap and e["status"] == 1:
            out.setdefault(e["data_file"]["content"], []).append(e["data_file"]["record_count"])
    return out


def test_a_delete_reads_only_the_changed_files(catalog, monkeypatch):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    src.table().append(rows_table([(3, "cy", 1)]))
    src.table().append(rows_table([(4, "dan", 2)]))
    node = doubled(src)
    node.refresh()
    old = src.snapshot().table
    src.table().delete("id = 3")
    import sverify.io.iceberg as ice

    real, read = ice._scan, []

    def spy(t, tasks):
        read.extend(task.file.file_path for task in tasks)
        return real(t, tasks)

    monkeypatch.setattr(ice, "_scan", spy)
    change = src.changes(3)
    # Copy-on-write: one file removed, none added (it held only id 3).
    assert len(read) == 1 and change.kind == "snapshot diff"
    assert change.changes is not None
    want = snapshot_diff(old, src.snapshot().table)
    assert change.changes == want == sv.Changes(deletes=[(3, "cy", 1, T0)])
    node.refresh(audit=True)
    assert rows(node) == recomputed(node, src) == [(1, "ada", 10), (2, "bob", 14), (4, "dan", 4)]


@sv.transform(
    requires={"orders": [_.id.notnull(), sv.unique("id")]},
    ensures=[sv.unique("id")],
)
def amounts(orders):
    return orders.select(orders.id, orders.amount)


def test_sink_writes_a_change_as_position_deletes(catalog):
    src = make_orders(catalog, [(i, "c", i) for i in range(1, 101)])
    view = amounts(src).write(IcebergSink(catalog, "db.amounts"))
    view.refresh()
    # Update two of 100 rows, delete one.
    src.table().delete("id IN (1, 2, 3)")
    src.table().append(rows_table([(1, "c", 10), (2, "c", 20)]))
    w = view.refresh().writes[0]
    assert (w.mode, w.inserted, w.deleted) == ("row-level", 2, 3)
    out = catalog.load_table("db.amounts")
    # One data file of the two new rows and one delete file of three positions.
    assert written_entries(out) == {0: [2], 1: [3]}
    assert out.current_snapshot().summary.operation == Operation.OVERWRITE
    got = sorted(tuple(r.values()) for r in out.scan().to_arrow().to_pylist())
    assert got == rows(view) == recomputed(amounts(src), src)
    assert view.refresh().writes[0].mode == "skipped"


def test_sink_deletes_one_copy_of_a_duplicate(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "ada", 5), (3, "bob", 7)])
    names = src.pipe(lambda o: o.select(o.customer, o.amount))
    names = names.write(IcebergSink(catalog, "db.names"))
    names.refresh()
    src.table().delete("id = 1")
    w = names.refresh().writes[0]
    assert (w.mode, w.inserted, w.deleted) == ("row-level", 0, 1)
    got = sorted(
        tuple(r.values()) for r in catalog.load_table("db.names").scan().to_arrow().to_pylist()
    )
    assert got == rows(names) == [("ada", 5), ("bob", 7)]
    # Again: the deleted position is not deleted twice.
    src.table().delete("id = 2")
    assert names.refresh().writes[0].deleted == 1
    got = catalog.load_table("db.names").scan().to_arrow().to_pylist()
    assert [tuple(r.values()) for r in got] == rows(names) == [("bob", 7)]


def test_reading_a_table_with_position_deletes(catalog):
    """Merge-on-read: a downstream job reads the sink, whose data files now
    have delete files. Their statistics still describe all physical rows, a
    superset, so the facts from them hold; the change is read from the
    changed files only and matches the full snapshot diff."""
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7), (3, "cy", 100)])
    view = amounts(src).write(IcebergSink(catalog, "db.amounts"))
    view.refresh()
    down = IcebergSource(catalog, "db.amounts")
    copy = down_view(down)
    copy.refresh()
    before = down.snapshot().table
    src.table().delete("id = 3")
    assert view.refresh().writes[0].mode == "row-level"
    # The deleted 100 is still in the data file's statistics.
    snap = down.snapshot()
    assert '"amount" IS NOT NULL AND "amount" >= 5 AND "amount" <= 100' in [
        f.condition for f in snap.facts
    ]
    change = down.changes(copy.versions["amounts"])
    assert change.changes == snapshot_diff(before, snap.table)
    assert "on the 1 + 1 data file(s) that changed" in change.trusted
    copy.refresh(audit=True)
    assert rows(copy) == recomputed(copy, down) == [(1, 5), (2, 7)]


@sv.transform(requires={"t": [(_.amount >= 0) | _.amount.isnull()]}, ensures=[])
def down_view(t):
    return t.select(t.id, t.amount)


@sv.transform(
    requires={"t": [_.doubled >= 0, _.doubled.notnull()]},
    ensures=[_.doubled > 5],
)
def large(t):
    return t.filter(t.doubled > 5)


def test_nodes_store_in_iceberg_and_read_it_back(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 2)])
    d = doubled(src).write(IcebergSink(catalog, "db.doubled"))
    out = large(d).write(IcebergSink(catalog, "db.large"))
    report = out.refresh()
    assert [w.mode for w in report.writes] == ["created", "created"]
    assert out.versions == {"doubled": 1}
    src.table().append(rows_table([(3, "cy", 4)]))
    report = out.refresh(engine="polars")
    assert [w.mode for w in report.writes] == ["append", "append"]
    assert "Iceberg appends" in str(report["large"])
    assert rows(out) == [(1, "ada", 10), (3, "cy", 8)]
    assert len(catalog.load_table("db.large").scan().to_arrow()) == 2
