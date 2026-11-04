"""Iceberg tables (pyiceberg, SQLite catalog in a temporary directory) as
change sources, sources of preconditions and sinks."""

import warnings
from datetime import datetime, timedelta

import pyarrow as pa
import pytest
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog
from pyiceberg.table.snapshots import Operation

import sverify as sv
from _pipelines import batch, discharged, recomputed, rows
from sverify._weighted import consolidated
from sverify.contracts import ON_DATA, SCHEMA
from sverify.errors import PreconditionError
from sverify.incremental import arrow_rows, change_table, snapshot_diff
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


def as_diff(batch) -> list[tuple]:
    """A batch's change as `snapshot_diff` gives one: rows with weights."""
    return arrow_rows(consolidated(change_table(batch.changes, batch.schema)))


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
            _.amount < 1_000_000_000,
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
        ("orders", "(_.amount < 1000000000)"): "file stats @v1",
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


def as_text(orders):
    return orders.select(orders.customer, doubled=orders.amount.cast("string"))


def big_rows(catalog):
    got = catalog.load_table("db.big").scan().to_arrow().to_pylist()
    return sorted(tuple(r.values()) for r in got)


def test_another_plan_overwrites_the_iceberg_sink(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    doubled(src).write(IcebergSink(catalog, "db.big")).refresh()
    # Another plan at the same source versions, with a column of another
    # type: the table gets its schema and its rows, not a skip.
    other = src.pipe(as_text).write(IcebergSink(catalog, "db.big"))
    w = other.refresh().writes[0]
    assert (w.mode, w.inserted, w.deleted) == ("overwrite", 2, 0)
    fields = catalog.load_table("db.big").schema().fields
    assert [(f.name, str(f.field_type), f.required) for f in fields] == [
        ("customer", "string", False),
        ("doubled", "string", False),
    ]
    assert big_rows(catalog) == rows(other) == [("ada", "5"), ("bob", "7")]
    contract = IcebergSource(catalog, "db.big").contract()
    assert contract is not None and contract.plan == w.contract.plan
    src.table().append(rows_table([(3, "cy", 1)]))
    assert other.refresh().writes[0].mode == "append"
    assert big_rows(catalog) == rows(other)


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
    deletes, inserts = change.changes.deletes, change.changes.inserts
    assert isinstance(deletes, pa.Table) and isinstance(inserts, pa.Table)
    assert arrow_rows(deletes) == [(3, "cy", 1, T0)] and inserts.num_rows == 0
    assert as_diff(change) == arrow_rows(snapshot_diff(old, src.snapshot().table))
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
    assert as_diff(change) == arrow_rows(snapshot_diff(before, snap.table))
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


def compact(catalog, name, monkeypatch):
    """Rewrite the table's data files as one, in a `replace` snapshot, as
    compaction by another writer does. pyiceberg 0.12 has no compaction and
    refuses to write the summary of a `replace` snapshot, so the summary is
    an overwrite's, relabelled."""
    from pyiceberg.io.pyarrow import _dataframe_to_data_files
    from pyiceberg.table.snapshots import Operation, Summary
    from pyiceberg.table.update import snapshot
    from pyiceberg.table.update.snapshot import _OverwriteFiles

    summarize = snapshot.update_snapshot_summaries

    def relabelled(summary, previous_summary=None):
        out = summarize(
            Summary(Operation.OVERWRITE, **summary.additional_properties), previous_summary
        )
        return Summary(Operation.REPLACE, **out.additional_properties)

    monkeypatch.setattr(snapshot, "update_snapshot_summaries", relabelled)

    t = catalog.load_table(name)
    data = t.scan().to_arrow()
    old = [task.file for task in t.scan().plan_files()]
    with t.transaction() as tx, _OverwriteFiles(Operation.REPLACE, tx, t.io) as rewrite:
        for f in old:
            rewrite.delete_data_file(f)
        for f in _dataframe_to_data_files(tx.table_metadata, data, t.io):
            rewrite.append_data_file(f)
    monkeypatch.undo()


def test_a_restart_resumes_past_a_compaction(catalog, monkeypatch):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    big = doubled(src).write(IcebergSink(catalog, "db.big"))
    big.refresh()
    src.table().append(rows_table([(3, "cy", 1)]))
    big.refresh()
    compact(catalog, "db.big", monkeypatch)
    t = catalog.load_table("db.big")
    assert t.current_snapshot().summary.operation.value == "replace"
    assert len(list(t.scan().plan_files())) == 1
    stored = IcebergSource(catalog, "db.big").stored()
    assert stored is not None and stored.sources == {"orders": 2}
    src.table().append(rows_table([(4, "di", 2)]))
    again = doubled(src).write(IcebergSink(catalog, "db.big"))
    entry = again.refresh()["big"]
    assert entry.started == f"resumed from {stored.where}"
    assert entry.write is not None and entry.write.mode == "append"
    assert big_rows(catalog) == rows(again) == recomputed(doubled(src), src)


def test_rows_another_writer_changed_are_not_resumed_from(catalog, monkeypatch):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    doubled(src).write(IcebergSink(catalog, "db.big")).refresh()
    compact(catalog, "db.big", monkeypatch)
    catalog.load_table("db.big").append(
        pa.Table.from_pylist(
            [{"id": 9, "customer": "x", "doubled": 2}], schema=sink_schema_of(catalog)
        )
    )
    assert IcebergSource(catalog, "db.big").stored() is None


@sv.transform(
    requires={"orders": [_.id.notnull(), sv.unique("id")]},
    ensures=[sv.unique("id")],
)
def by_day(orders):
    return orders.select(orders.id, orders.customer, orders.amount, orders.ts)


def dated(rows):
    """Orders `(id, customer, amount, day)`, at noon of that day of 2024-01."""
    return pa.Table.from_pylist(
        [
            dict(zip(SCHEMA_ORDERS.names, (i, c, a, datetime(2024, 1, d, 12)), strict=True))
            for i, c, a, d in rows
        ],
        schema=SCHEMA_ORDERS,
    )


def files_by_partition(t) -> dict:
    """Each partition's data files, with the delete files they read."""
    out: dict = {}
    for task in t.scan().plan_files():
        files = out.setdefault(task.file.partition, set())
        files.add((task.file.file_path, frozenset(d.file_path for d in task.delete_files)))
    return out


@pytest.mark.parametrize("spec", ["identity", "day"])
def test_partitioned_sink_writes_only_the_change(catalog, spec):
    """#466: a sink table partitioned by `customer` (identity) or by `day(ts)`
    takes each change as one snapshot of position deletes and new rows, in
    the partitions the change touches. The table equals a full recompute at
    every step, and the other partitions keep their data files."""
    from pyiceberg.transforms import DayTransform
    from pyiceberg.typedef import Record

    # Customer a orders on day 1, b on day 2, c on day 3.
    catalog.create_table("db.orders", schema=SCHEMA_ORDERS).append(
        dated([(i, "abc"[i % 3], i, 1 + i % 3) for i in range(1, 13)])
    )
    src = IcebergSource(catalog, "db.orders")
    sink = catalog.create_table("db.out", schema=SCHEMA_ORDERS)
    with sink.update_spec() as update:
        if spec == "identity":
            update.add_identity("customer")
        else:
            update.add_field("ts", DayTransform(), "ts_day")
    view = by_day(src).write(IcebergSink(catalog, "db.out"))

    def partition(customer: str, day: int) -> Record:
        if spec == "identity":
            return Record(customer)
        return Record((datetime(2024, 1, day) - datetime(1970, 1, 1)).days)

    def step(mode, touched):
        before = files_by_partition(catalog.load_table("db.out"))
        snapshots = len(catalog.load_table("db.out").snapshots())
        assert view.refresh().writes[0].mode == mode
        out = catalog.load_table("db.out")
        table = out.scan().to_arrow().select(SCHEMA_ORDERS.names)
        got = sorted(tuple(r.values()) for r in table.to_pylist())
        assert got == rows(view) == recomputed(by_day(src), src)
        assert len(out.snapshots()) == snapshots + 1
        after = files_by_partition(out)
        changed = {p for p in before.keys() | after.keys() if before.get(p) != after.get(p)}
        assert changed == {partition(*t) for t in touched}
        # Each delete file is in the partition of the data file it applies to.
        for task in out.scan().plan_files():
            assert all(d.partition == task.file.partition for d in task.delete_files)
        return out

    # The first write replaces what the table held: one data file per partition.
    assert view.refresh().writes[0].mode == "overwrite"
    assert len(files_by_partition(catalog.load_table("db.out"))) == 3
    # A new order of a on day 2.
    src.table().append(dated([(20, "a", 7, 2)]))
    out = step("append", [("a", 2)])
    assert written_entries(out) == {0: [1]}
    # Delete an order of c (day 3), update one of a (day 1).
    src.table().delete("id IN (2, 3)")
    src.table().append(dated([(3, "a", 99, 1)]))
    out = step("row-level", [("a", 1), ("c", 3)])
    assert written_entries(out) == {0: [1], 1: [1, 1]}
    # Every order of one partition goes.
    src.table().delete("customer = 'b'" if spec == "identity" else "id IN (1, 4, 7, 10, 20)")
    step("row-level", [("b", 2)])
    assert view.refresh().writes[0].mode == "skipped"


@pytest.mark.parametrize("transform", ["identity", "day"])
def test_sink_creates_its_table_with_location_partitions_and_properties(
    catalog, tmp_path, transform
):
    """#468: the first write creates the table at `location`, partitioned by
    `partition_by`, with `properties` beside the contract; later refreshes
    write row-level changes into it (#466)."""
    catalog.create_table("db.orders", schema=SCHEMA_ORDERS).append(
        dated([(i, "abc"[i % 3], i, 1 + i % 3) for i in range(1, 13)])
    )
    src = IcebergSource(catalog, "db.orders")
    column = "customer" if transform == "identity" else "ts"
    where = f"file://{tmp_path}/elsewhere/out"
    sink = IcebergSink(
        catalog,
        "db.out",
        location=where,
        partition_by=[(column, transform)],
        properties={"write.target-file-size-bytes": "1048576"},
    )
    view = by_day(src).write(sink)

    def check(mode):
        assert view.refresh().writes[0].mode == mode
        out = catalog.load_table("db.out")
        table = out.scan().to_arrow().select(SCHEMA_ORDERS.names)
        assert sorted(tuple(r.values()) for r in table.to_pylist()) == rows(view)
        assert rows(view) == recomputed(by_day(src), src)
        for task in out.scan().plan_files():
            assert task.file.file_path.startswith(where)
            assert all(d.partition == task.file.partition for d in task.delete_files)
        return out

    out = check("created")
    assert out.location() == where
    assert [(f.source_id, str(f.transform)) for f in out.spec().fields] == [
        (out.schema().find_field(column).field_id, transform)
    ]
    assert out.properties["write.target-file-size-bytes"] == "1048576"
    assert IcebergSource(catalog, "db.out").contract() is not None
    assert len(out.snapshots()) == 1 and len(files_by_partition(out)) == 3
    src.table().delete("id IN (2, 3)")
    src.table().append(dated([(3, "a", 99, 1)]))
    out = check("row-level")
    assert written_entries(out) == {0: [1], 1: [1, 1]}
    # A sink on the existing table with the same options warns about nothing.
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        again = by_day(src).write(
            IcebergSink(catalog, "db.out", location=where, partition_by=[(column, transform)])
        )
        src.table().append(dated([(30, "b", 1, 2)]))
        assert again.refresh().writes[0].mode == "append"


def test_create_options_of_an_existing_table_are_ignored_with_a_warning(catalog, tmp_path):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    doubled(src).write(IcebergSink(catalog, "db.big")).refresh()
    before = catalog.load_table("db.big")
    sink = IcebergSink(
        catalog,
        "db.big",
        location=f"file://{tmp_path}/other",
        partition_by=[("customer", "identity")],
        properties={"a": "b"},
    )
    big = doubled(src).write(sink)
    src.table().append(rows_table([(3, "cy", 1)]))
    with pytest.warns(UserWarning, match=IcebergSink.create_options_ignored) as caught:
        big.refresh()
    message = str(caught[0].message)
    assert "location" in message and "partition fields" in message and "'a'" in message
    after = catalog.load_table("db.big")
    assert after.location() == before.location() and after.spec().is_unpartitioned()
    assert "a" not in after.properties
    # Once per sink.
    src.table().append(rows_table([(4, "di", 1)]))
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        big.refresh()


def test_unknown_transforms_and_the_sinks_own_properties_are_refused(catalog):
    with pytest.raises(ValueError, match="unknown transform 'dya'"):
        IcebergSink(catalog, "db.out", partition_by=[("ts", "dya")])
    with pytest.raises(ValueError, match="sverify.contract"):
        IcebergSink(catalog, "db.out", properties={"sverify.contract": "{}"})


@sv.transform(ensures=[sv.unique("customer")])
def totals(orders):
    return orders.group_by(orders.customer).agg(n=orders.id.count(), total=orders.amount.sum())


@sv.transform(ensures=[])
def busy(t):
    return t.filter(t.n > 2)


def live_files(t) -> tuple[int, int]:
    """The current snapshot's data files and delete files."""
    tasks = list(t.scan().plan_files())
    return len(tasks), len({d.file_path for task in tasks for d in task.delete_files})


def files_on_disk(root) -> int:
    return sum(1 for p in root.rglob("*") if p.is_file())


@pytest.mark.parametrize("partition_by", [None, [("customer", "identity")]])
def test_maintenance_keeps_a_streaming_sink_bounded(catalog, tmp_path, partition_by):
    """#465: an aggregate refreshed after every append adds a snapshot, a
    data file and a delete file per refresh. With `compact_every` and
    `snapshot_retention`, its table stays bounded (snapshots, live files and
    files on disk) and equals a full recompute, and so does a node reading
    it."""

    catalog.create_table("db.orders", schema=SCHEMA_ORDERS).append(
        dated([(1, "a", 1, 1), (2, "b", 2, 2)])
    )
    src = IcebergSource(catalog, "db.orders")
    where = tmp_path / "sink"
    sink = IcebergSink(
        catalog,
        "db.totals",
        location=f"file://{where}",
        partition_by=partition_by,
        properties={
            "write.metadata.delete-after-commit.enabled": "true",
            "write.metadata.previous-versions-max": "3",
        },
        compact_every=4,
        snapshot_retention=timedelta(0),
        min_snapshots=2,
    )
    agg = totals(src).write(sink)
    down = busy(agg)
    sizes = []
    for i in range(3, 40):
        src.table().append(dated([(i, "ab"[i % 2], i, 1 + i % 3)]))
        with warnings.catch_warnings():
            warnings.simplefilter("error", UserWarning)
            down.refresh()
        t = catalog.load_table("db.totals")
        table = t.scan().to_arrow().select(["customer", "n", "total"])
        assert sorted(tuple(r.values()) for r in table.to_pylist()) == rows(agg)
        assert rows(agg) == recomputed(totals(src), src)
        assert rows(down) == recomputed(busy(agg), IcebergSource(catalog, "db.totals"))
        sizes.append((len(t.snapshots()), *live_files(t), files_on_disk(where)))
    # Without maintenance: 37 snapshots, 1 + 36 data files, 36 delete files.
    snapshots, data, deletes, disk = map(max, zip(*sizes, strict=True))
    assert snapshots <= 6 and data <= 2 * 4 + 2 and deletes <= 2 * 4
    assert disk <= 60
    # A steady cycle of `compact_every` writes.
    assert sizes[-8:] == sizes[-16:-8]
    t = catalog.load_table("db.totals")
    assert any(s.summary.operation == Operation.REPLACE for s in t.snapshots())
    assert IcebergSource(catalog, "db.totals").contract() is not None
    assert IcebergSource(catalog, "db.totals").stored() is not None


def test_a_restart_resumes_past_the_sinks_own_compaction(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7), (3, "ada", 1)])
    sink = IcebergSink(catalog, "db.totals")
    agg = totals(src).write(sink)
    agg.refresh()
    for i in range(4, 8):
        src.table().append(rows_table([(i, "ada", i)]))
        assert agg.refresh().writes[0].mode == "row-level"
    before = live_files(catalog.load_table("db.totals"))
    assert before == (5, 4)
    done = sink.maintain()
    assert done == {"data_files_removed": 5, "delete_files_removed": 4, "data_files_added": 1}
    t = catalog.load_table("db.totals")
    assert live_files(t) == (1, 0)
    assert t.current_snapshot().summary.operation == Operation.REPLACE
    # Nothing left to compact: no snapshot.
    assert sink.maintain()["data_files_added"] == 0
    assert len(catalog.load_table("db.totals").snapshots()) == len(t.snapshots())
    stored = IcebergSource(catalog, "db.totals").stored()
    assert stored is not None and stored.sources == {"orders": 5}
    src.table().append(rows_table([(9, "bob", 1)]))
    again = totals(src).write(IcebergSink(catalog, "db.totals"))
    entry = again.refresh()["totals"]
    assert entry.started == f"resumed from {stored.where}"
    assert entry.write is not None and entry.write.mode == "row-level"
    assert rows(again) == recomputed(totals(src), src)
    # Expiry keeps the newest snapshots and the sink's last one.
    count = len(catalog.load_table("db.totals").snapshots())
    out = IcebergSink(catalog, "db.totals").maintain(expire=timedelta(0), min_snapshots=1)
    t = catalog.load_table("db.totals")
    # The compaction adds one snapshot, and only it is left.
    assert len(t.snapshots()) == 1 and out["snapshots_expired"] == count
    assert out["files_deleted"] > 0
    assert sorted(tuple(r.values()) for r in t.scan().to_arrow().to_pylist()) == rows(again)
    stored = IcebergSource(catalog, "db.totals").stored()
    assert stored is not None and stored.sources == {"orders": 6}


def test_maintenance_options_are_checked(catalog):
    with pytest.raises(ValueError, match="compact_every"):
        IcebergSink(catalog, "db.out", compact_every=0)
    with pytest.raises(ValueError, match="min_snapshots"):
        IcebergSink(catalog, "db.out", min_snapshots=0)
    assert IcebergSink(catalog, "db.missing").maintain() == {}
