"""Iceberg tables (pyiceberg, SQLite catalog in a temporary directory) as
change sources, sources of preconditions and sinks."""

import warnings
from datetime import datetime

import pyarrow as pa
import pytest
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.contracts import ON_DATA, SCHEMA
from sverify.io import IcebergSink, IcebergSource
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


def sources(found):
    return {(p.table, p.condition): p.source for p in found}


def test_appends_are_a_change_feed(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    assert big.versions == {"orders": 1}
    assert sources(pipe.preconditions) == {
        ("orders", "_.id.notnull()"): SCHEMA,
        ("orders", "(_.amount >= 0)"): "file stats @v1",
        ("orders", f"(_.ts >= {datetime(2024, 1, 1)!r})"): "file stats @v1",
        ("orders", "(_.customer != 'eve')"): ON_DATA,
        ("orders", "unique(id)"): ON_DATA,
    }
    src.table().append(rows_table([(3, "cy", 1)]))
    src.table().append(rows_table([(4, "dan", 2)]))
    report = pipe.refresh()
    [s] = report.sources
    assert (s.start, s.end, s.mode, s.inserts) == (1, 3, "change feed", 2)
    assert "Δ trusted as the files Iceberg appends v1→v3 added" in str(report)
    assert sources(report.preconditions)[("orders", "(_.amount >= 0)")] == (
        "file stats @v3 (new files)"
    )
    assert big.rows() == big.recompute()
    assert big.versions == {"orders": 3}


def test_row_level_deletes_fall_back_to_a_snapshot_diff(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    src.table().delete("id = 1")
    src.table().append(rows_table([(3, "cy", 1)]))
    report = pipe.refresh()
    [s] = report.sources
    assert s.mode == "snapshot diff"
    assert "not append-only" in s.detail and "only the snapshots are trusted" in s.detail
    assert big.rows() == big.recompute() == [(2, "bob", 14), (3, "cy", 2)]


def test_iceberg_batch_violations_are_caught(catalog):
    src = make_orders(catalog, [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    src.table().append(rows_table([(2, "eve", 1)]))
    with pytest.raises(sv.PreconditionError, match="customer"):
        pipe.refresh()
    assert pipe.versions == {"orders": 1} and big.rows() == [(1, "ada", 10)]


def test_iceberg_sink_carries_the_contract(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    sink = IcebergSink(catalog, "db.big", big)
    assert sink.write().mode == "created"
    out = catalog.load_table("db.big")
    assert {f.name: f.required for f in out.schema().fields} == {
        "id": False,
        "customer": False,
        "doubled": True,
    }
    contract = IcebergSource(catalog, "db.big").contract()
    assert contract is not None and contract.checks == {"sverify_1": "doubled >= 0"}
    assert out.current_snapshot().summary.get("sverify.epoch") == "1"
    assert sink.write().mode == "skipped"
    # Inserts only: an append. Then a deletion: an overwrite.
    src.table().append(rows_table([(3, "cy", 1)]))
    pipe.refresh()
    assert sink.write().mode == "append"
    src.table().delete("id = 2")
    pipe.refresh()
    assert sink.write().mode == "overwrite"
    got = catalog.load_table("db.big").scan().to_arrow().to_pylist()
    assert sorted(tuple(r.values()) for r in got) == big.rows()

    # A downstream job builds on the contract.
    @sv.transform(requires={"t": [_.doubled >= 0, _.doubled.notnull()]}, ensures=[_.half >= 0])
    def halved(t):
        return t.select(t.id, half=t.doubled // 2)

    pipe2 = sv.Pipeline(sv.connect())
    halves = pipe2.view("halves", halved(pipe2.source("big", IcebergSource(catalog, "db.big"))))
    assert sources(pipe2.preconditions) == {
        ("big", "(_.doubled >= 0)"): CONTRACT,
        ("big", "_.doubled.notnull()"): SCHEMA,
    }
    assert halves.rows() == [(1, 5), (3, 1)]
    # Another writer voids the contract.
    catalog.load_table("db.big").append(
        pa.Table.from_pylist(
            [{"id": 9, "customer": "x", "doubled": -2}], schema=sink_schema_of(catalog)
        )
    )
    pipe3 = sv.Pipeline(sv.connect())
    with pytest.raises(sv.PreconditionError, match="doubled >= 0"):
        pipe3.view("halves", halved(pipe3.source("big", IcebergSource(catalog, "db.big"))))


def sink_schema_of(catalog):
    from sverify.io.iceberg import _arrow_schema

    return _arrow_schema(catalog.load_table("db.big"))


def test_added_column_is_left_out(catalog):
    from pyiceberg.types import StringType

    src = make_orders(catalog, [(1, "ada", 5)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    with src.table().update_schema() as update:
        update.add_column("note", StringType())
    wide = rows_table([(2, "bob", 1)]).append_column("note", pa.array(["new"]))
    src.table().append(wide)
    [s] = pipe.refresh().sources
    assert s.mode == "change feed" and "schema: added note, read in the old schema" in s.detail
    assert big.rows() == big.recompute() == [(1, "ada", 10), (2, "bob", 2)]


def test_restarted_pipeline_resumes_from_its_iceberg_sink(catalog):
    src = make_orders(catalog, [(1, "ada", 5), (2, "bob", 7)])
    pipe = sv.Pipeline(sv.connect())
    big = pipe.view("big", doubled(pipe.source("orders", src)))
    IcebergSink(catalog, "db.big", big).write()
    src.table().append(rows_table([(3, "cy", 1)]))
    stored = IcebergSource(catalog, "db.big").stored()
    assert stored is not None and stored.sources == {"orders": 1}
    pipe2 = sv.Pipeline(sv.connect())
    orders = pipe2.source("orders", src, version=stored.sources["orders"])
    big2 = pipe2.view("big", doubled(orders), resume=stored)
    assert big2.resumed is not None and big2.resumed.startswith("resumed from db.big@v")
    sink2 = IcebergSink(catalog, "db.big", big2)
    pipe2.refresh()
    assert sink2.write().mode == "append"
    got = catalog.load_table("db.big").scan().to_arrow().to_pylist()
    assert sorted(tuple(r.values()) for r in got) == big2.rows() == big2.recompute()
