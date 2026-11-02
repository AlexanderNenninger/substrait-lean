"""Delta and Iceberg sinks written by DuckDB (#173).

When a view keeps its state in DuckDB, its sinks have DuckDB write the
Parquet files and sverify commits them (`sverify.io._engine`). These tests
run the same nodes on DuckDB and on Polars (whose state is Arrow, so its
sinks write through delta-rs and pyiceberg) and compare the sink tables after
every refresh, with the Arrow writers made to fail on the DuckDB run. They
also compare the statistics both writers record."""

import warnings
from datetime import date, datetime
from decimal import Decimal

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog

import sverify as sv
from sverify.incremental import snapshot_diff
from sverify.io import DeltaSink, DeltaSource, IcebergSink, IcebergSource
from sverify.io.delta import file_stats

pytest.importorskip("polars")

CDF = {"delta.enableChangeDataFeed": "true"}
NAN = float("nan")
SCHEMA = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("name", pa.string()),
        pa.field("x", pa.float64()),
        pa.field("day", pa.date32()),
        pa.field("ts", pa.timestamp("us")),
        pa.field("ok", pa.bool_()),
    ]
)


def orders(ids, x=1.5):
    return pa.Table.from_pylist(
        [
            {
                "id": i,
                "name": None if i % 4 == 0 else f"n{i % 3}",
                "x": [x, NAN, -0.0, None, 2.5][i % 5],
                "day": date(2024, 1, 1 + i % 28),
                "ts": datetime(2024, 1, 1, 0, 0, i % 60, 123456),
                "ok": i % 2 == 0,
            }
            for i in ids
        ],
        schema=SCHEMA,
    )


@sv.transform(ensures=[_.x >= 0.0])
def kept(o):
    # Duplicates: rows differ only in `id`, which this drops.
    return o.filter(o.x >= 0.0).select(o.name, o.x, o.day, o.ts, o.ok)


def same(a: pa.Table, b: pa.Table) -> bool:
    return snapshot_diff(a.cast(b.schema), b).num_rows == 0


def no_arrow_writes(monkeypatch):
    def fail(*args, **kwargs):
        raise AssertionError("the sink wrote through Arrow")

    monkeypatch.setattr("sverify.io.delta.write_deltalake", fail)
    monkeypatch.setattr("sverify.io.delta.DeltaSink._merge", fail)
    monkeypatch.setattr("sverify.io.iceberg._dataframe_to_data_files", fail)
    monkeypatch.setattr("sverify.io.iceberg._positions", fail)


def steps_delta(path):
    def append():
        write_deltalake(path, orders(range(20, 30), x=3.5), mode="append")

    def delete():
        DeltaTable(str(path)).delete("id % 3 = 1")

    def update():
        DeltaTable(str(path)).update({"x": "x + 1.0"}, predicate="id < 12")

    def everything():
        DeltaTable(str(path)).delete("id >= 0")

    return [append, delete, update, everything]


def follow(tmp_path, monkeypatch, make_source, make_sink, read_sink, steps):
    """Refresh `kept` over the source with a sink on DuckDB and on Polars,
    through `steps`, and compare the sink tables after each refresh."""
    nodes = {
        engine: kept(make_source()).write(make_sink(engine)) for engine in ("duckdb", "polars")
    }

    def refresh():
        with monkeypatch.context() as m:
            no_arrow_writes(m)
            duck = nodes["duckdb"].refresh(engine="duckdb").writes[0]
        arrow = nodes["polars"].refresh(engine="polars").writes[0]
        assert (duck.inserted, duck.deleted) == (arrow.inserted, arrow.deleted)
        got, want = read_sink("duckdb"), read_sink("polars")
        assert got.num_rows == want.num_rows and same(got, want)
        assert same(got, nodes["duckdb"].to_arrow())
        return duck

    writes = [refresh()]
    for step in steps:
        step()
        writes.append(refresh())
    # Exactly once: the same state is not written again.
    with monkeypatch.context() as m:
        no_arrow_writes(m)
        assert nodes["duckdb"].refresh(engine="duckdb").writes[0].mode == "skipped"
    return writes


def test_delta_sinks_written_by_duckdb(tmp_path, monkeypatch):
    path = tmp_path / "orders"
    write_deltalake(path, orders(range(20)), configuration=CDF)
    writes = follow(
        tmp_path,
        monkeypatch,
        lambda: DeltaSource(str(path)),
        lambda engine: DeltaSink(str(tmp_path / f"kept_{engine}")),
        lambda engine: DeltaTable(str(tmp_path / f"kept_{engine}")).to_pyarrow_table(),
        steps_delta(path),
    )
    assert [w.mode for w in writes] == ["created"] + ["merge"] * 4
    # The constraint the node proves, added before the rows.
    sink = DeltaSource(str(tmp_path / "kept_duckdb"))
    contract = sink.contract()
    assert contract is not None and list(contract.checks.values()) == ["x >= 0.0"]
    assert "delta.constraints.sverify_1" in sink.table().metadata().configuration


def test_a_node_reads_a_duckdb_written_delta_sink(tmp_path):
    """The change feed of the commits DuckDB's files make (files rewritten
    and added, without CDC files) is the change, net."""
    path = tmp_path / "orders"
    write_deltalake(path, orders(range(20)), configuration=CDF)
    node = kept(DeltaSource(str(path))).write(DeltaSink(str(tmp_path / "kept")))
    node.refresh()
    down = DeltaSource(str(tmp_path / "kept")).pipe(lambda t: t.select(t.name, t.x))
    down.refresh()
    for step in steps_delta(path):
        step()
        node.refresh()
        report = down.refresh()[down.name].report
        assert report is not None
        [s] = report.sources
        assert s.mode == "change feed"
        assert repr(sorted(map(repr, down.to_arrow().to_pylist()))) == repr(
            sorted(map(repr, node.to_arrow().select(["name", "x"]).to_pylist()))
        )


def test_delta_statistics_as_delta_rs_writes_them(tmp_path):
    rows = orders(range(30))
    write_deltalake(tmp_path / "rs", rows)
    node = sv.transform()(lambda o: o.select(*SCHEMA.names))(
        DeltaSource(str(tmp_path / "rs"), name="o")
    ).write(DeltaSink(str(tmp_path / "duck")))
    node.refresh(engine="duckdb")
    [rs] = file_stats(DeltaTable(str(tmp_path / "rs"))).values()
    [duck] = file_stats(DeltaTable(str(tmp_path / "duck"))).values()
    assert duck == rs


def test_delta_decimals_and_empty_writes(tmp_path):
    path = tmp_path / "o"
    rows = pa.table({"id": [1, 2], "price": pa.array([Decimal("1.25"), None], pa.decimal128(9, 2))})
    write_deltalake(path, rows, configuration=CDF)
    node = (
        DeltaSource(str(path))
        .pipe(lambda o: o.filter(o.id > 5))
        .write(DeltaSink(str(tmp_path / "s")))
    )
    assert node.refresh(engine="duckdb").writes[0].inserted == 0
    write_deltalake(
        path, pa.table({"id": [7], "price": rows.column("price").slice(0, 1)}), mode="append"
    )
    assert node.refresh(engine="duckdb").writes[0].inserted == 1
    got = DeltaTable(str(tmp_path / "s")).to_pyarrow_table().to_pylist()
    assert got == [{"id": 7, "price": Decimal("1.25")}]


# -- Iceberg -------------------------------------------------------------------


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    return cat


def test_iceberg_sinks_written_by_duckdb(tmp_path, monkeypatch, catalog):
    t = catalog.create_table("db.orders", schema=SCHEMA)
    t.append(orders(range(20)))

    def append():
        catalog.load_table("db.orders").append(orders(range(20, 30), x=3.5))

    def delete():
        catalog.load_table("db.orders").delete("id >= 25")

    def everything():
        catalog.load_table("db.orders").delete("id >= 0")

    writes = follow(
        tmp_path,
        monkeypatch,
        lambda: IcebergSource(catalog, "db.orders"),
        lambda engine: IcebergSink(catalog, f"db.kept_{engine}"),
        lambda engine: catalog.load_table(f"db.kept_{engine}").scan().to_arrow(),
        [append, delete, everything],
    )
    assert [w.mode for w in writes] == ["created", "append", "row-level", "row-level"]


def test_iceberg_statistics_as_pyiceberg_writes_them(tmp_path, catalog):
    from sverify.io.iceberg import _live_files, _stats

    t = catalog.create_table("db.rs", schema=SCHEMA)
    t.append(orders(range(30)))
    node = IcebergSource(catalog, "db.rs").pipe(lambda o: o.select(*SCHEMA.names))
    node = node.write(IcebergSink(catalog, "db.duck"))
    node.refresh(engine="duckdb")

    def stats(name):
        t = catalog.load_table(name)
        [entry] = _live_files(t, t.current_snapshot())
        return _stats(entry, SCHEMA.names)

    assert stats("db.duck") == stats("db.rs")


def test_a_node_reads_a_duckdb_written_iceberg_sink(tmp_path, catalog):
    t = catalog.create_table("db.orders", schema=SCHEMA)
    t.append(orders(range(20)))
    node = kept(IcebergSource(catalog, "db.orders")).write(IcebergSink(catalog, "db.kept"))
    node.refresh()
    down = IcebergSource(catalog, "db.kept").pipe(lambda k: k.select(k.name, k.x))
    down.refresh()
    catalog.load_table("db.orders").delete("id IN (1, 4, 7, 10, 13, 16, 19)")
    node.refresh()
    down.refresh(audit=True)
    assert sorted(map(repr, down.to_arrow().to_pylist())) == sorted(
        map(repr, node.to_arrow().select(["name", "x"]).to_pylist())
    )


def test_constraints_compare_numbers_by_value():
    """Delta stores `x >= 0.0` as `x >= 0`: the sink's own constraint."""
    from sverify.io.delta import _same_sql

    assert _same_sql("x >= 0.0", "x >= 0")
    assert _same_sql("(x IS NULL) OR (x > 1.50)", "x IS NULL OR x > 1.5")
    assert not _same_sql("x >= 0.5", "x >= 0")
