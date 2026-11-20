"""Other engines read what sverify's Delta and Iceberg sinks write (#861).

Each format's sink writes one set of tables per module: a table merged
after deletes and appends (duplicates and NULLs kept), one the sink
compacted, checkpointed and vacuumed (Delta) or compacted and expired
(Iceberg), and one another plan with other columns replaced. Every reader
gives the rows sverify's own source gives: delta-rs's and pyiceberg's
scans, and DuckDB's `delta` and `iceberg` extensions (`delta_scan`,
`iceberg_scan`), which share no code with sverify's writers. The contract
record survives each library's own maintenance, which breaks no reader.
The Spark readers are #861's remainder."""

from __future__ import annotations

import warnings
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

import duckdb
import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake

from _pipelines import make_orders, orders_table
from sverify.io import DeltaSink, DeltaSource

pytestmark = pytest.mark.filterwarnings("ignore::UserWarning")


def _rows(table: Any) -> list[tuple]:
    t = pa.table(table)
    return sorted((tuple(r.values()) for r in t.to_pylist()), key=repr)


def _duckdb(extension: str) -> duckdb.DuckDBPyConnection:
    """A connection with DuckDB's own `extension`, installed where it is
    missing; the test skips where that fails (no network)."""
    con = duckdb.connect()
    try:
        con.execute(f"INSTALL {extension}")
        con.execute(f"LOAD {extension}")
    except duckdb.Error as e:
        pytest.skip(f"DuckDB's {extension} extension: {e}")
    return con


# -- Delta -----------------------------------------------------------------------


def _delta_tables(root: Any) -> dict[str, str]:
    src = make_orders(root / "orders", [(1, "ada", 5), (2, "ada", 5), (3, None, 1)])

    def names(orders: Any) -> Any:
        return orders.select(orders.customer, orders.amount)

    merged = src.pipe(names).write(DeltaSink(str(root / "merged")))
    merged.refresh()
    # A row gone and one new: the sink writes a MERGE.
    DeltaTable(src.uri).delete("id = 3")
    write_deltalake(src.uri, orders_table([(4, "cy", 2), (5, "ada", 5)]), mode="append")
    merged.refresh()

    kept = DeltaSink(
        str(root / "maintained"),
        checkpoint_interval=2,
        compact_every=2,
        vacuum_retention=timedelta(0),
    )
    maintained = src.pipe(names).write(kept)
    for i in range(6, 11):
        write_deltalake(src.uri, orders_table([(i, "bob", i)]), mode="append")
        maintained.refresh()

    replaced = str(root / "replaced")
    src.pipe(names).write(DeltaSink(replaced)).refresh()

    def wider(orders: Any) -> Any:
        return orders.select(orders.id, orders.customer, orders.amount)

    src.pipe(wider).write(DeltaSink(replaced)).refresh()
    return {"merged": str(root / "merged"), "maintained": kept.uri, "replaced": replaced}


@pytest.fixture(scope="module")
def delta_tables(tmp_path_factory: pytest.TempPathFactory) -> dict[str, str]:
    return _delta_tables(tmp_path_factory.mktemp("delta"))


DELTA = ["merged", "maintained", "replaced"]


@pytest.mark.parametrize("name", DELTA)
def test_delta_rs_reads_the_sinks_rows(delta_tables, name) -> None:
    uri = delta_tables[name]
    assert _rows(DeltaTable(uri).to_pyarrow_table()) == _rows(DeltaSource(uri).snapshot().table)


@pytest.mark.parametrize("name", DELTA)
def test_duckdb_delta_scan_reads_the_sinks_rows(delta_tables, name) -> None:
    uri = delta_tables[name]
    con = _duckdb("delta")
    got = con.execute(f"SELECT * FROM delta_scan('{uri}')").to_arrow_table()
    assert _rows(got) == _rows(DeltaSource(uri).snapshot().table)


def test_the_sinks_tables_are_maintained(delta_tables) -> None:
    """The maintained table was compacted, checkpointed and vacuumed by the
    sink itself, so the readers above read it past that."""
    uri = delta_tables["maintained"]
    ops = {h.get("operation") for h in DeltaTable(uri).history()}
    assert {"OPTIMIZE", "VACUUM END"} <= ops
    assert any(p.name.endswith(".checkpoint.parquet") for p in (Path(uri) / "_delta_log").iterdir())


def test_the_contract_survives_delta_rs_maintenance(tmp_path_factory) -> None:
    """delta-rs's own compaction and vacuum keep the contract record, and
    every reader still gives the same rows."""
    tables = _delta_tables(tmp_path_factory.mktemp("delta-maintained"))
    uri = tables["merged"]
    before = DeltaSource(uri).contract()
    rows = _rows(DeltaSource(uri).snapshot().table)
    dt = DeltaTable(uri)
    dt.optimize.compact()
    dt.vacuum(retention_hours=0, enforce_retention_duration=False, dry_run=False)
    assert DeltaSource(uri).contract() == before is not None
    assert _rows(DeltaTable(uri).to_pyarrow_table()) == rows
    got = _duckdb("delta").execute(f"SELECT * FROM delta_scan('{uri}')").to_arrow_table()
    assert _rows(got) == rows


# -- Iceberg ---------------------------------------------------------------------

iceberg = pytest.importorskip("pyiceberg")


def _iceberg_tables(root: Any) -> tuple[Any, dict[str, str]]:
    from pyiceberg.catalog.sql import SqlCatalog

    from sverify.io import IcebergSink, IcebergSource

    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("t", uri=f"sqlite:///{root}/catalog.db", warehouse=f"file://{root}")
    cat.create_namespace("db")
    schema = pa.schema([("id", pa.int64()), ("customer", pa.string()), ("amount", pa.int64())])

    def batch(rows: list[tuple]) -> pa.Table:
        return pa.Table.from_pylist(
            [dict(zip(schema.names, r, strict=True)) for r in rows], schema=schema
        )

    cat.create_table("db.orders", schema=schema).append(
        batch([(1, "ada", 5), (2, "ada", 5), (3, None, 1)])
    )
    src = IcebergSource(cat, "db.orders")

    def names(orders: Any) -> Any:
        return orders.select(orders.customer, orders.amount)

    merged = src.pipe(names).write(IcebergSink(cat, "db.merged"))
    merged.refresh()
    # A row gone and one new: the sink writes a position delete.
    src.table().delete("id = 3")
    src.table().append(batch([(4, "cy", 2), (5, "ada", 5)]))
    merged.refresh()

    maintained = src.pipe(names).write(
        IcebergSink(cat, "db.maintained", compact_every=2, snapshot_retention=timedelta(0))
    )
    for i in range(6, 11):
        src.table().append(batch([(i, "bob", i)]))
        maintained.refresh()

    src.pipe(names).write(IcebergSink(cat, "db.replaced")).refresh()

    def wider(orders: Any) -> Any:
        return orders.select(orders.id, orders.customer, orders.amount)

    src.pipe(wider).write(IcebergSink(cat, "db.replaced")).refresh()
    return cat, {n: f"db.{n}" for n in ("merged", "maintained", "replaced")}


@pytest.fixture(scope="module")
def iceberg_tables(tmp_path_factory: pytest.TempPathFactory) -> tuple[Any, dict[str, str]]:
    return _iceberg_tables(tmp_path_factory.mktemp("iceberg"))


def _ours(cat: Any, ident: str) -> list[tuple]:
    from sverify.io import IcebergSource

    return _rows(IcebergSource(cat, ident).snapshot().table)


@pytest.mark.parametrize("name", DELTA)
def test_pyiceberg_reads_the_sinks_rows(iceberg_tables, name) -> None:
    cat, idents = iceberg_tables
    t = cat.load_table(idents[name])
    assert _rows(t.scan().to_arrow()) == _ours(cat, idents[name])


@pytest.mark.parametrize("name", DELTA)
def test_duckdb_iceberg_scan_reads_the_sinks_rows(iceberg_tables, name) -> None:
    cat, idents = iceberg_tables
    meta = cat.load_table(idents[name]).metadata_location
    con = _duckdb("iceberg")
    got = con.execute(f"SELECT * FROM iceberg_scan('{meta}')").to_arrow_table()
    assert _rows(got) == _ours(cat, idents[name])


def test_the_contract_survives_pyiceberg_maintenance(tmp_path_factory) -> None:
    """pyiceberg's own snapshot expiry keeps the contract, and the readers
    give the same rows after it."""
    from sverify.io import IcebergSource

    cat, idents = _iceberg_tables(tmp_path_factory.mktemp("iceberg-maintained"))
    ident = idents["merged"]
    before = IcebergSource(cat, ident).contract()
    rows = _ours(cat, ident)
    t = cat.load_table(ident)
    t.maintenance.expire_snapshots().older_than(datetime.now()).commit()
    assert IcebergSource(cat, ident).contract() == before is not None
    t = cat.load_table(ident)
    assert _rows(t.scan().to_arrow()) == rows
    got = _duckdb("iceberg").execute(f"SELECT * FROM iceberg_scan('{t.metadata_location}')")
    assert _rows(got.to_arrow_table()) == rows
