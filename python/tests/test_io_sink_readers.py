"""Other engines read what sverify's Delta and Iceberg sinks write (#861).

Each format's sink writes one set of tables per module from one orders
table: a table merged after a delete and appends (a row removed, duplicates
kept), one the sink compacted, checkpointed and vacuumed (Delta) or
compacted and expired (Iceberg), and one another plan with another column
set replaced. Every reader gives the rows the orders call for, written out
below: delta-rs's and pyiceberg's scans, DuckDB's `delta` and `iceberg`
extensions (`delta_scan`, `iceberg_scan`), which share no code with sverify's
writers, and sverify's own source. The contract record survives each
library's own maintenance, which breaks no reader. Spark's readers are
left out: no delta-spark or iceberg-spark-runtime builds against the Spark
sverify pins (`docs/how-it-works.md`, #2140)."""

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

#: The orders: three, then id 3 deleted and ids 4 and 5 appended, then ids
#: 6 to 10 appended one by one.
FIRST = [(1, "ada", 5), (2, "ada", 5), (3, None, 1)]
CHANGE = [(4, "cy", 2), (5, "ada", 5)]
LATER = [(i, "bob", i) for i in range(6, 11)]


def _rows(table: Any) -> list[tuple]:
    """The rows, by column name: Iceberg's schema evolution appends a new
    column after the old ones, which every reader keeps."""
    t = pa.table(table)
    cols = [c for c in ("id", "customer", "amount") if c in t.column_names]
    return sorted((tuple(r.values()) for r in t.select(cols).to_pylist()), key=repr)


def _sorted(rows: list[tuple]) -> list[tuple]:
    return sorted(rows, key=repr)


#: What each table holds: `customer, amount` of the orders after the change
#: (merged), after the later ones too (maintained), and every column of them
#: all (replaced).
EXPECTED = {
    "merged": _sorted([(c, a) for _, c, a in FIRST[:2] + CHANGE]),
    "maintained": _sorted([(c, a) for _, c, a in FIRST[:2] + CHANGE + LATER]),
    "replaced": _sorted(FIRST[:2] + CHANGE + LATER),
}
NAMES = list(EXPECTED)


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


def _names(orders: Any) -> Any:
    return orders.select(orders.customer, orders.amount)


def _wider(orders: Any) -> Any:
    return orders.select(orders.id, orders.customer, orders.amount)


# -- Delta -----------------------------------------------------------------------


def _delta_tables(root: Path) -> dict[str, Any]:
    src = make_orders(root / "orders", FIRST)
    merged = src.pipe(_names).write(DeltaSink(str(root / "merged")))
    merged.refresh()
    DeltaTable(src.uri).delete("id = 3")
    write_deltalake(src.uri, orders_table(CHANGE), mode="append")
    merge = merged.refresh().writes[0]

    kept = DeltaSink(
        str(root / "maintained"),
        checkpoint_interval=2,
        compact_every=2,
        vacuum_retention=timedelta(0),
    )
    maintained = src.pipe(_names).write(kept)
    maintained.refresh()
    for row in LATER:
        write_deltalake(src.uri, orders_table([row]), mode="append")
        maintained.refresh()

    replaced = str(root / "replaced")
    src.pipe(_names).write(DeltaSink(replaced)).refresh()
    src.pipe(_wider).write(DeltaSink(replaced)).refresh()
    uris = {"merged": str(root / "merged"), "maintained": kept.uri, "replaced": replaced}
    return {"uris": uris, "merge": merge}


@pytest.fixture(scope="module")
def delta(tmp_path_factory: pytest.TempPathFactory) -> dict[str, Any]:
    return _delta_tables(tmp_path_factory.mktemp("delta"))


def test_the_delta_tables_hold_a_merge_and_maintenance(delta) -> None:
    """The change is one MERGE commit that deletes a row and inserts two, and
    the maintained table was compacted, checkpointed and vacuumed by the
    sink, so the readers below read past each."""
    merge = delta["merge"]
    assert merge.mode == "merge" and (merge.inserted, merge.deleted) == (2, 1)
    before = DeltaTable(delta["uris"]["merged"], version=merge.version - 1)
    assert (None, 1) in _rows(before.to_pyarrow_table())
    maintained = delta["uris"]["maintained"]
    ops = {h.get("operation") for h in DeltaTable(maintained).history()}
    assert {"OPTIMIZE", "VACUUM END"} <= ops
    log = Path(maintained) / "_delta_log"
    assert any(p.name.endswith(".checkpoint.parquet") for p in log.iterdir())


@pytest.mark.parametrize("name", NAMES)
def test_sverify_reads_the_delta_sinks_rows(delta, name) -> None:
    assert _rows(DeltaSource(delta["uris"][name]).snapshot().table) == EXPECTED[name]


@pytest.mark.parametrize("name", NAMES)
def test_delta_rs_reads_the_sinks_rows(delta, name) -> None:
    assert _rows(DeltaTable(delta["uris"][name]).to_pyarrow_table()) == EXPECTED[name]


@pytest.mark.parametrize("name", NAMES)
def test_duckdb_delta_scan_reads_the_sinks_rows(delta, name) -> None:
    got = _duckdb("delta").execute(f"SELECT * FROM delta_scan('{delta['uris'][name]}')")
    assert _rows(got.to_arrow_table()) == EXPECTED[name]


def test_the_contract_survives_delta_rs_maintenance(tmp_path_factory) -> None:
    """delta-rs's own compaction and vacuum keep the contract record, and
    every reader still gives the expected rows."""
    uri = _delta_tables(tmp_path_factory.mktemp("delta-maintained"))["uris"]["merged"]
    before = DeltaSource(uri).contract()
    dt = DeltaTable(uri)
    dt.optimize.compact()
    dt.vacuum(retention_hours=0, enforce_retention_duration=False, dry_run=False)
    assert DeltaSource(uri).contract() == before is not None
    assert _rows(DeltaTable(uri).to_pyarrow_table()) == EXPECTED["merged"]
    assert _rows(DeltaSource(uri).snapshot().table) == EXPECTED["merged"]
    got = _duckdb("delta").execute(f"SELECT * FROM delta_scan('{uri}')").to_arrow_table()
    assert _rows(got) == EXPECTED["merged"]


# -- Iceberg ---------------------------------------------------------------------

SCHEMA = pa.schema([("id", pa.int64()), ("customer", pa.string()), ("amount", pa.int64())])


def _batch(rows: list[tuple]) -> pa.Table:
    return pa.Table.from_pylist(
        [dict(zip(SCHEMA.names, r, strict=True)) for r in rows], schema=SCHEMA
    )


def _iceberg_tables(root: Path) -> dict[str, Any]:
    pytest.importorskip("pyiceberg")
    from pyiceberg.catalog.sql import SqlCatalog

    from sverify.io import IcebergSink, IcebergSource

    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("t", uri=f"sqlite:///{root}/catalog.db", warehouse=f"file://{root}")
    cat.create_namespace("db")
    cat.create_table("db.orders", schema=SCHEMA).append(_batch(FIRST))
    src = IcebergSource(cat, "db.orders")

    merged = src.pipe(_names).write(IcebergSink(cat, "db.merged"))
    merged.refresh()
    src.table().delete("id = 3")
    src.table().append(_batch(CHANGE))
    merge = merged.refresh().writes[0]

    maintained = src.pipe(_names).write(
        IcebergSink(cat, "db.maintained", compact_every=2, snapshot_retention=timedelta(0))
    )
    maintained.refresh()
    for row in LATER:
        src.table().append(_batch([row]))
        maintained.refresh()

    src.pipe(_names).write(IcebergSink(cat, "db.replaced")).refresh()
    src.pipe(_wider).write(IcebergSink(cat, "db.replaced")).refresh()
    return {"catalog": cat, "idents": {n: f"db.{n}" for n in NAMES}, "merge": merge}


@pytest.fixture(scope="module")
def iceberg(tmp_path_factory: pytest.TempPathFactory) -> dict[str, Any]:
    return _iceberg_tables(tmp_path_factory.mktemp("iceberg"))


def test_the_iceberg_tables_hold_a_delete_and_maintenance(iceberg) -> None:
    """The change deletes a row with a position-delete file, and the
    maintained table was compacted by the sink."""
    from pyiceberg.table.snapshots import Operation

    cat, idents = iceberg["catalog"], iceberg["idents"]
    assert iceberg["merge"].deleted == 1
    tasks = list(cat.load_table(idents["merged"]).scan().plan_files())
    assert sum(len(t.delete_files) for t in tasks) >= 1
    ops = {s.summary.operation for s in cat.load_table(idents["maintained"]).snapshots()}
    assert Operation.REPLACE in ops


@pytest.mark.parametrize("name", NAMES)
def test_sverify_reads_the_iceberg_sinks_rows(iceberg, name) -> None:
    from sverify.io import IcebergSource

    src = IcebergSource(iceberg["catalog"], iceberg["idents"][name])
    assert _rows(src.snapshot().table) == EXPECTED[name]


@pytest.mark.parametrize("name", NAMES)
def test_pyiceberg_reads_the_sinks_rows(iceberg, name) -> None:
    t = iceberg["catalog"].load_table(iceberg["idents"][name])
    assert _rows(t.scan().to_arrow()) == EXPECTED[name]


@pytest.mark.parametrize("name", NAMES)
def test_duckdb_iceberg_scan_reads_the_sinks_rows(iceberg, name) -> None:
    meta = iceberg["catalog"].load_table(iceberg["idents"][name]).metadata_location
    got = _duckdb("iceberg").execute(f"SELECT * FROM iceberg_scan('{meta}')")
    assert _rows(got.to_arrow_table()) == EXPECTED[name]


def test_the_contract_survives_pyiceberg_maintenance(tmp_path_factory) -> None:
    """pyiceberg's own snapshot expiry keeps the contract, and the readers
    give the expected rows after it."""
    from sverify.io import IcebergSource

    tables = _iceberg_tables(tmp_path_factory.mktemp("iceberg-maintained"))
    cat, ident = tables["catalog"], tables["idents"]["merged"]
    before = IcebergSource(cat, ident).contract()
    cat.load_table(ident).maintenance.expire_snapshots().older_than(datetime.now()).commit()
    assert IcebergSource(cat, ident).contract() == before is not None
    t = cat.load_table(ident)
    assert _rows(t.scan().to_arrow()) == EXPECTED["merged"]
    got = _duckdb("iceberg").execute(f"SELECT * FROM iceberg_scan('{t.metadata_location}')")
    assert _rows(got.to_arrow_table()) == EXPECTED["merged"]
