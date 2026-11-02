"""Delta and Iceberg tables read natively by DuckDB (#173).

On DuckDB, a pipeline holds a Delta or Iceberg source as the Parquet files
of its version (`sverify._scan.Scan`), which DuckDB reads itself. These
tests compare that path with the Arrow path the sources take otherwise:
the same rows at every version (deletion vectors, position deletes, added
columns, empty tables, pruned files), and the same views through a series
of refreshes, without the table passing through Python."""

import shutil
import warnings
from datetime import date, datetime
from decimal import Decimal
from pathlib import Path

import pyarrow as pa
import pytest
from deltalake import DeltaTable, write_deltalake
from pyiceberg.catalog.sql import SqlCatalog
from pyiceberg.types import StringType

import sverify as sv
from sverify._scan import Scan
from sverify.incremental import Pipeline, snapshot_diff
from sverify.io import DeltaSource, IcebergSink, IcebergSource

FIXTURE_DV = Path(__file__).parent / "data" / "delta_deletion_vectors"
CDF = {"delta.enableChangeDataFeed": "true"}

SCHEMA = pa.schema(
    [
        pa.field("id", pa.int64(), nullable=False),
        pa.field("name", pa.string()),
        pa.field("x", pa.float64()),
        pa.field("ts", pa.timestamp("us")),
        pa.field("day", pa.date32()),
        pa.field("ok", pa.bool_()),
        pa.field("price", pa.decimal128(10, 2)),
        pa.field("tags", pa.list_(pa.int64())),
        pa.field("pt", pa.struct([pa.field("a", pa.int64()), pa.field("b", pa.string())])),
    ]
)
T0 = datetime(2024, 1, 1)


def wide(ids, x=0.5):
    return pa.Table.from_pylist(
        [
            {
                "id": i,
                "name": None if i % 3 == 0 else f"n{i}",
                "x": [x, float("nan"), -0.0, None][i % 4],
                "ts": T0,
                "day": date(2024, 1, 1 + i % 28),
                "ok": i % 2 == 0,
                "price": Decimal(f"{i}.25"),
                "tags": [i, i + 1] if i % 2 else None,
                "pt": {"a": i, "b": "s"},
            }
            for i in ids
        ],
        schema=SCHEMA,
    )


def flat(ids, x=0.5):
    """`wide` without the struct column, which plans cannot read yet (#94)."""
    return wide(ids, x).drop_columns(["pt"])


def same_rows(got: pa.Table, want: pa.Table) -> bool:
    """The same bag of rows, as the model compares them (one NaN, one zero)."""
    assert got.schema.names == want.schema.names
    return snapshot_diff(got.cast(want.schema), want).num_rows == 0


def native(src, version=None) -> Scan:
    snap = src._native(version)
    assert snap is not None, "the source fell back to Arrow"
    return snap.scan


def check_versions(src, versions):
    """The native scan and the source's Arrow snapshot agree at each version."""
    for v in versions:
        scan, snap = native(src, v), src.snapshot(v)
        assert src._native(v).version == snap.version
        assert same_rows(scan.to_arrow(), snap.table), f"version {v}"
        assert src._native(v).facts == snap.facts


class ArrowOnly:
    """A source without a native scan: the Arrow path."""

    def __init__(self, src):
        self._src = src
        self.name = src.name

    def __getattr__(self, name):
        if name == "_native":
            raise AttributeError(name)
        return getattr(self._src, name)


def no_python_reads(monkeypatch):
    """Fail if a table is read into Arrow: by delta-rs, pyiceberg or a scan."""

    def fail(*args, **kwargs):
        raise AssertionError("the table was read into Python")

    monkeypatch.setattr("sverify.io.delta._read", fail)
    monkeypatch.setattr("sverify.io.iceberg._read", fail)
    monkeypatch.setattr(Scan, "to_arrow", fail)


def follow(make_source, steps, monkeypatch, view=lambda t: t.filter(t.x > 0.0)):
    """Run `view` over the source natively and on the Arrow path, through
    each of `steps` (functions changing the table, each followed by a
    refresh), and compare the views after each. The native pipeline never
    reads the table into Python."""
    pipes = []
    for src in (make_source(), ArrowOnly(make_source())):
        pipe = Pipeline(sv.connect())
        v = pipe.view("v", view(pipe.source("t", src)))
        pipes.append((pipe, v))
    (native_pipe, native_view), (arrow_pipe, arrow_view) = pipes
    assert isinstance(native_pipe.con.get("t"), Scan)
    assert isinstance(arrow_pipe.con.get("t"), pa.Table)
    assert repr(native_view.rows()) == repr(arrow_view.rows())
    reports = []
    for step in steps:
        step()
        with monkeypatch.context() as m:
            no_python_reads(m)
            reports.append(native_pipe.refresh())
        arrow_pipe.refresh()
        assert isinstance(native_pipe.con.get("t"), Scan)
        assert native_pipe.versions == arrow_pipe.versions
        got = repr(native_view.rows())
        assert got == repr(arrow_view.rows()) == repr(native_view.recompute())
    return reports


# -- Delta ---------------------------------------------------------------------


def test_delta_scan_reads_the_snapshots_rows(tmp_path):
    path = tmp_path / "t"
    write_deltalake(path, wide(range(0, 8)))
    write_deltalake(path, wide(range(8, 12), x=-1.5), mode="append")
    DeltaTable(str(path)).delete("id = 3")
    src = DeltaSource(str(path))
    assert len(native(src).files) == 2
    check_versions(src, [0, 1, 2, None])


def test_delta_deletion_vectors(tmp_path):
    shutil.copytree(FIXTURE_DV, tmp_path / "dv")
    src = DeltaSource(str(tmp_path / "dv"), name="orders")
    scan = native(src)
    assert scan.deleted is not None and scan.deleted.column("pos").to_pylist() == [1, 3]
    check_versions(src, [1, 2])


def test_delta_added_column(tmp_path):
    path = tmp_path / "t"
    write_deltalake(path, pa.table({"id": [1, 2], "a": [10, 20]}))
    new = pa.table({"id": [3], "a": [30], "b": ["x"]})
    write_deltalake(path, new, mode="append", schema_mode="merge")
    src = DeltaSource(str(path))
    # The first file has no `b`: it reads as NULL.
    assert sorted(native(src).to_arrow().to_pylist(), key=lambda r: r["id"])[0]["b"] is None
    check_versions(src, [0, 1])


def test_delta_empty_tables(tmp_path):
    DeltaTable.create(str(tmp_path / "e"), SCHEMA)
    src = DeltaSource(str(tmp_path / "e"))
    assert native(src).files == ()
    check_versions(src, [0])
    write_deltalake(tmp_path / "d", wide([1, 2]))
    DeltaTable(str(tmp_path / "d")).delete("id > 0")
    check_versions(DeltaSource(str(tmp_path / "d")), [1])


def test_delta_where_prunes_the_same_files(tmp_path):
    path = tmp_path / "t"
    write_deltalake(path, pa.table({"id": [1, 2], "amount": [5, 50]}))
    write_deltalake(path, pa.table({"id": [3, 4], "amount": [60, 80]}), mode="append")
    src = DeltaSource(str(path), where="amount * 2 > 100")
    scan = native(src)
    assert len(scan.files) == 1 and len(src.skipped) == 1
    assert scan.where == "amount * 2 > 100"
    check_versions(src, [0, 1])


def test_delta_partitions_fall_back_to_arrow(tmp_path):
    write_deltalake(tmp_path / "p", pa.table({"id": [1, 2], "k": ["a", "b"]}), partition_by=["k"])
    src = DeltaSource(str(tmp_path / "p"))
    assert src._native() is None
    pipe = Pipeline(sv.connect())
    pipe.source("p", src)
    assert isinstance(pipe.con.get("p"), pa.Table)


def test_other_engines_get_arrow(tmp_path):
    write_deltalake(tmp_path / "t", pa.table({"id": [1]}))
    pipe = Pipeline(sv.connect("polars"))
    pipe.source("t", DeltaSource(str(tmp_path / "t")))
    assert isinstance(pipe.con.get("t"), pa.Table)


def test_delta_refreshes_match_the_arrow_path(tmp_path, monkeypatch):
    path = tmp_path / "t"
    write_deltalake(path, flat(range(0, 20)), configuration=CDF)

    def append():
        write_deltalake(path, flat(range(20, 30), x=2.5), mode="append")

    def delete():
        DeltaTable(str(path)).delete("id % 5 = 1")

    def update():
        DeltaTable(str(path)).update({"x": "x + 1.0"}, predicate="id < 10")

    reports = follow(lambda: DeltaSource(str(path)), [append, delete, update], monkeypatch)
    assert [r.sources[0].mode for r in reports] == ["change feed"] * 3


def test_delta_where_refreshes_match_the_arrow_path(tmp_path, monkeypatch):
    path = tmp_path / "t"
    write_deltalake(path, flat(range(0, 10)), configuration=CDF)

    def append():
        write_deltalake(path, flat(range(10, 20), x=3.0), mode="append")

    follow(
        lambda: DeltaSource(str(path), where="id >= 5"),
        [append],
        monkeypatch,
        view=lambda t: t.select(t.id, t.name),
    )


def test_delta_without_a_feed_stays_native(tmp_path):
    """No Change Data Feed: the snapshot diff reads the new snapshot, and the
    table is held as files of the new version again."""
    path = tmp_path / "t"
    write_deltalake(path, pa.table({"id": [1, 2], "x": [1.0, 2.0]}))
    pipe = Pipeline(sv.connect())
    t = pipe.source("t", DeltaSource(str(path)))
    v = pipe.view("v", t.filter(t.x > 1.0))
    write_deltalake(path, pa.table({"id": [3], "x": [3.0]}), mode="append")
    assert pipe.refresh().sources[0].mode == "recomputed"
    scan = pipe.con.get("t")
    assert isinstance(scan, Scan) and scan.origin == "t@v1"
    assert v.rows() == [(2, 2.0), (3, 3.0)]


def test_delta_deletes_are_checked_against_the_files(tmp_path, monkeypatch):
    path = tmp_path / "t"
    write_deltalake(path, pa.table({"id": [1, 2]}), configuration=CDF)
    src = DeltaSource(str(path))
    pipe = Pipeline(sv.connect())
    pipe.view("v", pipe.source("t", src))
    DeltaTable(str(path)).delete("id = 1")
    real = DeltaSource.changes

    def wrong(self, since, *args):
        out = real(self, since, *args)
        out.changes = sv.Changes(deletes=[(7,)])
        return out

    monkeypatch.setattr(DeltaSource, "changes", wrong)
    with pytest.raises(ValueError, match=r"cannot delete \(7,\) from t"):
        pipe.refresh()
    assert pipe.versions == {"t": 0}


# -- Iceberg -------------------------------------------------------------------


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    return cat


def iceberg(catalog, table: pa.Table, name="db.t") -> IcebergSource:
    t = catalog.create_table(name, schema=table.schema)
    t.append(table)
    return IcebergSource(catalog, name)


def test_iceberg_scan_reads_the_snapshots_rows(catalog):
    src = iceberg(catalog, wide(range(0, 8)))
    src.table().append(wide(range(8, 12), x=-1.5))
    src.table().delete("id = 3")
    assert src._native(0).scan.files == ()
    check_versions(src, [0, 1, 2, 3, None])


def test_iceberg_position_deletes(catalog):
    """A table an `IcebergSink` wrote: its changes are position delete files."""
    src = iceberg(catalog, pa.table({"id": list(range(10)), "amount": list(range(10))}), "db.o")
    node = src.pipe(lambda o: o.select(o.id, o.amount)).write(IcebergSink(catalog, "db.out"))
    node.refresh()
    src.table().delete("id IN (2, 5)")
    assert node.refresh().writes[0].mode == "row-level"
    out = IcebergSource(catalog, "db.out")
    scan = native(out)
    assert scan.deleted is not None and scan.deleted.num_rows == 2
    check_versions(out, [1, 2])


def test_iceberg_added_and_renamed_columns(catalog):
    src = iceberg(catalog, pa.table({"id": [1, 2], "a": [10, 20]}))
    with src.table().update_schema() as update:
        update.add_column("b", StringType())
    src.table().append(pa.table({"id": [3], "a": [30], "b": ["x"]}))
    # (pyiceberg's own read of version 1 fails: it casts to the new schema.)
    check_versions(src, [2])
    with src.table().update_schema() as update:
        update.rename_column("a", "c")
    # The old files have the column as `a`: only pyiceberg reads it by id.
    assert src._native() is None


def test_iceberg_partitions_fall_back_to_arrow(catalog):
    table = pa.table({"id": [1, 2], "k": ["a", "b"]})
    t = catalog.create_table("db.p", schema=table.schema)
    with t.update_spec() as update:
        update.add_identity("k")
    t.append(table)
    assert IcebergSource(catalog, "db.p")._native() is None


def test_iceberg_refreshes_match_the_arrow_path(catalog, monkeypatch):
    src = iceberg(catalog, flat(range(0, 20)))

    def append():
        src.table().append(flat(range(20, 30), x=2.5))

    def delete():
        src.table().delete("id >= 25")

    reports = follow(lambda: IcebergSource(catalog, "db.t"), [append, delete], monkeypatch)
    assert [r.sources[0].mode for r in reports] == ["change feed", "snapshot diff"]


def test_nans_beyond_the_file_statistics(tmp_path, monkeypatch):
    """Parquet statistics leave NaN out, and DuckDB 2.0 trusts them on a raw
    `read_parquet` column (upstream/LEDGER.md DD-4): the scan's columns hide
    them, so a NaN stays above every double."""
    path = tmp_path / "t"
    write_deltalake(path, pa.table({"id": [1, 2], "x": [0.5, float("nan")]}), configuration=CDF)
    reports = follow(
        lambda: DeltaSource(str(path)),
        [lambda: write_deltalake(path, pa.table({"id": [3], "x": [7.0]}), mode="append")],
        monkeypatch,
        view=lambda t: t.filter(t.x > 100.0),
    )
    assert reports[0].sources[0].mode == "change feed"
    pipe = Pipeline(sv.connect())
    t = pipe.source("t", DeltaSource(str(path)))
    assert pipe.view("v", t.filter(t.x > 100.0)).rows()[0][0] == 2
    # Ibis on the connection reads the same view of the files.
    assert t.filter(t.x > 100.0).count().execute() == 1
