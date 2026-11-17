"""Iceberg equality deletes, read by DuckDB (#173, native scans N3).

pyiceberg reads none (`plan_files` raises), so the reference here is the rule
of the table spec written in plain Python: a row is deleted when a delete file
of a higher sequence number has a row equal on the delete's columns, NULL equal
to NULL."""

import uuid
import warnings

import pyarrow as pa
import pyarrow.parquet as pq
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from pyiceberg.catalog.sql import SqlCatalog
from pyiceberg.manifest import DataFile, DataFileContent, FileFormat
from pyiceberg.table.snapshots import Operation
from pyiceberg.typedef import Record

from sverify.io import IcebergSource
from sverify.io.iceberg import _RowLevel

pytestmark = pytest.mark.backend("duckdb")


@pytest.fixture
def catalog(tmp_path):
    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog("test", uri=f"sqlite:///{tmp_path}/catalog.db", warehouse=f"file://{tmp_path}")
    cat.create_namespace("db")
    return cat


def rows(ids, ks=None):
    ks = ks or [None if i % 2 else f"k{i % 3}" for i in ids]
    return pa.table({"id": pa.array(ids, pa.int64()), "k": pa.array(ks, pa.string())})


def delete_where_equal(t, columns: list[str], keys: pa.Table) -> None:
    """Commit an equality delete file of `keys`, on `columns`."""
    by_name = {f.name: f.field_id for f in t.schema().fields}
    schema = pa.schema(
        [
            pa.field(c, keys.schema.field(c).type, metadata={"PARQUET:field_id": str(by_name[c])})
            for c in columns
        ]
    )
    name = t.location_provider().new_data_location(f"{uuid.uuid4()}-eq-deletes.parquet")
    with t.io.new_output(name).create(overwrite=True) as f:
        pq.write_table(keys.select(columns).cast(schema), f)
    data = DataFile.from_args(
        content=DataFileContent.EQUALITY_DELETES,
        file_path=name,
        file_format=FileFormat.PARQUET,
        partition=Record(),
        record_count=keys.num_rows,
        file_size_in_bytes=len(t.io.new_input(name)),
        column_sizes={},
        value_counts={},
        null_value_counts={},
        nan_value_counts={},
        lower_bounds={},
        upper_bounds={},
        equality_ids=[by_name[c] for c in columns],
        spec_id=t.spec().spec_id,
    )
    with t.transaction() as tx:
        _RowLevel(
            [data], operation=Operation.OVERWRITE, transaction=tx, io=t.io, snapshot_properties={}
        ).commit()


def bag(t: pa.Table) -> list[tuple]:
    return sorted(
        ((r["id"], r["k"]) for r in t.to_pylist()), key=lambda r: (r[0], r[1] is None, r[1] or "")
    )


def test_an_equality_delete_applies_to_the_files_written_before_it(catalog):
    t = catalog.create_table("db.t", schema=rows([1]).schema)
    t.append(rows([1, 2, 3, 4]))  # seq 1
    delete_where_equal(t, ["id"], rows([2, 3]))  # seq 2
    t.append(rows([2, 5]))  # seq 3: the same id, written after the delete
    src = IcebergSource(catalog, "db.t")
    want = bag(rows([1, 4, 2, 5]))
    snap = src._native()
    assert snap is not None
    assert bag(snap.scan.to_arrow()) == want
    # The Arrow route is the descriptor's reader here: pyiceberg reads none.
    assert bag(src.snapshot().table) == want


def test_null_matches_null_and_all_columns_must_match(catalog):
    t = catalog.create_table("db.t", schema=rows([1]).schema)
    t.append(rows([1, 2, 3, 4], [None, "a", None, "b"]))
    delete_where_equal(t, ["id", "k"], rows([1, 2, 3], [None, "b", "x"]))  # only (1, NULL)
    delete_where_equal(t, ["k"], rows([0], ["b"]))  # every row with k = 'b'
    src = IcebergSource(catalog, "db.t")
    assert bag(src._native().scan.to_arrow()) == [(2, "a"), (3, None)]


def test_a_table_with_equality_deletes_and_a_rename(catalog):
    t = catalog.create_table("db.t", schema=rows([1]).schema)
    t.append(rows([1, 2, 3], ["a", "b", "a"]))
    with t.update_schema() as update:
        update.rename_column("k", "key")
    t = catalog.load_table("db.t")
    delete_where_equal(t, ["key"], pa.table({"key": pa.array(["a"], pa.string())}))
    src = IcebergSource(catalog, "db.t")
    got = src._native().scan.to_arrow()
    assert got.schema.names == ["id", "key"]
    assert sorted(r["id"] for r in got.to_pylist()) == [2]


@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(
    history=st.lists(
        st.one_of(
            st.tuples(st.just("append"), st.lists(st.integers(0, 6), min_size=1, max_size=4)),
            st.tuples(
                st.just("delete"),
                st.sampled_from([("id",), ("k",), ("id", "k")]),
                st.lists(
                    st.tuples(st.integers(0, 6), st.sampled_from([None, "a", "b"])), max_size=3
                ),
            ),
        ),
        min_size=1,
        max_size=6,
    )
)
def test_the_scan_equals_the_spec_over_histories(history, tmp_path_factory):
    """Appends and equality deletes in any order: a row survives a delete file
    unless the delete file is newer and has an equal row on its columns."""
    warnings.filterwarnings("ignore", module="pyiceberg")
    root = tmp_path_factory.mktemp("eq")
    cat = SqlCatalog("test", uri=f"sqlite:///{root}/c.db", warehouse=f"file://{root}")
    cat.create_namespace("db")
    t = cat.create_table("db.t", schema=rows([1]).schema)
    live: list[tuple] = []  # (id, k)
    for step in history:
        if step[0] == "append":
            new = rows(step[1], [(None, "a", "b")[i % 3] for i in step[1]])
            t.append(new)
            live += [(r["id"], r["k"]) for r in new.to_pylist()]
        else:
            _, cols, keys = step
            if not keys:
                continue
            table = pa.table(
                {
                    "id": pa.array([i for i, _ in keys], pa.int64()),
                    "k": pa.array([k for _, k in keys], pa.string()),
                }
            )
            delete_where_equal(t, list(cols), table)
            pick = [0 if c == "id" else 1 for c in cols]
            gone = {tuple(key[j] for j in pick) for key in keys}
            live = [r for r in live if tuple(r[j] for j in pick) not in gone]
    src = IcebergSource(cat, "db.t")
    snap = src._native()
    assert snap is not None
    assert bag(snap.scan.to_arrow()) == sorted(live, key=lambda r: (r[0], r[1] is None, r[1] or ""))
