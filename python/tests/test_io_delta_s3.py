"""A `DeltaSink` on S3 (moto's server, `conftest.py`): writes, maintenance and
a restart past another writer's compaction."""

from datetime import timedelta

import pytest
from deltalake import DeltaTable

from _pipelines import doubled, make_orders, paid, recomputed, rows
from sverify.io import DeltaSink, DeltaSource

pytest.importorskip("moto.server")


def job(tmp_path, uri, store, src=None, **options):
    if src is None:
        src = make_orders(tmp_path / "orders", [(1, "ada", 5), (2, "bob", 7)])
    sink = DeltaSink(uri, storage_options=store, **options)
    return src, doubled(paid(src)).write(sink)


def grow(src):
    from deltalake import write_deltalake

    from _pipelines import orders_table

    n = DeltaTable(src.uri).to_pyarrow_table().num_rows
    write_deltalake(src.uri, orders_table([(10 + n, "cy", 1)]), mode="append")


@pytest.mark.slow
def test_maintenance_on_s3(tmp_path, lake):
    root, store = lake
    uri = f"{root}/big"
    src, stored = job(
        tmp_path,
        uri,
        store,
        checkpoint_interval=2,
        compact_every=2,
        vacuum_retention=timedelta(0),
    )
    for _ in range(3):
        stored.refresh()
        grow(src)
    stored.refresh()
    dt = DeltaTable(uri, storage_options=store.options())
    assert dt.metadata().configuration["delta.checkpointInterval"] == "2"
    assert "OPTIMIZE" in [c["operation"] for c in dt.history()]
    assert len(dt.file_uris()) <= 2
    _, again = job(tmp_path, uri, store, src)
    entry = again.refresh()["big"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    assert rows(again) == recomputed(doubled(paid(src)), src)


@pytest.mark.slow
def test_a_restart_on_s3_resumes_past_another_writers_compaction(tmp_path, lake):
    root, store = lake
    uri = f"{root}/big"
    src, stored = job(tmp_path, uri, store)
    stored.refresh()
    grow(src)
    stored.refresh()
    DeltaTable(uri, storage_options=store.options()).optimize.compact()
    assert DeltaSource(uri, storage_options=store).stored() is not None
    grow(src)
    _, again = job(tmp_path, uri, store, src)
    entry = again.refresh()["big"]
    assert entry.started is not None and entry.started.startswith("resumed from")
    assert entry.write is not None and entry.write.mode == "merge"
    assert rows(again) == recomputed(doubled(paid(src)), src)
