"""A `DeltaSink` on S3 (moto's server, in another process: delta-rs hangs
against one in this process, `upstream/LEDGER.md` DL-1): writes, maintenance
and a restart past another writer's compaction."""

import socket
import subprocess
import sys
import time
import uuid
from datetime import timedelta

import pytest
from deltalake import DeltaTable

from _pipelines import doubled, make_orders, paid, recomputed, rows
from sverify.io import DeltaSink, DeltaSource, Storage

pytest.importorskip("moto.server")
boto3 = pytest.importorskip("boto3")


@pytest.fixture(scope="module")
def endpoint():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        port = s.getsockname()[1]
    server = subprocess.Popen(
        [sys.executable, "-m", "moto.server", "-p", str(port)],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    url = f"http://127.0.0.1:{port}"
    try:
        for _ in range(100):
            try:
                socket.create_connection(("127.0.0.1", port), timeout=0.1).close()
                break
            except OSError:
                time.sleep(0.1)
        else:
            pytest.fail("moto's server did not start")
        yield url
    finally:
        server.kill()
        server.wait()


@pytest.fixture
def lake(endpoint):
    """A new bucket, and the storage options to reach it."""
    bucket = f"lake-{uuid.uuid4().hex[:12]}"
    boto3.client(
        "s3",
        endpoint_url=endpoint,
        aws_access_key_id="test",
        aws_secret_access_key="test",
        region_name="us-east-1",
    ).create_bucket(Bucket=bucket)
    options = {
        "AWS_ENDPOINT_URL": endpoint,
        "AWS_ACCESS_KEY_ID": "test",
        "AWS_SECRET_ACCESS_KEY": "test",
        "AWS_REGION": "us-east-1",
        "AWS_ALLOW_HTTP": "true",
        "AWS_CONDITIONAL_PUT": "etag",
    }
    return f"s3://{bucket}", Storage(options)


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
