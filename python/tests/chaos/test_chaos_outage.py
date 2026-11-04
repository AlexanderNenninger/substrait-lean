"""The object store goes away and comes back, as MinIO restarting does.

The sinks are on S3 (moto's server, in its own process), reached through a
proxy (`_proxy.py`) that drops every connection while its flag file exists.
The store goes down for a whole refresh, or at a fault point mid-refresh:
before the write, between reading the sink and committing, or right after
the commit landed (#488, here through the network rather than a mock).
Once it is back, the same process carries on, and so does a fresh one.
"""

from __future__ import annotations

import socket
import subprocess
import sys
import time
import uuid
from pathlib import Path

import pytest

from _faults import Faults, caused_by_crash
from _ledger import Violation
from _world import World, check, quiet

boto3 = pytest.importorskip("boto3")
pytest.importorskip("moto.server")

HERE = Path(__file__).parent


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def serve(args: list[str], port: int) -> subprocess.Popen:
    p = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(100):
        try:
            socket.create_connection(("127.0.0.1", port), timeout=0.1).close()
            return p
        except OSError:
            time.sleep(0.1)
    p.kill()
    pytest.fail(f"{args[1:3]} did not start")


class Store:
    """The S3 endpoint behind the proxy, and its switch."""

    def __init__(self, url: str, flag: Path):
        self.url, self.flag = url, flag

    def down(self) -> None:
        self.flag.touch()

    def up(self) -> None:
        self.flag.unlink(missing_ok=True)


@pytest.fixture(scope="module")
def store(tmp_path_factory):
    flag = tmp_path_factory.mktemp("proxy") / "down"
    moto_port, proxy_port = free_port(), free_port()
    moto = serve([sys.executable, "-m", "moto.server", "-p", str(moto_port)], moto_port)
    proxy = serve(
        [sys.executable, str(HERE / "_proxy.py"), str(proxy_port), str(moto_port), str(flag)],
        proxy_port,
    )
    try:
        yield Store(f"http://127.0.0.1:{proxy_port}", flag)
    finally:
        for p in (proxy, moto):
            p.kill()
            p.wait()


@pytest.fixture
def world(tmp_path, store):
    store.up()
    bucket = f"chaos-{uuid.uuid4().hex[:12]}"
    boto3.client(
        "s3",
        endpoint_url=store.url,
        aws_access_key_id="test",
        aws_secret_access_key="test",
        region_name="us-east-1",
    ).create_bucket(Bucket=bucket)
    options = {
        "AWS_ENDPOINT_URL": store.url,
        "AWS_ACCESS_KEY_ID": "test",
        "AWS_SECRET_ACCESS_KEY": "test",
        "AWS_REGION": "us-east-1",
        "AWS_ALLOW_HTTP": "true",
        "AWS_CONDITIONAL_PUT": "etag",
        # Fail fast while the store is down, rather than retry for minutes.
        "max_retries": "1",
        "retry_timeout": "2s",
        "connect_timeout": "1s",
        "timeout": "10s",
    }
    w = World(tmp_path / "w", "delta", storage={"uri": f"s3://{bucket}", "options": options})
    yield w.create()
    store.up()


def names_the_store(error: BaseException, world: World) -> None:
    """The error says it was the store: its endpoint or a sink's URI."""
    text = str(error)
    assert world.storage is not None
    if not (world.storage["uri"] in text or "127.0.0.1" in text or "S3" in text):
        raise Violation("unclear-error", "the error names the store", repr(error))


def recover(world: World, job) -> None:
    job.refresh()
    check(world, job)
    world.step(2)
    job.refresh()
    check(world, job)
    quiet(job)
    fresh = world.job()
    fresh.refresh()
    check(world, fresh)


@pytest.mark.parametrize("at", ["first", "later"])
def test_the_store_is_down_for_a_whole_refresh(world, store, scenario, at):
    scenario["setup"] = {"kind": "delta", "store": "s3", "at": at}
    scenario["fault"] = {"point": "store down", "when": "whole refresh", "action": "outage"}
    job = world.job()
    if at == "later":
        job.refresh()
        world.step(1)
    store.down()
    with pytest.raises(Exception) as raised:
        job.refresh()
    names_the_store(raised.value, world)
    store.up()
    recover(world, job)


#: Where the store goes down: the point, and before or after its call.
POINTS = [
    ("delta.committed", "before"),
    ("delta.committed", "after"),
    ("delta.write", "before"),
    ("delta.constraint", "after"),
    ("delta.merge", "before"),
    ("delta.merge", "after"),
    ("delta.overwrite", "after"),
    ("delta.version", "before"),
]


@pytest.mark.parametrize("nth", [1, 3])
@pytest.mark.parametrize(("point", "when"), POINTS)
@pytest.mark.parametrize("at", ["first", "later"])
def test_the_store_goes_down_mid_refresh(world, store, scenario, at, point, when, nth):
    scenario["setup"] = {"kind": "delta", "store": "s3", "at": at}
    scenario["fault"] = {"point": point, "when": when, "nth": nth, "action": "outage"}
    job = world.job()
    if at == "later":
        job.refresh()
        world.step(1)
    with Faults() as faults:
        fault = faults.arm(point, when=when, nth=nth, action="call", callback=store.down)
        try:
            job.refresh()
        except Exception as e:  # noqa: BLE001
            error: BaseException | None = e
        else:
            error = None
    store.up()
    if not fault.fired:
        pytest.skip(f"{fault.describe()} is not reached")
    if error is not None:
        assert caused_by_crash(error) is None
        names_the_store(error, world)
    recover(world, job)
