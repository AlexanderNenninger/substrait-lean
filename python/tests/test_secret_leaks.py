"""Gate: no secret leaks into an output sverify writes (#777).

Every source and sink type gets sentinel secrets: by name through the
resolver, as `Secret` option values, and as plain values (inline options, a
deprecated Flight token, catalog properties). Then every output is grepped
for them: the check's text, JSON, SARIF, GitHub and JUnit formats, the
report and its JSON, the refresh and its JSON and alert, sink contract
records, every file the tables and catalogs left on disk, the Substrait
export, the ODCS export, OpenLineage events, logs, warnings, printed output
and the exceptions of a failed resolution. Each sentinel is a fresh test
value, never a real credential.

Credentials can also hide in a URI's userinfo (`s3://key:secret@bucket`):
a `from_files` source and a Delta sink written that way are checked and
exported, and no output may carry the sentinel (#887). A custom source's
cursor is stored in clear in the sink's own record, which resumes from it:
the gate plants one and allows it there and nowhere else.

A new source, sink or output format joins the fixture and the `outputs`
it greps in the same pull request.

The ontology index (#772) does not exist yet; when it does, its output
belongs in `outputs` below.
"""

from __future__ import annotations

import json
import logging
import pickle
import runpy
import threading
import traceback
import uuid
import warnings
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

import pytest

pytest.importorskip("deltalake")
pytest.importorskip("pyiceberg")
fl = pytest.importorskip("pyarrow.flight")

from sverify import odcs  # noqa: E402
from sverify import openlineage as ol  # noqa: E402
from sverify.cli import main  # noqa: E402
from sverify.errors import SecretError  # noqa: E402
from sverify.io import Resolver, Secret, set_resolver  # noqa: E402
from sverify.io.flight import FlightLog  # noqa: E402
from sverify.openlineage import Lineage  # noqa: E402

SENTINELS = {
    name: f"svleak-{name}-{uuid.uuid4().hex}"
    for name in (
        "lake-key",
        "lake-id",
        "option",
        "inline",
        "flight",
        "flight-inline",
        "api",
        "sink",
        "catalog",
        "lineage",
        "userinfo",
    )
}
CURSOR = f"svleak-cursor-{uuid.uuid4().hex}"
"""A custom source's cursor. The sink stores it in clear in the table's
own record, which resumes from it (`Source.restore` says a cursor holds no
credential): it may be there, and nowhere else (#887)."""
CURSOR_CARRIERS = ("contract g", "file marts/g/_delta_log/")

PIPELINE = """
import os
import pyarrow as pa
import sverify as sv
from ibis import _
from pyiceberg.catalog.sql import SqlCatalog
from sverify.io import (
    Batch, DeltaSink, DeltaSource, Secret, Source, Storage, from_files, from_query, sink_from,
)
from sverify.io.flight import FlightSource
from sverify.io.iceberg import IcebergSink, IcebergSource

root = os.environ["SVLEAK_ROOT"]
lake = Storage(credentials="lake", writes=[root + "/marts"], reads=[root])
options = {"AWS_REGION": "eu-central-1", "AWS_SECRET_ACCESS_KEY": Secret("env:SVLEAK_OPTION")}
inline = {"AWS_SECRET_ACCESS_KEY": os.environ["SVLEAK_INLINE"]}

orders = DeltaSource(root + "/orders", storage_options=lake)
orders_b = DeltaSource(root + "/orders", storage_options=options, name="orders_b")
orders_c = DeltaSource(root + "/orders", storage_options=inline, name="orders_c")
catalog = SqlCatalog(
    "lakecat", uri=f"sqlite:///{root}/catalog.db", warehouse=f"file://{root}/warehouse",
    **{"svleak.token": os.environ["SVLEAK_CATALOG"]},
)
ice = IcebergSource(catalog, "db.events")
samples = FlightSource(
    os.environ["SVLEAK_FLIGHT_AT"], "samples", secret="flight-token",
    schema=pa.schema([("id", pa.int64()), ("amount", pa.int64())]),
)


def api(since):
    assert Secret("api").value() == os.environ["SVLEAK_API"]
    return pa.table({"id": [1, 2], "amount": [5, 50]}).filter(
        pa.compute.greater(pa.array([1, 2]), since or 0)
    )


fetched = from_query(api, cursor_on="id", name="fetched", credentials="api")
saved = []


def save(table):
    assert Secret("env:SVLEAK_SINK").value() == os.environ["SVLEAK_SINK"]
    saved.append(table)


@sv.transform(
    requires={"t": [_.amount >= 0, _.amount < 1000, sv.unique("id")]},
    ensures=[_.amount > 10],
)
def big(t):
    return t.filter(t.amount > 10)


a = orders.pipe(big).write(DeltaSink(root + "/marts/a", storage_options=lake))
b = orders_b.pipe(big).write(DeltaSink(root + "/elsewhere/b", storage_options=lake))
c = orders_c.pipe(big).write(DeltaSink(root + "/marts/c", storage_options=inline))
d = ice.pipe(big).write(IcebergSink(catalog, "db.big"))
e = samples.pipe(big).write(sink_from(save, name="e", credentials="env:SVLEAK_SINK"))
f = fetched.pipe(big).write(DeltaSink(root + "/marts/f"))


class Feed(Source):
    def read(self, since):
        if since is None:
            rows = pa.table({"id": [1, 2], "amount": [5, 50]})
            return Batch(rows, cursor=os.environ["SVLEAK_CURSOR"])
        return None

    def restore(self, cursor):
        return None


feed = Feed("feed", schema=pa.schema([("id", pa.int64()), ("amount", pa.int64())]))
g = feed.pipe(big).write(DeltaSink(root + "/marts/g"))

# Credentials in a URI's userinfo: checked, never refreshed (no such
# bucket); `sverify check` reads no data, since the schema is declared.
bucket = "s3://svleak:" + os.environ["SVLEAK_USERINFO"] + "@bucket"
drop = from_files(
    bucket + "/drop", name="drop",
    schema=pa.schema([("id", pa.int64()), ("amount", pa.int64())]),
)
h = drop.pipe(big).write(DeltaSink(bucket + "/marts/h"))
NODES = [a, b, c, d, e, f, g]
UNREFRESHED = [h]
"""


class _Lineage(BaseHTTPRequestHandler):
    seen: list[tuple[str, bytes]] = []

    def log_message(self, format, *args):  # noqa: A002 - the parent's name
        pass

    def do_POST(self):
        body = self.rfile.read(int(self.headers["Content-Length"]))
        _Lineage.seen.append((self.headers.get("Authorization", ""), body))
        self.send_response(201)
        self.end_headers()


def _has(text: str | bytes, value: str) -> bool:
    return value.encode() in text if isinstance(text, bytes) else value in text


def _found(text: str | bytes) -> list[str]:
    if isinstance(text, bytes):
        text = text.decode("utf-8", "replace")
    return [k for k, v in SENTINELS.items() if v in text]


@pytest.fixture
def lake(tmp_path, monkeypatch):
    import pyarrow as pa
    from deltalake import write_deltalake

    root = tmp_path / "lake"
    root.mkdir()
    env = {
        "SVLEAK_ROOT": str(root),
        "SVLAKE_AWS_SECRET_ACCESS_KEY": SENTINELS["lake-key"],
        "SVLAKE_AWS_ACCESS_KEY_ID": SENTINELS["lake-id"],
        "SVLEAK_OPTION": SENTINELS["option"],
        "SVLEAK_INLINE": SENTINELS["inline"],
        "FLIGHT_TOKEN": SENTINELS["flight"],
        "SVLEAK_API": SENTINELS["api"],
        "API": SENTINELS["api"],
        "SVLEAK_SINK": SENTINELS["sink"],
        "SVLEAK_CATALOG": SENTINELS["catalog"],
        "SVLEAK_LINEAGE": SENTINELS["lineage"],
        "SVLEAK_USERINFO": SENTINELS["userinfo"],
        "SVLEAK_CURSOR": CURSOR,
    }
    for k, v in env.items():
        monkeypatch.setenv(k, v)
    config = tmp_path / "secrets.toml"
    config.write_text('[names]\nlake = "env:SVLAKE_*"\n')
    monkeypatch.setenv("SVERIFY_SECRETS", str(config))
    set_resolver(None)

    table = pa.table({"id": [1, 2, 3], "amount": [5, 50, 500]})
    write_deltalake(str(root / "orders"), table)
    from pyiceberg.catalog.sql import SqlCatalog

    warnings.filterwarnings("ignore", module="pyiceberg")
    cat = SqlCatalog(
        "lakecat", uri=f"sqlite:///{root}/catalog.db", warehouse=f"file://{root}/warehouse"
    )
    cat.create_namespace("db")
    cat.create_table("db.events", schema=table.schema).append(table)

    class Token(fl.ServerMiddlewareFactory):
        def start_call(self, info, headers):
            if f"Bearer {SENTINELS['flight']}" not in headers.get("authorization", []):
                raise fl.FlightUnauthenticatedError("a valid bearer token is needed")

    server = FlightLog(middleware={"token": Token()})
    client = fl.connect(f"grpc://127.0.0.1:{server.port}")
    opts = fl.FlightCallOptions(
        headers=[(b"authorization", f"Bearer {SENTINELS['flight']}".encode())]
    )
    writer, _ = client.do_put(fl.FlightDescriptor.for_path("samples"), table.schema, opts)
    writer.write_table(table)
    writer.close()
    monkeypatch.setenv("SVLEAK_FLIGHT_AT", f"grpc://127.0.0.1:{server.port}")

    http = HTTPServer(("127.0.0.1", 0), _Lineage)
    threading.Thread(target=http.serve_forever, daemon=True).start()
    _Lineage.seen = []
    path = tmp_path / "pipeline.py"
    path.write_text(PIPELINE)
    yield path, root, f"http://127.0.0.1:{http.server_port}"
    http.shutdown()
    server.shutdown()
    set_resolver(None)


def test_no_secret_reaches_any_output(lake, capsys, caplog):
    path, root, lineage_url = lake
    caplog.set_level(logging.DEBUG)
    outputs: dict[str, str | bytes] = {}

    # The command line, in every format.
    for fmt in ("text", "json", "sarif", "github", "junit"):
        main(["check", str(path), "--format", fmt, "--full"])
        outputs[f"check {fmt}"] = capsys.readouterr().out
    doc = json.loads(outputs["check json"])
    # The credentials are listed by name, with the scope warning (#778).
    assert doc["credentials"], (doc["error"], doc["findings"])
    names = {(c["node"], c["table"], c["credential"], c["access"]) for c in doc["credentials"]}
    assert ("a", "orders", "lake", "read") in names
    assert ("a", "a", "lake", "write") in names
    assert ("e", "samples", "flight-token", "read") in names
    assert ("f", "fetched", "api", "read") in names
    assert ("e", "e", "env:SVLEAK_SINK", "write") in names
    assert ("c", "orders_c", "inline values", "read") in names
    # A URI with userinfo counts as inline credentials, and is listed without them.
    assert ("h", "drop", "inline values", "read") in names
    assert ("h", "h", "inline values", "write") in names
    located = {(c["node"], c["table"]): c["location"] for c in doc["credentials"]}
    assert located["h", "drop"] == "s3://bucket/drop"
    assert located["h", "h"] == "s3://bucket/marts/h"
    codes = {(f["code"], f["item"]) for f in doc["findings"]}
    assert ("scope", "b") in codes and ("inline_credentials", "c") in codes
    assert ("inline_credentials", "h") in codes

    # The pipeline, refreshed in this process.
    g = runpy.run_path(str(path))
    lineage = Lineage(lineage_url, api_key=Secret("env:SVLEAK_LINEAGE"))
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        for node in g["NODES"]:
            r = node.refresh(lineage=lineage)
            outputs[f"refresh {node.name}"] = f"{r}\n{r.summary()}\n{r.to_json()}\n{r.alert()}"
            outputs[f"report {node.name}"] = f"{node.report}\n{node.report.to_json()}"
            outputs[f"repr {node.name}"] = repr(node) + repr(node.credentials())
            outputs[f"substrait {node.name}"] = node.to_substrait()
            outputs[f"odcs {node.name}"] = odcs.dumps(odcs.export(node), "json")
            contract = node.sink.contract()
            outputs[f"contract {node.name}"] = "" if contract is None else contract.to_json()
            outputs[f"status {node.name}"] = str(node.status())
        for node in g["UNREFRESHED"]:
            outputs[f"report {node.name}"] = f"{node.report}\n{node.report.to_json()}"
            outputs[f"repr {node.name}"] = repr(node) + repr(node.credentials())
            outputs[f"odcs {node.name}"] = odcs.dumps(odcs.export(node), "json")
            outputs[f"lineage id {node.name}"] = repr(ol.dataset_id(node.sink))
        outputs["lineage ids"] = repr(ol.dataset_id(g["drop"]))
    outputs["warnings"] = "\n".join(str(w.message) for w in caught)
    assert g["saved"], "the function sink wrote"
    # The lineage server got the token as a header, and only there.
    assert _Lineage.seen and all(h == f"Bearer {SENTINELS['lineage']}" for h, _ in _Lineage.seen)
    outputs["lineage events"] = b"\n".join(body for _, body in _Lineage.seen)
    outputs["lineage repr"] = repr(lineage)

    # Every file the tables and catalogs left: Delta logs with their
    # contracts, Iceberg metadata and snapshot summaries, the catalog's
    # database, sverify's state.
    for f in root.rglob("*"):
        if f.is_file():
            outputs[f"file {f.relative_to(root)}"] = f.read_bytes()

    # A failed resolution, with its whole traceback.
    set_resolver(Resolver(backends={"leaky": _Leaky()}, default="leaky"))
    for ref in ("lake", "bao-thing"):
        try:
            Secret(ref).value()
        except SecretError as e:
            outputs[f"error {ref}"] = "".join(traceback.format_exception(e))
    set_resolver(None)

    # A positive control: the inline value is planted where the gate looks,
    # in the object a user built, so a writer that serialised it would leak.
    assert _found(pickle.dumps(g["orders_c"])) == ["inline"]

    outputs["printed"] = capsys.readouterr().out + capsys.readouterr().err
    outputs["logs"] = caplog.text
    leaks = {where: found for where, text in outputs.items() if (found := _found(text))}
    assert not leaks, f"secret values reached: {leaks}"
    # The cursor is in the table's own record, which resumes from it, and in
    # no report, document, event or export.
    carriers = [where for where, text in outputs.items() if _has(text, CURSOR)]
    assert carriers and "contract g" in carriers, carriers
    assert all(w.startswith(CURSOR_CARRIERS) for w in carriers), carriers
    assert len([k for k in outputs if k.startswith("file ")]) > 10


class _Leaky:
    def get(self, path):
        raise RuntimeError(f"backend echoed {SENTINELS['lake-key']}")


def test_the_gate_finds_a_planted_leak():
    """The grep itself works: a value in an output is found."""
    assert _found(f"x {SENTINELS['api']} y") == ["api"]
    assert _found(Path(__file__).read_text()) == []
