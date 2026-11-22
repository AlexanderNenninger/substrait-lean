"""OpenLineage (#792): run events from `refresh`, valid against the spec of
the pinned client (`tests/standards/openlineage-1.55.0/`), with column
lineage from the plan and the `sverify_contract` facet; and events read
back, where only a facet sverify proves again becomes `requires`."""

from __future__ import annotations

import json
import os
import textwrap
import time
import urllib.error
import urllib.request
import uuid
import warnings
from pathlib import Path

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from _repo import ROOT, needs_repo
from sverify import openlineage as ol
from sverify.cli import main
from sverify.conditions import MaxRows, Unique
from sverify.errors import PreconditionError
from sverify.io import Changes, DeltaSink, StaticSource

# The wheel's tests install only what the Wheels workflow lists.
jsonschema = pytest.importorskip("jsonschema")
referencing = pytest.importorskip("referencing")

HERE = Path(__file__).parent
SPEC = HERE / "standards" / f"openlineage-{ol.CLIENT_VERSION}"
FACET = HERE.parent / "src" / "sverify" / "schemas" / "openlineage-contract-facet.schema.json"


@needs_repo
def test_the_client_version_is_the_extras_floor():
    """`CLIENT_VERSION` is in no output; the `openlineage` extra's pin, which
    a user reads from the installed metadata, carries it."""
    import tomllib

    extras = tomllib.loads((ROOT / "python" / "pyproject.toml").read_text())
    pin = extras["project"]["optional-dependencies"]["openlineage"]
    assert f"openlineage-python>={ol.CLIENT_VERSION}," in pin[0]


def _registry() -> referencing.Registry:
    docs = [json.loads((SPEC / "OpenLineage.json").read_text())]
    docs += [json.loads(p.read_text()) for p in sorted((SPEC / "facets").glob("*.json"))]
    docs.append(json.loads(FACET.read_text()))
    resources = ((d["$id"], referencing.Resource.from_contents(d)) for d in docs)
    return referencing.Registry().with_resources(resources)


REGISTRY = _registry()


def _check(instance: dict, ref: str) -> None:
    jsonschema.Draft202012Validator({"$ref": ref}, registry=REGISTRY).validate(instance)


def valid(event: dict) -> dict:
    """`event` against the spec's RunEvent, and each facet against its own
    schema (`_schemaURL`), the `sverify_contract` facet included."""
    assert ol.SPEC_VERSION in event["schemaURL"]
    _check(event, f"https://openlineage.io/spec/{ol.SPEC_VERSION}/OpenLineage.json#/$defs/RunEvent")
    facets = [*event["run"].get("facets", {}).values(), *event["job"].get("facets", {}).values()]
    for d in event.get("inputs", []) + event.get("outputs", []):
        for key in ("facets", "inputFacets", "outputFacets"):
            facets += d.get(key, {}).values()
    for f in facets:
        url = f["_schemaURL"]
        _check(f, url if "#" in url else url)
    return event


def orders(name: str = "orders") -> StaticSource:
    return StaticSource(
        pa.table({"id": [1, 2, 3], "cust": [10, 20, 10], "amount": [30, 5, 50]}), name=name
    )


def customers() -> StaticSource:
    return StaticSource(pa.table({"id": [10, 20], "region": ["eu", "us"]}), name="customers")


REQUIRES = [_.amount >= 0, _.amount < 1000, sv.key("id"), _.cust.notnull()]


@sv.transform(requires={"orders": REQUIRES}, ensures=[_.amount > 10, _.amount < 1000, sv.key("id")])
def paid(orders):
    """Paid orders over ten."""
    return orders.filter(orders.amount > 10)


@sv.transform(
    requires={
        "orders": REQUIRES,
        "customers": [sv.key("id"), _.region.notnull()],
    },
    ensures=[sv.key("region"), _.total >= 0],
)
def revenue(orders, customers):
    j = orders.join(customers, orders.cust == customers.id)
    return j.group_by("region").agg(total=j.amount.sum())


def events(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


def test_off_by_default(tmp_path, monkeypatch):
    monkeypatch.setenv("OPENLINEAGE_URL", "http://127.0.0.1:9")  # nothing listens
    n = orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    with warnings.catch_warnings():
        # A failed emit is what this test is about; the engine-version warning of an unprobed
        # DuckDB (#2045) is not.
        warnings.simplefilter("error", ol.LineageWarning)
        n.refresh()


def test_refresh_emits_start_and_complete(tmp_path):
    log = tmp_path / "events.jsonl"
    lake = tmp_path / "lake"
    p = orders().pipe(paid).write(DeltaSink(str(lake / "paid")))
    (write,) = p.refresh(lineage=ol.Lineage(log, namespace="shop")).writes
    start, done = events(log)
    for e in (start, done):
        valid(e)
    assert [start["eventType"], done["eventType"]] == ["START", "COMPLETE"]
    assert start["run"]["runId"] == done["run"]["runId"]
    assert done["job"]["namespace"] == "shop" and done["job"]["name"] == "paid"
    (src,) = done["inputs"]
    assert (src["namespace"], src["name"]) == ("sverify", "orders")
    assert src["facets"]["version"]["datasetVersion"] == str(p.versions["orders"])
    asserts = src["inputFacets"]["dataQualityAssertions"]["assertions"]
    assert {a["assertion"] for a in asserts} >= {"(_.amount >= 0)", "unique(id)"}
    assert all(a["success"] for a in asserts)
    (out,) = done["outputs"]
    assert (out["namespace"], out["name"]) == ("file", str((lake / "paid").resolve()))
    facets = out["facets"]
    assert [f["name"] for f in facets["schema"]["fields"]] == ["id", "cust", "amount"]
    assert facets["version"]["datasetVersion"] == str(write.version)
    assert out["outputFacets"]["outputStatistics"]["rowCount"] == 2
    c = facets["sverify_contract"]
    assert c["format"] == 3 and c["node"] == "paid" and c["proved"] is True
    assert c["_schemaURL"] == ol.FACET_SCHEMA_URL
    assert {e["label"]: e["status"] for e in c["ensures"]} == {
        "(_.amount > 10)": "proved",
        "(_.amount < 1000)": "proved",
        "unique(id)": "proved",
        '"id" IS NOT NULL': "proved",
    }
    assert c["route"]["engine"] == "duckdb" and c["outcome"] == "ok" and c["quarantined"] == 0
    assert "substrait" in c
    # Column lineage: each column is its input's, the filter reads amount.
    cl = facets["columnLineage"]
    assert cl["fields"]["amount"]["inputFields"] == [
        {
            "namespace": "sverify",
            "name": "orders",
            "field": "amount",
            "transformations": [{"type": "DIRECT", "subtype": "IDENTITY"}],
        }
    ]
    assert [(d["field"], d["transformations"]) for d in cl["dataset"]] == [
        ("amount", [{"type": "INDIRECT", "subtype": "FILTER"}])
    ]


def test_column_lineage_of_a_join_and_an_aggregate(tmp_path):
    log = tmp_path / "events.jsonl"
    r = revenue(orders(), customers()).write(DeltaSink(str(tmp_path / "revenue")))
    r.refresh(lineage=ol.Lineage(log))
    done = valid(events(log)[-1])
    cl = done["outputs"][0]["facets"]["columnLineage"]

    def ins(col: str) -> list[tuple]:
        return [
            (f["name"], f["field"], [t["subtype"] for t in f["transformations"]])
            for f in cl["fields"][col]["inputFields"]
        ]

    assert ins("region") == [("customers", "region", ["IDENTITY"])]
    assert ins("total") == [("orders", "amount", ["AGGREGATION"])]
    whole = {
        (d["name"], d["field"]): [t["subtype"] for t in d["transformations"]] for d in cl["dataset"]
    }
    assert whole == {
        ("customers", "id"): ["JOIN"],
        ("customers", "region"): ["GROUP_BY"],
        ("orders", "cust"): ["JOIN"],
    }
    assert {d["name"] for d in done["inputs"]} == {"orders", "customers"}


def test_column_lineage_of_sorts_and_windows():
    import ibis

    t = ibis.table({"k": "string", "ts": "int64", "v": "int64"}, name="t")
    w = ibis.window(group_by=t.k, order_by=t.ts)
    expr = t.select(t.k, run=t.v.sum().over(w)).order_by("k")
    facet = ol.column_lineage(expr, {"t": ("ns", "t")})
    assert facet is not None
    assert [f["field"] for f in facet["fields"]["run"]["inputFields"]] == ["v"]
    whole = {d["field"]: [t["subtype"] for t in d["transformations"]] for d in facet["dataset"]}
    assert whole == {"k": ["SORT", "WINDOW"], "ts": ["WINDOW"]}


def test_a_failure_fails_the_run_and_aborts_the_rest(tmp_path):
    log = tmp_path / "events.jsonl"
    bad = StaticSource(pa.table({"id": [1, 1], "cust": [1, 1], "amount": [30, 40]}), name="orders")
    p = bad.pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    with pytest.raises(PreconditionError):
        p.refresh(lineage=ol.Lineage(log))
    start, fail = (valid(e) for e in events(log))
    assert [start["eventType"], fail["eventType"]] == ["START", "FAIL"]
    assert "PreconditionError" in fail["run"]["facets"]["errorMessage"]["message"]


def test_a_library_error_sends_its_type_and_the_trace_only_when_asked(tmp_path, monkeypatch):
    """Another library's error text can name a bucket, an endpoint or a
    catalog URI, and a trace the paths of the machine: neither reaches the
    lineage server unless `trace=True` (#887)."""
    leak = "s3://svfake-user:svfake-password@bucket/raw"

    def broken(self, change):
        raise RuntimeError(f"cannot reach {leak}")

    monkeypatch.setattr(DeltaSink, "write", broken)
    for trace in (False, True):
        log = tmp_path / f"events-{trace}.jsonl"
        p = orders().pipe(paid).write(DeltaSink(str(tmp_path / f"paid-{trace}")))
        with pytest.raises(RuntimeError):
            p.refresh(lineage=ol.Lineage(log, trace=trace))
        (fail,) = (valid(e) for e in events(log) if e["eventType"] == "FAIL")
        facet = fail["run"]["facets"]["errorMessage"]
        assert facet["message"] == "RuntimeError"
        assert ("stackTrace" in facet) is trace
        assert (leak in log.read_text()) is trace


def test_recorded_uris_carry_no_userinfo():
    """A URI with credentials in it is recorded without them (#887)."""
    sink = DeltaSink("s3://AKIAFAKE:svfake-secret@bucket/marts/paid?versionId=1#x")
    assert sink.location == "s3://bucket/marts/paid"
    assert sink.name == "paid"
    assert ol.dataset_id(sink) == ("s3://bucket", "marts/paid")
    lineage = ol.Lineage("https://svfake:svfake-secret@marquez.example/api?key=svfake-key")
    assert "svfake" not in repr(lineage) and "marquez.example/api" in repr(lineage)


def test_the_plan_parts_are_built_once_per_node(tmp_path, monkeypatch):
    """The contract, its Substrait export and the column lineage change only
    with the plan: later refreshes reuse them."""
    calls = []
    export = ol._export
    monkeypatch.setattr(ol, "_export", lambda r: calls.append(r) or export(r))
    src = orders()
    p = src.pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    log = tmp_path / "events.jsonl"
    lineage = ol.Lineage(log)
    p.refresh(lineage=lineage)
    src.apply(Changes(inserts=[(4, 10, 70)]))
    p.refresh(lineage=lineage)
    assert len(calls) == 1
    first, second = (e for e in events(log) if e["eventType"] == "COMPLETE")
    c1, c2 = (e["outputs"][0]["facets"]["sverify_contract"] for e in (first, second))
    assert c1["substrait"] == c2["substrait"] and c1["ensures"] == c2["ensures"]


def test_a_dead_target_warns_and_the_refresh_goes_on(tmp_path):
    p = orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    with pytest.warns(ol.LineageWarning, match="not sent"):
        result = p.refresh(lineage=ol.Lineage("http://127.0.0.1:9", timeout=0.5))
    assert result.writes[0].mode == "created"


def test_disabled_by_the_standard_variable(tmp_path, monkeypatch):
    monkeypatch.setenv("OPENLINEAGE_DISABLED", "true")
    log = tmp_path / "events.jsonl"
    orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid"))).refresh(lineage=log)
    assert not log.exists()


def test_console_target(tmp_path, capsys):
    orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid"))).refresh(lineage="console")
    lines = [json.loads(x) for x in capsys.readouterr().out.splitlines()]
    assert [e["eventType"] for e in lines] == ["START", "COMPLETE"]


def test_the_client_transport(tmp_path, monkeypatch):
    pytest.importorskip("openlineage.client")
    monkeypatch.delenv("OPENLINEAGE_URL", raising=False)
    monkeypatch.setenv("OPENLINEAGE__TRANSPORT__TYPE", "file")
    monkeypatch.setenv("OPENLINEAGE__TRANSPORT__LOG_FILE_PATH", str(tmp_path / "ol.jsonl"))
    monkeypatch.setenv("OPENLINEAGE__TRANSPORT__APPEND", "true")
    orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid"))).refresh(lineage=True)
    got = [valid(e) for e in events(tmp_path / "ol.jsonl")]
    assert [e["eventType"] for e in got] == ["START", "COMPLETE"]


# -- reading ----------------------------------------------------------------------


def _upstream(tmp_path: Path) -> tuple[Path, DeltaSink]:
    log = tmp_path / "events.jsonl"
    sink = DeltaSink(str(tmp_path / "paid"))
    orders().pipe(paid).write(sink).refresh(lineage=ol.Lineage(log, namespace="upstream"))
    return log, sink


def _written(log: Path) -> str:
    return events(log)[-1]["outputs"][0]["facets"]["version"]["datasetVersion"]


def test_a_verified_facet_becomes_requires(tmp_path):
    log, sink = _upstream(tmp_path)
    up = ol.read(log).dataset(sink)
    assert up.producer["job"] == "upstream/paid"
    assert [f["name"] for f in up.fields] == ["id", "cust", "amount"]
    assert str(up.schema["amount"]) == "int64" and up.version == _written(log)
    assert up.verified and up.why is None
    reqs = up.requires
    assert "amount > 10" in reqs
    assert any(isinstance(c, Unique) and c.cols == ("id",) for c in reqs)

    # A downstream pipeline, in another repository, assumes what upstream
    # proved and proves its own contract from it.
    @sv.transform(requires={"paid": reqs}, ensures=[_.doubled > 20, sv.unique("id")])
    def doubled(paid):
        return paid.select(paid.id, doubled=paid.amount * 2)

    assert doubled.verify(paid=up.schema).verdict == sv.Verdict.PROVED


def test_an_unverifiable_facet_is_evidence(tmp_path):
    log, sink = _upstream(tmp_path)
    lines = events(log)
    facet = lines[-1]["outputs"][0]["facets"]["sverify_contract"]
    # No plan: nothing to prove again.
    del facet["substrait"]
    up = ol.read(lines).dataset(sink)
    assert not up.verified and up.requires == []
    assert "no plan" in (up.why or "")
    assert any("(_.amount > 10)" in a.assertion for a in up.assertions)
    # A claim the plan does not prove stays evidence too.
    lines = events(log)
    facet = lines[-1]["outputs"][0]["facets"]["sverify_contract"]
    facet["ensures"].append({"label": "amount > 500", "status": "proved", "sql": "amount > 500"})
    up = ol.read(lines).dataset(sink)
    assert up.verified and "amount > 500" not in up.requires
    assert any("amount > 500" in a.assertion for a in up.assertions)


def test_read_other_tools_events():
    """A dbt run's events, in the shape openlineage-dbt emits them (a model run,
    then its tests): the schema and the assertions are read, and the
    assertions are evidence, never `requires`."""
    up = ol.read(HERE / "standards" / "dbt-run-events.jsonl").dataset(
        "postgres://warehouse:5432", "analytics.public.orders"
    )
    assert up.producer["job"] == "dbt-prod/analytics.orders"
    assert str(up.schema["order_id"]) == "int32" and str(up.schema["status"]) == "string"
    assert up.contract is None and up.requires == [] and not up.verified
    assert {(a.assertion, a.column, a.success) for a in up.assertions} == {
        ("not_null", "order_id", True),
        ("unique", "order_id", True),
        ("accepted_values", "status", False),
    }


def test_max_rows_in_the_facet(tmp_path):
    @sv.transform(requires={"orders": [*REQUIRES, sv.max_rows(100)]}, ensures=[sv.max_rows(100)])
    def capped(orders):
        return orders.filter(orders.amount > 10)

    log = tmp_path / "events.jsonl"
    sink = DeltaSink(str(tmp_path / "capped"))
    orders().pipe(capped).write(sink).refresh(lineage=log)
    up = ol.read(log).dataset(sink)
    assert any(isinstance(c, MaxRows) and c.n == 100 for c in up.requires)


def test_cli_refresh_lineage(tmp_path):
    path = tmp_path / "pipe.py"
    lake = tmp_path / "lake"
    path.write_text(
        textwrap.dedent(
            f"""
            import pyarrow as pa
            import sverify as sv
            from ibis import _
            from sverify.io import DeltaSink, StaticSource

            orders = StaticSource(pa.table({{"id": [1, 2], "amount": [30, 5]}}), name="orders")

            @sv.transform(
                requires={{"orders": [_.amount >= 0, _.amount < 1000, sv.key("id")]}},
                ensures=[_.amount > 10, sv.key("id")],
            )
            def paid(orders):
                return orders.filter(orders.amount > 10)

            p = orders.pipe(paid).write(DeltaSink({str(lake / "paid")!r}))
            """
        )
    )
    log = tmp_path / "events.jsonl"
    assert main(["refresh", f"{path}:p", "--lineage", str(log)]) == 0
    assert [valid(e)["eventType"] for e in events(log)] == ["START", "COMPLETE"]


MARQUEZ = os.environ.get("SVERIFY_MARQUEZ_URL")


def _marquez_get(path: str):
    assert MARQUEZ is not None
    with urllib.request.urlopen(MARQUEZ.rstrip("/") + path, timeout=10) as resp:  # noqa: S310
        return json.loads(resp.read())


@pytest.mark.skipif(
    not MARQUEZ and not os.environ.get("SVERIFY_MARQUEZ_REQUIRED"),
    reason="needs a Marquez server: SVERIFY_MARQUEZ_URL (scripts/marquez.sh starts one)",
)
def test_marquez_round_trip(tmp_path):
    """A refresh posts its events to Marquez, and a downstream job reads the
    dataset back from Marquez's API, with a verified contract."""
    # CI's `marquez` job sets SVERIFY_MARQUEZ_REQUIRED: a missing server fails.
    assert MARQUEZ, "SVERIFY_MARQUEZ_URL is not set"
    namespace = f"sverify-test-{uuid.uuid4().hex[:8]}"
    sink = DeltaSink(str(tmp_path / "paid"))
    with warnings.catch_warnings():
        warnings.simplefilter("error", ol.LineageWarning)
        orders().pipe(paid).write(sink).refresh(lineage=ol.Lineage(MARQUEZ, namespace=namespace))
    ns, name = ol.dataset_id(sink)
    up = None
    for _attempt in range(50):  # Marquez writes the event asynchronously
        try:
            up = ol.marquez(MARQUEZ, ns, name)
        except urllib.error.HTTPError:
            time.sleep(0.2)
            continue
        if up.contract is not None:
            break
        time.sleep(0.2)
    assert up is not None and up.contract is not None
    assert [f["name"] for f in up.fields] == ["id", "cust", "amount"]
    assert up.producer["job"] == f"{namespace}/paid"
    assert up.verified and "amount > 10" in up.requires

    # The lineage graph Marquez shows: the job, its input and output datasets,
    # and the run that completed.
    job = None
    for _attempt in range(50):
        try:
            job = _marquez_get(f"/api/v1/namespaces/{namespace}/jobs/paid")
        except urllib.error.HTTPError:
            job = None
        if job and job.get("outputs") and (job.get("latestRun") or {}).get("state") == "COMPLETED":
            break
        time.sleep(0.2)
    assert job is not None
    assert [d["name"] for d in job["outputs"]] == [name]
    assert [d["name"] for d in job["inputs"]] == [ol.dataset_id(orders())[1]]
    assert job["latestRun"]["state"] == "COMPLETED"
    assert job["latestRun"]["id"] == up.producer["run"]


# -- reading files, types and names (#750) ------------------------------------------


def _event(version: str = "3") -> dict:
    return {
        "eventType": "COMPLETE",
        "producer": "https://example/producer",
        "job": {"namespace": "n", "name": "j"},
        "run": {"runId": "r1"},
        "outputs": [
            {
                "namespace": "file",
                "name": "/lake/t",
                "facets": {
                    "schema": {"fields": [{"name": "a", "type": "long"}]},
                    "version": {"datasetVersion": version},
                },
            }
        ],
    }


def test_read_takes_json_lines_a_list_or_one_event(tmp_path):
    one, two = _event("1"), _event("2")
    files = {
        "lines.jsonl": json.dumps(one) + "\n\n" + json.dumps(two) + "\n",
        "list.json": json.dumps([one, two], indent=2),
        "one_line.json": json.dumps(two),
        # #2447: one event over several lines, as `jq .` writes it.
        "indented.json": json.dumps(two, indent=2),
    }
    for name, text in files.items():
        (tmp_path / name).write_text(text)
        got = ol.read(tmp_path / name)
        assert got.dataset("file", "/lake/t").version == "2", name
        assert len(got) == (1 if name in ("one_line.json", "indented.json") else 2), name
    assert len(ol.read([one, two])) == 2
    (tmp_path / "bad.json").write_text("{not json\n")
    with pytest.raises(json.JSONDecodeError):
        ol.read(tmp_path / "bad.json")


@pytest.mark.parametrize(
    ("name", "ibis_type"),
    [
        ("long", "int64"),
        ("INTEGER", "int32"),
        ("int", "int32"),
        ("short", "int16"),
        ("float", "float32"),
        ("double", "float64"),
        ("timestamp", "timestamp('UTC')"),
        ("timestamp_ntz", "timestamp"),
        ("VARCHAR", "string"),
        ("DECIMAL(10,2)", "decimal(10, 2)"),
        ("array<string>", "array<string>"),
        ("no such type", "unknown"),
        (None, "unknown"),
        (3, "unknown"),
    ],
)
def test_a_schema_facets_type_names(name, ibis_type):
    """Spark's names first, then DuckDB's, then Ibis's; anything else is unknown."""
    got = ol._ibis_type(name)
    assert got.is_unknown() if ibis_type == "unknown" else str(got) == ibis_type


def test_dataset_names_follow_the_naming_conventions(tmp_path, monkeypatch):
    class Iceberg:
        def __init__(self, identifier, catalog):
            self.identifier, self.catalog = identifier, catalog

    catalog = type("Catalog", (), {"name": "lake"})()
    assert ol.dataset_id(Iceberg(("db", "t"), catalog)) == ("iceberg://lake", "db.t")
    assert ol.dataset_id(Iceberg("db.t", object())) == ("iceberg://catalog", "db.t")
    monkeypatch.chdir(tmp_path)
    local = type("Local", (), {"uri": "data/t", "name": "t"})()
    assert ol.dataset_id(local) == ("file", str((tmp_path / "data" / "t").resolve()))
    file_uri = type("F", (), {"uri": f"file://{tmp_path}/t", "name": "t"})()
    assert ol.dataset_id(file_uri) == ("file", str((tmp_path / "t").resolve()))
    gcs = type("G", (), {"location": "gs://bucket/a/b", "name": "b"})()
    assert ol.dataset_id(gcs) == ("gs://bucket", "a/b")
    assert ol.dataset_id(type("N", (), {"name": "orders"})()) == ("sverify", "orders")


# -- an HTTP target and a Marquez API, served here -----------------------------------


class _Marquez:
    """What a Marquez server answers, and what it was sent."""

    def __init__(self, dataset: dict, versions: dict | None):
        from http.server import BaseHTTPRequestHandler, HTTPServer
        from threading import Thread

        self.got: list[tuple[str, str, str | None, dict | None]] = []
        outer = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, format, *args):  # noqa: A002 - the parent's name
                pass

            def _send(self, code, body):
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.end_headers()
                self.wfile.write(json.dumps(body).encode())

            def do_GET(self):
                outer.got.append(("GET", self.path, self.headers.get("Authorization"), None))
                if self.path.endswith("/versions?limit=1"):
                    if versions is None:
                        return self._send(500, {})
                    return self._send(200, versions)
                return self._send(200, dataset)

            def do_POST(self):
                body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                outer.got.append(("POST", self.path, self.headers.get("Authorization"), body))
                return self._send(201, {})

        self.server = HTTPServer(("127.0.0.1", 0), Handler)
        Thread(target=self.server.serve_forever, daemon=True).start()
        self.url = f"http://127.0.0.1:{self.server.server_port}"

    def close(self):
        self.server.shutdown()


@pytest.fixture
def marquez_server():
    servers = []

    def start(dataset=None, versions=None):
        s = _Marquez(dataset or {}, versions)
        servers.append(s)
        return s

    yield start
    for s in servers:
        s.close()


def test_an_http_target_posts_each_event_with_its_bearer_token(
    tmp_path, monkeypatch, marquez_server
):
    from sverify.io import Secret

    server = marquez_server()
    monkeypatch.setenv("SV_TEST_LINEAGE_TOKEN", "sv-test-token")
    p = orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    p.refresh(lineage=ol.Lineage(server.url + "/", api_key=Secret("env:SV_TEST_LINEAGE_TOKEN")))
    assert [(m, path, auth) for m, path, auth, _ in server.got] == [
        ("POST", "/api/v1/lineage", "Bearer sv-test-token")
    ] * 2
    assert [b["eventType"] for *_, b in server.got] == ["START", "COMPLETE"]
    # OPENLINEAGE_API_KEY when no key is given, and no header without either.
    monkeypatch.setenv("OPENLINEAGE_API_KEY", "sv-test-env-token")
    ol.Lineage(server.url).emit({"job": {"name": "x"}})
    monkeypatch.delenv("OPENLINEAGE_API_KEY")
    ol.Lineage(server.url).emit({"job": {"name": "x"}})
    assert [auth for _, _, auth, _ in server.got[2:]] == ["Bearer sv-test-env-token", None]


def test_marquez_reads_a_dataset_its_version_and_its_writer(marquez_server, monkeypatch):
    dataset = {
        "fields": [{"name": "id", "type": "BIGINT"}, {"name": "amount"}],
        "facets": {
            "version": {"datasetVersion": "7"},
            "sverify_contract": {"_producer": "https://example/sverify", "ensures": []},
            "dataQualityAssertions": {
                "assertions": [{"assertion": "not_null", "success": True, "column": "id"}]
            },
        },
    }
    versions = {
        "versions": [
            {
                "createdByRun": {
                    "id": "run-7",
                    "jobVersion": {"namespace": "upstream", "name": "paid"},
                }
            }
        ]
    }
    server = marquez_server(dataset, versions)
    monkeypatch.setenv("OPENLINEAGE_API_KEY", "sv-test-token")
    up = ol.marquez(server.url, "s3://bucket", "marts/paid")
    # The namespace and name are one path segment each.
    assert server.got[0][1] == "/api/v1/namespaces/s3%3A%2F%2Fbucket/datasets/marts%2Fpaid"
    assert server.got[0][2] == "Bearer sv-test-token"
    assert up.fields == [{"name": "id", "type": "BIGINT"}, {"name": "amount", "type": None}]
    assert str(up.schema["amount"]) == "unknown" and up.version == "7"
    assert up.producer == {
        "job": "upstream/paid",
        "run": "run-7",
        "producer": "https://example/sverify",
    }
    assert [(a.assertion, a.column, a.job) for a in up.assertions] == [
        ("not_null", "id", "upstream/paid")
    ]
    # No plan in the facet: evidence only.
    assert not up.verified and "no plan" in (up.why or "")


def test_marquez_without_versions_or_fields(marquez_server):
    """The producer is a courtesy: a versions endpoint that fails leaves it
    empty. Without `fields`, the schema facet's fields are read."""
    dataset = {"facets": {"schema": {"fields": [{"name": "a", "type": "long"}]}}}
    server = marquez_server(dataset, None)
    up = ol.marquez(server.url, "n", "t", api_key="sv-test-token")
    assert up.producer == {} and up.contract is None and up.version is None
    assert str(up.schema["a"]) == "int64"
    assert server.got[0][2] == "Bearer sv-test-token"


def test_a_facet_whose_plan_the_checker_rejects_is_evidence(tmp_path):
    log, sink = _upstream(tmp_path)
    lines = events(log)
    facet = lines[-1]["outputs"][0]["facets"]["sverify_contract"]
    facet["substrait"] = {"relations": "not a plan"}
    up = ol.read(lines).dataset(sink)
    assert not up.verified and up.requires == []
    assert (up.why or "").startswith("the checker rejects the exported plan")
    assert any("(_.amount > 10)" in a.assertion for a in up.assertions)
    # A not_null claim is evidence too.
    assert any(a.assertion.endswith("not_null (proved)") for a in up.assertions)


def test_runs_are_off_without_lineage(tmp_path):
    assert ol.runs(None, []) is None and ol.runs(False, []) is None
    log = tmp_path / "events.jsonl"
    r = ol.runs(str(log), [])
    assert r is not None and isinstance(r.lineage._transport, ol._File)
