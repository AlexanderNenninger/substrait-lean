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
import uuid
import warnings
from pathlib import Path

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import openlineage as ol
from sverify.cli import main
from sverify.contracts import MaxRows, Unique
from sverify.errors import PreconditionError
from sverify.io import Changes, DeltaSink, StaticSource

# The wheel's tests install only what the Wheels workflow lists.
jsonschema = pytest.importorskip("jsonschema")
referencing = pytest.importorskip("referencing")

HERE = Path(__file__).parent
SPEC = HERE / "standards" / f"openlineage-{ol.CLIENT_VERSION}"
FACET = HERE.parent / "src" / "sverify" / "schemas" / "openlineage-contract-facet.schema.json"


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
    return [json.loads(line) for line in path.read_text().splitlines()]


def test_off_by_default(tmp_path, monkeypatch):
    monkeypatch.setenv("OPENLINEAGE_URL", "http://127.0.0.1:9")  # nothing listens
    n = orders().pipe(paid).write(DeltaSink(str(tmp_path / "paid")))
    with warnings.catch_warnings():
        warnings.simplefilter("error")
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
    assert c["format"] == 1 and c["node"] == "paid" and c["proved"] is True
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
    assert up.verified and up.why_unverified is None
    reqs = up.requires
    assert "amount > 10" in reqs
    assert any(isinstance(c, Unique) and c.cols == ("id",) for c in reqs)

    # A downstream pipeline, in another repository, assumes what upstream
    # proved and proves its own contract from it.
    @sv.transform(requires={"paid": reqs}, ensures=[_.doubled > 20, sv.unique("id")])
    def doubled(paid):
        return paid.select(paid.id, doubled=paid.amount * 2)

    assert doubled.check(paid=up.schema).proved


def test_an_unverifiable_facet_is_evidence(tmp_path):
    log, sink = _upstream(tmp_path)
    lines = events(log)
    facet = lines[-1]["outputs"][0]["facets"]["sverify_contract"]
    # No plan: nothing to prove again.
    del facet["substrait"]
    up = ol.read(lines).dataset(sink)
    assert not up.verified and up.requires == []
    assert "no plan" in (up.why_unverified or "")
    assert any("(_.amount > 10)" in a.assertion for a in up.evidence)
    # A claim the plan does not prove stays evidence too.
    lines = events(log)
    facet = lines[-1]["outputs"][0]["facets"]["sverify_contract"]
    facet["ensures"].append({"label": "amount > 500", "status": "proved", "sql": "amount > 500"})
    up = ol.read(lines).dataset(sink)
    assert up.verified and "amount > 500" not in up.requires
    assert any("amount > 500" in a.assertion for a in up.evidence)


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
    assert {(a.assertion, a.column, a.success) for a in up.evidence} == {
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


@pytest.mark.skipif(
    not MARQUEZ,
    reason="needs a Marquez server: SVERIFY_MARQUEZ_URL (scripts/marquez.sh starts one)",
)
def test_marquez_round_trip(tmp_path):
    """A refresh posts its events to Marquez, and a downstream job reads the
    dataset back from Marquez's API, with a verified contract."""
    assert MARQUEZ is not None
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
