"""`Report.to_json` and `Report.from_json` (#736): the report as a
versioned JSON document, in the format of `sverify/schemas/report.schema.json`.

Each report here goes to JSON, follows the schema, and comes back with the
same verdict and the same document. `tests/test_formats.py` reads the
reports each release wrote."""

from __future__ import annotations

import json
from pathlib import Path

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import report_json
from sverify.contracts import Report

jsonschema = pytest.importorskip("jsonschema")

SCHEMA = json.loads(
    (Path(sv.__file__).resolve().parent / "schemas" / "report.schema.json").read_text()
)

orders = ibis.table(
    {"id": "int64", "qty": "int64", "total": "int64", "x": "float64"}, name="orders"
)
BOUNDED = {"orders": [_.total >= 0, _.total < 1000, sv.unique("id")]}


def _round_trip(report: Report) -> dict:
    """The report's JSON, checked against the schema and read back."""
    text = report.to_json()
    doc = json.loads(text)
    jsonschema.validate(doc, SCHEMA)
    back = Report.from_json(text)
    assert back.proved == report.proved
    assert back.verdict == report.verdict
    assert json.loads(back.to_json()) == doc
    assert str(back.observation) == str(report.observation)
    return doc


def test_proved() -> None:
    report = sv.verify(
        orders.select("id", d=_.total * 2), requires=BOUNDED, ensures=[_.d >= 0, sv.unique("id")]
    )
    doc = _round_trip(report)
    assert doc["format"] == report_json.FORMAT == 1
    assert doc["proved"] and doc["verdict"] == "proved"
    assert [(c["label"], c["proved"], c["reason"]) for c in doc["ensures"]] == [
        ("(_.d >= 0)", True, None),
        ("unique(id)", True, None),
    ]
    assert doc["facts"]["d"] and doc["output"] == {"id": "int64", "d": "int64"}


def test_unproved_with_reasons_and_counterexample() -> None:
    report = sv.verify(
        orders.select("id", d=_.total - 5),
        requires={"orders": [_.total >= 0, _.total < 1000]},
        ensures=[_.d >= 0, sv.unique("id")],
    )
    doc = _round_trip(report)
    assert not doc["proved"]
    d, key = doc["ensures"]
    assert d["reason"] == "may_be_false" and d["message"].startswith("NOT proved")
    assert key["reason"] == "not_a_key"
    back = Report.from_json(json.dumps(doc))
    assert [c.reason for c in back.ensures] == ["may_be_false", "not_a_key"]
    if report.ensures[0].counterexample is not None:
        assert d["counterexample"]["tables"]["orders"]


def test_needs_and_issues() -> None:
    """`on_inferred="error"`: what the proof needs, each with the runtime
    error it rules out; with `"warn"` the issue is assumed instead."""
    report = sv.verify(orders.select(r=_.total // _.qty), on_inferred="error")
    doc = _round_trip(report)
    assert {(n["column"], n["op"], n["code"]) for n in doc["needs"]} >= {
        ("qty", "<>", "_.qty != 0")
    }
    by_code = {n["code"]: n for n in doc["needs"]}
    assert by_code["_.qty != 0"]["issue"]["kind"] == "division by zero"
    back = Report.from_json(json.dumps(doc))
    assert [n.code for n in back.needs] == [n.code for n in report.needs]

    summed = sv.verify(orders.aggregate(s=orders.total.sum()))
    doc = _round_trip(summed)
    assert [i["kind"] for i in doc["assumed"]] == ["SUM overflow"]
    assert doc["assumed"][0]["assumption"]


def test_routes_after_a_run() -> None:
    """A report whose plan ran names the route, its class and evidence."""
    report = sv.verify(orders.select("id", d=_.total * 2), requires=BOUNDED)
    con = sv.connect()
    con.put(
        "orders",
        pa.table({"id": [1, 2], "qty": [1, 1], "total": [3, 4], "x": [0.5, 1.5]}),
    )
    report.run(con)
    doc = _round_trip(report)
    assert set(doc["routes"]) == {"duckdb"}
    r = doc["routes"]["duckdb"]
    assert r["kind"] and r["class"] == "exact" and r["reason"]
    assert Report.from_json(report.to_json()).routes["duckdb"].kind == r["kind"]


def test_tolerance_observation() -> None:
    report = sv.verify(
        orders.select("id", y=_.x * 2),
        requires={"orders": [_.x.between(-1000, 1000)]},
        ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
    )
    doc = _round_trip(report)
    assert doc["observation"]["components"]["floats"] == {"abs": 1e-6, "rel": None, "ulps": None}


def test_newer_format_refused_and_unknown_keys_ignored() -> None:
    doc = json.loads(sv.verify(orders.select("id"), requires=BOUNDED).to_json())
    with pytest.raises(ValueError, match="upgrade sverify"):
        Report.from_json({**doc, "format": 2})
    later = {**doc, "added_in_1_9": True}
    later["ensures"] = [{**c, "new_field": 1} for c in doc["ensures"]]
    assert json.loads(Report.from_json(later).to_json()) == doc
