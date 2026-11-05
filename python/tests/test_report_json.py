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
    assert doc["format"] == report_json.FORMAT == 2
    assert doc["proved"] and doc["verdict"] == "proved"
    assert [
        (c["properties"]["label"], c["ruleId"], c["level"], c["kind"]) for c in doc["ensures"]
    ] == [
        ("(_.d >= 0)", "proved", "none", "pass"),
        ("unique(id)", "proved", "none", "pass"),
    ]
    assert doc["equivalence"]["text"] and "observation" not in doc
    assert doc["facts"]["d"] and doc["output"] == {"id": "int64", "d": "int64"}
    assert doc["not_null"] == report.not_null


def test_unproved_with_reasons_and_counterexample() -> None:
    report = sv.verify(
        orders.select("id", d=_.total - 5),
        requires={"orders": [_.total >= 0, _.total < 1000]},
        ensures=[_.d >= 0, sv.unique("id")],
    )
    doc = _round_trip(report)
    assert not doc["proved"]
    d, key = doc["ensures"]
    assert (d["ruleId"], d["level"], d["kind"]) == ("may_be_false", "error", "fail")
    assert d["message"]["text"].startswith("NOT proved")
    assert key["ruleId"] == "not_a_key"
    back = Report.from_json(json.dumps(doc))
    assert [c.reason for c in back.ensures] == ["may_be_false", "not_a_key"]
    if report.ensures[0].counterexample is not None:
        assert d["properties"]["counterexample"]["tables"]["orders"]


def test_needs_and_issues() -> None:
    """`on_inferred="error"`: what the proof needs, each with the runtime
    error it rules out; with `"warn"` the issue is assumed instead."""
    report = sv.verify(orders.select(r=_.total // _.qty), on_inferred="error")
    doc = _round_trip(report)
    assert {(n["column"], n["op"], n["code"]) for n in doc["needs"]} >= {
        ("qty", "<>", "_.qty != 0")
    }
    by_code = {n["code"]: n for n in doc["needs"]}
    issue = by_code["_.qty != 0"]["issue"]
    assert (issue["ruleId"], issue["level"]) == ("division_by_zero", "error")
    back = Report.from_json(json.dumps(doc))
    assert [n.code for n in back.needs] == [n.code for n in report.needs]

    summed = sv.verify(orders.aggregate(s=orders.total.sum()))
    doc = _round_trip(summed)
    assert [(i["ruleId"], i["level"], i["kind"]) for i in doc["assumed"]] == [
        ("sum_overflow", "note", "informational")
    ]
    assert doc["assumed"][0]["properties"]["assumption"]
    assert [i.kind for i in Report.from_json(doc).assumed] == ["SUM overflow"]


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
    assert r["semantics"] == "reference" and "profile" not in r
    assert Report.from_json(report.to_json()).routes["duckdb"].kind == r["kind"]


def test_tolerance_observation() -> None:
    report = sv.verify(
        orders.select("id", y=_.x * 2),
        requires={"orders": [_.x.between(-1000, 1000)]},
        ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
    )
    doc = _round_trip(report)
    assert doc["equivalence"]["components"]["floats"] == {"abs": 1e-6, "rel": None, "ulps": None}


def test_newer_format_refused_and_unknown_keys_ignored() -> None:
    doc = json.loads(sv.verify(orders.select("id"), requires=BOUNDED).to_json())
    with pytest.raises(ValueError, match="upgrade sverify"):
        Report.from_json({**doc, "format": 3})
    later = {**doc, "added_in_1_9": True}
    later["ensures"] = [
        {**c, "new_field": 1, "properties": {**c["properties"], "new": 2}} for c in doc["ensures"]
    ]
    assert json.loads(Report.from_json(later).to_json()) == doc


def test_ties() -> None:
    """One `ties` object: the places a tie is open and the keys that would
    close them, as `needed` objects."""
    w = ibis.window(group_by="qty", order_by="total")
    report = sv.verify(orders.select("id", r=ibis.row_number().over(w)), requires=BOUNDED)
    doc = _round_trip(report)
    assert not doc["deterministic"]
    assert [p["op"] for p in doc["ties"]["places"]] == ["window"]
    assert {(n["table"], n["label"]) for n in doc["ties"]["needs"]} == {
        (t, lab) for t, labs in report.ties.items() for lab in labs
    }
    assert "tie_places" not in doc and "hints" not in doc
