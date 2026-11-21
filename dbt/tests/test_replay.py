"""The replay of dbt packages' integration projects (#859, `sverify_dbt.replay`):
its ledgers, and how it records a project's tests."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from sverify_dbt import check, replay
from sverify_dbt.manifest import load


@pytest.fixture(scope="module")
def ledgers() -> dict[str, dict]:
    return {
        p.stem: json.loads(p.read_text())
        for p in sorted(replay.LEDGERS.glob("*.json"))
        if p.name != "constructs.json"
    }


def test_one_ledger_per_source(ledgers) -> None:
    assert set(ledgers) == set(replay.SOURCES)
    for name, led in ledgers.items():
        source = replay.SOURCES[name]
        assert (led["repo"], led["tag"], led["commit"], led["license"]) == (
            source.repo,
            source.tag,
            source.commit,
            source.license,
        )
        assert all("@" in p for p in led["packages"])


def test_no_proved_test_fails_in_dbt(ledgers) -> None:
    """A test sverify-dbt proves passes in dbt's own run of the project."""
    for name, led in ledgers.items():
        assert led["unsound"] == 0, name
        for key, r in led["results"].items():
            if r["outcome"] == "proved":
                assert r["dbt"] == "pass", f"{name}: {key}"


def test_summaries_count_the_results(ledgers) -> None:
    for led in ledgers.values():
        counts = {k: 0 for k in replay.OUTCOMES}
        for r in led["results"].values():
            counts[r["outcome"]] += 1
        assert led["summary"] == counts


def test_every_refusal_waits_on_an_issue_or_is_by_design(ledgers) -> None:
    for name, led in ledgers.items():
        for key, r in led["results"].items():
            if r["outcome"] in ("refused", "not checked"):
                assert r.get("issue") or r.get("design"), f"{name}: {key}: {r}"


def test_every_construct_entry_is_used(ledgers) -> None:
    reasons = [
        r.get("construct") or r.get("why") or ""
        for led in ledgers.values()
        for r in led["results"].values()
    ]
    for c in json.loads(replay.CONSTRUCTS.read_text())["constructs"]:
        assert any(c["match"] in x for x in reasons), c["match"]
        assert ("issue" in c) != ("design" in c), c


def test_records_name_every_test_and_flag_a_proof_dbt_contradicts(shop: Path) -> None:
    proj = load(shop)
    result = check(proj, counterexamples=0)
    records = replay._records(proj, result, {})
    assert len(records) == len(proj.tests)
    assert {r["outcome"] for r in records.values()} <= set(replay.OUTCOMES)
    proved = [
        uid
        for uid, t in proj.tests.items()
        if records[uid.split(".", 2)[-1]]["outcome"] == "proved"
    ]
    assert proved, "the shop proves some of its tests"
    failed = replay._records(proj, result, {proved[0]: "fail"})
    assert failed[proved[0].split(".", 2)[-1]].get("unsound") is True
    assert not any(r.get("unsound") for r in records.values())


def test_an_entry_waiting_on_a_closed_issue_is_found() -> None:
    ledgers = {
        "src": {
            "results": {
                "a": {"issue": 1, "outcome": "refused"},
                "b": {"issue": 1, "outcome": "refused"},
                "c": {"issue": 2, "outcome": "refused"},
                "d": {"design": "x", "outcome": "refused"},
            }
        }
    }
    states = {1: "CLOSED", 2: "OPEN"}
    assert replay.closed_issues(ledgers, states.get) == [
        "#1 is closed; 2 entries wait on it, such as src: a"
    ]
    assert replay.closed_issues(ledgers, lambda n: None) == []
