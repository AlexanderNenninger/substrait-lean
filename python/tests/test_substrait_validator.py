"""The ledger of `substrait-validator` over every plan `to_substrait` exports
(#862, `sverify_dev.substrait_validator`).

The validator runs in an interpreter of its own (its Substrait bindings
cannot share a process with sverify's), which CI's `evidence` job builds;
these tests read the ledger it writes, and compare a fresh run with it where
`SUBSTRAIT_VALIDATOR_PYTHON` names that interpreter."""

from __future__ import annotations

import collections
import json
import os
import re

import pytest

from _repo import needs_repo
from sverify_dev import substrait_validator as gate

pytestmark = needs_repo

ROOT = gate.ROOT
OUTCOMES = {"agree", "disagree", "refused", "skipped"}


@pytest.fixture(scope="module")
def ledger() -> dict:
    return json.loads(gate.LEDGER.read_text())


def test_summary_counts_the_results(ledger) -> None:
    counts = collections.Counter(r["outcome"] for r in ledger["results"].values())
    assert set(counts) <= OUTCOMES
    assert ledger["summary"] == dict(sorted(counts.items()))


def test_every_disagreement_is_a_listed_finding(ledger) -> None:
    for key, r in ledger["results"].items():
        if r["outcome"] == "disagree":
            assert r["findings"], key
            assert set(r["findings"]) <= set(ledger["findings"]), key
        else:
            assert "findings" not in r, key


def test_every_finding_names_its_record(ledger) -> None:
    """A finding is the validator's or the spec's (an `ST-n` record of
    `upstream/bugs/`) or sverify's (an issue of the fix)."""
    for f, e in ledger["findings"].items():
        record = e["record"]
        assert record, f"finding without a record: {f}"
        if m := re.fullmatch(r"ST-\d+", record):
            assert (ROOT / "upstream" / "bugs" / f"{m[0]}.json").exists(), record
        else:
            assert re.fullmatch(r"#\d+", record), record


def test_the_validator_and_the_version_are_pinned(ledger) -> None:
    from sverify.substrait_export import SUBSTRAIT_VERSION

    assert ledger["validator"]["commit"] == gate.COMMIT
    assert ledger["sverify_substrait"] == ".".join(map(str, SUBSTRAIT_VERSION))


def test_normalize_keeps_the_cause_and_drops_the_plan() -> None:
    a = gate.normalize("no impl of lag takes (precision_timestamp<6>, i64)")
    b = gate.normalize("no impl of lag takes (precision_timestamp<9>, i64)")
    assert a == b and "lag" in a


@pytest.mark.slow
@pytest.mark.skipif(
    not os.environ.get("SUBSTRAIT_VALIDATOR_PYTHON"),
    reason="needs substrait-validator's interpreter (CI's evidence job builds it)",
)
def test_a_fresh_run_matches_the_ledger(ledger) -> None:
    fresh = gate.ledger(os.environ["SUBSTRAIT_VALIDATOR_PYTHON"])
    assert gate.problems(fresh, ledger)[0] == []


def test_drift_prints_and_a_lost_validation_fails(ledger) -> None:
    import copy

    fresh = copy.deepcopy(ledger)
    agreed = next(k for k, r in ledger["results"].items() if r["outcome"] == "agree")
    refused = next(k for k, r in ledger["results"].items() if r["outcome"] == "refused")
    fresh["results"][refused] = {"outcome": "agree"}
    fresh["results"]["coverage/new/case [apply]"] = {"outcome": "agree"}
    assert gate.problems(fresh, ledger)[0] == []
    f = next(iter(ledger["findings"]))
    fresh["results"][agreed] = {"outcome": "disagree", "findings": [f]}
    assert gate.problems(fresh, ledger)[0] == [f"{agreed}: validated, now disagree"]
