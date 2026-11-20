"""The ledgers of the replay of Ibis's own backend tests (#860,
`sverify_dev.ibis_replay`).

The replay itself needs Ibis's sources and test data, which CI's `evidence`
job fetches; these tests read the ledgers it writes."""

from __future__ import annotations

import json
import re

import pytest

from _repo import needs_repo
from sverify_dev import ibis_replay as replay

pytestmark = needs_repo


@pytest.fixture(scope="module")
def ledgers() -> dict[str, dict]:
    return {p.stem: json.loads(p.read_text()) for p in sorted(replay.LEDGERS.glob("test_*.json"))}


def test_one_ledger_per_module(ledgers) -> None:
    assert set(ledgers) == set(replay.MODULES)
    for module, led in ledgers.items():
        assert led["module"] == module
        assert led["ibis"] == replay.IBIS_TAG
        assert led["license"] == "Apache-2.0"
    assert (replay.LEDGERS / "LICENSE-ibis").read_text().strip().startswith("Apache License")


def test_ibis_is_the_release_the_lock_pins() -> None:
    lock = (replay.ROOT / "python" / "uv.lock").read_text()
    m = re.search(r'name = "ibis-framework"\nversion = "([^"]+)"', lock)
    assert m and m[1] == replay.IBIS_TAG


def test_summaries_count_the_results(ledgers) -> None:
    for led in ledgers.values():
        counts = {k: 0 for k in replay.OUTCOMES}
        for r in led["results"].values():
            counts[r["outcome"]] += 1
        assert led["summary"] == counts


def test_no_disagreement_without_an_issue(ledgers) -> None:
    """A proved expression that gives other rows than Ibis's is a soundness
    question: it is fixed, or its entry names the issue."""
    for module, led in ledgers.items():
        for test, r in led["results"].items():
            if r["outcome"] == "disagree":
                assert r.get("issue"), f"{module}::{test}: {r['reason']}"


def test_every_refusal_waits_on_an_issue_or_is_by_design(ledgers) -> None:
    for module, led in ledgers.items():
        for test, r in led["results"].items():
            if r["outcome"] == "refused":
                assert r.get("issue") or r.get("design"), f"{module}::{test}: {r['construct']}"


def test_every_construct_entry_is_used(ledgers) -> None:
    """`constructs.json` lists only what the ledgers meet."""
    refused = [
        r["construct"]
        for led in ledgers.values()
        for r in led["results"].values()
        if r["outcome"] == "refused"
    ]
    for c in json.loads(replay.CONSTRUCTS.read_text())["constructs"]:
        assert any(c["match"] in x for x in refused), c["match"]
        assert ("issue" in c) != ("design" in c), c


def test_normalize_keeps_the_issue_and_drops_the_numbers() -> None:
    assert replay.normalize("lambdas have no SQL form yet (#1234), 12 rows") == (
        "lambdas have no SQL form yet (#1234), N rows"
    )


def test_rows_compare_as_multisets_with_doubles_to_twelve_digits() -> None:
    import pyarrow as pa

    a = pa.table({"x": [1.0, 0.1 + 0.2, float("nan")], "s": ["a", "b", None]})
    b = pa.table({"x": [0.3, float("nan"), 1.0], "s": ["b", None, "a"]})
    assert replay.same(a, b) is None
    assert replay.same(a, b.slice(0, 2)) == "3 rows, Ibis 2"
