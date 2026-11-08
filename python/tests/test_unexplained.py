"""No recorded engine disagreement without an explanation (#747).

Each `disagree` entry of DuckDB's ledgers (`characterization/duckdb/<area>.json`:
the sqllogictest replay and `fuzz__<target>.json`) is explained by an open
issue, a fact or an upstream bug, through `sverify_dev.slt.KNOWN`. Spark's fuzz
ledger (`characterization/spark/fuzz.json`) keeps no finding, and each target
names the fact whose deviation it measures."""

import json
import re

import pytest

from _repo import ROOT, needs_repo
from sverify_dev import slt

pytestmark = [needs_repo, pytest.mark.backend("duckdb")]

FACTS = ROOT / "characterization"
BUGS = ROOT / "upstream" / "bugs"


def _disagreements() -> list[dict]:
    found = []
    for path in sorted((FACTS / "duckdb").glob("*.json")):
        ledger = json.loads(path.read_text())
        if isinstance(ledger, dict) and "results" in ledger:
            found += [r for r in ledger["results"] if r["cls"] == "disagree"]
    return found


def _exists(by: str) -> bool:
    if re.fullmatch(r"#\d+", by):
        return True
    if re.fullmatch(r"[A-Z]{2}-\d+", by):
        return (BUGS / f"{by}.json").is_file()
    return any(FACTS.glob(f"*/facts/{by}.json"))


def test_every_duckdb_disagreement_is_explained():
    unexplained = [
        f"{r['file']}:{r['line']} {r['sql'][:80]}"
        for r in _disagreements()
        if slt.explained_by(r) is None
    ]
    assert not unexplained, (
        f"{len(unexplained)} disagreement(s) without an issue, fact or upstream bug; "
        "add each to `sverify_dev.slt.KNOWN`:\n" + "\n".join(unexplained)
    )


def test_every_explanation_exists_and_is_used():
    results = _disagreements()
    for known in slt.KNOWN:
        assert _exists(known.by), f"{known.by}: no such fact or upstream bug"
        assert any(known.matches(r) for r in results), f"{known}: explains no disagreement"


def test_spark_fuzz_has_no_finding():
    ledger = json.loads((FACTS / "spark" / "fuzz.json").read_text())
    for name, target in ledger.items():
        if name == "_meta":
            continue
        assert not target["findings"], f"{name}: Spark differs from {target['fact']}"
        assert _exists(target["fact"]), f"{name}: no fact {target['fact']}"
