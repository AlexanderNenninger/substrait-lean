"""The engine facts (`characterization/<engine>/facts/*.json`) are well-formed:
each follows `fact.schema.json`, ids are unique and name their files, and the
files, probes and facts they point at exist."""

import json

import pytest

from sverify_dev import facts

pytestmark = pytest.mark.skipif(
    not facts.SCHEMA.is_file(), reason="characterization/ of the repository is not here"
)


def test_facts_are_well_formed():
    docs = facts.load()
    assert len(docs) >= 30
    assert facts.validate(docs) == []


def test_validate_finds_problems(tmp_path):
    root = tmp_path / "characterization"
    (root / "duckdb" / "facts").mkdir(parents=True)
    (root / "fact.schema.json").write_text(facts.SCHEMA.read_text())
    fact = {
        "id": "duckdb-X1",
        "engine": "duckdb",
        "engine_version": "2.0.0",
        "title": "t",
        "area": "integers",
        "description": "d, see duckdb-X9",
        "status": "open",
        "provenance": [
            {
                "checked_at": "unknown",
                "method": "docs",
                "checked_by": "a session",
                "evidence": [{"file": "characterization/duckdb/missing.json"}],
            }
        ],
        "superseded_by": "duckdb-X2",
    }
    (root / "duckdb" / "facts" / "duckdb-X0.json").write_text(json.dumps(fact))
    bad = dict(fact, id="duckdb-X3", area="geometry")
    (root / "duckdb" / "facts" / "duckdb-X3.json").write_text(json.dumps(bad))
    problems = "\n".join(facts.validate(facts.load(root), root))
    assert "not named after its id" in problems
    assert "no file characterization/duckdb/missing.json" in problems
    assert "no fact duckdb-X2" in problems
    assert "names duckdb-X9" in problems
    assert "'geometry' is not one of" in problems


def test_overview_generates():
    """`--write` works on this branch. Whether each FACTS.md is current is not
    checked here: the `Generated files` workflow rewrites them on `main`, so
    feature branches leave them alone."""
    docs = facts.load()
    for engine in facts.engines():
        text = facts.render(engine, [f for f in docs.values() if f["engine"] == engine])
        assert all(f["id"] in text for f in docs.values() if f["engine"] == engine)
