"""The engine facts (`characterization/<engine>/facts/*.json`) are well-formed:
each follows `fact.schema.json`, ids are unique and name their files, and the
files, probes and facts they point at exist."""

import json

import pytest

# A dev dependency: the installed wheel's tests go without it.
pytest.importorskip("jsonschema")

from sverify_dev import facts  # noqa: E402

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
    (root / "areas.json").write_text(facts.AREAS.read_text())
    fact = {
        "id": "duckdb-X1",
        "engine": "duckdb",
        "engine_version": "2.0.0",
        "title": "t",
        "area": "integers",
        "description": "d, see duckdb-X9",
        "status": "open",
        "options": ["overflow", "no_such_item"],
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
    assert "'no_such_item' is not an item of areas.json" in problems


def test_checklist_items_are_unique_and_cover_the_core_options():
    found = facts.checklist()
    items = [i for area in found.values() for i in area]
    assert len(items) == len(set(items))
    assert len(found) == 14
    areas = json.loads(facts.AREAS.read_text())["areas"]
    options = [i["id"] for a in areas for i in a["items"] if i["kind"] == "option"]
    assert len(options) == 39


def test_coverage_lists_facts_per_item(tmp_path):
    root = tmp_path / "characterization"
    (root / "polars" / "facts").mkdir(parents=True)
    (root / "areas.json").write_text(facts.AREAS.read_text())
    docs = {
        root / "polars" / "facts" / "polars-a.json": {
            "id": "polars-a", "engine": "polars", "options": ["overflow", "zero_sign"]
        },
        root / "polars" / "facts" / "polars-b.json": {
            "id": "polars-b", "engine": "polars", "options": ["overflow"],
            "superseded_by": "polars-a",
        },
        root / "duckdb" / "facts" / "duckdb-c.json": {
            "id": "duckdb-c", "engine": "duckdb", "options": ["division_type"]
        },
    }  # fmt: skip
    found = facts.coverage(docs, "polars", root)
    assert found["integers"]["overflow"] == ["polars-a"]
    assert found["doubles"]["zero_sign"] == ["polars-a"]
    assert found["integers"]["division_type"] == []
    text = facts.report(found)
    assert "  division_type: missing" in text
    assert text.endswith("2/62 items covered; gaps in: " + ", ".join(found))


def test_coverage_of_the_repository():
    found = facts.coverage(facts.load(), "duckdb")
    assert found["integers"]["overflow"]
    assert "items covered" in facts.report(found)
