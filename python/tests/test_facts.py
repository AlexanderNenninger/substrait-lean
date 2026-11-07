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
        "evidence": "probe",
        "options": ["overflow", "no_such_item"],
        "rows": [
            {"group": "int.arith", "option": "overflow", "types": ["i64", "fp64"]},
            {"group": "int.arith", "option": "zero_sign", "types": ["i64"]},
            {"group": "int.mod", "option": "division_type", "types": ["i64"]},
            {"group": "int.mod", "option": "overflow", "types": ["i8"], "evidence": "fuzz"},
            {"group": "int.mod", "option": "division_type", "types": ["i64"]},
        ],
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
    assert "evidence is 'probe'; its provenance's strongest is 'docs'" in problems
    assert "int.arith × overflow has no type 'fp64'" in problems
    assert "int.arith × zero_sign is not a row of the choice tables" in problems
    assert "rows name 'division_type', which options lack" in problems
    assert "int.mod × overflow's evidence 'fuzz' is stronger than the fact's" in problems
    assert "rows name int.mod × division_type × i64 twice" in problems


def test_checklist_items_are_unique_and_cover_the_core_options():
    found = facts.checklist()
    items = [i for area in found.values() for i in area]
    assert len(items) == len(set(items))
    assert len(found) == 15
    assert found["execution"][0] == "evaluation_order"
    areas = json.loads(facts.AREAS.read_text())["areas"]
    options = [i["id"] for a in areas for i in a["items"] if i["kind"] == "option"]
    assert len(options) == 40


def test_coverage_lists_facts_per_item(tmp_path):
    root = tmp_path / "characterization"
    (root / "polars" / "facts").mkdir(parents=True)
    (root / "areas.json").write_text(facts.AREAS.read_text())
    docs = {
        root / "polars" / "facts" / "polars-a.json": {
            "id": "polars-a", "engine": "polars", "options": ["overflow", "zero_sign"],
            "evidence": "source",
            "rows": [
                {"group": "int.arith", "option": "overflow", "types": ["i64"]},
                {"group": "int.arith", "option": "overflow", "types": ["i32"], "evidence": "docs"},
            ],
        },
        root / "polars" / "facts" / "polars-b.json": {
            "id": "polars-b", "engine": "polars", "options": ["overflow"],
            "superseded_by": "polars-a", "evidence": "probe",
            "rows": [{"group": "int.arith", "option": "overflow", "types": ["i8"]}],
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
    assert text.endswith("2/70 items covered; gaps in: " + ", ".join(found))
    rows = facts.row_coverage(docs, "polars", root)
    assert rows[("int.arith", "overflow", "i64")] == [("polars-a", "source")]
    assert rows[("int.arith", "overflow", "i8")] == []
    assert ("-", "null_order", "any") in rows
    text = facts.row_report(rows, root)
    assert "  i8: missing" in text
    assert "  i64: polars-a (source)" in text
    assert rows[("int.arith", "overflow", "i32")] == [("polars-a", "docs")]
    assert text.endswith(f"2/{len(rows)} rows settled")


def test_rows_follow_the_groups_of_functions_lean():
    groups = facts.groups()
    assert groups["int.mod"][:2] == ["overflow", "on_division_by_zero"]
    rows = facts.rows()
    assert len(rows) == len(set(rows))
    assert ("int.arith", "overflow", "i8") in rows
    assert ("fp.arith", "zero_sign", "fp32") in rows
    assert ("agg.order", "list_null_order", "list") in rows
    assert ("agg.order", "list_null_order", "fp64") not in rows


def test_evidence_is_the_strongest_method():
    fact = {"provenance": [{"method": "docs"}, {"method": "replay"}, {"method": "source-reading"}]}
    assert facts.evidence_of(fact) == "engine_test"
    fact["provenance"].append({"method": "manual-repro"})
    assert facts.evidence_of(fact) == "probe"
    assert facts.evidence_of({"provenance": [{"method": "fuzz"}, {"method": "proof"}]}) == "proof"


def test_coverage_of_the_repository():
    found = facts.coverage(facts.load(), "duckdb")
    assert found["integers"]["overflow"]
    assert "items covered" in facts.report(found)
    assert "rows settled" in facts.row_report(facts.row_coverage(facts.load(), "duckdb"))
