"""The upstream bugs (`upstream/bugs/*.json`) are well-formed: each follows
`bug.schema.json`, ids are unique, name their files and match their project,
and the files and engine facts they link to exist. Each test of the lift's
backlog (`tests/lift_backlog.json`) exists and has a reason."""

import json
import shutil

import pytest

# A dev dependency: the installed wheel's tests go without it.
pytest.importorskip("jsonschema")

from sverify_dev import bugs, facts  # noqa: E402

pytestmark = pytest.mark.skipif(
    not bugs.SCHEMA.is_file() or not facts.SCHEMA.is_file(),
    reason="upstream/ and characterization/ of the repository are not here",
)


def test_bugs_are_well_formed():
    docs = bugs.load()
    assert len(docs) >= 23
    assert bugs.validate(docs) == []


def test_lift_backlog_is_well_formed():
    assert bugs.validate_backlog() == []


def _bug(**changes):
    bug = {
        "id": "DD-1",
        "project": "duckdb",
        "version": "2.0.0",
        "status": "confirmed",
        "status_note": "confirmed on 2.0.0",
        "summary": "s",
        "repro": "r",
        "found_by": "a probe",
        "files": ["python/missing.py"],
        "facts": ["duckdb-X9"],
        "checked": [{"checked_at": "2026-11-03", "against": {"duckdb": "2.0.0"}}],
    }
    return bug | changes


def test_validate_finds_problems(tmp_path):
    root = tmp_path / "upstream"
    (root / "bugs").mkdir(parents=True)
    (tmp_path / "characterization").mkdir()
    shutil.copy(facts.SCHEMA, tmp_path / "characterization" / facts.SCHEMA.name)
    shutil.copy(bugs.SCHEMA, root / bugs.SCHEMA.name)
    docs = {
        "DD-0": _bug(),
        "SG-1": _bug(id="SG-1"),
        "DD-2": _bug(id="DD-2", status="filed"),
        "DD-3": _bug(id="DD-3", status="fixed upstream"),
        "DD-4": _bug(id="DD-4", status="wontfix"),
        "DD-5": _bug(id="DD-5", kind="spec-gap"),
    }
    for name, doc in docs.items():
        (root / "bugs" / f"{name}.json").write_text(json.dumps(doc))
    problems = "\n".join(bugs.validate(bugs.load(root), root))
    assert "not named after its id" in problems
    assert "a duckdb bug's id starts with DD-" in problems
    assert "no file python/missing.py" in problems
    assert "no fact duckdb-X9" in problems
    assert "'upstream' is a required property" in problems
    assert "'fixed_in' is a required property" in problems
    assert "'wontfix' is not one of" in problems
    assert "only Substrait's entries are spec gaps" in problems
    assert "a bug to report has a title" in problems


def test_classify():
    assert bugs.classify(_bug()) == "report"
    assert bugs.classify(_bug(status="fixed upstream")) == "fixed"
    assert bugs.classify(_bug(status="not a bug")) == "not-a-bug"
    assert bugs.classify(_bug(id="ST-1", project="substrait", kind="spec-gap")) == "spec-gap"


def test_report_renders():
    """`upstream/REPORT.md` renders on this branch: every bug to report has a
    row, and the classes add up to the ledger. Whether the committed file is
    current is not checked here: the `Generated files` workflow rewrites it on
    `main`, so feature branches leave it alone."""
    docs = bugs.load()
    text = bugs.render(docs)
    assert text.startswith("# Upstream report")
    for b in docs.values():
        if bugs.classify(b) == "report":
            assert f"| [{b['id']}](bugs/{b['id']}.json) |" in text
    (total,) = [line for line in text.splitlines() if line.startswith("| total |")]
    assert total.endswith(f"| {len(docs)} |")


def test_validate_backlog_finds_problems(tmp_path):
    tests = tmp_path / "tests"
    tests.mkdir()
    source = "class TestA:\n    def test_b(self): ...\n\ndef test_c(): ...\n"
    (tests / "test_x.py").write_text(source)
    backlog = tests / "lift_backlog.json"
    entries = [
        {"test": "tests/test_x.py::TestA::test_b[p]", "reason": "r"},
        {"test": "tests/test_x.py::test_c", "reason": "r"},
        {"test": "tests/test_x.py::test_c", "reason": "r"},
        {"test": "tests/test_x.py::test_d", "reason": "r"},
        {"test": "tests/test_y.py::test_c", "reason": "r"},
    ]
    backlog.write_text(json.dumps({"tests": entries}))
    assert bugs.validate_backlog(backlog) == [
        "lift_backlog.json: tests/test_x.py::test_c repeats",
        "lift_backlog.json: tests/test_x.py::test_d: tests/test_x.py has no def test_d",
        "lift_backlog.json: tests/test_y.py::test_c: no test file tests/test_y.py",
    ]
    backlog.write_text(json.dumps({"tests": [{"test": "tests/test_x.py::test_c"}]}))
    assert "'reason' is a required property" in "\n".join(bugs.validate_backlog(backlog))
