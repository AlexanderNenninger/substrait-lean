"""The engine release canary (#2053, `sverify_dev.canary`): which engines have an unprobed
release, how a probe's drift is classed, and the issue it files."""

import json

import pytest

from _repo import needs_repo
from sverify_dev import canary


@needs_repo
# A parameter named `engine` would select that backend (`tests/conftest.py`).
@pytest.mark.parametrize("name", sorted(canary.ENGINES))
def test_the_probed_versions_are_read_from_the_profile_table(name: str) -> None:
    versions = canary.probed(name)
    assert versions and all(canary.is_release(v) for v in versions)


def test_alsoprobed_adds_versions(tmp_path) -> None:
    t = tmp_path / canary.ENGINES["duckdb"]["tables"]
    t.parent.mkdir(parents=True)
    t.write_text('  version := "2.0.0"\n  alsoProbed := ["2.0.1", "2.0.2"]\n')
    assert canary.probed("duckdb", tmp_path) == ["2.0.0", "2.0.1", "2.0.2"]


@needs_repo
def test_a_new_release_is_one_nobody_probed() -> None:
    have = {e: canary.probed(e) for e in canary.ENGINES}
    newest = {e: max(v, key=canary._key) for e, v in have.items()}

    def latest(package: str) -> str:
        engine = next(e for e, s in canary.ENGINES.items() if s["package"] == package)
        return newest[engine]

    assert canary.new_releases(latest) == []

    def bumped(package: str) -> str:
        v = latest(package).split(".")
        return ".".join([*v[:-1], str(int(v[-1]) + 1)])

    assert {t["engine"] for t in canary.new_releases(bumped)} == set(canary.ENGINES)


def test_pre_releases_are_not_releases() -> None:
    assert [canary.is_release(v) for v in ("2.0.1", "2.1", "2.1.0rc1", "2.1.0.dev3")] == [
        True,
        True,
        False,
        False,
    ]


@pytest.mark.parametrize(
    ("old", "new", "cls"),
    [
        ("error InvalidInputException: Division by zero", "1", "error-side"),
        ("1", "error Out of Range", "error-side"),
        ("1", "2", "value-side"),
        ("", "1", "value-side"),
    ],
)
def test_a_raise_that_appears_or_goes_is_error_side(old: str, new: str, cls: str) -> None:
    assert canary.classify(old, new) == cls


def _doc(**rows: dict) -> dict:
    return {
        "duckdb": "x",
        "probes": [{"construct": c, "sql": "SELECT 1", **r} for c, r in rows.items()],
    }


def test_drift_names_each_changed_row_and_its_class() -> None:
    old = _doc(a={"observed": "error E: boom"}, b={"matching": ["ERROR"]}, c={"observed": "1"})
    new = _doc(a={"observed": "1"}, b={"matching": ["NULL"]}, c={"observed": "1"})
    found = {d["row"]["construct"]: d["class"] for d in canary.drift(old, new)}
    assert found == {"a": "error-side", "b": "value-side"}


def test_drift_sees_a_row_that_appears_or_vanishes() -> None:
    old = _doc(a={"observed": "1"})
    new = _doc(b={"observed": "1"})
    assert sorted(d["row"]["construct"] for d in canary.drift(old, new)) == ["a", "b"]
    assert canary.drift(old, old) == []


@needs_repo
def test_the_recorded_probes_do_not_drift_from_themselves() -> None:
    for engine, files in canary.PROBES.items():
        for f in files:
            doc = json.loads((canary.REPO / f).read_text())
            assert canary.drift(doc, doc) == [], (engine, f)


def test_the_ledger_lists_the_bugs_a_release_fixes(tmp_path) -> None:
    d = tmp_path / "upstream" / "bugs"
    d.mkdir(parents=True)
    for i, fixed in (("DD-1", "2.0.1"), ("DD-2", "2.0.10"), ("DD-3", "2.0.1 (unreleased)")):
        (d / f"{i}.json").write_text(
            json.dumps(
                {"id": i, "project": "duckdb", "status": "fixed upstream", "fixed_in": fixed}
            )
        )
    (d / "PL-1.json").write_text(
        json.dumps({"id": "PL-1", "project": "polars", "fixed_in": "2.0.1"})
    )
    assert [b["id"] for b in canary.ledger("duckdb", "2.0.1", tmp_path)] == ["DD-1", "DD-3"]


def test_the_issue_says_value_side_drift_is_a_bug() -> None:
    value = {
        "row": {"construct": "x"},
        "field": "observed",
        "old": "1",
        "new": "2",
        "class": "value-side",
    }
    text = canary.body(
        "duckdb", "2.0.2", {"probed": ["2.0.0", "2.0.1"], "drift": [value], "suite": {"exit": 0}}
    )
    assert "this is a bug" in text and "value-side" in text


def test_a_clean_run_names_the_one_line_change() -> None:
    text = canary.body(
        "duckdb", "2.0.2", {"probed": ["2.0.0"], "suite": {"exit": 0}, "outside": {"exit": 0}}
    )
    assert "No value-side drift" in text and 'alsoProbed := [..., "2.0.2"]' in text


def test_a_failing_suite_is_a_bug_too() -> None:
    text = canary.body("polars", "2.1.1", {"probed": ["2.1.0"], "suite": {"exit": 1}})
    assert "failing step(s): suite" in text


@needs_repo
def test_collect_gathers_the_steps_of_the_heavy_job(tmp_path) -> None:
    drift = tmp_path / "drift.json"
    drift.write_text(
        json.dumps([{"row": {"construct": "x"}, "class": "error-side", "old": "error", "new": "1"}])
    )
    log = tmp_path / "suite.log"
    log.write_text("\n".join(f"line {i}" for i in range(50)))
    out = canary.collect("duckdb", "9.9.9", [drift], (1, log), (0, None))
    assert out["drift"][0]["class"] == "error-side"
    assert out["suite"]["exit"] == 1 and out["suite"]["summary"].endswith("line 49")
    assert out["outside"] == {"exit": 0, "summary": ""}
    assert out["ledger"] == []
