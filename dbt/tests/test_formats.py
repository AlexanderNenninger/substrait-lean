"""`sverify-dbt check --format github|sarif|junit` (#891)."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

from sverify_dbt import formats
from sverify_dbt.cli import BUDGET, main
from sverify_dbt.result import CheckResult, ContractIssue, ModelResult, TestResult


def _result() -> CheckResult:
    def t(
        label: str, status: str, why: str | None = None, counterexample: str | None = None
    ) -> TestResult:
        return TestResult(None, None, label, "test", status, why, counterexample)

    ok = ModelResult("ok", "model.p.ok", "models/ok.sql", "ref('ok')")
    ok.tests = [t("unique(id)", "proved")]
    bad = ModelResult("bad", "model.p.bad", "models/bad.sql", "ref('bad')")
    bad.tests = [
        t("not_null(x)", "not proved", why="a row may be NULL", counterexample="x = NULL"),
        t("unique(y)", "not checked", why="the model was refused"),
    ]
    bad.contract = [ContractIssue("z", "declared int, found text")]
    refused = ModelResult(
        "rec", "model.p.rec", "models/rec.sql", "ref('rec')", refused="no WITH RECURSIVE"
    )
    return CheckResult("p", "/p", [ok, bad, refused], {})


def test_github_has_one_annotation_per_finding() -> None:
    lines = formats.github(_result()).splitlines()
    assert len(lines) == 4
    assert lines[0].startswith("::error file=models/bad.sql,title=sverify contract_mismatch")
    assert any("counterexample: x = NULL" in line.replace("%0A", "\n") for line in lines)
    assert any(line.startswith("::warning file=models/rec.sql") for line in lines)


def test_sarif_is_a_log_with_a_result_per_finding() -> None:
    log = json.loads(formats.sarif(_result(), "1.0"))
    run = log["runs"][0]
    assert log["version"] == "2.1.0" and len(run["results"]) == 4
    assert {r["ruleId"] for r in run["results"]} <= {
        r["id"] for r in run["tool"]["driver"]["rules"]
    }
    uris = {
        r["locations"][0]["physicalLocation"]["artifactLocation"]["uri"] for r in run["results"]
    }
    assert uris == {"models/bad.sql", "models/rec.sql"}


def test_junit_fails_what_is_not_proved_and_skips_what_is_not_checked() -> None:
    root = ET.fromstring(formats.junit(_result()))
    suites = {s.get("name"): s for s in root}
    assert suites["ok"].get("failures") == "0"
    assert suites["bad"].get("failures") == "2" and suites["bad"].get("skipped") == "1"
    assert suites["rec"].get("skipped") == "1"


def test_a_check_past_its_time_budget_exits_4(tmp_path, monkeypatch, capsys) -> None:
    from sverify.cli import _limits

    def slow(*args: object, **kw: object) -> None:
        raise _limits.BudgetExceeded("time", "1 s")

    monkeypatch.setattr("sverify_dbt.cli.check", slow)
    assert main(["check", str(tmp_path), "--timeout", "1"]) == BUDGET
    assert "time budget exceeded" in capsys.readouterr().err


def test_a_bad_memory_limit_is_a_usage_error(tmp_path, capsys) -> None:
    assert main(["check", str(tmp_path), "--memory-limit", "lots"]) == 2
    assert "memory limit" in capsys.readouterr().err


def test_the_time_budget_is_off_unless_asked_for(tmp_path, monkeypatch) -> None:
    from sverify_dbt.cli import _timeout_asked

    monkeypatch.delenv("SVERIFY_TIMEOUT", raising=False)
    assert not _timeout_asked(None)
    assert _timeout_asked(5.0)
    monkeypatch.setenv("SVERIFY_TIMEOUT", "60")
    assert _timeout_asked(None)


def _schema() -> dict:
    import sverify

    path = Path(sverify.__file__).parent / "schemas" / "cli.schema.json"
    return json.loads(path.read_text())


def test_the_json_is_sverifys_envelope_and_keeps_the_models(capsys, monkeypatch) -> None:
    """`--format json` prints `cli.schema.json`'s document (`format`, `exit`,
    `status`, `findings`, `error`) with the models beside it (#891, 1.5)."""
    jsonschema = pytest.importorskip("jsonschema")
    from sverify_dbt import cli

    monkeypatch.setattr(cli, "check", lambda *a, **k: _result())
    assert main(["check", ".", "--format", "json", "--fail-on", "unproved"]) == 1
    doc = json.loads(capsys.readouterr().out)
    jsonschema.validate(doc, _schema())
    assert (doc["format"], doc["command"], doc["exit"], doc["status"]) == (
        1,
        "check",
        1,
        "not_proved",
    )
    assert doc["error"] is None and {m["name"] for m in doc["models"]} == {"ok", "bad", "rec"}
    assert {f["code"] for f in doc["findings"]} >= {"may_be_false", "contract_mismatch"}
    assert all(f["nodes"] == [f["item"]] and f["line"] is None for f in doc["findings"])


def test_an_error_is_a_json_document_too(capsys, monkeypatch) -> None:
    jsonschema = pytest.importorskip("jsonschema")
    from sverify_dbt import cli

    def boom(*a: object, **k: object) -> None:
        raise FileNotFoundError("substrait-check is missing")

    monkeypatch.setattr(cli, "check", boom)
    assert main(["check", ".", "--json"]) == cli.ERROR
    doc = json.loads(capsys.readouterr().out)
    jsonschema.validate(doc, _schema())
    assert doc["status"] == "error" and doc["error"]["code"] == "error"
    assert "substrait-check is missing" in doc["error"]["message"]
